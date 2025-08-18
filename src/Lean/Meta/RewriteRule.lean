/-
Copyright (c) 2025 Arthur Adjedj. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Adjedj
-/
import Lean.Meta.ExprDefEq
import Lean.Meta.CollectFVars
import Lean.Meta.DiscrTree
import Lean.Meta.AppBuilder
import Lean.Elab.Term
namespace Lean.Meta.RewriteRule

open Elab.Term
def alterRewriteRule (head : Name) (candidate : Kernel.RewriteCandidate) (tree : Kernel.RewriteRuleTree): Kernel.RewriteRuleTree :=
  tree.alter head (fun | none => #[candidate] | some arr => arr.push candidate)

/-- If the head is not a constant, we simply index the tree by `Name.anonymous`, which should never appear in real terms
    TODO use better discrimination techniques to be more accurate/try less rewrite rules ?
-/
def rewriteRuleTreeKeyOf (e : Expr) : Name :=
  e.getAppFn.constName?.getD Name.anonymous

-- TODO check that the head is a non-reducible constant, i.e not a recursor/def ?
def isValidNeutralHead (e : Expr) : Bool :=
  if e.isFVar || e.isApp then false
  else true

-- @[export lean_environment_add_rewrite_rule]
-- def addRewriteRule (env : Environment) (_const : Name) : Environment := env
-- (no need to check that both lhs and rhs are neutrals, worst case scenario, the rule will never trigger)
-- TODO implement a local confluence checker ?
def addAndCheckRewriteRule (declName : Name) : TermElabM Unit := do
  withNewMCtxDepth do
    let cinfo ← getConstInfo declName
    withLevelNames cinfo.levelParams do
    let us := cinfo.levelParams.map mkLevelParam
    let type ← instantiateTypeLevelParams cinfo.toConstantVal us
    forallTelescopeReducing type fun xs type => do
      match type.eq? with
      | none => throwError m!"Error when trying to add new rewrite rule \
          The inferred type {indentExpr type} of {declName} should be of the form `(A₁ : A₁) → ... → (aₙ : Aₙ) → x = y`"
      | some (_,lhs,rhs) =>
          let (_,lhs_fvars) ← Expr.collectFVars lhs |>.run {}
          let tooFreeFVars := xs.filter (!lhs_fvars.fvarIds.contains ·.fvarId!)
          unless tooFreeFVars.isEmpty do
            throwError "Cannot add {declName} as a rewrite rule: \
             The following variables do not appear in the left-hand-side of the equality: {tooFreeFVars}"
          if (← Meta.isDefEq lhs rhs) then
            throwError m!"Cannot add {declName} as a rewrite rule: \
             The two sides of the equality are already definitionally equal."
          let lhs ← whnf lhs
          unless isValidNeutralHead lhs.getAppFn do
            throwError m!"Invalid rewrite rule: left-hand side of equality cannot be matched on."
          let headName := rewriteRuleTreeKeyOf lhs
          trace[Meta.IsDefEq.RewriteRule.add] "Adding {declName} indexed by {headName}"
          let type ← mkAppM ``Eq #[lhs, rhs]
          let type ← mkForallFVars xs type
          modifyEnv (·.addRewriteRule (alterRewriteRule headName {declName, expr := type }))
          resetCache

abbrev Subst := Std.HashMap Expr Expr

structure Context where
  addedFVars : Array Expr := #[]
  subst? : Option Subst := some {}

abbrev MatchM := StateT Context MetaM

def addFVar (fvar: Expr): MatchM Unit := do
  modify (fun ctx => {ctx with addedFVars := ctx.addedFVars.push fvar})

def withSubst (k : Subst → MatchM Unit) : MatchM Unit := do
  let some subst := (← get).subst? | return
  k subst

def noSubst : MatchM Unit := do
  modify (fun ctx => { ctx with subst? := none})

partial def matchAgainstPattern (e lhs : Expr) : MatchM Unit := do
  withIncRecDepth do
  -- withTraceNode `Meta.IsDefEq.RewriteRule
      -- (return m!"{exceptBoolEmoji <| (← get).addedFVars.isSome} matchAgainstPattern {e} ≟ {lhs} ({(← get).addedFVars} {(← get).addedFVars})") do
  let flhs := lhs.getAppFn
  let argslhs := lhs.getAppArgs
  let fe := e.getBoundedAppFn argslhs.size
  let argse := e.getBoundedAppArgs argslhs.size
  if argslhs.size != argse.size then
    noSubst
    return
  unless isValidNeutralHead fe do
    noSubst
    return
  go fe flhs
  withSubst fun _ => do
      for i in [:argslhs.size] do
        matchAgainstPattern (← whnf argse[i]!) argslhs[i]!
where
  go (e lhs : Expr) : MatchM Unit := do
    withTraceNode `Meta.IsDefEq.RewriteRule
      (fun exn => do
        let ctx ← get
        let exn := exn.map (fun _ => ctx.subst?.isSome)
        return m!"{exceptBoolEmoji <|exn} go {e} ≟ {lhs} ({ctx.addedFVars} {ctx.addedFVars})") do
    match e.consumeMData , lhs.consumeMData with
      | .sort u, .sort v =>
        if !(← isLevelDefEq u v) then
          noSubst
      | .const ne use, .const nlhs uslhs =>
        if !(ne == nlhs) || !(← isListLevelDefEqAux use uslhs) then
          noSubst
      | .lit le, .lit llhs =>
        if !le != llhs then
          noSubst
      | _,.fvar _ =>
        if ((← get).addedFVars.contains lhs) then
          if (e == lhs) then
            return
          else
            noSubst
        withSubst fun subst =>
          match subst[lhs]? with
          | none =>
            modify (fun ctx => {ctx with subst? := subst.insert lhs e})
          | some y =>
            -- TODO only use syntactic equality here ?
            unless (← isDefEq e y) do
              noSubst
      | .forallE ne de be bi, .forallE _ dlhs blhs _  =>
        matchAgainstPattern (← whnf de) dlhs
        withSubst fun _ =>
        withLocalDecl ne bi de fun fvar => do
          addFVar fvar
          matchAgainstPattern (← whnf <| be.instantiate1 fvar) (blhs.instantiate1 fvar)
      | .lam ne de be bi, .lam _ dlhs blhs _ =>
        matchAgainstPattern (← whnf de) dlhs
        withSubst fun _ =>
        withLocalDecl ne bi de fun fvar => do
          addFVar fvar
          matchAgainstPattern (← whnf <| be.instantiate1 fvar) (blhs.instantiate1 fvar)
      | .proj ne ie struct, .proj nlhs ilhs structlhs =>
          if ne != nlhs || ie != ilhs then
            noSubst
          matchAgainstPattern (← whnf struct) structlhs
      | _,_ =>
        trace[Meta.IsDefEq.RewriteRule] "matching failure : {e} ≟ {lhs}"
        noSubst

-- TODO defeq check between type of (substituted) rewrite-rule triggered and original term
-- TODO type-directed rewrite ? match first against types or rwrule/term and only then extend the substitution to the term ?
-- Might lead to faster aborting of a tentative match, easier matching on universes
-- Will make working with eta/proof-irrelevance easier too
@[export lean_rewrite]
def rewrite?Impl (e : Expr) : MetaM (Option Expr) :=
  withIncRecDepth do
  withTraceNode `Meta.IsDefEq.RewriteRule
    (return m!"{exceptBoolEmoji <| ·.map Option.isSome} Trying to rewrite {indentExpr e}") do
  let headName := rewriteRuleTreeKeyOf e
  trace[Meta.IsDefEq.RewriteRule] "Head : {headName}"
  let some candidates := (← getEnv).toKernelEnv.rewriteRulesTree[headName]? | return none
  trace[Meta.IsDefEq.RewriteRule] "Candidates : {candidates.map Kernel.RewriteCandidate.declName}"
  for candidate in candidates do
    let cinfo ← getConstInfo candidate.declName
    let us ← cinfo.levelParams.mapM fun _ => mkFreshLevelMVar
    let type := candidate.expr.instantiateLevelParams cinfo.levelParams us
    let rhs? ← forallTelescope type fun xs type => do
      let some (_,lhs,rhs) := type.eq? | unreachable!
      let (_,ctx) ← matchAgainstPattern e lhs |>.run {}
      let some subst := ctx.subst? | return none
      trace[Meta.IsDefEq.RewriteRule] "FVars : {xs} \\ Mappings : {subst.toArray} "
      let patternInst := xs.map (fun fvar => subst[fvar]!)
      return some <| rhs.replaceFVars xs patternInst
    if let some rhs := rhs? then
      let rhs ← whnf rhs
      trace[Meta.IsDefEq.RewriteRule] "{e} ⇒ {rhs}"
      recordUnfold headName
      return rhs
  return none

builtin_initialize
  registerBuiltinAttribute {
    name  := `rewrite_rule
    descr := "rewrite rule"
    add   := fun declName stx kind => do
      Attribute.Builtin.ensureNoArgs stx
      discard <| addAndCheckRewriteRule declName |>.run |>.run
  }

  registerTraceClass `Meta.IsDefEq.RewriteRule
  registerTraceClass `Meta.IsDefEq.RewriteRule.add
end Lean.Meta.RewriteRule
