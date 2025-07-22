/-
Copyright (c) 2025 Arthur Adjedj. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Adjedj
-/
import Lean.Meta.ExprDefEq
import Lean.Meta.CollectFVars
import Lean.Meta.DiscrTree
namespace Lean.Meta

def alterRewriteRule (head declName : Name) (tree : Kernel.RewriteRuleTree): Kernel.RewriteRuleTree :=
  tree.alter head (fun | none => #[declName] | some arr => arr.push declName)

-- TODO check/add rewrite rule
-- @[export lean_environment_add_rewrite_rule]
-- def addRewriteRule (env : Environment) (_const : Name) : Environment := env
-- (no need to check that both lhs and rhs are neutrals, worst case scenario, the rule will never trigger)
-- TODO implement a local confluence checker ?
def addAndCheckRewriteRule (declName : Name) : MetaM Unit := do
  withNewMCtxDepth do
    let cinfo ← getConstInfo declName
    let us ← cinfo.levelParams.mapM fun _ => mkFreshLevelMVar
    let type ← instantiateTypeLevelParams cinfo.toConstantVal us
    let (xs,_bids,type) ← forallMetaTelescope type
    match type.eq? with
    | none => throwError m!"Error when trying to add new rewrite rule \\
        The inferred type {indentExpr type} of {declName} should be of the form `(A₁ : A₁) → ... → (aₙ : Aₙ) → x = y`"
    | some (_,lhs,rhs) =>
        let lhs_mvars := Expr.collectMVars {} lhs
        unless (xs.all (lhs_mvars.result.contains ·.mvarId!)) do
          throwError "Cannot add {declName} as a rewrite rule: \\ Some variables introduced do not appear in the left-hand-side of the equality."
        unless !(← Meta.isDefEq lhs rhs) do
          throwError m!"Cannot add {declName} as a rewrite rule: \\ The two sides of the equality are already definitionally equal."
        -- let lhs ← whnf lhs
        let headName := lhs.getAppFn.constName?.getD Name.anonymous
        trace[Meta.IsDefEq.RewriteRule.add] "Adding {declName} indexed by {headName}"
        modifyEnv (·.addRewriteRule (alterRewriteRule headName declName))
        resetCache

partial def matchAgainstPattern (e lhs : Expr) (addedFVars : Array Expr := #[]) (map : Std.HashMap Expr Expr := {}) : MetaM (Option (Std.HashMap Expr Expr)) :=
  withIncRecDepth do
  withTraceNode `Meta.IsDefEq.RewriteRule
      (return m!"{exceptBoolEmoji <| ·.map Option.isSome} matchAgainstPattern {e} ≟ {lhs} ({addedFVars} {map.toArray})") do
  let fe := e.getAppFn
  let argse := e.getAppArgs
  let flhs := lhs.getAppFn
  let argslhs := lhs.getAppArgs
  if argslhs.size != argse.size then
  -- TODO do proper eta-expansion when possible
    return none
  let head_map ← go fe flhs addedFVars map
  match head_map with
    | none => return none
    | some map => do
      let mut res := map
      for i in [:argslhs.size] do
        if let some map ← matchAgainstPattern (← whnf argse[i]!) (← whnf argslhs[i]!) #[] res then
          res := map
        else
          return none
      return res
where
  go (e lhs : Expr) (addedFVars : Array Expr) (map : Std.HashMap Expr Expr) : MetaM (Option (Std.HashMap Expr Expr)) := do
    withTraceNode `Meta.IsDefEq.RewriteRule
      (return m!"{exceptBoolEmoji <| ·.map Option.isSome} go {e} ≟ {lhs} ({addedFVars} {map.toArray})") do
    -- TODO manage projections, ensure mdata is stripped
    match e , lhs with
      | .sort u, .sort v =>
        unless (← isLevelDefEq u v) do return none
        return map
      | .const ne use, .const nlhs uslhs =>
        unless (ne == nlhs) && (← isListLevelDefEqAux use uslhs) do return none
        return map
      | _,.fvar _ =>
        if (addedFVars.contains lhs) then
          trace[Meta.IsDefEq.RewriteRule] "lhs is in addedFVars"
          if (e == lhs) then
            return map
          else
            return none
        match map[lhs]? with
          | none =>
            let map := map.insert lhs e
            trace[Meta.IsDefEq.RewriteRule] "mapping fvar {lhs} to {e} : {map.toArray}"
            return map
          | some y =>
            -- TODO use DefEq here ?
            unless (e == y) do
              trace[Meta.IsDefEq.RewriteRule] "Failure, fvar {lhs} needs to be mapped to both {e} and {y}"
              return none
            trace[Meta.IsDefEq.RewriteRule] "{lhs} is already in the map"
            return map
      | .forallE ne de be bi, .forallE _ dlhs blhs _  =>
        let some map ← matchAgainstPattern (← whnf de) (← whnf dlhs) addedFVars map | return none
        withLocalDecl ne bi de fun fvar => do
          matchAgainstPattern (← whnf <| be.instantiate1 fvar) (← whnf <| blhs.instantiate1 fvar) (addedFVars.push fvar) map
      | .lam ne de be bi, .lam _ dlhs blhs _ =>
        let some map ← matchAgainstPattern (← whnf de) (← whnf dlhs) addedFVars map | return none
        withLocalDecl ne bi de fun fvar => do
          matchAgainstPattern (← whnf <| be.instantiate1 fvar) (← whnf <| blhs.instantiate1 fvar) (addedFVars.push fvar) map
      | .lit le, .lit llhs =>
        unless le == llhs do
          return none
        return map
      | _,_ =>
        trace[Meta.IsDefEq.RewriteRule] "matching failure : {e} ≟ {lhs}"
        return none

@[export lean_rewrite]
def rewrite?Impl (e : Expr) : MetaM (Option Expr) :=
  withIncRecDepth do
  withTraceNode `Meta.IsDefEq.RewriteRule
    (return m!"{exceptBoolEmoji <| ·.map Option.isSome} Trying to rewrite {indentExpr e}") do
  let head := e.getAppFn.constName?.getD Name.anonymous
  trace[Meta.IsDefEq.RewriteRule] "Head : {head}"
  let some candidates := (← getEnv).toKernelEnv.rewriteRulesTree[head]? | return none
  trace[Meta.IsDefEq.RewriteRule] "Candidates : {candidates}"
  for candidate in candidates do
    let cinfo ← getConstInfo candidate
    let us ← cinfo.levelParams.mapM fun _ => mkFreshLevelMVar
    let type ← instantiateTypeLevelParams cinfo.toConstantVal us
    let rhs? ← forallTelescope type fun xs type => do
      let some (_,lhs,rhs) := type.eq? | unreachable!
      let some map ← matchAgainstPattern e lhs | return none
      trace[Meta.IsDefEq.RewriteRule] "FVars : {xs} \\ Mappings : {map.toArray} "
      let patternInst := xs.map (fun fvar => map[fvar]!)
      return some <| rhs.replaceFVars xs patternInst
    if let some rhs := rhs? then
      let rhs ← whnf rhs
      trace[Meta.IsDefEq.RewriteRule] "{e} ⇒ {rhs}"
      return rhs
  return none

builtin_initialize
  registerBuiltinAttribute {
    name  := `rewrite_rule
    descr := "rewrite rule"
    add   := fun declName stx kind => do
      Attribute.Builtin.ensureNoArgs stx
      discard <| addAndCheckRewriteRule declName |>.run
  }


  registerTraceClass `Meta.IsDefEq.RewriteRule
  registerTraceClass `Meta.IsDefEq.RewriteRule.add
end Lean.Meta
