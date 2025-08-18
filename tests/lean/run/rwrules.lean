import Lean
set_option debug.skipKernelTC true

open Lean PrettyPrinter Delaborator SubExpr

noncomputable section
axiom Ctx: Type
axiom Subs : Ctx → Ctx → Type
axiom Ty : Ctx → Type
axiom Tm : {Γ : Ctx} → Ty Γ → Type

axiom ε : Ctx
axiom snoc : (Γ : Ctx) → Ty Γ → Ctx
infixl:62 "▹" => snoc

axiom subsTy (A : Ty Γ) (σ : Subs Δ Γ): Ty Δ

syntax:max term noWs "[" withoutPosition(term) "]₁" : term
macro_rules | `($x[$i]₁) => `(subsTy $x $i)
@[delab app.subsTy]
def delabfooFinal : Delab := do
  let e ← getExpr
  guard $ e.isAppOfArity' `subsTy 4 -- only delab full applications this way
  let args := e.getAppArgs
  let A ← delab args[2]!
  let σ ← delab args[3]!
  `($A[$σ]₁)

axiom subsTm (A : Ty Γ) (t : Tm A) (σ : Subs Δ Γ): Tm A[σ]₁

syntax:max term noWs "[" withoutPosition(term) "]₂" : term
macro_rules | `($x[$i]₂) => `(subsTm _ $x $i)

@[delab app.subsTm]
def delabbarFinal : Delab := do
  let e ← getExpr
  guard $ e.isAppOfArity' `subsTm 5 -- only delab full applications this way
  let args := e.getAppArgs
  let A ← delab args[3]!
  let σ ← delab args[4]!
  `($A[$σ]₂)

axiom idₛ (Γ) : Subs Γ Γ
axiom wk (A) : Subs (Γ ▹ A) Γ
axiom comp :  Subs Φ Γ → Subs Δ Φ → Subs Δ Γ
infixr:61 " ∘ₛ " => comp
@[rewrite_rule]
axiom comp_id (σ : Subs Γ Δ) : σ ∘ₛ idₛ Γ = σ
@[rewrite_rule]
axiom id_comp (σ : Subs Γ Δ) : idₛ Δ ∘ₛ σ  = σ
@[rewrite_rule]
axiom comp_assoc (σ : Subs Φ Δ) (δ : Subs Γ Φ) (τ : Subs Ξ Γ)  : (σ ∘ₛ δ) ∘ₛ τ = σ ∘ₛ δ ∘ₛ τ
@[rewrite_rule]
axiom Tyid (A : Ty Γ) : A[idₛ Γ]₁ = A
@[rewrite_rule]
axiom Tmid (A : Ty Γ) (t : Tm A) : t[idₛ Γ]₂ = t

@[rewrite_rule]
axiom Tycomp (A : Ty Γ) (σ : Subs Φ Γ) (τ : Subs Δ Φ) : A[σ]₁[τ]₁ = A[σ ∘ₛ τ]₁

axiom ssnoc (σ : Subs Δ Γ) {A : Ty Γ} : Tm A[σ]₁ → Subs Δ (Γ ▹ A)
infixl:60 " ▹ₛ " => ssnoc
@[rewrite_rule]
axiom snoc_comp (σ : Subs Δ Γ) {A : Ty Γ} (t : Tm A[σ]₁) (τ : Subs Φ Δ) : (σ ▹ₛ t) ∘ₛ τ = (σ ∘ₛ τ) ▹ₛ t[τ]₂

axiom vz (A : Ty Γ) : Tm A[wk A]₁
@[rewrite_rule]
axiom ssnoc_vz (σ : Subs Δ Γ)(A : Ty Γ) (t : Tm A[σ]₁): wk A ∘ₛ (σ ▹ₛ t) = σ

@[rewrite_rule]
axiom vz_sub (A : Ty Γ) (σ : Subs Δ Γ) (t : Tm A[σ]₁): (vz A)[σ ▹ₛ t]₂ = t

axiom Pi (A : Ty Γ) (B : Ty (Γ ▹ A)) : Ty Γ
@[rewrite_rule]
axiom subsPi (A : Ty Γ) (B : Ty (Γ ▹ A)) (σ : Subs Δ Γ) : (Pi A B)[σ]₁ = Pi A[σ]₁ B[(σ ∘ₛ wk A[σ]₁) ▹ₛ vz A[σ]₁ ]₁
axiom lam {A : Ty Γ} {B : Ty (Γ ▹ A)} (f : Tm B) : Tm (Pi A B)
axiom app {A : Ty Γ} {B : Ty (Γ ▹ A)} (f : Tm (Pi A B)) (x : Tm A) : Tm B[idₛ Γ ▹ₛ x]₁

-- set_option trace.Meta.isDefEq true
set_option trace.Meta.IsDefEq.RewriteRule true
-- axiom η  (A : Ty Γ) (B : Ty (Γ ▹ A)) (f : Tm (Pi A B)) :
-- f = lam (app f[wk A]₂ (vz A))
end
