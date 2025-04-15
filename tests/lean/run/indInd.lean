-- import Lean
--
-- open Lean Elab Meta
--
-- def con.nil : Constructor := {
  -- name := `Con.nil
  -- type := mkConst `Con []
-- }
--
-- def con.ext : Constructor := {
  -- name := `Con.ext
  -- type := mkForall `Γ default (mkConst `Con []) <|
          -- mkForall `A default (mkApp (mkConst `Ty []) (.bvar 0)) <|
          -- mkConst `Con []
-- }
--
-- def ty.U : Constructor := {
  -- name := `Ty.U
  -- type := mkForall `Γ default (mkConst `Con []) <|
          -- mkApp (mkConst `Ty []) (.bvar 0)
-- }
--
-- def ty.Pi : Constructor := {
  -- name := `Ty.Pi
  -- type := mkForall `Γ default (mkConst `Con []) <|
          -- mkForall `A default (mkApp (mkConst `Ty []) (.bvar 0)) <|
          -- mkForall `B default (mkApp (mkConst `Ty []) (mkAppN (mkConst `Con.ext [])  #[.bvar 1,.bvar 0])) <|
          -- mkApp (mkConst `Ty []) (.bvar 2)
-- }
--
-- def indind : Declaration :=
  -- let con : InductiveType := {
    -- name := `Con
    -- type := mkSort 1
    -- ctors := [con.nil,con.ext]
  -- }
  -- let ty : InductiveType := {
    -- name := `Ty
    -- type := mkForall `Γ default (mkConst `Con []) (mkSort 1)
    -- ctors := [ty.U,ty.Pi]
  -- }
  -- .inductDecl [] 0 [con,ty] false
-- run_cmd Command.liftTermElabM do
    -- addDecl indind

-- set_option autoImplicit false
-- set_option trace.Elab.inductive true

mutual
inductive Con : Type where

inductive Ty : (Γ : Con) → Type where

inductive Tm : (Γ : Con) → (A : Ty Γ) → Type where
end
universe u
#check Tm.rec
#check {motive_1 : Con → Sort u} →
  {motive_2 : (Γ : Con) → motive_1 Γ → Ty Γ → Sort u} →
    {motive_3 : (Γ : Con) → motive_1 Γ → (A : Ty Γ) → motive_2 Γ A → Tm Γ A → Sort u} →
      (nil : motive_1 Con.nil) →
        {ext : (Γ : Con) → (A : Ty Γ) → (Γ_ih : motive_1 Γ) → motive_2 Γ Γ_ih A → motive_1 (Γ.ext A)} →
          {U : {Γ : Con} → (Γ_ih : motive_1 Γ) → motive_2 Γ Γ_ih Ty.U} →
            (Pi :
                {Γ : Con} →
                  (A : Ty Γ) →
                    (B : Ty (Γ.ext A)) →
                      (Γ_ih : motive_1 Γ) →
                        (A_ih : motive_2 Γ Γ_ih A) →
                          motive_2 (Γ.ext A) (ext Γ A Γ_ih A_ih) B → motive_2 Γ Γ_ih (A.Pi B)) →
              (El : (Δ : Con) → (Δ_ih : motive_1 Δ) → motive_3 Δ Δ_ih Ty.U (U Δ_ih) (Tm.El Δ)) →
                {Γ : Con} → {A : Ty Γ} → (t : Tm Γ A) → motive_3 Γ (Con.rec nil Pi El Γ) A (Ty.rec nil Pi El) t

-- run_cmd Command.liftTermElabM do
  -- let recInfo ← getConstInfoRec ``Ty.rec
  -- for rule in recInfo.rules do
    -- logInfo m!"{rule.ctor} : {indentExpr rule.rhs}"
--
-- run_cmd Command.liftTermElabM do
  -- let recInfo ← getConstInfoRec ``Ty.rec
  -- check recInfo.type
  -- for rule in recInfo.rules do
    -- check rule.rhs
--
-- #check
  --  @Ty.rec.{1}
    -- (fun Γ => ∀ Γ A, Ty (Γ.ext A))
    -- (fun Γ _ _ => ∀ A, Ty (Γ.ext A))
    -- (fun A => .U _)
    -- (fun Γ A Γ_ih A_ih B => sorryAx.{1} _ _)
    -- (fun Γ Γ_ih A => Γ.ext A)
    -- (sorryAx.{1} _ _)
