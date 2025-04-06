
import Lean

open Lean Elab Meta

def con.nil : Constructor := {
  name := `Con.nil
  type := mkConst `Con []
}

def con.ext : Constructor := {
  name := `Con.ext
  type := mkForall `Γ default (mkConst `Con []) <|
          mkForall `A default (mkApp (mkConst `Ty []) (.bvar 0)) <|
          mkConst `Con []
}

def ty.U : Constructor := {
  name := `Ty.U
  type := mkForall `Γ default (mkConst `Con []) <|
          mkApp (mkConst `Ty []) (.bvar 0)
}

def ty.Pi : Constructor := {
  name := `Ty.Pi
  type := mkForall `Γ default (mkConst `Con []) <|
          mkForall `A default (mkApp (mkConst `Ty []) (.bvar 0)) <|
          mkForall `B default (mkApp (mkConst `Ty []) (mkAppN (mkConst `Con.ext [])  #[.bvar 1,.bvar 0])) <|
          mkApp (mkConst `Ty []) (.bvar 2)
}

def indind : Declaration :=
  let con : InductiveType := {
    name := `Con
    type := mkSort 1
    ctors := [con.nil,con.ext]
  }
  let ty : InductiveType := {
    name := `Ty
    type := mkForall `Γ default (mkConst `Con []) (mkSort 1)
    ctors := [ty.U,ty.Pi]
  }
  .inductDecl [] 0 [con,ty] false


/-
mutual
inductive Con : Type where
  | nil : Con
  | ext (Γ : Con) (A : Ty Γ): Con

inductive Ty : Con → Type where
  | U (Γ : Con): Ty Γ
  | Pi (Γ : Con) (A : Ty Con) (B : Ty (.ext Γ A)): Ty Γ
end
-/

run_cmd Command.liftTermElabM do
    addDecl indind
/--
info: Ty.rec.{u} {motive_1 : Con → Sort u} {motive_2 : (Γ : Con) → motive_1 Γ → Ty Γ → Sort u} (nil : motive_1 Con.nil)
  {ext : (Γ : Con) → (A : Ty Γ) → (Γ_ih : motive_1 Γ) → motive_2 Γ Γ_ih A → motive_1 (Γ.ext A)}
  (U : (Γ : Con) → (Γ_ih : motive_1 Γ) → motive_2 Γ Γ_ih (Ty.U Γ))
  (Pi :
    (Γ : Con) →
      (A : Ty Γ) →
        (B : Ty (Γ.ext A)) →
          (Γ_ih : motive_1 Γ) →
            (A_ih : motive_2 Γ Γ_ih A) → motive_2 (Γ.ext A) (ext Γ A Γ_ih A_ih) B → motive_2 Γ Γ_ih (Ty.Pi Γ A B))
  {Γ : Con} (t : Ty Γ) : motive_2 Γ (Con.rec nil U Pi Γ) t
-/
#guard_msgs in
#check Ty.rec

run_cmd Command.liftTermElabM do
  let recInfo ← getConstInfoRec ``Ty.rec
  for rule in recInfo.rules do
    logInfo m!"{rule.ctor} : {indentExpr rule.rhs}"
/-TODO tail or recursor should be of the form
`{Γ : Con} → (t : Ty Γ) → motive_2 Γ (@Con.rec motive_1 motive_2 nil ext U Pi Γ) t`
-/

def type_of (_x : α) := α

run_cmd Command.liftTermElabM do
  let recInfo ← getConstInfoRec ``Ty.rec
  check recInfo.type

-- #check
--    @Ty.rec.{1}
--     (fun Γ => ∀ Γ A, Ty (Γ.ext A))
--     (fun Γ _ _ => ∀ A, Ty (Γ.ext A))
--     (fun A => .U _)
--     (fun Γ A Γ_ih A_ih B => by dsimp at Γ_ih;dsimp at A_ih;)
--     (fun Γ Γ_ih A => Γ.ext A)
--     (sorryAx.{1} _ _)
