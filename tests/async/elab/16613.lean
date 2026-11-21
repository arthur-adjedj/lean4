import Lean
open Lean Meta Elab Term

/-- A structure with one predicate field, like Mathlib's `Set` since mathlib4#41506. -/
structure PSet (α : Type) where
  Mem : α → Prop

instance : Membership α (PSet α) := ⟨fun s a => s.Mem a⟩

/-- Reducing `big n` to a constructor computes `2 ^ n`. -/
def big (n : Nat) : PSet Nat := if 2 ^ n = 0 then ⟨fun _ => True⟩ else ⟨fun a => a = 0⟩

/-- `small` unfolds to `big (2 ^ 32)` in one delta step. -/
def small : PSet Nat := big (2 ^ 32)

/-- The same construction with a function type, like Mathlib's `Set` before mathlib4#41506. -/
def FSet (α : Type) := α → Prop

instance : Membership α (FSet α) := ⟨fun s a => s a⟩

def bigF (n : Nat) : FSet Nat := if 2 ^ n = 0 then fun _ => True else fun a => a = 0

def smallF : FSet Nat := bigF (2 ^ 32)

/-- Elaborate a statement `∀ xs, P → Q` and add the theorem `fun xs h => h` with `addDecl`.
The elaborator does not unify `P` with `Q`, so only the kernel checks that they are
definitionally equal. -/
def addIdentityTheorem (name : Name) (stmt : Term) : TermElabM Unit := do
  let type ← elabType stmt
  synthesizeSyntheticMVarsNoPostponing
  let type ← instantiateMVars type
  let value ← forallTelescope type fun xs _ => mkLambdaFVars xs xs.back!
  addDecl (.thmDecl { name, levelParams := [], type, value })

/-- `#add_identity_theorem name : ∀ xs, P → Q` runs `addIdentityTheorem`. -/
elab "#add_identity_theorem " name:ident " : " stmt:term : command =>
  Command.liftTermElabM <| addIdentityTheorem name.getId stmt

-- Accepted: the kernel compares the bare projections `small.Mem` and `(big (2 ^ 32)).Mem` with
-- `lazy_delta_proj_reduction`, which unfolds `small` before it reduces either structure.
#add_identity_theorem bare : ∀ P : (Nat → Prop) → Prop, P small.Mem → P (big (2 ^ 32)).Mem

-- Accepted: with a function type, `smallF a` and `bigF (2 ^ 32) a` have constant heads, and lazy
-- delta reduction unfolds `smallF` to make them syntactically equal.
#add_identity_theorem functionType : ∀ a : Nat, a ∈ smallF → a ∈ bigF (2 ^ 32)

-- Rejected: `a ∈ small` unfolds to the applied projection `small.Mem a`. The kernel reduces
-- `small` to a constructor before it compares the two sides, so it evaluates `2 ^ (2 ^ 32)`:
-- "(kernel) the kernel refused to evaluate `Nat.pow` because its second argument does not fit in
-- a 32-bit unsigned integer".
#add_identity_theorem applied : ∀ a : Nat, a ∈ small → a ∈ big (2 ^ 32)
