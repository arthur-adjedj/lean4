/-! Checks that eta-for-unit functions correctly-/

example (p q : Unit) : p = q := rfl

structure Foo (A B: Type) where
    foo : B
    bar : Unit
    baz : True
    barf : A = B

example (p q : Foo Nat Unit) : p = q := rfl

structure Wrap : Type where
    wrap : True

example (p q : Wrap) : p = q := rfl

example (p q : id (α → id Unit)) : p = q := rfl

/-The product of a unit type is a unit type-/
def b : Unit × Unit := (Unit.unit, Unit.unit)
example (a b : Unit × Unit) : a = b ∧ b = b := ⟨rfl, rfl⟩
example (a b : Unit × Unit) : a = b := rfl


structure PSigma' {α : Sort u} (β : α → Sort v) : Sort (max 1 u v) where
  fst : α
  snd : β fst

example (a b : @PSigma PUnit (fun _ => PUnit)) : a = b := rfl

example (a b : Nat → Unit) : a = b := rfl

structure Bar (n : Nat) where
  h : n = n

example (a b : (n : Nat) → Bar n) : a = b := rfl
