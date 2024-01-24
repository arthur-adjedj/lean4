

def f: True ∧ True → Nat := fun ⟨_, _⟩ => 0
def g: True ∧ True → True ∧ True := fun ⟨_, _⟩ => ⟨trivial, trivial⟩
example: ∀x, f (g x) = 0 := fun _ => rfl

variable (P Q : Prop) (A : Type) (f : P → Q → A) (x : P ∧ Q)

example : And.rec f ⟨x.1,x.2⟩ = f (And.left x) (And.right x) := rfl
example : (And.rec f ⟨x.1,x.2⟩ : A) = And.rec f x  := rfl
