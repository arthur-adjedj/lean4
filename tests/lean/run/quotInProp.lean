#check Quot

variable (s : Squash True)
def elim := Quot.lift (fun _ => 1) (fun _ _ _ => rfl) s
#check (Squash True : Type) --ensures ``
#check (rfl : s = Squash.mk ⟨⟩)
#check (rfl : elim s = elim (Squash.mk ⟨⟩))
#check (rfl : elim (Squash.mk ⟨⟩) = 1)
#check (rfl : elim s = 1)
