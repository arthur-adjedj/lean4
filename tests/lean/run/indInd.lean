mutual
inductive Con : Type where
  | nil : Con
  | ext (Γ : Con) (A : Ty Γ) :  Con

inductive Ty : (Γ : Con) → Type where
  | U : Ty Γ
  | Pi (A : Ty Γ) (B : Ty (Con.ext Γ A)) :Ty Γ

inductive Tm : (Γ : Con) → (A : Ty Γ) → Type where
  | Nat : Tm Γ Ty.U
  | lam (A : Ty Γ) (B : Ty (Con.ext  Γ A)) : Tm Γ (Ty.Pi A B)
end

def typeOf (_ : α) := α
#check Tm.rec
#check typeOf @Tm.rec
