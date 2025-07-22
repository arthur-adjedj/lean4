-- TODO rewrite rewrite rules code in the kernel
set_option debug.skipKernelTC true
axiom A : Type
axiom a : Nat → A
@[rewrite_rule]
axiom wut : A = Nat
@[rewrite_rule]
axiom eq : ∀ x, a x = 2
example : a x = 2 := rfl
@[rewrite_rule]
axiom arr : (Nat → Nat) = (Nat → Bool)

attribute [rewrite_rule] Nat.succ_add Nat.zero_add

example {n k : Nat} : n + 1 + k = n + k + 1 := rfl
example {n : Nat}: 0 + n = n := rfl
