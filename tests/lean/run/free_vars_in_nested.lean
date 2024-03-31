--set_option autoImplicit false
--set_option genSizeOfSpec false
-- set_option pp.explicit true

-- inductive Foo (n : Nat) (T : Type) (k : Nat) : Nat → Type
--   | foo : Nat → Foo n T k 0

-- inductive Bar : Type
--   | bar : Foo n Bar k 0 → Bar

-- #check @Bar.rec

-- #check Bar.rec
-- /-Bar.rec.{u} {motive_1 : Bar → Sort u} {motive_2 : {n : Nat} → (a : Nat) → Foo n Bar a → Sort u}
--   (bar : {n : Nat} → (a : Foo n Bar 0) → motive_2 0 a → motive_1 (Bar.bar a)) (foo : {n : Nat} → motive_2 0 Foo.foo)
--   (t : Bar) : motive_1 t-/

-- inductive Test : Nat → Type
--   | foo :{n : Nat} → List (Test n) → Test n.succ

-- -- #check Test.rec

inductive Regex : (α: Type u) -> Type (u + 1) where
  | or : Regex α → Regex α → Regex α
  | eps : Regex α


inductive Lang : {α : Type u} -> Regex α -> List α -> Type (u + 2) where
  | lang_eps : Lang Regex.eps []
  | lang_or (str: List α) (r1 r2: Regex α):
    Lang r1 str ⊕ Lang r2 str ->
    Lang (Regex.or r1 r2) str
