inductive Foo (n : Nat) (T : Type) : Nat → Type
  | foo : Foo n T 0

inductive Bar : Type
  | bar : Foo n Bar 0 → Bar

-- inductive Regex : (α: Type u) -> Type (u + 1) where
--   | emptyset : Regex α
--   | emptystr : Regex α
--   | char : α → Regex α
--   | or : Regex α → Regex α → Regex α
--   | concat : Regex α → Regex α → Regex α
--   | star : Regex α → Regex α

-- inductive Lang : {α : Type u} -> Regex α -> List α -> Type (u + 2) where
--   | lang_emptyset (str : List α):
--     False ->
--     Lang Regex.emptyset str
--   | lang_emptystr:
--     Lang Regex.emptystr ([]: List α)
--   | lang_char (c: α):
--     Lang (Regex.char c) [c]
--   | lang_or (str: List α) (r1 r2: Regex α):
--     Lang r1 str ⊕ Lang r2 str ->
--     Lang (Regex.or r1 r2) str
