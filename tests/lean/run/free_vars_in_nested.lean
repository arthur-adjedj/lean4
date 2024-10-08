
set_option autoImplicit false
set_option genSizeOfSpec false
set_option pp.explicit true


inductive Foo (n : Nat) (T : Type) (k : Nat) : Nat → Type
  | foo : Nat → Foo n T k 0

inductive Bar : Type
  | bar {n k}: Foo n Bar k 0 → Bar

/--
info: Bar.rec.{u} {motive_1 : Bar → Sort u} {motive_2 : {n k : Nat} → (a : Nat) → Foo n Bar k a → Sort u}
  (bar : {n k : Nat} → (a : Foo n Bar k 0) → @motive_2 n k 0 a → motive_1 (@Bar.bar n k a))
  (foo : {n k : Nat} → (a : Nat) → @motive_2 n k 0 (@Foo.foo n Bar k a)) (t : Bar) : motive_1 t
-/
#guard_msgs in
#check Bar.rec

inductive Test : Nat → Type
  | foo :{n : Nat} → List (Test n) → Test n.succ

/--
info: Test.rec.{u} {motive_1 : (a : Nat) → Test a → Sort u} {motive_2 : {n : Nat} → List (Test n) → Sort u}
  (foo : {n : Nat} → (a : List (Test n)) → @motive_2 n a → motive_1 n.succ (@Test.foo n a))
  (nil : {n : Nat} → @motive_2 n (@List.nil (Test n)))
  (cons :
    {n : Nat} →
      (head : Test n) →
        (tail : List (Test n)) → motive_1 n head → @motive_2 n tail → @motive_2 n (@List.cons (Test n) head tail)) :
  {a : Nat} → (t : Test a) → motive_1 a t
-/
#guard_msgs in
#check Test.rec

universe u

inductive Regex : Type  where
  | or : Regex → Regex → Regex
  | and : Regex → Regex → Regex
  | concat : Regex → Regex → Regex
  | eps : Regex

inductive Lang : Regex -> String -> Type 1 where
  | eps : Lang Regex.eps ""
  | or (str: String) (r1 r2: Regex):
    Lang r1 str ⊕ Lang r2 str ->
    Lang (Regex.or r1 r2) str
  | and (str: String) (r1 r2: Regex):
    Lang r1 str → Lang r2 str ->
    Lang (Regex.and r1 r2) str
  | concat (r1 : Regex) (str1 str2 : String) (r2 : Regex):
    Lang r1 str1 → Lang r2 str2 → Lang (Regex.concat r1 r2) (str1 ++ str2)

/--
info: Lang.rec.{u} {motive_1 : (a : Regex) → (a_1 : String) → Lang a a_1 → Sort u}
  {motive_2 : (str : String) → (r1 r2 : Regex) → Sum (Lang r1 str) (Lang r2 str) → Sort u}
  (eps : motive_1 Regex.eps "" Lang.eps)
  (or :
    (str : String) →
      (r1 r2 : Regex) →
        (a : Sum (Lang r1 str) (Lang r2 str)) → motive_2 str r1 r2 a → motive_1 (r1.or r2) str (Lang.or str r1 r2 a))
  (and :
    (str : String) →
      (r1 r2 : Regex) →
        (a : Lang r1 str) →
          (a_1 : Lang r2 str) →
            motive_1 r1 str a → motive_1 r2 str a_1 → motive_1 (r1.and r2) str (Lang.and str r1 r2 a a_1))
  (concat :
    (r1 : Regex) →
      (str1 str2 : String) →
        (r2 : Regex) →
          (a : Lang r1 str1) →
            (a_1 : Lang r2 str2) →
              motive_1 r1 str1 a →
                motive_1 r2 str2 a_1 →
                  motive_1 (r1.concat r2)
                    (@HAppend.hAppend String String String (@instHAppend String String.instAppendString) str1 str2)
                    (Lang.concat r1 str1 str2 r2 a a_1))
  (inl :
    (str : String) →
      (r1 r2 : Regex) →
        (val : Lang r1 str) → motive_1 r1 str val → motive_2 str r1 r2 (@Sum.inl (Lang r1 str) (Lang r2 str) val))
  (inr :
    (str : String) →
      (r1 r2 : Regex) →
        (val : Lang r2 str) → motive_1 r2 str val → motive_2 str r1 r2 (@Sum.inr (Lang r1 str) (Lang r2 str) val)) :
  {a : Regex} → {a_1 : String} → (t : Lang a a_1) → motive_1 a a_1 t
-/
#guard_msgs in
#check Lang.rec
