opaque Op1 : Type
opaque Op2 : Type
opaque ID : Type

inductive Expr where
  | integer (n : Nat)
  | boolean (b : Bool)
  | character (c : Char)
  | prim1  (op : Op1) (e : Expr)
  | prim2  (op : Op2) (e1 : Expr) (e2 : Expr)
  | letstd (ids : List ID) (es : List Expr) (body : Expr)
  | begin  (e1 : Expr) (e2 : Expr)
  | var (id : ID)
  | if (e1 : Expr) (e2 : Expr) (e3: Expr)

universe u

#check (Unit -> PUnit.{u} : Sort u)

noncomputable def Expr.rec' {motive_1 : Expr → Sort u} :=
  Expr.rec (motive_1 := motive_1) (motive_2 := fun es => ∀ x ∈ es, motive_1 x)

example (e : Expr) : e = e := by
  induction e using Expr.rec' <;> rfl


set_option trace.Elab.definition.body true in
unsafe example : Type := Type
