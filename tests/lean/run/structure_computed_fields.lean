import Lean.Expr
open Lean (Expr)

structure Foo where
  foo : Nat
  bar : Fin foo
  baz : True
with
  @[computed_field]
  hash : Foo → Nat
    | ⟨n,bar,_⟩ =>
        mixHash (Hashable.hash n) (Hashable.hash bar) |>.toNat

structure HoldsAtAtoms where
  bvExpr : Expr
  proof : Expr
  expr : Expr
with
  @[computed_field]
  hash : HoldsAtAtoms → UInt64
    | ⟨bvExpr,proof,expr⟩ =>
        bvExpr.hash |> mixHash proof.hash |> mixHash expr.hash
