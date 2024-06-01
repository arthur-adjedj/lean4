class Foo

set_option trace.Elab.inductive true

mutual
  inductive Bar [Foo] where
  inductive Baz [Foo] where
end
