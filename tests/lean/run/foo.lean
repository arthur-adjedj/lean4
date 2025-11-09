
set_option trace.Meta.sizeOf true
set_option trace.Meta.sizeOf.aux true
set_option trace.Meta.sizeOf.loop true
set_option trace.Meta.sizeOf.minor true
set_option trace.Meta.sizeOf.minor.step true

mutual

inductive DepthTreeAux : Nat → Type
  | foo {n : Nat} : ListDepthTreeAux n → DepthTreeAux (n+1)

inductive ListDepthTreeAux : Nat → Type
 | nil : ListDepthTreeAux n
 | cons : DepthTreeAux n → ListDepthTreeAux n → ListDepthTreeAux n

end
/- Trees of depth at most n-/
inductive DepthTree : Nat → Type
  | foo {n : Nat} : List (DepthTree n) → DepthTree (n+1)

variable (n : Nat)

#print DepthTree._sizeOf_1
#reduce @DepthTree.rec_1 (fun _ _ => Nat) (fun _ => Nat) (fun {n} a a_ih => 1 + sizeOf n + a_ih) (fun {n} => 1+n)
        (fun {n} head tail head_ih tail_ih => 1 + head_ih + tail_ih) n []
