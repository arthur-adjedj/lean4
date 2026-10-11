/-!
# Kernel defeq: one `rfl` costs 1.8x the memory it did at v4.34.0

Peak RSS compiling this file (`/usr/bin/time -l elan run <toolchain> lean mwe.lean`):

    v4.34.0                3.02 GB    76s
    v4.35.0-rc3            5.40 GB   192s      (1.79x memory, 2.5x time)
    nightly-2026-10-01     5.40 GB   195s

Everything here is a stub; only the *shape* matters. The whole cost is the
single `rfl` marked `COST SITE` at the bottom, in the `error` branch of the
induction step. Replace it with the `simp only` on the line above it (see KNOB)
and the file compiles in 0.33 s / 0.42 GB on **both** toolchains.

## What the cost is

`bind (.error e) K` discards `K` by iota, so closing that branch should not
depend on `K` at all. It does: the two sides are
`bind (.error e) K_fast` and `bind (.error e) K_canonical`, where the two
continuations are the remainders of the two unfolded `go` bodies -- large and
structurally different. The kernel compares them before the enclosing equality
succeeds, rather than reducing the bind first.

That comparison happens on both toolchains; v4.35 makes each one cost more.
leanprover/lean4#8309 ("`Decidable` as subtype of `Bool`") redefines `ite` as
`dite c (fun _ => t) (fun _ => e)`, which roughly doubles the kernel's
`Nat.casesOn` unfolds over a body of nested `ite`s. Substituting only `ite`'s
value in the environment, holding its type, universes and reducibility hints
fixed, moves the cost both ways, so this is a library definition change
amplifying kernel behaviour that was already there, not a change to `isDefEq`.

The cost scales with the size of the two compared bodies: deleting the
distance-decode half of both `go` bodies drops it to 0.60 GB and removes the
difference between the toolchains.
-/

structure BitReader where
  data : ByteArray
  bitPos : Nat

/-- Canonical bit reader. -/
def BitReader.readBits (br : BitReader) (n : Nat) : Except String (UInt32 × BitReader) :=
  go br.bitPos 0 n
where
  go (bp : Nat) (acc : UInt32) : Nat → Except String (UInt32 × BitReader)
    | 0 => .ok (acc, { br with bitPos := bp })
    | k + 1 =>
      if bp ≥ br.data.size * 8 then .error "eof"
      else go (bp + 1) (acc <<< 1) k

/-- Same thing by a different route. -/
def readBitsFast (br : BitReader) (n : Nat) : Except String (UInt32 × BitReader) :=
  loop br.bitPos 0 n
where
  loop (bp : Nat) (acc : UInt32) : Nat → Except String (UInt32 × BitReader)
    | 0 => .ok (acc, { br with bitPos := bp })
    | k + 1 =>
      if _h : br.data.size * 8 ≤ bp then .error "eof"
      else loop (bp + 1) (acc * 2) k

theorem readBitsFast_eq (br : BitReader) (n : Nat) :
    readBitsFast br n = br.readBits n := sorry

inductive HuffTree where
  | leaf (symbol : UInt16)
  | node (zero one : HuffTree)
  | empty

namespace HuffTree

def decode (tree : HuffTree) (br : BitReader) : Except String (UInt16 × BitReader) :=
  go tree br 0
where
  go : HuffTree → BitReader → Nat → Except String (UInt16 × BitReader)
    | .leaf s, br, _ => .ok (s, br)
    | .empty, _, _ => .error "empty"
    | .node z o, br, d =>
      if br.bitPos ≥ br.data.size * 8 then .error "eof"
      else if d ≥ 15 then .error "deep"
      else if br.bitPos % 2 = 0 then go z { br with bitPos := br.bitPos + 1 } (d + 1)
      else go o { br with bitPos := br.bitPos + 1 } (d + 1)

structure DecodeTable where
  packed : Array UInt32

def buildTable (_tree : HuffTree) : DecodeTable where
  packed := #[0]

def decodeWithTable (tree : HuffTree) (table : DecodeTable) (br : BitReader) :
    Except String (UInt16 × BitReader) :=
  if table.packed.isEmpty then tree.decode br
  else
    match tree with
    | .leaf s => .ok (s, br)
    | .empty => .error "empty"
    | .node _ _ => tree.decode br

theorem decodeWithTable_eq (tree : HuffTree) (br : BitReader) :
    tree.decodeWithTable tree.buildTable br = tree.decode br := sorry

end HuffTree

def lengthBase : Array UInt32 := #[3, 4, 5, 6]
def lengthExtra : Array UInt8 := #[0, 0, 0, 1]
def distBase : Array UInt32 := #[1, 2, 3, 4]
def distExtra : Array UInt8 := #[0, 0, 1, 1]
set_option maxRecDepth 100000

/-- Canonical decoder. -/
def decodeHuffman (br : BitReader) (output : ByteArray)
    (litTree distTree : HuffTree) (maxOutputSize : Nat)
    : Except String (ByteArray × BitReader) :=
  go br.data.size br output
where
  go (dataSize : Nat) (br : BitReader) (output : ByteArray)
      : Except String (ByteArray × BitReader) := do
    let (sym, br₁) ← litTree.decode br
    if sym < 256 then
      if output.size ≥ maxOutputSize then
        throw "output exceeds maximum size"
      if _h₁ : br₁.bitPos ≤ br.bitPos then
        throw "no progress"
      else if _h₂ : dataSize * 8 < br₁.bitPos then
        throw "bit position out of range"
      else
        go dataSize br₁ (output.push sym.toUInt8)
    else if sym == 256 then
      .ok (output, br₁)
    else
      let idx := sym.toNat - 257
      if _h : idx ≥ lengthBase.size then
        throw "invalid length code"
      else
      let extra := lengthExtra.getD idx 0
      let (_extraBits, br₂) ← br₁.readBits extra.toNat
      let (distSym, br₃) ← distTree.decode br₂
      let dIdx := distSym.toNat
      if _h : dIdx ≥ distBase.size then
        throw "invalid distance code"
      else
      let dExtra := distExtra.getD dIdx 0
      let (_dExtraBits, br₄) ← br₃.readBits dExtra.toNat
      let out := output
      if _h₁ : br₄.bitPos ≤ br.bitPos then
        throw "no progress"
      else if _h₂ : dataSize * 8 < br₄.bitPos then
        throw "bit position out of range"
      else
        go dataSize br₄ out
  termination_by dataSize * 8 - br.bitPos
  decreasing_by all_goals omega

/-- Table-driven variant: identical except the two symbol decodes go through
`decodeWithTable` and the extra-bit reads through `readBitsFast`. -/
def decodeHuffmanFastBR (br : BitReader) (output : ByteArray)
    (litTree distTree : HuffTree) (maxOutputSize : Nat)
    : Except String (ByteArray × BitReader) :=
  go litTree.buildTable distTree.buildTable br.data.size br output
where
  go (litTable distTable : HuffTree.DecodeTable)
      (dataSize : Nat) (br : BitReader) (output : ByteArray)
      : Except String (ByteArray × BitReader) := do
    let (sym, br₁) ← litTree.decodeWithTable litTable br
    if sym < 256 then
      if output.size ≥ maxOutputSize then
        throw "output exceeds maximum size"
      if _h₁ : br₁.bitPos ≤ br.bitPos then
        throw "no progress"
      else if _h₂ : dataSize * 8 < br₁.bitPos then
        throw "bit position out of range"
      else
        go litTable distTable dataSize br₁ (output.push sym.toUInt8)
    else if sym == 256 then
      .ok (output, br₁)
    else
      let idx := sym.toNat - 257
      if _h : idx ≥ lengthBase.size then
        throw "invalid length code"
      else
      let extra := lengthExtra.getD idx 0
      let (_extraBits, br₂) ← readBitsFast br₁ extra.toNat
      let (distSym, br₃) ← distTree.decodeWithTable distTable br₂
      let dIdx := distSym.toNat
      if _h : dIdx ≥ distBase.size then
        throw "invalid distance code"
      else
      let dExtra := distExtra.getD dIdx 0
      let (_dExtraBits, br₄) ← readBitsFast br₃ dExtra.toNat
      let out := output
      if _h₁ : br₄.bitPos ≤ br.bitPos then
        throw "no progress"
      else if _h₂ : dataSize * 8 < br₄.bitPos then
        throw "bit position out of range"
      else
        go litTable distTable dataSize br₄ out
  termination_by dataSize * 8 - br.bitPos
  decreasing_by all_goals omega

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem decodeHuffmanFastBR_eq (br : BitReader) (output : ByteArray)
    (litTree distTree : HuffTree) (maxOut : Nat) :
    decodeHuffmanFastBR br output litTree distTree maxOut
      = decodeHuffman br output litTree distTree maxOut := by
  unfold decodeHuffmanFastBR decodeHuffman
  suffices H : ∀ (dataSize : Nat) (br : BitReader) (output : ByteArray),
      decodeHuffmanFastBR.go litTree distTree maxOut
          litTree.buildTable distTree.buildTable dataSize br output
        = decodeHuffman.go litTree distTree maxOut dataSize br output by
    exact H br.data.size br output
  intro dataSize br output
  induction br, output using
      decodeHuffman.go.induct (dataSize := dataSize) with
  | _ br output ih_lit ih_ld =>
    unfold decodeHuffmanFastBR.go decodeHuffman.go
    rw [HuffTree.decodeWithTable_eq litTree br]
    cases hlit : litTree.decode br with
    -- KNOB. Swap which of these two lines is commented out:
    --   `rfl`                              3.02 GB / 5.40 GB   (v4.34.0 / rc3)
    --   `simp only [bind, Except.bind]`    0.42 GB / 0.41 GB
    -- | error e => simp only [bind, Except.bind]
    | error e => rfl   -- >>> COST SITE <<<
    | ok p => sorry
