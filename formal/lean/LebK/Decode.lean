/-!
# Packed leaf data (core Lean)

The witnesses of a leaf are stored as one natural number: slot `j` (bits `152 j` to `152 j + 151`) holds the body in
its low 4 bits and then the two coordinates, each packed as `(|a| · 2^8 + e) · 2 + sign` for the dyadic `±a / 2^e`.
`unpackW m n` reads `m` slots. The leaf theorems state `leafOKF … (unpackW m n) … = true`, so the kernel decodes the
data as part of the check; nothing about the packing is assumed.
-/

namespace LebesgueCover.Fast

/-- The dyadic `±a / 2^e` from its packed form `(a · 2^8 + e) · 2 + sign`. -/
def decQ (c : Nat) : Rat :=
  let s := c % 2; let e := (c / 2) % 256; let a := c / 512
  (if s = 1 then -(a : Int) else (a : Int)) / ((2 : Rat) ^ e)

/-- The first `m` witnesses packed in `n`. -/
def unpackW : Nat → Nat → List (Nat × (Rat × Rat))
  | 0, _ => []
  | m + 1, n =>
    let c := n % 2 ^ 152
    (c % 16, (decQ (c / 16 / 2 ^ 73), decQ ((c / 16) % 2 ^ 73))) :: unpackW m (n / 2 ^ 152)

end LebesgueCover.Fast
