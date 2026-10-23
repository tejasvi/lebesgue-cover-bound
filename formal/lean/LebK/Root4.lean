/-!
# The 8D root box of the four-body bound (core Lean, shared by the leaf modules and the final theorem)

Coordinates `(t₁ₓ, t₁ᵧ, s₂, t₂ₓ, t₂ᵧ, s₃, t₃ₓ, t₃ᵧ)`: the translation of `B₃`, the rotation parameter `s₂ = tan(ρ₂/2)` and
translation of `B₅`, and the rotation parameter `s₃ = tan(ρ₃/2)` and translation of `B₇`. The range of `s₂` uses the
rotations by `2π/3` that map `B₃` to itself (`s₂ ≤ tan(π/30)`).
-/

namespace LebesgueCover.Fast

def ns4 : List Nat := [3, 5, 7]
def tau4 : Rat := mkRat 209 250
def nu4 : Rat := mkRat 1 (2 ^ 36)
def rl4 : Array Rat := #[mkRat (-3351629) 16777216, mkRat (-3351629) 16777216, mkRat 0 1, mkRat (-423263) 2097152,
  mkRat (-423263) 2097152, mkRat 0 1, mkRat (-421033) 2097152, mkRat (-421033) 2097152]
def rh4 : Array Rat := #[mkRat 3351629 16777216, mkRat 3351629 16777216, mkRat 6889 65536, mkRat 423263 2097152,
  mkRat 423263 2097152, mkRat 1973 4096, mkRat 421033 2097152, mkRat 421033 2097152]

end LebesgueCover.Fast
