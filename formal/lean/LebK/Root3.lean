/-!
# The 5D root box of the three-body bound (core Lean, shared by the leaf modules and the final theorem)

Coordinates `(t₁ₓ, t₁ᵧ, s₂, t₂ₓ, t₂ᵧ)`: the translation of `B₃`, and the rotation parameter `s₂ = tan(ρ₂/2)` and
translation of `B₅`.
-/

namespace LebesgueCover.Fast

def ns3 : List Nat := [3, 5]
def tau3 : Rat := mkRat 8347 10000
def nu3 : Rat := mkRat 1 (2 ^ 36)
def rl3 : Array Rat := #[mkRat (-3267777) 16777216, mkRat (-3267777) 16777216, mkRat 0 1, mkRat (-3322521) 16777216,
  mkRat (-3322521) 16777216]
def rh3 : Array Rat := #[mkRat 3267777 16777216, mkRat 3267777 16777216, mkRat 333 1024, mkRat 3322521 16777216,
  mkRat 3322521 16777216]

end LebesgueCover.Fast
