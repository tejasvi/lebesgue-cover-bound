import LebesgueCover.Defs

/-!
# Statements for the three-body bound `Λ ≥ 0.8347`

`Hull3Statement` (`M(D, B₃, B₅) ≥ 0.8347`) is in `LebesgueCover/Defs.lean`. The two readings of the consequence
for the Lebesgue constant follow the conventions there (`MainStatement`, `WeakMainStatement` with `0.8347`).
-/

open MeasureTheory

namespace LebesgueCover

/-- `Λ ≥ 0.8347`. -/
def Main3Statement : Prop := ENNReal.ofReal (8347 / 10000) ≤ lebesgueConstant

/-- `Λ ≥ 0.8347` for the weaker notion of cover. -/
def WeakMain3Statement : Prop :=
  ∀ Ω : Set Plane, IsWeakUniversalCover Ω → ENNReal.ofReal (8347 / 10000) ≤ volume Ω

end LebesgueCover
