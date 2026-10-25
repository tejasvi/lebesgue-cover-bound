import LebesgueCover.TreeK
import LebesgueCover.TreeSound
import LebFast.Root11

/-!
# Base of the kernel-checked 11D certificate

The vertex table for `B₃, B₅, B₇, B₉`, and the kernel-side lemma for combination leaves with explicit data: a
combination leaf that passes `combOKF` is good (`comb_good` with the bridge `combOKF_sound`).
-/

open LebesgueCover.Fast

namespace LebesgueCover.Cert

/-- The vertex table for `B₃, B₅, B₇, B₉`. -/
theorem vt11 : VertTableOK ns11 VQ (mkRat 1 (2 ^ 36)) := vertTable_ok (by decide)

/-- **A combination leaf with explicit data** that passes the fast check is good. -/
theorem combF_good {ns : List ℕ} {V : ℕ → ℕ → ℚ × ℚ} {ν τ : ℚ} (hV : VertTableOK ns V ν) {lo hi : Array ℚ}
    {fans : List (List (ℕ × (ℚ × ℚ)) × (ℚ × ℚ) × (ℕ → ℚ) × (ℕ → ℚ) × ℚ)}
    (h : combOKF ns V ν τ (fun a => lo.getD a 0) (fun a => hi.getD a 0) fans = true) :
    GoodBox ns τ (fun i => lo.getD i 0) (fun i => hi.getD i 0) :=
  comb_good hV (combOKF_sound h)

end LebesgueCover.Cert
