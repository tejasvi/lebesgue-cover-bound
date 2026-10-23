import LebesgueCover.Main3
import LebesgueCover.K3.G00
import LebesgueCover.K3.G01
import LebesgueCover.K3.G02
import LebesgueCover.K3.G03
import LebesgueCover.K3.G04
import LebesgueCover.K3.G05
import LebesgueCover.K3.G06
import LebesgueCover.K3.G07
import LebesgueCover.K3.G08
import LebesgueCover.K3.G09
import LebesgueCover.K3.G10
import LebesgueCover.K3.G11
import LebesgueCover.K3.G12
import LebesgueCover.K3.G13
import LebesgueCover.K3.G14
import LebesgueCover.K3.G15
import LebesgueCover.K3.G16
import LebesgueCover.K3.G17
import LebesgueCover.K3.G18
import LebesgueCover.K3.G19
import LebesgueCover.K3.G20
import LebesgueCover.K3.G21
import LebesgueCover.K3.G22
import LebesgueCover.K3.G23
import LebesgueCover.K3.G24
import LebesgueCover.K3.G25
import LebesgueCover.K3.G26
import LebesgueCover.K3.G27
import LebesgueCover.K3.G28
import LebesgueCover.K3.G29
import LebesgueCover.K3.G30
import LebesgueCover.K3.G31

/-!
# `M(D, B₃, B₅) ≥ 0.8347` and `Λ ≥ 0.8347` with a kernel-checked certificate

The root box is good: its grid of 1024 cells is covered by the chunks (32 cells each). The certificate modules use `decide +kernel` only.
-/

open LebesgueCover.Fast LebesgueCover.Cert

namespace LebesgueCover.K3

/-- The root box is good. -/
theorem root3_good : GoodBox ns3 tau3 (fun i => rl3.getD i 0) (fun i => rh3.getD i 0) := by
  refine root_good' (d := 5) (e := 2) (B := 32) (J := 32) (fun j hj => ?_) (by norm_num)
  interval_cases j
  exacts [chunk00, chunk01, chunk02, chunk03, chunk04, chunk05, chunk06, chunk07, chunk08, chunk09, chunk10, chunk11, chunk12, chunk13, chunk14, chunk15, chunk16, chunk17, chunk18, chunk19, chunk20, chunk21, chunk22, chunk23, chunk24, chunk25, chunk26, chunk27, chunk28, chunk29, chunk30, chunk31]

/-- **`M(D, B₃, B₅) ≥ 0.8347`.** -/
theorem hull3_geK : Hull3Statement := hull3_of_root_good root3_good

/-- **`Λ ≥ 0.8347`** for weak universal covers. -/
theorem weak_main3K : WeakMain3Statement := weak3_of_hull3 hull3_geK

/-- **`Λ ≥ 0.8347`.** -/
theorem main3K : Main3Statement := main3_of_weak3 weak_main3K

end LebesgueCover.K3
