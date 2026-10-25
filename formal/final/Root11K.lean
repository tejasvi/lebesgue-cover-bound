import LebesgueCover.Main5
import LebesgueCover.Diam
import LebesgueCover.K11.C00
import LebesgueCover.K11.C01
import LebesgueCover.K11.C02
import LebesgueCover.K11.C03
import LebesgueCover.K11.C04
import LebesgueCover.K11.C05
import LebesgueCover.K11.C06
import LebesgueCover.K11.C07
import LebesgueCover.K11.C08
import LebesgueCover.K11.C09
import LebesgueCover.K11.C10
import LebesgueCover.K11.C11
import LebesgueCover.K11.C12
import LebesgueCover.K11.C13
import LebesgueCover.K11.C14
import LebesgueCover.K11.C15
import LebesgueCover.K11.C16
import LebesgueCover.K11.C17
import LebesgueCover.K11.C18
import LebesgueCover.K11.C19
import LebesgueCover.K11.C20
import LebesgueCover.K11.C21
import LebesgueCover.K11.C22
import LebesgueCover.K11.C23
import LebesgueCover.K11.C24
import LebesgueCover.K11.C25
import LebesgueCover.K11.C26
import LebesgueCover.K11.C27
import LebesgueCover.K11.C28
import LebesgueCover.K11.C29
import LebesgueCover.K11.C30
import LebesgueCover.K11.C31
import LebesgueCover.K11.C32
import LebesgueCover.K11.C33
import LebesgueCover.K11.C34
import LebesgueCover.K11.C35
import LebesgueCover.K11.C36
import LebesgueCover.K11.C37
import LebesgueCover.K11.C38
import LebesgueCover.K11.C39
import LebesgueCover.K11.C40
import LebesgueCover.K11.C41
import LebesgueCover.K11.C42
import LebesgueCover.K11.C43
import LebesgueCover.K11.C44
import LebesgueCover.K11.C45
import LebesgueCover.K11.C46
import LebesgueCover.K11.C47
import LebesgueCover.K11.C48
import LebesgueCover.K11.C49
import LebesgueCover.K11.C50
import LebesgueCover.K11.C51
import LebesgueCover.K11.C52
import LebesgueCover.K11.C53
import LebesgueCover.K11.C54
import LebesgueCover.K11.C55
import LebesgueCover.K11.C56
import LebesgueCover.K11.C57
import LebesgueCover.K11.C58
import LebesgueCover.K11.C59
import LebesgueCover.K11.C60
import LebesgueCover.K11.C61
import LebesgueCover.K11.C62
import LebesgueCover.K11.C63

/-!
# `M(D, B₃, B₅, B₇, B₉) ≥ 0.8366` and `Λ ≥ 0.8366` with a kernel-checked certificate

The root box is good: its grid of 2048 cells is covered by 64 chunks of 32 cells. The certificate modules use `decide +kernel` only.
-/

open LebesgueCover.Fast LebesgueCover.Cert

namespace LebesgueCover.K11

/-- The root box is good. -/
theorem root11_good : GoodBox ns11 tau11 (fun i => rl11.getD i 0) (fun i => rh11.getD i 0) := by
  refine root_good' (d := 11) (e := 1) (B := 32) (J := 64) (fun j hj => ?_) (by norm_num)
  interval_cases j
  exacts [chunk00, chunk01, chunk02, chunk03, chunk04, chunk05, chunk06, chunk07, chunk08, chunk09, chunk10, chunk11, chunk12, chunk13, chunk14, chunk15, chunk16, chunk17, chunk18, chunk19, chunk20, chunk21, chunk22, chunk23, chunk24, chunk25, chunk26, chunk27, chunk28, chunk29, chunk30, chunk31, chunk32, chunk33, chunk34, chunk35, chunk36, chunk37, chunk38, chunk39, chunk40, chunk41, chunk42, chunk43, chunk44, chunk45, chunk46, chunk47, chunk48, chunk49, chunk50, chunk51, chunk52, chunk53, chunk54, chunk55, chunk56, chunk57, chunk58, chunk59, chunk60, chunk61, chunk62, chunk63]

/-- **`M(D, B₃, B₅, B₇, B₉) ≥ 0.8366`.** -/
theorem hull5_geK : Hull5Statement := hull5_of_root_good root11_good

/-- **`Λ ≥ 0.8366`** for weak universal covers. -/
theorem weak_main5K : WeakMain5Statement := weak5_of_hull5 hull5_geK

/-- **`Λ ≥ 0.8366`.** -/
theorem main5K : Main5Statement := main5_of_hull5 hull5_geK

end LebesgueCover.K11
