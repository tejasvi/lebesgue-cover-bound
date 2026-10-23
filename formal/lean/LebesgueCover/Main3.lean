import LebesgueCover.Main5
import LebesgueCover.Diam
import LebesgueCover.DefsK
import LebesgueCover.Far5Data
import LebK.Root3

/-!
# `M(D, B₃, B₅) ≥ 0.8347` from the 5D root box

The three-body version of `LebesgueCover/Main5.lean`: every configuration of congruent copies of `D, B₃, B₅` is,
after a common isometry, a placement in the fundamental domain (`normal_form3`); a placement with both translations
in the root box is covered by the certificate (`GoodBox` of the root box); every other placement has a body
translated beyond the root box and is covered by the far polygon (`far_good`). The bridges to `Λ` are those of
`LebesgueCover/Diam.lean` and `LebesgueCover/Basic.lean` with three bodies.
-/

open MeasureTheory Set Complex LebesgueCover.Fast

namespace LebesgueCover.Cert

/-- Placements in the fundamental domain for `D, B₃, B₅`. -/
def InFund3 (p : ℕ → ℝ) : Prop := 0 ≤ p (bS 2) ∧ p (bS 2) ≤ Real.tan (Real.pi / 10)

/-- **Normal form** for `D, B₃, B₅`: congruent copies in a convex set `S ⊆ ℂ` give, after a common isometry, a
convex set of the same area containing the disk and the bodies placed by a placement in the fundamental domain. -/
theorem normal_form3 (h : Fin 3 → (ℂ ≃ᵢ ℂ)) {S : Set ℂ} (hS : Convex ℝ S)
    (h0 : h 0 '' diskC ⊆ S) (h1 : h 1 '' reuleauxC 3 ⊆ S) (h2 : h 2 '' reuleauxC 5 ⊆ S) :
    ∃ p, InFund3 p ∧ ∃ K : Set ℂ, Convex ℝ K ∧ volume K = volume S ∧ diskC ⊆ K ∧
      (∀ q ∈ reuleauxC 3, placeC p 1 q ∈ K) ∧ (∀ q ∈ reuleauxC 5, placeC p 2 q ∈ K) := by
  obtain ⟨a0, b0, ha0, σ0, hh0⟩ := iso_flip (h 0)
  obtain ⟨a1, b1, ha1, σ1, hh1⟩ := iso_flip (h 1)
  obtain ⟨a2, b2, ha2, σ2, hh2⟩ := iso_flip (h 2)
  set c := (starRingEnd ℂ) a1 with hc
  have hcn : ‖c‖ = 1 := by rw [hc, Complex.norm_conj, ha1]
  have hca1 : c * a1 = 1 := by
    rw [hc, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, ha1]; simp
  have hpi := Real.pi_pos
  -- body 2 and the reflection flag
  obtain ⟨k2, ρ2, hρ20, hρ21, hv2⟩ := reduce_angle (n := 5) (by norm_num) (v := c * a2)
    (by rw [norm_mul, hcn, ha2, one_mul])
  have key : ∃ ε : Bool, ∃ k : ℕ, ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ ≤ Real.pi / 5 ∧
      flipC ε (c * a2) * exp (((2 * Real.pi * k / 5 : ℝ) : ℂ) * I) = exp ((ρ : ℂ) * I) := by
    by_cases hle : ρ2 ≤ Real.pi / 5
    · refine ⟨false, k2, ρ2, hρ20, hle, ?_⟩
      simp only [flipC]; exact_mod_cast hv2
    · push Not at hle
      obtain ⟨k', hk'⟩ := conj_reduce (n := 5) (by norm_num) hv2
      refine ⟨true, k', 2 * Real.pi / 5 - ρ2, ?_, ?_, ?_⟩
      · push_cast at hρ21; linarith
      · linarith
      · simp only [flipC, if_true]; push_cast at hk' ⊢; exact hk'
  obtain ⟨ε, k2', ρ2', hρ0, hρ1, hv2'⟩ := key
  -- the placement
  set t : ℕ → ℂ := fun i => if i = 1 then flipC ε (c * (b1 - b0)) else flipC ε (c * (b2 - b0)) with ht
  set sv : ℕ → ℝ := fun _ => Real.tan (ρ2' / 2) with hsv
  set p := mkPlace t sv with hp
  have hK : ∀ i (w : ℂ) (B : Set ℂ), h i '' B ⊆ S → w ∈ B → Phi ε c b0 (h i w) ∈ Phi ε c b0 '' S :=
    fun i w B hB hw => ⟨h i w, hB ⟨w, hw, rfl⟩, rfl⟩
  refine ⟨p, ?_, Phi ε c b0 '' S, Phi_convex ε c b0 hS, Phi_volume hcn ε b0 S, ?_, ?_, ?_⟩
  · -- fundamental domain
    have e2 : p (bS 2) = Real.tan (ρ2' / 2) := by rw [hp, mkPlace_s t sv (by norm_num)]
    unfold InFund3
    rw [e2]
    have := tan_half_bounds (n := 10) (by norm_num) hρ0 (by push_cast; linarith)
    push_cast at this; exact this
  · -- the disk
    intro z hz
    set u := flipC ε (c * a0) with hu
    have hun : ‖u‖ = 1 := by rw [hu, norm_flip, norm_mul, hcn, ha0, one_mul]
    set w := flipC (xor ε σ0) ((starRingEnd ℂ) u * z) with hw
    have hwD : w ∈ diskC := by
      apply mem_diskC_of_norm
      rw [hw, norm_flip, norm_mul, Complex.norm_conj, hun, one_mul]
      simpa [diskC, Metric.mem_closedBall, dist_zero_right] using hz
    have := hK 0 w diskC h0 hwD
    rw [hh0, Phi_comp, ← hu, hw, flip_flip, sub_self, mul_zero] at this
    rw [show flipC ε 0 = 0 by cases ε <;> simp [flipC], add_zero, ← mul_assoc, Complex.mul_conj,
      Complex.normSq_eq_norm_sq, hun] at this
    simpa using this
  · -- body 1
    intro q hq
    have := hK 1 (flipC (xor ε σ1) q) (reuleauxC 3) h1 (mem_reuleauxC_flip (by norm_num) _ hq)
    rw [hh1, Phi_comp, hca1, flipC_one, one_mul, flip_flip] at this
    rw [hp, placeC_mk1]
    convert this using 2
    simp [ht]
  · -- body 2
    intro q hq
    obtain ⟨w, hwB, hweq⟩ := body_hits (n := 5) (by norm_num) (t := t 2) (xor ε σ2) (by exact_mod_cast hv2') hq
    have := hK 2 w (reuleauxC 5) h2 hwB
    rw [hh2, Phi_comp] at this
    rw [hp, placeC_mk (ρ := ρ2') (by norm_num) (by linarith) (by linarith) (by simp [hsv])]
    rw [← hweq]
    convert this using 2
    simp [ht]

/-- Half-widths of the root box in the translations. -/
def T3 (i : ℕ) : ℚ := LebesgueCover.Far5.Ts.getD (i - 1) 0

lemma far5_tau : LebesgueCover.Far5.τ = tau3 := by
  simp [LebesgueCover.Far5.τ, tau3, Rat.mkRat_eq_div]

/-- **`M(D, B₃, B₅) ≥ 0.8347`**, given that the root box is good (the certificate). -/
theorem hull3_of_root_good (hroot : GoodBox ns3 tau3 (fun i => rl3.getD i 0) (fun i => rh3.getD i 0)) :
    Hull3Statement := by
  unfold Hull3Statement hull3
  refine le_iInf fun g => ?_
  set U := g 0 '' disk ∪ g 1 '' reuleaux 3 ∪ g 2 '' reuleaux 5 with hU
  set S := convexHull ℝ U with hS
  rw [← volume_eC_image S]
  have hconv : Convex ℝ (eC '' S) := (convex_convexHull ℝ U).linear_image eC.toLinearEquiv.toLinearMap
  set h : Fin 3 → (ℂ ≃ᵢ ℂ) := fun i => (eC.symm.toIsometryEquiv).trans ((g i).trans eC.toIsometryEquiv) with hh
  have himg : ∀ i (B : Set Plane), h i '' (eC '' B) = eC '' (g i '' B) := by
    intro i B
    simp only [hh, Set.image_image, IsometryEquiv.trans_apply, LinearIsometryEquiv.coe_toIsometryEquiv,
      LinearIsometryEquiv.symm_apply_apply]
  have hsub : ∀ i (B : Set Plane), g i '' B ⊆ U → h i '' (eC '' B) ⊆ eC '' S := by
    intro i B hB
    rw [himg]
    exact Set.image_mono (hB.trans (subset_convexHull ℝ U))
  obtain ⟨p, hfund, K, hKc, hKvol, hKD, hK1, hK2⟩ := normal_form3 h hconv
    (by rw [← eC_disk]; exact hsub 0 disk (fun x hx => Or.inl (Or.inl hx)))
    (by rw [← eC_reuleaux]; exact hsub 1 _ (fun x hx => Or.inl (Or.inr hx)))
    (by rw [← eC_reuleaux]; exact hsub 2 _ (fun x hx => Or.inr hx))
  rw [← hKvol]
  have hτ : ENNReal.ofReal (8347 / 10000) = ENNReal.ofReal ((tau3 : ℚ) : ℝ) := by
    congr 1; norm_num [tau3, Rat.mkRat_eq_div]
  rw [hτ]
  apply le_of_lt
  have hB : ∀ i, 1 ≤ i → i ≤ ns3.length → ∀ q ∈ reuleauxC (ns3.getD (i - 1) 0), placeC p i q ∈ K := by
    intro i hi1 hi2 q hq
    have : i = 1 ∨ i = 2 := by simp [ns3] at hi2; omega
    rcases this with rfl | rfl
    · exact hK1 q (by simpa [ns3] using hq)
    · exact hK2 q (by simpa [ns3] using hq)
  by_cases hin : ∀ i, 1 ≤ i → i ≤ 2 → |p (bTx i)| ≤ T3 i ∧ |p (bTy i)| ≤ T3 i
  · refine hroot p (fun a ha => ?_) K hKc hKD hB
    obtain ⟨h2a, h2b⟩ := hfund
    have t5 := (tanCheck_sound tan5_ok).1
    push_cast at t5
    rw [show (1 : ℝ) * Real.pi / 10 = Real.pi / 10 by ring] at t5
    have b1 := hin 1 le_rfl (by norm_num)
    have b2 := hin 2 (by norm_num) le_rfl
    simp only [ns3, List.length_cons, List.length_nil] at ha
    simp only [bTx, bTy, bS, T3, LebesgueCover.Far5.Ts] at b1 b2 h2a h2b
    norm_num at b1 b2 h2a h2b
    simp only [abs_le] at b1 b2
    interval_cases a <;> simp [rl3, rh3, Rat.mkRat_eq_div] <;> norm_num <;>
      first | constructor <;> linarith | linarith
  · push Not at hin
    obtain ⟨i, hi1, hi2, hout⟩ := hin
    have hi : i = 1 ∨ i = 2 := by omega
    have hfar : (T3 i : ℝ) ≤ ‖toC (transAt p i)‖ := by
      simp only [transAt, if_neg (show i ≠ 0 by omega)]
      apply toC_norm_ge
      by_contra hc; push Not at hc
      exact absurd (hout hc.1) (not_lt.mpr hc.2)
    rw [← far5_tau]
    have hpoly := LebesgueCover.Far5.poly_ok
    have hg : gCheck (ns3.getD (i - 1) 0) (T3 i) LebesgueCover.Far5.g = true := by
      rcases hi with rfl | rfl
      · exact LebesgueCover.Far5.g3_ok
      · exact LebesgueCover.Far5.g5_ok
    have hodd : Odd (ns3.getD (i - 1) 0) := by
      rcases hi with rfl | rfl
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
    have h3 : 3 ≤ ns3.getD (i - 1) 0 := by
      rcases hi with rfl | rfl <;> decide
    have hik : i ≤ ns3.length := by simp [ns3]; omega
    exact far_good hpoly hi1 hik hodd h3 hg p hfar hKc hKD hB

/-- **`Hull3Statement → WeakMain3Statement`**: a weak universal cover contains congruent copies of `D, B₃, B₅`
(convex, diameter `1`), hence the convex hull of their union. -/
theorem weak3_of_hull3 (h : Hull3Statement) : WeakMain3Statement := by
  intro Ω hΩ
  obtain ⟨hconv, hcov⟩ := hΩ
  obtain ⟨φ0, h0⟩ := hcov disk convex_disk ediam_disk
  obtain ⟨φ1, h1⟩ := hcov (reuleaux 3) (convex_reuleaux 3) (ediam_reuleaux ⟨1, rfl⟩ le_rfl)
  obtain ⟨φ2, h2⟩ := hcov (reuleaux 5) (convex_reuleaux 5) (ediam_reuleaux ⟨2, rfl⟩ (by norm_num))
  refine le_trans h ?_
  let g : Fin 3 → (Plane ≃ᵢ Plane) := ![φ0, φ1, φ2]
  calc hull3 ≤ volume (convexHull ℝ (g 0 '' disk ∪ g 1 '' reuleaux 3 ∪ g 2 '' reuleaux 5)) :=
        iInf_le (fun g : Fin 3 → (Plane ≃ᵢ Plane) => volume (convexHull ℝ (g 0 '' disk ∪ g 1 '' reuleaux 3 ∪
          g 2 '' reuleaux 5))) g
    _ ≤ volume Ω := by
      apply measure_mono
      apply convexHull_min _ hconv
      simp only [g, union_subset_iff]
      exact ⟨⟨h0, h1⟩, h2⟩

/-- The strongest reading implies `Λ ≥ 0.8347`. -/
theorem main3_of_weak3 (h : WeakMain3Statement) : Main3Statement :=
  le_iInf₂ fun Ω hΩ => h Ω hΩ.weak

end LebesgueCover.Cert
