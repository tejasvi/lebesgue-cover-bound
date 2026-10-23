import LebesgueCover.Main5
import LebesgueCover.Diam
import LebesgueCover.Far8Data
import LebK.Root4

/-!
# `M(D, B₃, B₅, B₇) ≥ 0.836` from the 8D root box

The four-body version of `LebesgueCover/Main5.lean`, with one more symmetry in the normal form: rotations by `2π/3`
about the disk's centre map `B₃` to itself, so after the reflection the rotation of `B₅` can be taken in `[0, π/15]`
instead of `[0, π/5]` (`s₂ ≤ tan(π/30)`). A placement with all translations in the root box is covered by the
certificate (`GoodBox` of the root box); every other placement has a body translated beyond the root box and is covered
by the far polygon (`far_good`). The bridges to `Λ` are `weak_of_hull4` and `main_of_hull4` (`Diam.lean`).
-/

open MeasureTheory Set Complex LebesgueCover.Fast

namespace LebesgueCover.Cert

/-- Placements in the fundamental domain for `D, B₃, B₅, B₇`, with the rotations of `B₃` used for `B₅`. -/
def InFund4 (p : ℕ → ℝ) : Prop :=
  (0 ≤ p (bS 2) ∧ p (bS 2) ≤ Real.tan (Real.pi / 30)) ∧ (0 ≤ p (bS 3) ∧ p (bS 3) ≤ Real.tan (Real.pi / 7))

/-- `e^{2πiK/15} = e^{2πi·2K/3} · e^{2πi·2K/5}`. -/
lemma exp15_split (K : ℕ) : exp (((2 * Real.pi * K / 15 : ℝ) : ℂ) * I) =
    exp (((2 * Real.pi * (2 * K : ℕ) / 3 : ℝ) : ℂ) * I) * exp (((2 * Real.pi * (2 * K : ℕ) / 5 : ℝ) : ℂ) * I) := by
  rw [← Complex.exp_add]
  have e : ((2 * Real.pi * (2 * K : ℕ) / 3 : ℝ) : ℂ) * I + ((2 * Real.pi * (2 * K : ℕ) / 5 : ℝ) : ℂ) * I
      = ((2 * Real.pi * K / 15 : ℝ) : ℂ) * I + (K : ℂ) * (2 * Real.pi * I) := by
    push_cast; ring
  rw [e, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

/-- `e^{2πi·2K/3} · e^{2πi·4K/3} = 1`. -/
lemma exp3_cancel (K : ℕ) : exp (((2 * Real.pi * (2 * K : ℕ) / 3 : ℝ) : ℂ) * I) *
    exp (((2 * Real.pi * (4 * K : ℕ) / 3 : ℝ) : ℂ) * I) = exp (((0 : ℝ) : ℂ) * I) := by
  rw [← Complex.exp_add]
  have e : ((2 * Real.pi * (2 * K : ℕ) / 3 : ℝ) : ℂ) * I + ((2 * Real.pi * (4 * K : ℕ) / 3 : ℝ) : ℂ) * I
      = ((2 * K : ℕ) : ℂ) * (2 * Real.pi * I) := by
    push_cast; ring
  rw [e, Complex.exp_nat_mul_two_pi_mul_I]; simp

/-- **Normal form** for `D, B₃, B₅, B₇`: congruent copies in a convex set `S ⊆ ℂ` give, after a common isometry, a
convex set of the same area containing the disk and the bodies placed by a placement in the fundamental domain. The
common isometry includes a rotation by a multiple of `2π/3`, which maps `B₃` to itself. -/
theorem normal_form4 (h : Fin 4 → (ℂ ≃ᵢ ℂ)) {S : Set ℂ} (hS : Convex ℝ S)
    (h0 : h 0 '' diskC ⊆ S) (h1 : h 1 '' reuleauxC 3 ⊆ S) (h2 : h 2 '' reuleauxC 5 ⊆ S)
    (h3 : h 3 '' reuleauxC 7 ⊆ S) :
    ∃ p, InFund4 p ∧ ∃ K : Set ℂ, Convex ℝ K ∧ volume K = volume S ∧ diskC ⊆ K ∧
      (∀ q ∈ reuleauxC 3, placeC p 1 q ∈ K) ∧ (∀ q ∈ reuleauxC 5, placeC p 2 q ∈ K) ∧
      (∀ q ∈ reuleauxC 7, placeC p 3 q ∈ K) := by
  obtain ⟨a0, b0, ha0, σ0, hh0⟩ := iso_flip (h 0)
  obtain ⟨a1, b1, ha1, σ1, hh1⟩ := iso_flip (h 1)
  obtain ⟨a2, b2, ha2, σ2, hh2⟩ := iso_flip (h 2)
  obtain ⟨a3, b3, ha3, σ3, hh3⟩ := iso_flip (h 3)
  set c := (starRingEnd ℂ) a1 with hc
  have hcn : ‖c‖ = 1 := by rw [hc, Complex.norm_conj, ha1]
  have hca1 : c * a1 = 1 := by
    rw [hc, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, ha1]; simp
  have hpi := Real.pi_pos
  -- body 2: an angle modulo `2π/15`, then the reflection
  obtain ⟨k2, ρ2, hρ20, hρ21, hv2⟩ := reduce_angle (n := 15) (by norm_num) (v := c * a2)
    (by rw [norm_mul, hcn, ha2, one_mul])
  have key : ∃ ε : Bool, ∃ K : ℕ, ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ ≤ Real.pi / 15 ∧
      flipC ε (c * a2) * exp (((2 * Real.pi * K / 15 : ℝ) : ℂ) * I) = exp ((ρ : ℂ) * I) := by
    by_cases hle : ρ2 ≤ Real.pi / 15
    · refine ⟨false, k2, ρ2, hρ20, hle, ?_⟩
      simp only [flipC]; exact_mod_cast hv2
    · push Not at hle
      obtain ⟨k', hk'⟩ := conj_reduce (n := 15) (by norm_num) hv2
      refine ⟨true, k', 2 * Real.pi / 15 - ρ2, ?_, ?_, ?_⟩
      · push_cast at hρ21; linarith
      · linarith
      · simp only [flipC, if_true]; push_cast at hk' ⊢; exact hk'
  obtain ⟨ε, K2, ρ2', hρ0, hρ1, hv2'⟩ := key
  -- the common rotation by a multiple of `2π/3`
  obtain ⟨u, hu⟩ : ∃ u : ℂ, u = exp (((2 * Real.pi * (2 * K2 : ℕ) / 3 : ℝ) : ℂ) * I) := ⟨_, rfl⟩
  have hun : ‖u‖ = 1 := by rw [hu]; exact norm_exp_I _
  obtain ⟨c', hc'⟩ : ∃ c' : ℂ, c' = c * flipC ε u := ⟨_, rfl⟩
  have hc'n : ‖c'‖ = 1 := by rw [hc', norm_mul, hcn, norm_flip, hun, one_mul]
  have hB2 : flipC ε (c' * a2) * exp (((2 * Real.pi * (2 * K2 : ℕ) / 5 : ℝ) : ℂ) * I) =
      exp ((ρ2' : ℂ) * I) := by
    have e1 : c' * a2 = c * a2 * flipC ε u := by rw [hc']; ring
    rw [e1, flip_mul, flip_flip, mul_assoc, hu, ← exp15_split]
    exact hv2'
  have hB1 : flipC ε (c' * a1) * exp (((2 * Real.pi * (4 * K2 : ℕ) / 3 : ℝ) : ℂ) * I) =
      exp (((0 : ℝ) : ℂ) * I) := by
    have e1 : c' * a1 = c * a1 * flipC ε u := by rw [hc']; ring
    rw [e1, hca1, one_mul, flip_flip, hu]
    exact exp3_cancel K2
  -- body 3
  obtain ⟨k3, ρ3, hρ30, hρ31, hv3⟩ := reduce_angle (n := 7) (by norm_num) (v := flipC ε (c' * a3))
    (by rw [norm_flip, norm_mul, hc'n, ha3, one_mul])
  -- the placement
  set t : ℕ → ℂ := fun i => if i = 1 then flipC ε (c' * (b1 - b0)) else if i = 2 then flipC ε (c' * (b2 - b0))
    else flipC ε (c' * (b3 - b0)) with ht
  set sv : ℕ → ℝ := fun i => if i = 2 then Real.tan (ρ2' / 2) else Real.tan (ρ3 / 2) with hsv
  set p := mkPlace t sv with hp
  have hK : ∀ i (w : ℂ) (B : Set ℂ), h i '' B ⊆ S → w ∈ B → Phi ε c' b0 (h i w) ∈ Phi ε c' b0 '' S :=
    fun i w B hB hw => ⟨h i w, hB ⟨w, hw, rfl⟩, rfl⟩
  refine ⟨p, ?_, Phi ε c' b0 '' S, Phi_convex ε c' b0 hS, Phi_volume hc'n ε b0 S, ?_, ?_, ?_, ?_⟩
  · -- fundamental domain
    have e2 : p (bS 2) = Real.tan (ρ2' / 2) := by rw [hp, mkPlace_s t sv (by norm_num)]; simp [hsv]
    have e3 : p (bS 3) = Real.tan (ρ3 / 2) := by rw [hp, mkPlace_s t sv (by norm_num)]; simp [hsv]
    refine ⟨?_, ?_⟩
    · rw [e2]
      have := tan_half_bounds (n := 30) (by norm_num) hρ0 (by push_cast; linarith)
      push_cast at this; exact this
    · rw [e3]
      have := tan_half_bounds (n := 7) (by norm_num) hρ30 hρ31.le
      push_cast at this; exact this
  · -- the disk
    intro z hz
    set w0 := flipC ε (c' * a0) with hw0
    have hw0n : ‖w0‖ = 1 := by rw [hw0, norm_flip, norm_mul, hc'n, ha0, one_mul]
    set w := flipC (xor ε σ0) ((starRingEnd ℂ) w0 * z) with hw
    have hwD : w ∈ diskC := by
      apply mem_diskC_of_norm
      rw [hw, norm_flip, norm_mul, Complex.norm_conj, hw0n, one_mul]
      simpa [diskC, Metric.mem_closedBall, dist_zero_right] using hz
    have := hK 0 w diskC h0 hwD
    rw [hh0, Phi_comp, ← hw0, hw, flip_flip, sub_self, mul_zero] at this
    rw [show flipC ε 0 = 0 by cases ε <;> simp [flipC], add_zero, ← mul_assoc, Complex.mul_conj,
      Complex.normSq_eq_norm_sq, hw0n] at this
    simpa using this
  · -- body 1: its rotation is a multiple of `2π/3`, which maps `B₃` to itself
    intro q hq
    obtain ⟨w, hwB, hweq⟩ := body_hits (n := 3) (by norm_num) (t := t 1) (xor ε σ1) (by exact_mod_cast hB1) hq
    have := hK 1 w (reuleauxC 3) h1 hwB
    rw [hh1, Phi_comp] at this
    rw [hp, placeC_mk1]
    have e0 : exp (((0 : ℝ) : ℂ) * I) * q + t 1 = q + t 1 := by simp
    rw [← e0, ← hweq]
    convert this using 2
    simp [ht]
  · -- body 2
    intro q hq
    obtain ⟨w, hwB, hweq⟩ := body_hits (n := 5) (by norm_num) (t := t 2) (xor ε σ2) (by exact_mod_cast hB2) hq
    have := hK 2 w (reuleauxC 5) h2 hwB
    rw [hh2, Phi_comp] at this
    rw [hp, placeC_mk (ρ := ρ2') (by norm_num) (by linarith) (by linarith) (by simp [hsv])]
    rw [← hweq]
    convert this using 2
    simp [ht]
  · -- body 3
    intro q hq
    obtain ⟨w, hwB, hweq⟩ := body_hits (n := 7) (by norm_num) (t := t 3) (xor ε σ3) (by exact_mod_cast hv3) hq
    have := hK 3 w (reuleauxC 7) h3 hwB
    rw [hh3, Phi_comp] at this
    have hρ31' : ρ3 < Real.pi := by push_cast at hρ31; linarith
    rw [hp, placeC_mk (ρ := ρ3) (by norm_num) (by linarith) hρ31' (by simp [hsv])]
    rw [← hweq]
    convert this using 2
    simp [ht]

/-- Half-widths of the root box in the translations. -/
def T4 (i : ℕ) : ℚ := LebesgueCover.Far8.Ts.getD (i - 1) 0

lemma far8_tau : LebesgueCover.Far8.τ = tau4 := by
  simp [LebesgueCover.Far8.τ, tau4, Rat.mkRat_eq_div]

theorem tan30_ok : tanCheck 1 30 (6889 / 65536) = true := by decide +kernel

/-- **`M(D, B₃, B₅, B₇) ≥ 0.836`**, given that the root box is good (the certificate). -/
theorem hull4_of_root_good (hroot : GoodBox ns4 tau4 (fun i => rl4.getD i 0) (fun i => rh4.getD i 0)) :
    Hull4Statement := by
  unfold Hull4Statement hull4
  refine le_iInf fun g => ?_
  set U := g 0 '' disk ∪ g 1 '' reuleaux 3 ∪ g 2 '' reuleaux 5 ∪ g 3 '' reuleaux 7 with hU
  set S := convexHull ℝ U with hS
  rw [← volume_eC_image S]
  have hconv : Convex ℝ (eC '' S) := (convex_convexHull ℝ U).linear_image eC.toLinearEquiv.toLinearMap
  set h : Fin 4 → (ℂ ≃ᵢ ℂ) := fun i => (eC.symm.toIsometryEquiv).trans ((g i).trans eC.toIsometryEquiv) with hh
  have himg : ∀ i (B : Set Plane), h i '' (eC '' B) = eC '' (g i '' B) := by
    intro i B
    simp only [hh, Set.image_image, IsometryEquiv.trans_apply, LinearIsometryEquiv.coe_toIsometryEquiv,
      LinearIsometryEquiv.symm_apply_apply]
  have hsub : ∀ i (B : Set Plane), g i '' B ⊆ U → h i '' (eC '' B) ⊆ eC '' S := by
    intro i B hB
    rw [himg]
    exact Set.image_mono (hB.trans (subset_convexHull ℝ U))
  obtain ⟨p, hfund, K, hKc, hKvol, hKD, hK1, hK2, hK3⟩ := normal_form4 h hconv
    (by rw [← eC_disk]; exact hsub 0 disk (fun x hx => Or.inl (Or.inl (Or.inl hx))))
    (by rw [← eC_reuleaux]; exact hsub 1 _ (fun x hx => Or.inl (Or.inl (Or.inr hx))))
    (by rw [← eC_reuleaux]; exact hsub 2 _ (fun x hx => Or.inl (Or.inr hx)))
    (by rw [← eC_reuleaux]; exact hsub 3 _ (fun x hx => Or.inr hx))
  rw [← hKvol]
  have hτ : ENNReal.ofReal (836 / 1000) = ENNReal.ofReal ((tau4 : ℚ) : ℝ) := by
    congr 1; norm_num [tau4, Rat.mkRat_eq_div]
  rw [hτ]
  apply le_of_lt
  have hB : ∀ i, 1 ≤ i → i ≤ ns4.length → ∀ q ∈ reuleauxC (ns4.getD (i - 1) 0), placeC p i q ∈ K := by
    intro i hi1 hi2 q hq
    have : i = 1 ∨ i = 2 ∨ i = 3 := by simp [ns4] at hi2; omega
    rcases this with rfl | rfl | rfl
    · exact hK1 q (by simpa [ns4] using hq)
    · exact hK2 q (by simpa [ns4] using hq)
    · exact hK3 q (by simpa [ns4] using hq)
  by_cases hin : ∀ i, 1 ≤ i → i ≤ 3 → |p (bTx i)| ≤ T4 i ∧ |p (bTy i)| ≤ T4 i
  · refine hroot p (fun a ha => ?_) K hKc hKD hB
    obtain ⟨⟨h2a, h2b⟩, ⟨h3a, h3b⟩⟩ := hfund
    have t30 := (tanCheck_sound tan30_ok).1
    have t7 := (tanCheck_sound tan7_ok).1
    push_cast at t30 t7
    rw [show (1 : ℝ) * Real.pi / 30 = Real.pi / 30 by ring] at t30
    rw [show (1 : ℝ) * Real.pi / 7 = Real.pi / 7 by ring] at t7
    have b1 := hin 1 le_rfl (by norm_num)
    have b2 := hin 2 (by norm_num) (by norm_num)
    have b3 := hin 3 (by norm_num) le_rfl
    simp only [ns4, List.length_cons, List.length_nil] at ha
    simp only [bTx, bTy, bS, T4, LebesgueCover.Far8.Ts] at b1 b2 b3 h2a h2b h3a h3b
    norm_num at b1 b2 b3 h2a h2b h3a h3b
    simp only [abs_le] at b1 b2 b3
    interval_cases a <;> simp [rl4, rh4, Rat.mkRat_eq_div] <;> norm_num <;> constructor <;> linarith
  · push Not at hin
    obtain ⟨i, hi1, hi3, hout⟩ := hin
    have hi : i = 1 ∨ i = 2 ∨ i = 3 := by omega
    have hfar : (T4 i : ℝ) ≤ ‖toC (transAt p i)‖ := by
      simp only [transAt, if_neg (show i ≠ 0 by omega)]
      apply toC_norm_ge
      by_contra hc; push Not at hc
      exact absurd (hout hc.1) (not_lt.mpr hc.2)
    rw [← far8_tau]
    have hpoly := LebesgueCover.Far8.poly_ok
    have hg : gCheck (ns4.getD (i - 1) 0) (T4 i) LebesgueCover.Far8.g = true := by
      rcases hi with rfl | rfl | rfl
      · exact LebesgueCover.Far8.g3_ok
      · exact LebesgueCover.Far8.g5_ok
      · exact LebesgueCover.Far8.g7_ok
    have hodd : Odd (ns4.getD (i - 1) 0) := by
      rcases hi with rfl | rfl | rfl
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
    have h3 : 3 ≤ ns4.getD (i - 1) 0 := by
      rcases hi with rfl | rfl | rfl <;> decide
    have hik : i ≤ ns4.length := by simp [ns4]; omega
    exact far_good hpoly hi1 hik hodd h3 hg p hfar hKc hKD hB

end LebesgueCover.Cert
