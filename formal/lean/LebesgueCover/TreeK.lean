import LebesgueCover.VertTable
import LebK.Root3

/-!
# Certificates with explicit leaf data (kernel-checked)

For a kernel-only proof the leaf data (witnesses, centre, `β`, `σ`) are written out and each leaf is a theorem
`leafOKF … = true` proved by `decide +kernel`. A cell's tree is walked by `walk` with every leaf delegated (code
`250`): the walk checks that the leaf boxes, in DFS order, are exactly the listed boxes, and `walk_good` turns good
leaf boxes into a good cell. No float code is evaluated (the walk never reaches a `254` or `252` leaf).
-/

open LebesgueCover.Fast

namespace LebesgueCover.Cert

/-- Every box of the list is good. -/
inductive AllGood (ns : List ℕ) (τ : ℚ) : List (Array ℚ × Array ℚ) → Prop
  | nil : AllGood ns τ []
  | cons {lo hi : Array ℚ} {l : List (Array ℚ × Array ℚ)} :
      GoodBox ns τ (fun i => lo.getD i 0) (fun i => hi.getD i 0) → AllGood ns τ l → AllGood ns τ ((lo, hi) :: l)

theorem AllGood.mem {ns : List ℕ} {τ : ℚ} {l : List (Array ℚ × Array ℚ)} (h : AllGood ns τ l) :
    ∀ c ∈ l, GoodBox ns τ (fun i => c.1.getD i 0) (fun i => c.2.getD i 0) := by
  induction h with
  | nil => intro c hc; simp at hc
  | cons hb _ ih =>
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hb
    · exact ih c hc

/-- **A leaf with explicit data** that passes the fast check is good. -/
theorem leafF_good {ns : List ℕ} {V : ℕ → ℕ → ℚ × ℚ} {ν τ : ℚ} (hV : VertTableOK ns V ν) {lo hi : Array ℚ}
    {W : List (ℕ × (ℚ × ℚ))} {z : ℚ × ℚ} {β σ : ℕ → ℚ}
    (h : leafOKF ns V ν τ (fun a => lo.getD a 0) (fun a => hi.getD a 0) W z β σ = true) :
    GoodBox ns τ (fun i => lo.getD i 0) (fun i => hi.getD i 0) :=
  leaf_good hV (leafOKF_sound h)

/-- **A cell** is good if its walk with delegated items passes and the delegated boxes are good. -/
theorem cellK_good {ns : List ℕ} {V : ℕ → ℕ → ℚ × ℚ} {ν τ : ℚ} (hV : VertTableOK ns V ν) {bs : Array FBody}
    {fuel : ℕ} {codes : List ℕ} {subs : List (Array ℚ × Array ℚ)} {lo hi : Array ℚ}
    (hsubs : AllGood ns τ subs) (h : (walk ns bs V ν τ fuel codes [] subs lo hi).isSome = true) :
    GoodBox ns τ (fun i => lo.getD i 0) (fun i => hi.getD i 0) := by
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp h
  exact walk_good hV fuel codes [] subs lo hi r hsubs.mem hr

/-- The vertex table for `B₃, B₅`. -/
theorem vt3 : VertTableOK ns3 VQ nu3 := vertTable_ok (by decide)

end LebesgueCover.Cert
