import Kneser.AsymptoticTruncation
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
Spatial holomorphy of finite asymptotic coefficients is a consequence of
compact uniform expansions of the actual positive-parameter holomorphic
family.  No regularity of the initially given coefficient functions is
assumed.  Holomorphy of the family is only required eventually on each
compact source set, as supplied by the prepared coordinates.
-/

set_option autoImplicit false
noncomputable section

namespace Kneser.FiniteExpansionHolomorphy

open Filter Set Metric
open scoped Topology BigOperators

def complexPolynomial (c : ℕ → ℂ → ℂ) (m : ℕ) (s u : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (m + 1), s ^ j * c j u

def extractor (F : ℝ → ℂ → ℂ) (c : ℕ → ℂ → ℂ) (j : ℕ) (s : ℝ) (u : ℂ) : ℂ :=
  ((s : ℂ) ^ j)⁻¹ * (F s u - ∑ k ∈ Finset.range j, (s : ℂ) ^ k * c k u)

theorem extractor_sub_identity (F : ℝ → ℂ → ℂ) (c : ℕ → ℂ → ℂ)
    (j : ℕ) (s : ℝ) (hs : s ≠ 0) (u : ℂ) :
    extractor F c j s u - c j u =
      ((s : ℂ) ^ j)⁻¹ * (F s u - complexPolynomial c j (s : ℂ) u) := by
  have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  unfold extractor complexPolynomial
  rw [Finset.sum_range_succ]
  field_simp
  ring

theorem norm_extractor_sub_le (F : ℝ → ℂ → ℂ) (c : ℕ → ℂ → ℂ)
    (j : ℕ) (C s : ℝ) (hs : 0 < s) (u : ℂ)
    (hb : ‖F s u - complexPolynomial c j (s : ℂ) u‖ ≤ C * s ^ (j + 1)) :
    ‖extractor F c j s u - c j u‖ ≤ C * s := by
  rw [extractor_sub_identity F c j s hs.ne' u, norm_mul, norm_inv, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  calc
    _ ≤ (s ^ j)⁻¹ * (C * s ^ (j + 1)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = C * s := by rw [pow_succ]; field_simp

theorem tendstoUniformlyOn_extractor (F : ℝ → ℂ → ℂ) (c : ℕ → ℂ → ℂ)
    (j : ℕ) (K : Set ℂ) (C : ℝ)
    (hb : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ K,
      ‖F s u - complexPolynomial c j (s : ℂ) u‖ ≤ C * s ^ (j + 1)) :
    TendstoUniformlyOn (extractor F c j) (c j) (𝓝[>] (0 : ℝ)) K := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have ht : Tendsto (fun s : ℝ => C * s) (𝓝[>] 0) (𝓝 0) := by
    simpa using ((tendsto_id : Tendsto (fun s : ℝ => s) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ))).const_mul C).mono_left
      nhdsWithin_le_nhds
  have he := ht.eventually (gt_mem_nhds hε)
  filter_upwards [hb, self_mem_nhdsWithin, he] with s hs hsp hsmall
  intro u hu
  have hh := (norm_extractor_sub_le F c j C s hsp u (hs u hu)).trans_lt hsmall
  simpa only [dist_eq_norm, norm_sub_rev] using hh

theorem extractor_differentiableOn (F : ℝ → ℂ → ℂ) (c : ℕ → ℂ → ℂ)
    (j : ℕ) (s : ℝ) (U : Set ℂ) (hF : DifferentiableOn ℂ (F s) U)
    (hc : ∀ k < j, DifferentiableOn ℂ (c k) U) :
    DifferentiableOn ℂ (extractor F c j s) U := by
  apply (differentiableOn_const (((s : ℂ) ^ j)⁻¹)).mul
  apply hF.sub
  apply DifferentiableOn.fun_sum
  intro k hk
  exact (differentiableOn_const ((s : ℂ) ^ k)).mul (hc k (Finset.mem_range.mp hk))

/-- Every coefficient through order m is genuinely holomorphic.  All
family assumptions are compact local; in particular there is no assumed
common parameter neighborhood on a noncompact petal or gate. -/
theorem coefficients_analyticOnNhd (F : ℝ → ℂ → ℂ) (c : ℕ → ℂ → ℂ)
    (m : ℕ) (U : Set ℂ) (hU : IsOpen U)
    (hF : ∀ K : Set ℂ, IsCompact K → K ⊆ U →
      ∀ᶠ s : ℝ in 𝓝[>] 0, AnalyticOnNhd ℂ (F s) K)
    (hExpansion : ∀ j ≤ m, ∀ K : Set ℂ, IsCompact K → K ⊆ U →
      ∃ C : ℝ, ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ K,
        ‖F s u - complexPolynomial c j (s : ℂ) u‖ ≤ C * s ^ (j + 1)) :
    ∀ j ≤ m, AnalyticOnNhd ℂ (c j) U := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj u hu
    obtain ⟨δ, hδ, hsub⟩ := Metric.isOpen_iff.mp hU u hu
    let r := δ / 2
    have hr : 0 < r := by dsimp [r]; linarith
    have hclosed : closedBall u r ⊆ U := by
      intro z hz
      apply hsub
      have hd : dist z u ≤ r := hz
      change dist z u < δ
      dsimp [r] at hd
      linarith
    obtain ⟨C, hb⟩ := hExpansion j hj (closedBall u r) (isCompact_closedBall u r) hclosed
    have hlimit := (tendstoUniformlyOn_extractor F c j (closedBall u r) C hb).tendstoLocallyUniformlyOn.mono
      (ball_subset_closedBall : ball u r ⊆ closedBall u r)
    have hfamily : ∀ᶠ s : ℝ in 𝓝[>] 0,
        DifferentiableOn ℂ (extractor F c j s) (ball u r) := by
      filter_upwards [hF (closedBall u r) (isCompact_closedBall u r) hclosed] with s hs
      apply extractor_differentiableOn F c j s (ball u r)
      · intro z hz
        exact (hs z (ball_subset_closedBall hz)).differentiableAt.differentiableWithinAt
      · intro k hk z hz
        exact (ih k hk (by omega) z (hclosed (ball_subset_closedBall hz))).differentiableAt.differentiableWithinAt
    exact (hlimit.differentiableOn hfamily isOpen_ball).analyticAt
      (isOpen_ball.mem_nhds (mem_ball_self hr))

theorem analyticAt_complexPolynomial (c : ℕ → ℂ → ℂ) (m : ℕ)
    (s u : ℂ) (hc : ∀ j ≤ m, AnalyticAt ℂ (c j) u) :
    AnalyticAt ℂ (fun p : ℂ × ℂ => complexPolynomial c m p.1 p.2) (s, u) := by
  have haj (j : ℕ) (hj : j ∈ Finset.range (m + 1)) :
      AnalyticAt ℂ (fun p : ℂ × ℂ => p.1 ^ j * c j p.2) (s, u) := by
    have hja : AnalyticAt ℂ (fun p : ℂ × ℂ => c j p.2) (s, u) :=
      (hc j (by have h := Finset.mem_range.mp hj; omega)).comp analyticAt_snd
    exact (analyticAt_fst.pow j).mul hja
  have he : (fun p : ℂ × ℂ => complexPolynomial c m p.1 p.2) =
      ∑ j ∈ Finset.range (m + 1), (fun p : ℂ × ℂ => p.1 ^ j * c j p.2) := by
    funext p
    simp only [complexPolynomial, Finset.sum_apply]
  rw [he]
  exact (Finset.range (m + 1)).analyticAt_sum haj

end Kneser.FiniteExpansionHolomorphy

end
