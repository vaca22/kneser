import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Constructed stable holomorphic inverses

A common affine approximation constructs an actual inverse on a common
smaller image disc by the quantitative Banach inverse theorem. Its spatial
holomorphy, Lipschitz bound, and stability are consequences rather than
hypotheses about a pre-existing moving inverse.
-/

set_option autoImplicit false
noncomputable section

namespace Kneser.StableHolomorphicInverse

open Filter Set Metric
open scoped Topology NNReal

/-- On a disc where a map approximates the identity with error at most
one half, its inverse distance estimate has the explicit constant two. -/
theorem norm_sub_le_two_mul_norm_image_sub (F : ℂ → ℂ) (r : ℝ)
    (hF : ApproximatesLinearOn F (ContinuousLinearMap.id ℂ ℂ) (ball 0 (2 * r)) (1 / 2))
    (x y : ℂ) (hx : x ∈ ball 0 (2 * r)) (hy : y ∈ ball 0 (2 * r)) :
    ‖x - y‖ ≤ 2 * ‖F x - F y‖ := by
  have h := hF x hx y hy
  norm_num at h
  have heq : x - y = (F x - F y) - (F x - F y - (x - y)) := by ring
  have hn := norm_sub_le (F x - F y) (F x - F y - (x - y))
  rw [← heq] at hn
  linarith

/-- The common affine approximation forces every spatial derivative on the
disc to remain nonzero. -/
theorem norm_deriv_lower (F : ℂ → ℂ) (r : ℝ)
    (hF : ApproximatesLinearOn F (ContinuousLinearMap.id ℂ ℂ) (ball 0 (2 * r)) (1 / 2))
    (ha : AnalyticOnNhd ℂ F (ball 0 (2 * r))) (x : ℂ) (hx : x ∈ ball 0 (2 * r)) :
    (1 / 2 : ℝ) ≤ ‖deriv F x‖ := by
  have hG : HasDerivAt (fun w : ℂ => F w - w) (deriv F x - 1) x :=
    (ha x hx).hasStrictDerivAt.hasDerivAt.sub (hasDerivAt_id x)
  have hlip : LipschitzOnWith (1 / 2 : ℝ≥0) (fun w : ℂ => F w - w) (ball 0 (2 * r)) := by
    convert hF.lipschitzOnWith using 1
    funext w
    simp
  have hb := norm_deriv_le_of_lipschitzOn (𝕜 := ℂ) (isOpen_ball.mem_nhds hx) hlip
  rw [hG.deriv] at hb
  norm_num at hb
  have hn := norm_sub_norm_le (1 : ℂ) (deriv F x)
  rw [norm_sub_rev] at hn
  norm_num at hn
  linarith

/-- Quantitative inverse construction on a common image disc. The proof
constructs the inverse, proves its equation and holomorphy, and obtains its
Lipschitz estimate. No inverse branch is an input. -/
theorem exists_holomorphic_inverse_on_disc (F : ℂ → ℂ) (r : ℝ) (hr : 0 < r)
    (hF : ApproximatesLinearOn F (ContinuousLinearMap.id ℂ ℂ) (ball 0 (2 * r)) (1 / 2))
    (ha : AnalyticOnNhd ℂ F (ball 0 (2 * r))) (hcenter : ‖F 0‖ ≤ r / 4) :
    ∃ V : ℂ → ℂ,
      (∀ z ∈ ball (0 : ℂ) (r / 4), V z ∈ closedBall (0 : ℂ) r ∧ F (V z) = z) ∧
      AnalyticOnNhd ℂ V (ball (0 : ℂ) (r / 4)) ∧
      (∀ z ∈ ball (0 : ℂ) (r / 4), ∀ w ∈ ball (0 : ℂ) (r / 4),
        ‖V z - V w‖ ≤ 2 * ‖z - w‖) := by
  have hsub : closedBall (0 : ℂ) r ⊆ ball (0 : ℂ) (2 * r) := by
    intro x hx
    have hxr : dist x 0 ≤ r := hx
    change dist x 0 < 2 * r
    linarith
  have hsurj : SurjOn F (closedBall (0 : ℂ) r) (closedBall (F 0) (r / 2)) := by
    have h := hF.surjOn_closedBall_of_nonlinearRightInverse
      (ContinuousLinearEquiv.refl ℂ ℂ).toNonlinearRightInverse hr.le hsub
    have hn : (ContinuousLinearEquiv.refl ℂ ℂ).toNonlinearRightInverse.nnnorm = 1 := by
      change ‖ContinuousLinearMap.id ℂ ℂ‖₊ = 1
      exact ContinuousLinearMap.nnnorm_id
    rw [hn] at h
    convert h using 1
    norm_num
    ring_nf
  have hex : ∀ z : ℂ, ∃ v : ℂ,
      z ∈ ball (0 : ℂ) (r / 4) → v ∈ closedBall (0 : ℂ) r ∧ F v = z := by
    intro z
    by_cases hz : z ∈ ball (0 : ℂ) (r / 4)
    · have hnorm : ‖z‖ < r / 4 := by simpa only [mem_ball, dist_zero_right] using hz
      have hzt : z ∈ closedBall (F 0) (r / 2) := by
        rw [mem_closedBall, dist_eq_norm]
        exact (norm_sub_le z (F 0)).trans (by linarith)
      obtain ⟨v, hv, heq⟩ := hsurj hzt
      exact ⟨v, fun _ => ⟨hv, heq⟩⟩
    · exact ⟨0, fun h => False.elim (hz h)⟩
  let V : ℂ → ℂ := fun z => Classical.choose (hex z)
  have hV : ∀ z ∈ ball (0 : ℂ) (r / 4), V z ∈ closedBall (0 : ℂ) r ∧ F (V z) = z :=
    fun z hz => Classical.choose_spec (hex z) hz
  have hdiff : DifferentiableOn ℂ V (ball (0 : ℂ) (r / 4)) := by
    intro z hz
    have hx := hsub (hV z hz).1
    have hFa := ha (V z) hx
    have hdne : deriv F (V z) ≠ 0 := by
      intro heq
      have h := norm_deriv_lower F r hF ha (V z) hx
      rw [heq, norm_zero] at h
      linarith
    have hleft : ∀ᶠ w : ℂ in 𝓝 (V z), V (F w) = w := by
      have hw : ∀ᶠ w : ℂ in 𝓝 (V z), w ∈ ball (0 : ℂ) (2 * r) := isOpen_ball.mem_nhds hx
      have hFz : F (V z) ∈ ball (0 : ℂ) (r / 4) := by rwa [(hV z hz).2]
      have hFw := hFa.continuousAt.eventually (isOpen_ball.mem_nhds hFz)
      filter_upwards [hw, hFw] with w hw hFw
      have hinv := hV (F w) hFw
      have h := norm_sub_le_two_mul_norm_image_sub F r hF (V (F w)) w (hsub hinv.1) hw
      rw [hinv.2, sub_self, norm_zero, mul_zero] at h
      exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))
    have hd := hFa.hasStrictDerivAt.to_local_left_inverse hdne hleft
    rw [(hV z hz).2] at hd
    exact hd.hasDerivAt.differentiableAt.differentiableWithinAt
  refine ⟨V, hV, fun z hz => hdiff.analyticAt (isOpen_ball.mem_nhds hz), ?_⟩
  intro z hz w hw
  have h := norm_sub_le_two_mul_norm_image_sub F r hF (V z) (V w)
    (hsub (hV z hz).1) (hsub (hV w hw).1)
  simpa only [(hV z hz).2, (hV w hw).2] using h

/-- The constructed inverse is uniformly stable under a uniform map error.
The second inverse is also constructed by the preceding theorem. -/
theorem norm_inverse_difference_le (F G V W : ℂ → ℂ) (r ε : ℝ)
    (hr : 0 < r)
    (hF : ApproximatesLinearOn F (ContinuousLinearMap.id ℂ ℂ) (ball 0 (2 * r)) (1 / 2))
    (hV : ∀ z ∈ ball (0 : ℂ) (r / 4), V z ∈ closedBall (0 : ℂ) r ∧ F (V z) = z)
    (hW : ∀ z ∈ ball (0 : ℂ) (r / 4), W z ∈ closedBall (0 : ℂ) r ∧ G (W z) = z)
    (herror : ∀ x ∈ closedBall (0 : ℂ) r, ‖F x - G x‖ ≤ ε)
    (z : ℂ) (hz : z ∈ ball (0 : ℂ) (r / 4)) :
    ‖V z - W z‖ ≤ 2 * ε := by
  have hsub : closedBall (0 : ℂ) r ⊆ ball (0 : ℂ) (2 * r) := by
    intro x hx
    have hxr : dist x 0 ≤ r := hx
    change dist x 0 < 2 * r
    linarith
  have h := norm_sub_le_two_mul_norm_image_sub F r hF (V z) (W z)
    (hsub (hV z hz).1) (hsub (hW z hz).1)
  calc
    _ ≤ 2 * ‖F (V z) - F (W z)‖ := h
    _ = 2 * ‖F (W z) - G (W z)‖ := by
      rw [(hV z hz).2, (hW z hz).2, norm_sub_rev]
    _ ≤ 2 * ε := mul_le_mul_of_nonneg_left (herror _ (hW z hz).1) (by norm_num)

/-- Cauchy's estimate converts a uniform holomorphic map error on a larger
closed disc into a derivative error on the smaller disc. -/
theorem norm_deriv_le_of_disc_bound (g : ℂ → ℂ) (r ε : ℝ) (hr : 0 < r)
    (hg : DiffContOnCl ℂ g (ball (0 : ℂ) (4 * r)))
    (hbound : ∀ w ∈ closedBall (0 : ℂ) (4 * r), ‖g w‖ ≤ ε)
    (x : ℂ) (hx : x ∈ ball (0 : ℂ) (2 * r)) : ‖deriv g x‖ ≤ ε / r := by
  have hxn : ‖x‖ < 2 * r := by simpa [mem_ball, dist_zero_right] using hx
  have hsub : ball x r ⊆ ball (0 : ℂ) (4 * r) := by
    intro w hw
    have hwn : ‖w - x‖ < r := by simpa [mem_ball, dist_eq_norm] using hw
    have hn := norm_add_le (w - x) x
    rw [sub_add_cancel] at hn
    simp only [mem_ball, dist_zero_right]
    linarith
  apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr (hg.mono hsub)
  intro w hw
  have hwn : ‖w - x‖ = r := by simpa [mem_sphere, dist_eq_norm] using hw
  apply hbound w
  have hn := norm_add_le (w - x) x
  rw [sub_add_cancel] at hn
  simp only [mem_closedBall, dist_zero_right]
  linarith

/-- Uniform holomorphic convergence preserves a strict affine approximation.
The approximation for the moving map is proved using a genuine Cauchy estimate. -/
theorem approximates_identity_of_disc_error (F G : ℂ → ℂ) (r ε : ℝ)
    (hr : 0 < r)
    (hF : ApproximatesLinearOn F (ContinuousLinearMap.id ℂ ℂ)
      (ball (0 : ℂ) (2 * r)) (1 / 4))
    (hg : DiffContOnCl ℂ (fun w => G w - F w) (ball (0 : ℂ) (4 * r)))
    (hbound : ∀ w ∈ closedBall (0 : ℂ) (4 * r), ‖G w - F w‖ ≤ ε)
    (hε : ε ≤ r / 4) :
    ApproximatesLinearOn G (ContinuousLinearMap.id ℂ ℂ)
      (ball (0 : ℂ) (2 * r)) (1 / 2) := by
  have hd : ∀ x ∈ ball (0 : ℂ) (2 * r), ‖deriv (fun w => G w - F w) x‖ ≤ (1 / 4 : ℝ) := by
    intro x hx
    exact (norm_deriv_le_of_disc_bound _ r ε hr hg hbound x hx).trans
      ((div_le_iff₀ hr).mpr (by linarith))
  intro x hx y hy
  have hxy := Convex.norm_image_sub_le_of_norm_deriv_le
    (𝕜 := ℂ) (f := fun w => G w - F w)
    (fun w hw => hg.differentiableAt isOpen_ball (by
      simp only [mem_ball, dist_zero_right] at hw ⊢
      linarith)) hd (convex_ball (0 : ℂ) (2 * r)) hy hx
  have hf := hF x hx y hy
  have heq : G x - G y - (ContinuousLinearMap.id ℂ ℂ) (x - y) =
      (F x - F y - (ContinuousLinearMap.id ℂ ℂ) (x - y)) +
        ((G x - F x) - (G y - F y)) := by simp; ring
  rw [heq]
  have hn := norm_add_le (F x - F y - (ContinuousLinearMap.id ℂ ℂ) (x - y))
    ((G x - F x) - (G y - F y))
  norm_num at hf hn ⊢
  exact hn.trans (by linarith)

/-- The normalized fixed map has a quantitative affine approximation on some
small disc solely from its strict derivative, rather than an inverse assumption. -/
theorem exists_identity_approximation_disc (F : ℂ → ℂ)
    (hF : HasStrictDerivAt F 1 0) :
    ∃ r > 0, ApproximatesLinearOn F (ContinuousLinearMap.id ℂ ℂ)
      (ball (0 : ℂ) (2 * r)) (1 / 4) := by
  have hstrict : HasStrictFDerivAt F (ContinuousLinearMap.id ℂ ℂ) 0 := by
    have heq : ContinuousLinearMap.toSpanSingleton ℂ (1 : ℂ) = ContinuousLinearMap.id ℂ ℂ := by
      ext
      simp
    simpa only [heq] using hF.hasStrictFDerivAt
  obtain ⟨t, ht, happ⟩ := hstrict.approximates_deriv_on_nhds (c := (1 / 4 : ℝ≥0))
    (Or.inr (by norm_num))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp ht
  refine ⟨δ / 2, by positivity, ?_⟩
  have heq : 2 * (δ / 2) = δ := by ring
  intro x hx y hy
  exact happ x (hball (by rwa [heq] at hx)) y (hball (by rwa [heq] at hy))

/-- A moving holomorphic inverse is constructed on a common image disc
from uniform holomorphic convergence. Neither existence nor continuity of
moving inverse branches is assumed. The estimate is uniform in the image point. -/
theorem exists_stable_inverse_family (F : ℝ → ℂ → ℂ) (r : ℝ) (ε : ℝ → ℝ)
    (hr : 0 < r) (h00 : F 0 0 = 0)
    (hF0 : ApproximatesLinearOn (F 0) (ContinuousLinearMap.id ℂ ℂ)
      (ball (0 : ℂ) (2 * r)) (1 / 4))
    (ha0 : DiffContOnCl ℂ (F 0) (ball (0 : ℂ) (4 * r)))
    (ha : ∀ᶠ s : ℝ in 𝓝[>] 0, DiffContOnCl ℂ (F s) (ball (0 : ℂ) (4 * r)))
    (hε : Tendsto ε (𝓝[>] 0) (𝓝 0))
    (hbound : ∀ᶠ s : ℝ in 𝓝[>] 0,
      ∀ x ∈ closedBall (0 : ℂ) (4 * r), ‖F s x - F 0 x‖ ≤ ε s) :
    ∃ V : ℝ → ℂ → ℂ,
      (∀ z ∈ ball (0 : ℂ) (r / 4), V 0 z ∈ closedBall (0 : ℂ) r ∧ F 0 (V 0 z) = z) ∧
      AnalyticOnNhd ℂ (V 0) (ball (0 : ℂ) (r / 4)) ∧
      (∀ᶠ s : ℝ in 𝓝[>] 0,
        (∀ z ∈ ball (0 : ℂ) (r / 4), V s z ∈ closedBall (0 : ℂ) r ∧ F s (V s z) = z) ∧
        AnalyticOnNhd ℂ (V s) (ball (0 : ℂ) (r / 4)) ∧
        (∀ z ∈ ball (0 : ℂ) (r / 4), ‖V s z - V 0 z‖ ≤ 2 * ε s)) ∧
      (∀ z ∈ ball (0 : ℂ) (r / 4), Tendsto (fun s => V s z) (𝓝[>] 0) (𝓝 (V 0 z))) := by
  let Good : ℝ → Prop := fun s =>
    ApproximatesLinearOn (F s) (ContinuousLinearMap.id ℂ ℂ)
      (ball (0 : ℂ) (2 * r)) (1 / 2) ∧
      AnalyticOnNhd ℂ (F s) (ball (0 : ℂ) (2 * r)) ∧ ‖F s 0‖ ≤ r / 4
  have hhalf : ApproximatesLinearOn (F 0) (ContinuousLinearMap.id ℂ ℂ)
      (ball (0 : ℂ) (2 * r)) (1 / 2) := by
    intro x hx y hy
    exact (hF0 x hx y hy).trans (by norm_num; nlinarith [norm_nonneg (x-y)])
  have hgood0 : Good 0 := by
    refine ⟨hhalf, ?_, ?_⟩
    · intro x hx
      exact ha0.differentiableOn.analyticAt (isOpen_ball.mem_nhds (by
        simp only [mem_ball, dist_zero_right] at hx ⊢; linarith))
    · rw [h00, norm_zero]
      positivity
  have hsmall : ∀ᶠ s : ℝ in 𝓝[>] 0, ε s ≤ r / 4 :=
    (hε.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < r / 4))).mono fun _ h => h.le
  have hgood : ∀ᶠ s : ℝ in 𝓝[>] 0, Good s := by
    filter_upwards [ha, hbound, hsmall] with s hs hb he
    refine ⟨approximates_identity_of_disc_error (F 0) (F s) r (ε s) hr hF0
      (by convert hs.sub ha0 using 1; rfl) hb he, ?_, ?_⟩
    · intro x hx
      exact hs.differentiableOn.analyticAt (isOpen_ball.mem_nhds (by
        simp only [mem_ball, dist_zero_right] at hx ⊢; linarith))
    · have h := hb 0 (by simp [hr.le])
      rw [h00, sub_zero] at h
      exact h.trans he
  have hex : ∀ s : ℝ, ∃ v : ℂ → ℂ, Good s →
      (∀ z ∈ ball (0 : ℂ) (r / 4), v z ∈ closedBall (0 : ℂ) r ∧ F s (v z) = z) ∧
      AnalyticOnNhd ℂ v (ball (0 : ℂ) (r / 4)) := by
    intro s
    by_cases hs : Good s
    · obtain ⟨v, hv, hav, _⟩ := exists_holomorphic_inverse_on_disc (F s) r hr hs.1 hs.2.1 hs.2.2
      exact ⟨v, fun _ => ⟨hv, hav⟩⟩
    · exact ⟨fun _ => 0, fun h => False.elim (hs h)⟩
  let V : ℝ → ℂ → ℂ := fun s => Classical.choose (hex s)
  have hV : ∀ s, Good s →
      (∀ z ∈ ball (0 : ℂ) (r / 4), V s z ∈ closedBall (0 : ℂ) r ∧ F s (V s z) = z) ∧
      AnalyticOnNhd ℂ (V s) (ball (0 : ℂ) (r / 4)) :=
    fun s hs => Classical.choose_spec (hex s) hs
  have hstability : ∀ᶠ s : ℝ in 𝓝[>] 0,
      (∀ z ∈ ball (0 : ℂ) (r / 4), V s z ∈ closedBall (0 : ℂ) r ∧ F s (V s z) = z) ∧
      AnalyticOnNhd ℂ (V s) (ball (0 : ℂ) (r / 4)) ∧
      (∀ z ∈ ball (0 : ℂ) (r / 4), ‖V s z - V 0 z‖ ≤ 2 * ε s) := by
    filter_upwards [hgood, hbound] with s hs hb
    refine ⟨(hV s hs).1, (hV s hs).2, ?_⟩
    intro z hz
    exact norm_inverse_difference_le (F s) (F 0) (V s) (V 0) r (ε s) hr hs.1
      (hV s hs).1 (hV 0 hgood0).1 (fun x hx => hb x (by
        simp only [mem_closedBall, dist_zero_right] at hx ⊢; linarith)) z hz
  refine ⟨V, (hV 0 hgood0).1, (hV 0 hgood0).2, hstability, ?_⟩
  intro z hz
  rw [← tendsto_sub_nhds_zero_iff, tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (hstability.mono fun s hs => hs.2.2 z hz)
  simpa using tendsto_const_nhds.mul hε

/-- General stable inverse construction at an arbitrary center and nonzero
slope. A small common source disc is chosen from the actual strict derivative;
the affine approximation and every moving inverse are conclusions. -/
theorem exists_stable_inverse_family_at (S : ℝ → ℂ → ℂ) (b α : ℂ) (R : ℝ)
    (ε : ℝ → ℝ) (hR : 0 < R) (hα : α ≠ 0)
    (hSder : HasStrictDerivAt (S 0) α b)
    (ha0 : DiffContOnCl ℂ (S 0) (ball b R))
    (ha : ∀ᶠ s : ℝ in 𝓝[>] 0, DiffContOnCl ℂ (S s) (ball b R))
    (hε : Tendsto ε (𝓝[>] 0) (𝓝 0))
    (hbound : ∀ᶠ s : ℝ in 𝓝[>] 0,
      ∀ x ∈ closedBall b R, ‖S s x - S 0 x‖ ≤ ε s) :
    ∃ r > 0, ∃ V : ℝ → ℂ → ℂ,
      (∀ z ∈ ball (S 0 b) (‖α‖ * r / 4), V 0 z ∈ closedBall b r ∧ S 0 (V 0 z) = z) ∧
      AnalyticOnNhd ℂ (V 0) (ball (S 0 b) (‖α‖ * r / 4)) ∧
      (∀ᶠ s : ℝ in 𝓝[>] 0,
        (∀ z ∈ ball (S 0 b) (‖α‖ * r / 4), V s z ∈ closedBall b r ∧ S s (V s z) = z) ∧
        AnalyticOnNhd ℂ (V s) (ball (S 0 b) (‖α‖ * r / 4)) ∧
        (∀ z ∈ ball (S 0 b) (‖α‖ * r / 4), ‖V s z - V 0 z‖ ≤ 2 * ε s / ‖α‖)) ∧
      (∀ z ∈ ball (S 0 b) (‖α‖ * r / 4), Tendsto (fun s => V s z) (𝓝[>] 0) (𝓝 (V 0 z))) := by
  let c := S 0 b
  let F : ℝ → ℂ → ℂ := fun s w => (S s (b + w) - c) / α
  have hFder : HasStrictDerivAt (F 0) 1 0 := by
    have hd : HasStrictDerivAt (S 0) α (b + (0 : ℂ)) := by simpa using hSder
    have hcomp : HasStrictDerivAt (fun w : ℂ => S 0 (b + w)) α 0 := by
      simpa [Function.comp_def] using hd.comp 0 ((hasStrictDerivAt_id (0 : ℂ)).const_add b)
    have hconst : HasStrictDerivAt (fun _ : ℂ => c) (0 : ℂ) (0 : ℂ) := hasStrictDerivAt_const _ _
    have hc : HasStrictDerivAt (fun w : ℂ => S 0 (b + w) - c) α 0 := by
      rw [HasStrictDerivAt, HasDerivAtFilter, hasFDerivAtFilter_iff_isLittleO]
      simpa [Pi.sub_apply, sub_zero] using (hcomp.sub hconst).hasStrictFDerivAt.isLittleO
    simpa [F, hα] using hc.div_const α
  obtain ⟨r₀, hr₀, happrox₀⟩ := exists_identity_approximation_disc (F 0) hFder
  let r := min r₀ (R / 8)
  have hr : 0 < r := lt_min hr₀ (by positivity)
  have hrr : r ≤ r₀ := min_le_left _ _
  have hrR : 4 * r < R := by have h := min_le_right r₀ (R/8); dsimp [r] at h ⊢; linarith
  have happrox : ApproximatesLinearOn (F 0) (ContinuousLinearMap.id ℂ ℂ)
      (ball (0 : ℂ) (2 * r)) (1 / 4) := by
    intro x hx y hy
    apply happrox₀ x _ y _ <;>
      simp only [mem_ball, dist_zero_right] at * <;> linarith
  have hnormDiff (f : ℂ → ℂ) (hf : DiffContOnCl ℂ f (ball b R)) :
      DiffContOnCl ℂ (fun w => (f (b + w) - c) / α) (ball (0 : ℂ) (4 * r)) := by
    have hc := hf.comp ((differentiable_const b).add differentiable_id).diffContOnCl
      (show MapsTo (fun w : ℂ => b + w) (ball (0 : ℂ) (4 * r)) (ball b R) from by
        intro w hw
        simpa [mem_ball, dist_eq_norm] using
          (show ‖w‖ < R from (by simpa [mem_ball, dist_zero_right] using hw : ‖w‖ < 4*r).trans hrR))
    have h := (hc.sub_const c).const_smul α⁻¹
    convert h using 1
    funext w
    simp [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  have hFa0 : DiffContOnCl ℂ (F 0) (ball (0 : ℂ) (4 * r)) := hnormDiff (S 0) ha0
  have hFa : ∀ᶠ s : ℝ in 𝓝[>] 0, DiffContOnCl ℂ (F s) (ball (0 : ℂ) (4 * r)) :=
    ha.mono fun s hs => hnormDiff (S s) hs
  have hbn : 0 < ‖α‖ := norm_pos_iff.mpr hα
  have hFbound : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ w ∈ closedBall (0 : ℂ) (4 * r),
      ‖F s w - F 0 w‖ ≤ ε s / ‖α‖ := by
    filter_upwards [hbound] with s hs
    intro w hw
    have hwR : b + w ∈ closedBall b R := by
      have hn : ‖w‖ ≤ 4 * r := by simpa [mem_closedBall, dist_zero_right] using hw
      simp only [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
      linarith
    have heq : F s w - F 0 w = (S s (b + w) - S 0 (b + w)) / α := by dsimp [F]; ring
    rw [heq, norm_div]
    exact div_le_div_of_nonneg_right (hs _ hwR) hbn.le
  have heps : Tendsto (fun s => ε s / ‖α‖) (𝓝[>] 0) (𝓝 0) := by simpa using hε.div_const ‖α‖
  obtain ⟨W, hW0, hWa0, hW, hWlim⟩ := exists_stable_inverse_family F r (fun s => ε s / ‖α‖)
    hr (by simp [F, c]) happrox hFa0 hFa heps hFbound
  let V : ℝ → ℂ → ℂ := fun s z => b + W s ((z - c) / α)
  have hzscale (z : ℂ) (hz : z ∈ ball c (‖α‖ * r / 4)) :
      (z - c) / α ∈ ball (0 : ℂ) (r / 4) := by
    have hn : ‖z - c‖ < ‖α‖ * r / 4 := by simpa [mem_ball, dist_eq_norm] using hz
    simp only [mem_ball, dist_zero_right, norm_div]
    apply (div_lt_iff₀ hbn).mpr
    nlinarith
  have hbranch (s : ℝ)
      (hw : ∀ z ∈ ball (0 : ℂ) (r / 4), W s z ∈ closedBall (0 : ℂ) r ∧ F s (W s z) = z) :
      ∀ z ∈ ball c (‖α‖ * r / 4), V s z ∈ closedBall b r ∧ S s (V s z) = z := by
    intro z hz
    have h := hw ((z-c)/α) (hzscale z hz)
    refine ⟨by simpa [V, mem_closedBall, dist_eq_norm] using h.1, ?_⟩
    have he := h.2
    change (S s (V s z) - c) / α = (z-c)/α at he
    have he' := (div_left_inj' hα).mp he
    linear_combination he'
  have hanalytic (s : ℝ) (hw : AnalyticOnNhd ℂ (W s) (ball (0 : ℂ) (r / 4))) :
      AnalyticOnNhd ℂ (V s) (ball c (‖α‖ * r / 4)) := by
    intro z hz
    have hscale : AnalyticAt ℂ (fun w : ℂ => (w - c) / α) z := by
      simpa using (analyticAt_id.sub (analyticAt_const (v := c))).div_const (c := α)
    exact analyticAt_const.add ((hw _ (hzscale z hz)).comp_of_eq hscale rfl)
  refine ⟨r, hr, V, hbranch 0 hW0, hanalytic 0 hWa0, ?_, ?_⟩
  · filter_upwards [hW] with s hs
    refine ⟨hbranch s hs.1, hanalytic s hs.2.1, ?_⟩
    intro z hz
    have h := hs.2.2 _ (hzscale z hz)
    simpa [V, div_eq_mul_inv, mul_assoc] using h
  · intro z hz
    simpa [V] using (hWlim _ (hzscale z hz)).const_add b

end Kneser.StableHolomorphicInverse

end
