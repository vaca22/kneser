import Kneser.FiniteZetaGateProjection
import Kneser.ParabolicCoordinateJacobian
import Kneser.ParabolicJacobianAsymptotic

/-!
A whole horizontal gate is in the image of the actual finite repelling
coordinate.  The proof uses true orbit estimates and a quantitative inverse
construction on a fixed ζ disc, rather than assuming gate containment.
-/

noncomputable section
namespace Kneser.FullCanonicalImageGate

open Set Metric Filter Kneser.ParabolicExponentialOrbit
open Kneser.ParabolicCoordinateJacobian Kneser.FiniteZetaGateProjection
open scoped Topology

def canonicalGateInZeta (N : ℕ) (z : ℂ) : ℂ :=
  -repellingInZeta (inverseZetaProjection N z) + (N : ℂ)

theorem canonicalGateInZeta_eq (N : ℕ) (z : ℂ) :
    canonicalGateInZeta N z =
      FiniteGateJacobian.transportedRepellingCoordinate N (inverseCoordinate z) := by
  dsimp [canonicalGateInZeta, repellingInZeta, inverseZetaProjection,
    FiniteGateJacobian.transportedRepellingCoordinate]
  rw [Kneser.ParabolicOverlapGate.inverseCoordinate_involutive]

/-- On a high enough actual ζ disc, the transported canonical coordinate
approximates the identity in derivative. -/
theorem canonicalGate_deriv_bound (N : ℕ) (R H Y : ℝ)
    (hN : R + 34 ≤ (N : ℝ))
    (hH : 64 * ((N : ℝ) + 1) ≤ H) (hY : H + 64 ≤ Y)
    (he : 16 * (N : ℝ) / (H - (N : ℝ) / 4) ≤ 1 / 16)
    (hrep : ∀ w : ℂ, R < w.re → AnalyticAt ℂ repellingInZeta w ∧
      ‖deriv repellingInZeta w - 1‖ ≤ 1 / 16)
    (z : ℂ) (hz : z ∈ ball (Complex.I * (Y : ℂ)) 32) :
    AnalyticAt ℂ (canonicalGateInZeta N) z ∧
      ‖deriv (canonicalGateInZeta N) z - 1‖ ≤ 1 / 4 := by
  have hH0 : 0 ≤ H := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hzc : z ∈ closedBall (Complex.I * (Y : ℂ)) 32 := mem_closedBall.mpr (mem_ball.mp hz).le
  have hzH := height_on_closedBall Y 32 H (by linarith) hH0 z hzc
  have hzGate := hH.trans hzH
  have hb := (inverseZetaProjection_bound N z H hH hzH).trans he
  have hzn : ‖z - Complex.I * (Y : ℂ)‖ ≤ 32 := by simpa [mem_closedBall, dist_eq_norm] using hzc
  have hzre := (Complex.abs_re_le_norm (z - Complex.I * (Y : ℂ))).trans hzn
  have hcre : (z - Complex.I * (Y : ℂ)).re = z.re := by simp
  rw [hcre] at hzre
  have hqre := (Complex.abs_re_le_norm (inverseZetaProjection N z - (-z + (N : ℂ)))).trans hb
  simp only [Complex.sub_re, Complex.add_re, Complex.neg_re, Complex.natCast_re] at hqre
  have hq : R < (inverseZetaProjection N z).re := by
    have hqlo := (abs_le.mp hqre).1
    have hzup := (abs_le.mp hzre).2
    linarith
  obtain ⟨hra, hrb⟩ := hrep _ hq
  have hqa := analyticAt_inverseZetaProjection N z hzGate
  have hqb := inverseZetaProjection_deriv_bound N Y 32 H (by norm_num) hH (by norm_num; exact hY) z hz
  have hqb' : ‖deriv (inverseZetaProjection N) z + 1‖ ≤ 1 / 16 := by linarith
  have hnormq : ‖deriv (inverseZetaProjection N) z‖ ≤ 17 / 16 := by
    have hn := norm_sub_le (deriv (inverseZetaProjection N) z + 1) (1 : ℂ)
    rw [add_sub_cancel_right] at hn
    norm_num at hn
    linarith
  have hd := ((hra.hasStrictDerivAt.hasDerivAt.comp z hqa.hasStrictDerivAt.hasDerivAt).neg).add_const (N : ℂ)
  have ha : AnalyticAt ℂ (canonicalGateInZeta N) z :=
    (hra.comp (f := inverseZetaProjection N) hqa).neg.add analyticAt_const
  refine ⟨ha, ?_⟩
  change HasDerivAt (canonicalGateInZeta N)
    (-(deriv repellingInZeta (inverseZetaProjection N z) * deriv (inverseZetaProjection N) z)) z at hd
  rw [hd.deriv]
  have heq : -(deriv repellingInZeta (inverseZetaProjection N z) * deriv (inverseZetaProjection N) z) - 1 =
      -(deriv repellingInZeta (inverseZetaProjection N z) - 1) * deriv (inverseZetaProjection N) z -
        (deriv (inverseZetaProjection N) z + 1) := by ring
  rw [heq]
  calc
    _ ≤ ‖-(deriv repellingInZeta (inverseZetaProjection N z) - 1) * deriv (inverseZetaProjection N) z‖ +
        ‖deriv (inverseZetaProjection N) z + 1‖ := norm_sub_le _ _
    _ = ‖deriv repellingInZeta (inverseZetaProjection N z) - 1‖ * ‖deriv (inverseZetaProjection N) z‖ +
        ‖deriv (inverseZetaProjection N) z + 1‖ := by rw [norm_mul, norm_neg]
    _ ≤ (1 / 16 : ℝ) * (17 / 16) + 1 / 16 :=
      add_le_add (mul_le_mul hrb hnormq (norm_nonneg _) (by norm_num)) hqb'
    _ ≤ 1 / 4 := by norm_num

theorem approximation_of_deriv_bound (F : ℂ → ℂ)
    (ha : AnalyticOnNhd ℂ F (ball (0 : ℂ) 32))
    (hb : ∀ z ∈ ball (0 : ℂ) 32, ‖deriv F z - 1‖ ≤ 1 / 4) :
    ApproximatesLinearOn F (ContinuousLinearMap.id ℂ ℂ) (ball (0 : ℂ) 32) (1 / 4) := by
  have hd : ∀ z ∈ ball (0 : ℂ) 32, DifferentiableAt ℂ (fun w => F w - w) z :=
    fun z hz => (ha z hz).differentiableAt.sub differentiableAt_id
  have hbd : ∀ z ∈ ball (0 : ℂ) 32, ‖deriv (fun w => F w - w) z‖ ≤ 1 / 4 := by
    intro z hz
    have he := ((ha z hz).hasStrictDerivAt.hasDerivAt.sub (hasDerivAt_id z)).deriv
    change deriv (fun w => F w - w) z = deriv F z - 1 at he
    rw [he]
    exact hb z hz
  intro x hx y hy
  have h := Convex.norm_image_sub_le_of_norm_deriv_le hd hbd (convex_ball (0 : ℂ) 32) hy hx
  have he : F x - x - (F y - y) = F x - F y - (x - y) := by ring
  simpa only [he, ContinuousLinearMap.id_apply, NNReal.coe_div, NNReal.coe_one,
    NNReal.coe_ofNat] using h

/-- A true affine approximation constructs an inverse covering an entire
unit horizontal segment, together with a surrounding image disc. -/
theorem exists_full_image_gate_of_bounds (N : ℕ) (R H Y : ℝ)
    (hN : R + 34 ≤ (N : ℝ))
    (hH : 64 * ((N : ℝ) + 1) ≤ H) (hY : H + 64 ≤ Y)
    (he : 16 * (N : ℝ) / (H - (N : ℝ) / 4) ≤ 1 / 16)
    (hrep : ∀ w : ℂ, R < w.re → AnalyticAt ℂ repellingInZeta w ∧
      ‖deriv repellingInZeta w - 1‖ ≤ 1 / 16) :
    ∃ V : ℂ → ℂ, AnalyticOnNhd ℂ V (ball (0 : ℂ) 4) ∧
      (∀ w ∈ ball (0 : ℂ) 4, V w ∈ closedBall (0 : ℂ) 16 ∧
        canonicalGateInZeta N (Complex.I * (Y : ℂ) + V w) =
          canonicalGateInZeta N (Complex.I * (Y : ℂ)) + w) ∧
      (∀ x : ℝ, x ∈ Icc 0 1 →
        canonicalGateInZeta N (Complex.I * (Y : ℂ)) + ((x : ℂ) - 1 / 2) ∈
          canonicalGateInZeta N '' closedBall (Complex.I * (Y : ℂ)) 16) := by
  let c : ℂ := Complex.I * (Y : ℂ)
  let F : ℂ → ℂ := fun z => canonicalGateInZeta N (c + z) - canonicalGateInZeta N c
  have hshift : ∀ z ∈ ball (0 : ℂ) 32, c + z ∈ ball c 32 := by
    intro z hz
    simpa only [mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero] using hz
  have hfa : AnalyticOnNhd ℂ F (ball (0 : ℂ) 32) := by
    intro z hz
    have ha := (canonicalGate_deriv_bound N R H Y hN hH hY he hrep _ (hshift z hz)).1
    exact (ha.comp (f := fun w : ℂ => c + w) (analyticAt_const.add analyticAt_id)).sub analyticAt_const
  have hfb : ∀ z ∈ ball (0 : ℂ) 32, ‖deriv F z - 1‖ ≤ 1 / 4 := by
    intro z hz
    have hb := canonicalGate_deriv_bound N R H Y hN hH hY he hrep _ (hshift z hz)
    have hd := ((hb.1.hasStrictDerivAt.hasDerivAt.comp z ((hasDerivAt_id z).const_add c)).sub_const
      (canonicalGateInZeta N c)).deriv
    change deriv F z = deriv (canonicalGateInZeta N) (c + z) * 1 at hd
    rw [hd, mul_one]
    exact hb.2
  have happ := approximation_of_deriv_bound F hfa hfb
  have happ' : ApproximatesLinearOn F (ContinuousLinearMap.id ℂ ℂ)
      (ball (0 : ℂ) (2 * 16)) (1 / 2) := by
    intro x hx y hy
    have h := happ x (by norm_num at hx ⊢; exact hx) y (by norm_num at hy ⊢; exact hy)
    norm_num at h ⊢
    exact h.trans (by nlinarith [norm_nonneg (x - y)])
  obtain ⟨V, hv, hva, _⟩ := StableHolomorphicInverse.exists_holomorphic_inverse_on_disc F 16
    (by norm_num) happ' (by norm_num; exact hfa) (by simp [F]; norm_num)
  refine ⟨V, by norm_num at hva ⊢; exact hva, ?_, ?_⟩
  · intro w hw
    have hvw := hv w (by norm_num at hw ⊢; exact hw)
    refine ⟨hvw.1, ?_⟩
    have h := hvw.2
    change canonicalGateInZeta N (c + V w) - canonicalGateInZeta N c = w at h
    simpa only [add_comm] using sub_eq_iff_eq_add.mp h
  · intro x hx
    have hw : (x : ℂ) - 1 / 2 ∈ ball (0 : ℂ) (16 / 4) := by
      have hn : ‖(x : ℂ) - 1 / 2‖ ≤ 1 / 2 := by
        have he : (x : ℂ) - 1 / 2 = ((x - 1 / 2 : ℝ) : ℂ) := by push_cast; ring
        rw [he, Complex.norm_real, Real.norm_eq_abs]
        exact abs_le.mpr (by constructor <;> linarith [hx.1, hx.2])
      simp only [mem_ball, dist_zero_right]
      linarith
    have hvw := hv _ hw
    refine ⟨c + V ((x : ℂ) - 1 / 2), ?_, ?_⟩
    · simpa only [c, mem_closedBall, dist_eq_norm, add_sub_cancel_left, sub_zero] using hvw.1
    · have hh := sub_eq_iff_eq_add.mp hvw.2
      change canonicalGateInZeta N (c + V ((x : ℂ) - 1 / 2)) =
        canonicalGateInZeta N c + ((x : ℂ) - 1 / 2)
      simpa only [F, add_comm] using hh


/-- For every required finite length there are actual numerical gate
parameters with the true affine geometry. No gate containment is an input. -/
theorem exists_canonical_gate_bounds (L : ℝ) :
    ∃ (N : ℕ) (R H Y : ℝ), L ≤ (N : ℝ) ∧
      R + 34 ≤ (N : ℝ) ∧ 64 * ((N : ℝ) + 1) ≤ H ∧ H + 64 ≤ Y ∧
      16 * (N : ℝ) / (H - (N : ℝ) / 4) ≤ 1 / 16 ∧
      (∀ w : ℂ, R < w.re → AnalyticAt ℂ repellingInZeta w ∧
        ‖deriv repellingInZeta w - 1‖ ≤ 1 / 16) := by
  obtain ⟨R, _hR, hr⟩ := ParabolicJacobianAsymptotic.exists_repelling_zeta_deriv_bound
    (1 / 16) (by norm_num)
  obtain ⟨N, hn⟩ := exists_nat_gt (max L (R + 34))
  have hL : L ≤ (N : ℝ) := (le_max_left _ _).trans hn.le
  have hNR : R + 34 ≤ (N : ℝ) := (le_max_right _ _).trans hn.le
  let H : ℝ := 1024 * ((N : ℝ) + 1)
  let Y : ℝ := H + 128
  have hH : 64 * ((N : ℝ) + 1) ≤ H := by
    dsimp [H]
    linarith [Nat.cast_nonneg (α := ℝ) N]
  have hden : 0 < H - (N : ℝ) / 4 := by
    dsimp [H]
    linarith [Nat.cast_nonneg (α := ℝ) N]
  refine ⟨N, R, H, Y, hL, hNR, hH, by dsimp [Y]; linarith, ?_, ?_⟩
  · apply (div_le_iff₀ hden).mpr
    dsimp [H]
    linarith [Nat.cast_nonneg (α := ℝ) N]
  · intro w hw
    exact hr w hw

/-- Unconditional whole horizontal gate coverage by the true transported
canonical repelling coordinate, at any chosen minimum finite length. -/
theorem exists_whole_canonical_image_gate (L : ℝ) :
    ∃ (N : ℕ) (Y : ℝ) (V : ℂ → ℂ), L ≤ (N : ℝ) ∧
      64 * ((N : ℝ) + 1) + 64 ≤ Y ∧
      (∀ z ∈ ball (Complex.I * (Y : ℂ)) 32,
        AnalyticAt ℂ (canonicalGateInZeta N) z ∧
          ‖deriv (canonicalGateInZeta N) z - 1‖ ≤ 1 / 4) ∧
      AnalyticOnNhd ℂ V (ball (0 : ℂ) 4) ∧
      (∀ w ∈ ball (0 : ℂ) 4, V w ∈ closedBall (0 : ℂ) 16 ∧
        canonicalGateInZeta N (Complex.I * (Y : ℂ) + V w) =
          canonicalGateInZeta N (Complex.I * (Y : ℂ)) + w) ∧
      (∀ x : ℝ, x ∈ Icc 0 1 →
        canonicalGateInZeta N (Complex.I * (Y : ℂ)) + ((x : ℂ) - 1 / 2) ∈
          canonicalGateInZeta N '' closedBall (Complex.I * (Y : ℂ)) 16) := by
  obtain ⟨N, R, H, Y, hL, hN, hH, hY, he, hr⟩ := exists_canonical_gate_bounds L
  obtain ⟨V, hva, hv, hseg⟩ := exists_full_image_gate_of_bounds N R H Y hN hH hY he hr
  exact ⟨N, Y, V, hL, by linarith,
    fun z hz => canonicalGate_deriv_bound N R H Y hN hH hY he hr z hz, hva, hv, hseg⟩

end Kneser.FullCanonicalImageGate
end
