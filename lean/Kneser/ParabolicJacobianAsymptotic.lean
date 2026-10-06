import Kneser.ParabolicCoordinateJacobian

/-!
The actual canonical reciprocal-coordinate Jacobians approach one
uniformly on deep right half-planes. All derivative bounds are obtained
from the true orbit tail and the proved Cauchy estimate.
-/

noncomputable section

namespace Kneser.ParabolicJacobianAsymptotic

open Kneser.ParabolicCoordinateJacobian

theorem exists_model_plus_tail_deriv_bound (T : ℂ → ℂ) (sign : ℂ)
    (hsign : ‖sign‖ ≤ 1) (R B : ℝ) (hR : 0 ≤ R) (hB : 0 ≤ B)
    (hhol : DifferentiableOn ℂ T (halfPlane R))
    (hb : ∀ z ∈ halfPlane R, ‖T z‖ ≤ B / z.re)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ S : ℝ, 2 * R + 1 ≤ S ∧ ∀ z ∈ halfPlane S,
      AnalyticAt ℂ (fun w => zetaModel sign w + T w) z ∧
        ‖deriv (fun w => zetaModel sign w + T w) z - 1‖ ≤ ε := by
  let S := max (2 * R + 1) (max 1 (max (2 / (3 * ε)) (8 * B / ε)))
  have hS : 2 * R + 1 ≤ S := le_max_left _ _
  have hS1 : 1 ≤ S := (le_max_left _ _).trans (le_max_right _ _)
  have hSlog : 2 / (3 * ε) ≤ S :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hStail : 8 * B / ε ≤ S :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  refine ⟨S, hS, ?_⟩
  intro z hz
  change S < z.re at hz
  have hp : 0 < z.re := by linarith
  have hbase : z ∈ halfPlane R := by change R < _; linarith
  have hTa := hhol.analyticAt ((halfPlane_isOpen R).mem_nhds hbase)
  have hGa := (analyticAt_zetaModel sign z hp).add hTa
  have hd := (hasDerivAt_zetaModel sign z hp).add hTa.hasStrictDerivAt.hasDerivAt
  change HasDerivAt (fun w => zetaModel sign w + T w)
    (1 - sign / (3 * z) + deriv T z) z at hd
  have hm := norm_model_deriv_sub_one_le sign z hsign hp
  have ht := norm_deriv_tail_le T R B hR hB hhol hb z (by linarith)
  have hmSmall : 1 / (3 * z.re) ≤ ε / 2 := by
    have h := (div_le_iff₀ (by positivity : 0 < 3 * ε)).mp (hSlog.trans hz.le)
    apply (div_le_iff₀ (by positivity : 0 < 3 * z.re)).mpr
    nlinarith
  have htSmall : 4 * B / z.re ^ 2 ≤ ε / 2 := by
    have h := (div_le_iff₀ hε).mp (hStail.trans hz.le)
    have hs : z.re ≤ z.re ^ 2 := by nlinarith [mul_nonneg hp.le (show 0 ≤ z.re - 1 by linarith)]
    have he := mul_le_mul_of_nonneg_left hs hε.le
    apply (div_le_iff₀ (sq_pos_of_pos hp)).mpr
    nlinarith
  refine ⟨hGa, ?_⟩
  rw [hd.deriv]
  have he : 1 - sign / (3 * z) + deriv T z - 1 =
      ((1 - sign / (3 * z)) - 1) + deriv T z := by ring
  rw [he, ← (hasDerivAt_zetaModel sign z hp).deriv]
  exact (norm_add_le _ _).trans (by linarith)

theorem exists_repelling_zeta_deriv_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 64 ≤ R ∧ ∀ z ∈ halfPlane R,
      AnalyticAt ℂ repellingInZeta z ∧ ‖deriv repellingInZeta z - 1‖ ≤ ε := by
  obtain ⟨R, B, hR, hB, hhol, hb⟩ := exists_repelling_zeta_tail_bound
  obtain ⟨S, hS, hs⟩ := exists_model_plus_tail_deriv_bound repellingTailInZeta (-1)
    (by norm_num) R B (by linarith) hB hhol hb ε hε
  have he : (fun w => zetaModel (-1) w + repellingTailInZeta w) = repellingInZeta :=
    funext (fun w => (repellingInZeta_eq w).symm)
  rw [he] at hs
  exact ⟨S, by linarith, hs⟩

theorem exists_attracting_zeta_deriv_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 32 ≤ R ∧ ∀ z ∈ halfPlane R,
      AnalyticAt ℂ attractingInZeta z ∧ ‖deriv attractingInZeta z - 1‖ ≤ ε := by
  obtain ⟨R, B, hR, hB, hhol, hb⟩ := exists_attracting_zeta_tail_bound
  obtain ⟨S, hS, hs⟩ := exists_model_plus_tail_deriv_bound attractingTailInZeta 1
    (by norm_num) R B (by linarith) hB hhol hb ε hε
  have he : (fun w => zetaModel 1 w + attractingTailInZeta w) = attractingInZeta :=
    funext (fun w => (attractingInZeta_eq w).symm)
  rw [he] at hs
  exact ⟨S, by linarith, hs⟩

end Kneser.ParabolicJacobianAsymptotic

end
