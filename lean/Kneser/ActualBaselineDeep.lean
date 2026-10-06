import Kneser.ActualDeepCoordinateData

/-! Every genuine actual preparation admits the same proved deep
coordinate certificate. This allows all-orders and first-order gate
constructions to retain identical preparation witnesses. -/

noncomputable section
namespace Kneser.ActualBaselineDeep

open Filter Set Kneser.ReflectedOrbitChainCoefficient
open Kneser.BilateralFirstOrder Kneser.ActualDeepCoordinateData
open Kneser.ParabolicExponentialOrbit Kneser.PreparedActualFirstOrder
open scoped Topology

theorem deep_data_of_actual (U H e₁ e₂ A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ)
    (F Γ : ℂ × ℂ → ℂ) (hdata : ActualPreparationData U H e₁ e₂ A B K F Γ) :
    ∃ R : ℝ, DeepCoordinateData U H e₁ e₂ A B Γ R := by
  have hcopy := hdata
  obtain ⟨hU, hU0, hUd, hH, hHne, hHlog, hA, hB, hA0, hB0, he₁, he₂,
    _hF, hΓ, hEven, hK0, hK, _hq, hroots, _hfactor, hprepared, hresidue⟩ := hcopy
  have heven : ∀ x v, Γ (-x, v) = Γ (x, v) := fun x v => hEven (x, v)
  have hKne : K 0 0 ≠ 0 := by rw [hK0]; norm_num
  obtain ⟨Ra, hRa, ha⟩ := Kneser.UniformAttractingFirstOrder.prepared_model_compact_first_order
    U H e₁ e₂ A B K Γ hU hU0 hH hHne he₁ he₂ hA hB hA0 hB0 hΓ heven hK hKne _hfactor
  obtain ⟨Rr, _hRr, hr⟩ := Kneser.UniformRepellingFirstOrder.prepared_model_compact_first_order
    U H e₁ e₂ A B K Γ hU hU0 hH hHne he₁ he₂ hA hB hA0 hB0 hΓ heven hK hKne _hfactor
  obtain ⟨Rca, _hRca, hca⟩ := Kneser.ActualOrbitChainCoefficient.exists_deep_petal_chain_identity
    A B Γ hA hB hΓ heven
  obtain ⟨Rcr, _hRcr, hcr⟩ := exists_deep_petal_chain_identity A B Γ hA hB hΓ heven
  have hcofactor := Kneser.ExponentialMatrixDividedDifference.eventually_symmetricCofactor_factor
    hU hroots (Kneser.PreparedLocalAbel.eventually_distinct_roots U hU hUd)
  obtain ⟨Rza, _hRza, hza⟩ := Kneser.PreparedCanonicalAtZero.exists_prepared_canonical_at_zero
    U H e₁ e₂ A B F Γ hU hU0 hUd (hroots.mono fun _ hx => hx.1) hH hHne hHlog
      he₁ he₂ hA hB hA0 hB0 hΓ heven hcofactor hprepared hresidue
  obtain ⟨Rzr, _hRzr, hzr⟩ := Kneser.ReflectedCanonicalAtZero.exists_reflected_canonical_at_zero
    U H e₁ e₂ A B K F Γ hdata
  let R := max Ra (max Rr (max Rca (max Rcr (max (Rza + 1) (Rzr + 1)))))
  have h₁ : Ra ≤ R := le_max_left _ _
  have h₂ : Rr ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have h₃ : Rca ≤ R := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have h₄ : Rcr ≤ R := (((le_max_left _ _).trans (le_max_right _ _)).trans
    (le_max_right _ _)).trans (le_max_right _ _)
  have h₅ : Rza + 1 ≤ R := ((((le_max_left _ _).trans (le_max_right _ _)).trans
    (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)
  have h₆ : Rzr + 1 ≤ R := ((((le_max_right _ _).trans (le_max_right _ _)).trans
    (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hat : AttractingCompactFirstOrder U H e₁ e₂ A B Γ R := by
    intro S hS hp
    have hpa : ∀ u ∈ S, Ra + 1 ≤ (inverseCoordinate u).re :=
      fun u hu => by linarith [hp u hu]
    have hchain : ∀ u ∈ S, ∀ k,
        deriv (fun s => Kneser.EvenPreparedOrbitDiscs.descendedTerm A B Γ 2 u s k) 0 =
          Kneser.ActualOrbitChainCoefficient.explicitTerm A B Γ u k :=
      fun u hu => hca u (by linarith [hp u hu])
    have heq : ∀ u ∈ S, actualPreparedCoefficient U H e₁ e₂ A B Γ u =
        Kneser.UniformActualAttracting.explicitCoefficient U H e₁ e₂ A B Γ u :=
      fun u hu => Kneser.ActualOrbitChainCoefficient.coefficient_eq_explicit_series
        U H e₁ e₂ A B Γ u (hchain u hu)
    obtain ⟨C, hC, he6, he10, hsum, hder⟩ := ha S hS hpa
    refine ⟨?_, heq, C, hC, ?_, ?_, ?_⟩
    · intro u hu
      simpa only [← hchain u hu] using hsum u hu
    · filter_upwards [he6] with s hs u hu
      simpa only [heq u hu] using hs u hu
    · filter_upwards [he10] with s hs u hu
      simpa only [heq u hu] using hs u hu
    · intro u hu
      simpa only [heq u hu] using hder u hu
  have hrep : ExplicitCompactFirstOrder U H e₁ e₂ A B Γ R := by
    apply explicit_compact_first_order_of_chain U H e₁ e₂ A B Γ R
    · intro S hS hp
      exact hr S hS (fun u hu => by linarith [hp u hu])
    · intro u hu
      exact hcr u (by linarith)
  exact deep_coordinate_data_of_bilateral U H e₁ e₂ A B K F Γ hdata R hat hrep
    (fun u hu => hza u (by linarith)) (fun u hu => hzr u (by linarith))

end Kneser.ActualBaselineDeep
