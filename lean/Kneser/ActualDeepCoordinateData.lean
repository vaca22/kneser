import Kneser.BilateralFirstOrder
import Kneser.ParabolicCoordinateJacobian

/-!
One actual preparation supplies the analytic zero-parameter coordinates,
analytic explicit coefficients and compact-uniform remainders on one
common deep petal.  All analytic and quantitative inputs are derived.
-/

noncomputable section

namespace Kneser.ActualDeepCoordinateData

open Filter Set Kneser.ParabolicExponentialOrbit Kneser.PreparedActualFirstOrder
open Kneser.ReflectedPreparedFirstOrder Kneser.ReflectedOrbitChainCoefficient
open Kneser.ParabolicFatouHolomorphic Kneser.PreparedSpatialHolomorphy
open Kneser.ParabolicCoordinateJacobian
open scoped Topology

def CompactError (Q : ℝ → ℂ → ℂ) (D : ℂ → ℂ) (V : Set ℂ) : Prop :=
  ∀ S : Set ℂ, IsCompact S → S ⊆ V →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ S,
      ‖Q s u - Q 0 u - (s : ℂ) * D u‖ ≤ C * s ^ (6 / 5 : ℝ)

structure DeepCoordinateData (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (R : ℝ) : Prop where
  depth : 64 ≤ R
  attracting_analytic : ∀ u ∈ petal (R + 1),
    AnalyticAt ℂ (fun v => actualPreparedCoordinate U H e₁ e₂ A B Γ v 0) u
  attracting_coefficient_analytic : ∀ u ∈ petal (R + 1),
    AnalyticAt ℂ (actualPreparedCoefficient U H e₁ e₂ A B Γ) u
  repelling_analytic : ∀ v ∈ petal (R + 1),
    AnalyticAt ℂ (fun w => actualInversePreparedCoordinate U H e₁ e₂ A B Γ w 0) v
  repelling_coefficient_analytic : ∀ v ∈ petal (R + 1),
    AnalyticAt ℂ (actualInversePreparedCoefficient U H e₁ e₂ A B Γ) v
  attracting_canonical : ∀ u ∈ petal (R + 1),
    actualPreparedCoordinate U H e₁ e₂ A B Γ u 0 = attractingCoordinate u
  repelling_canonical : ∀ v ∈ petal (R + 1),
    actualInversePreparedCoordinate U H e₁ e₂ A B Γ v 0 = repellingCoordinate v
  attracting_derivative : ∀ u ∈ petal (R + 1),
    deriv (fun v => actualPreparedCoordinate U H e₁ e₂ A B Γ v 0) u =
      deriv attractingCoordinate u
  repelling_derivative : ∀ v ∈ petal (R + 1),
    deriv (fun w => actualInversePreparedCoordinate U H e₁ e₂ A B Γ w 0) v =
      deriv repellingCoordinate v
  attracting_error : CompactError
    (fun s u => actualPreparedCoordinate U H e₁ e₂ A B Γ u s)
    (actualPreparedCoefficient U H e₁ e₂ A B Γ) (petal (R + 1))
  repelling_error : CompactError
    (fun s v => actualInversePreparedCoordinate U H e₁ e₂ A B Γ v s)
    (actualInversePreparedCoefficient U H e₁ e₂ A B Γ) (petal (R + 1))
  attracting_jacobian : CanonicalJacobian attractingCoordinate R
  repelling_jacobian : CanonicalJacobian repellingCoordinate R
  attracting_positive : ∀ Z : ℝ, 0 ≤ Z → ∃ s₀ : ℝ, 0 < s₀ ∧
    ∀ s : ℝ, 0 < s → s < s₀ → DifferentiableOn ℂ
      (fun u => actualPreparedCoordinate U H e₁ e₂ A B Γ u s) (boundedPetal R Z)
  repelling_positive : ∀ Z : ℝ, 0 ≤ Z → ∃ s₀ : ℝ, 0 < s₀ ∧
    ∀ s : ℝ, 0 < s → s < s₀ → DifferentiableOn ℂ
      (fun v => actualInversePreparedCoordinate U H e₁ e₂ A B Γ v s) (boundedPetal R Z)
  attracting_absolute : ∀ u ∈ petal (R + 1),
    Summable (fun k => ‖ActualOrbitChainCoefficient.explicitTerm A B Γ u k‖)
  repelling_absolute : ∀ v ∈ petal (R + 1),
    Summable (fun k => ‖ReflectedOrbitChainCoefficient.explicitTerm A B Γ v k‖)
  attracting_explicit : ∀ u ∈ petal (R + 1),
    actualPreparedCoefficient U H e₁ e₂ A B Γ u =
      deriv (fun s => ExponentialModelTime.preparedModelTime U H e₁ e₂ s u) 0 +
        ∑' k : ℕ, ActualOrbitChainCoefficient.explicitTerm A B Γ u k
  repelling_explicit : ∀ v ∈ petal (R + 1),
    actualInversePreparedCoefficient U H e₁ e₂ A B Γ v =
      deriv (fun s => ExponentialModelTime.preparedModelTime (-U) (-H) e₁ (-e₂) s v) 0 +
        ∑' k : ℕ, ReflectedOrbitChainCoefficient.explicitTerm A B Γ v k

theorem canonicalJacobian_mono (f : ℂ → ℂ) {R S : ℝ} (h : R ≤ S)
    (hf : CanonicalJacobian f R) : CanonicalJacobian f S := by
  have hs : petal S ⊆ petal R := fun _ hu => h.trans_lt hu
  exact ⟨hf.1.mono hs, fun u hu => hf.2 u (hs hu)⟩

theorem DeepCoordinateData.mono {U H e₁ e₂ A B : ℂ → ℂ} {Γ : ℂ × ℂ → ℂ}
    {R T : ℝ} (hd : DeepCoordinateData U H e₁ e₂ A B Γ R) (hRT : R ≤ T) :
    DeepCoordinateData U H e₁ e₂ A B Γ T := by
  have hp : petal (T + 1) ⊆ petal (R + 1) := fun _ hu => by
    change R + 1 < _
    change T + 1 < _ at hu
    linarith
  have hb : ∀ Z : ℝ, boundedPetal T Z ⊆ boundedPetal R Z := fun _ _ hu =>
    ⟨by have h := hu.1; linarith, hu.2⟩
  refine ⟨hd.depth.trans hRT, (fun u hu => hd.attracting_analytic u (hp hu)),
    (fun u hu => hd.attracting_coefficient_analytic u (hp hu)),
    (fun u hu => hd.repelling_analytic u (hp hu)),
    (fun u hu => hd.repelling_coefficient_analytic u (hp hu)),
    (fun u hu => hd.attracting_canonical u (hp hu)),
    (fun u hu => hd.repelling_canonical u (hp hu)),
    (fun u hu => hd.attracting_derivative u (hp hu)),
    (fun u hu => hd.repelling_derivative u (hp hu)),
    (fun S hS hs => hd.attracting_error S hS (hs.trans hp)),
    (fun S hS hs => hd.repelling_error S hS (hs.trans hp)),
    canonicalJacobian_mono _ hRT hd.attracting_jacobian,
    canonicalJacobian_mono _ hRT hd.repelling_jacobian, ?_, ?_,
    (fun u hu => hd.attracting_absolute u (hp hu)),
    (fun u hu => hd.repelling_absolute u (hp hu)),
    (fun u hu => hd.attracting_explicit u (hp hu)),
    (fun u hu => hd.repelling_explicit u (hp hu))⟩
  · intro Z hZ
    obtain ⟨s₀, hs₀, hpos⟩ := hd.attracting_positive Z hZ
    exact ⟨s₀, hs₀, fun s hs hss => (hpos s hs hss).mono (hb Z)⟩
  · intro Z hZ
    obtain ⟨s₀, hs₀, hpos⟩ := hd.repelling_positive Z hZ
    exact ⟨s₀, hs₀, fun s hs hss => (hpos s hs hss).mono (hb Z)⟩

theorem deep_coordinate_data_of_bilateral
    (U H e₁ e₂ A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F Γ : ℂ × ℂ → ℂ)
    (hdata : ActualPreparationData U H e₁ e₂ A B K F Γ)
    (R₁ : ℝ)
    (ha : BilateralFirstOrder.AttractingCompactFirstOrder U H e₁ e₂ A B Γ R₁)
    (hr : ExplicitCompactFirstOrder U H e₁ e₂ A B Γ R₁)
    (hca : ∀ u : ℂ, R₁ + 1 ≤ (inverseCoordinate u).re →
      actualPreparedCoordinate U H e₁ e₂ A B Γ u 0 = attractingCoordinate u)
    (hcr : ∀ v : ℂ, R₁ + 1 ≤ (inverseCoordinate v).re →
      actualInversePreparedCoordinate U H e₁ e₂ A B Γ v 0 = repellingCoordinate v) :
    ∃ R : ℝ, DeepCoordinateData U H e₁ e₂ A B Γ R := by
  rcases hdata with ⟨hU, hU0, _hUd, hH, hHne, _hHlog, hA, hB, hA0, hB0, he₁, he₂,
    _hF, hΓ, hEven, _hK0, _hK, _hq, _hroots, _hfactor, _hprepared, _hresidue⟩
  obtain ⟨R₂, _hR₂, hcoefA⟩ := PreparedCoefficientSpatialHolomorphy.exists_holomorphic_actualPreparedCoefficient
    U H e₁ e₂ A B Γ hU hU0 hH hHne he₁ he₂ hA hB hA0 hB0 hΓ (fun x v => hEven (x, v))
  obtain ⟨R₃, _hR₃, hcoefR⟩ := ReflectedCoefficientSpatialHolomorphy.exists_holomorphic_actualInversePreparedCoefficient
    U H e₁ e₂ A B Γ hU hU0 hH hHne he₁ he₂ hA hB hA0 hB0 hΓ (fun x v => hEven (x, v))
  obtain ⟨R₄, hR₄, hjA, hjR⟩ := exists_bilateral_canonicalJacobian
  obtain ⟨R₅, _hR₅, hposA⟩ := ActualPreparedSpatialHolomorphy.exists_holomorphic_actualPreparedCoordinate
    U H e₁ e₂ A B K Γ hU hU0 _hK (by rw [_hK0]; norm_num) _hfactor hΓ
  obtain ⟨R₆, _hR₆, hposR⟩ := ReflectedPreparedSpatialHolomorphy.exists_holomorphic_actualInversePreparedCoordinate
    U H e₁ e₂ A B K Γ hU hU0 _hK (by rw [_hK0]; norm_num) _hfactor hΓ
  let Rold := max 64 (max R₁ (max R₂ (max R₃ R₄)))
  let R := max Rold (max R₅ R₆)
  have hRold : Rold ≤ R := le_max_left _ _
  have hR : 64 ≤ R := (le_max_left 64 _).trans hRold
  have h₁old : R₁ ≤ Rold := (le_max_left _ _).trans (le_max_right _ _)
  have h₂old : R₂ ≤ Rold := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have h₃old : R₃ ≤ Rold :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)
  have h₄old : R₄ ≤ Rold :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)
  have h₁ : R₁ ≤ R := h₁old.trans hRold
  have h₂ : R₂ ≤ R := h₂old.trans hRold
  have h₃ : R₃ ≤ R := h₃old.trans hRold
  have h₄ : R₄ ≤ R := h₄old.trans hRold
  have h₅ : R₅ ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have h₆ : R₆ ≤ R := (le_max_right _ _).trans (le_max_right _ _)
  have hV : IsOpen (petal (R + 1)) := petal_isOpen (by linarith)
  have hcanonA : ∀ u ∈ petal (R + 1),
      actualPreparedCoordinate U H e₁ e₂ A B Γ u 0 = attractingCoordinate u := by
    intro u hu
    exact hca u (by change R + 1 < _ at hu; linarith)
  have hcanonR : ∀ u ∈ petal (R + 1),
      actualInversePreparedCoordinate U H e₁ e₂ A B Γ u 0 = repellingCoordinate u := by
    intro u hu
    exact hcr u (by change R + 1 < _ at hu; linarith)
  have hnearA : ∀ u ∈ petal (R + 1),
      (fun v => actualPreparedCoordinate U H e₁ e₂ A B Γ v 0) =ᶠ[𝓝 u] attractingCoordinate := by
    intro u hu
    filter_upwards [hV.mem_nhds hu] with v hv
    exact hcanonA v hv
  have hnearR : ∀ u ∈ petal (R + 1),
      (fun v => actualInversePreparedCoordinate U H e₁ e₂ A B Γ v 0) =ᶠ[𝓝 u] repellingCoordinate := by
    intro u hu
    filter_upwards [hV.mem_nhds hu] with v hv
    exact hcanonR v hv
  refine ⟨R, hR, ?_, ?_, ?_, ?_, hcanonA, hcanonR,
    (fun u hu => (hnearA u hu).deriv_eq), (fun u hu => (hnearR u hu).deriv_eq), ?_, ?_,
    canonicalJacobian_mono _ h₄ hjA, canonicalJacobian_mono _ h₄ hjR, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u hu
    exact ((hjA.2 u (by change R₄ < _; change R + 1 < _ at hu; linarith)).1).congr (hnearA u hu).symm
  · intro u hu
    obtain ⟨_, _, _, hhol, _⟩ := hcoefA R h₂ (‖inverseCoordinate u‖ + 1) (by positivity)
    exact hhol.analyticAt ((boundedPetal_isOpen (by linarith)).mem_nhds
      ⟨by change R + 1 < _ at hu; linarith, by linarith⟩)
  · intro u hu
    exact ((hjR.2 u (by change R₄ < _; change R + 1 < _ at hu; linarith)).1).congr (hnearR u hu).symm
  · intro u hu
    obtain ⟨_, _, _, hhol, _⟩ := hcoefR R h₃ (‖inverseCoordinate u‖ + 1) (by positivity)
    exact hhol.analyticAt ((boundedPetal_isOpen (by linarith)).mem_nhds
      ⟨by change R + 1 < _ at hu; linarith, by linarith⟩)
  · intro S hS hp
    obtain ⟨_, heq, C, hC, he6, _⟩ := ha S hS
      (fun u hu => by have h := hp hu; change R + 1 < _ at h; linarith)
    refine ⟨C, hC, ?_⟩
    filter_upwards [he6] with s hs u hu
    rw [heq u hu]
    simpa only [Complex.real_smul] using hs u hu
  · intro S hS hp
    obtain ⟨C, _, hC, _, _, _, heq, he6, _⟩ := hr S hS
      (fun u hu => by have h := hp hu; change R + 1 < _ at h; linarith)
    refine ⟨C, hC, ?_⟩
    filter_upwards [he6] with s hs u hu
    rw [heq u hu]
    simpa only [Complex.real_smul] using hs u hu
  · intro Z hZ
    obtain ⟨s₀, _, hs₀, _, hpos⟩ := hposA R h₅ Z hZ
    exact ⟨s₀, hs₀, fun s hs hss => (hpos s hs hss).1⟩
  · intro Z hZ
    obtain ⟨s₀, _, hs₀, _, hpos⟩ := hposR R h₆ Z hZ
    exact ⟨s₀, hs₀, fun s hs hss => (hpos s hs hss).1⟩
  · intro u hu
    obtain ⟨_, _, _, _, _, _, _, hsum⟩ := hcoefA R h₂ (‖inverseCoordinate u‖ + 1) (by positivity)
    apply hsum u
    exact ⟨by change R + 1 < _ at hu; linarith, by linarith⟩
  · intro u hu
    obtain ⟨_, _, _, _, _, _, _, hsum⟩ := hcoefR R h₃ (‖inverseCoordinate u‖ + 1) (by positivity)
    apply hsum u
    exact ⟨by change R + 1 < _ at hu; linarith, by linarith⟩
  · intro u hu
    obtain ⟨_, heq, _⟩ := ha {u} isCompact_singleton (by
      intro v hv
      rcases mem_singleton_iff.mp hv with rfl
      change R + 1 < _ at hu
      linarith)
    exact heq u (mem_singleton u)
  · intro u hu
    obtain ⟨_, _, _, _, _, _, heq, _⟩ := hr {u} isCompact_singleton (by
      intro v hv
      rcases mem_singleton_iff.mp hv with rfl
      change R + 1 < _ at hu
      linarith)
    exact heq u (mem_singleton u)

theorem exists_actual_deep_coordinate_data :
    ∃ U H e₁ e₂ A B : ℂ → ℂ, ∃ K : ℂ → ℂ → ℂ, ∃ F Γ : ℂ × ℂ → ℂ,
      ActualPreparationData U H e₁ e₂ A B K F Γ ∧
        ∃ R : ℝ, DeepCoordinateData U H e₁ e₂ A B Γ R := by
  obtain ⟨U, H, e₁, e₂, A, B, K, F, Γ, hdata, R₁, _, ha, hr, hca, hcr⟩ :=
    BilateralFirstOrder.exists_actual_bilateral_explicit_first_order
  exact ⟨U, H, e₁, e₂, A, B, K, F, Γ, hdata,
    deep_coordinate_data_of_bilateral U H e₁ e₂ A B K F Γ hdata R₁ ha hr hca hcr⟩

end Kneser.ActualDeepCoordinateData

end
