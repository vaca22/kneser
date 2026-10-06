import Kneser.ReflectedPreparedDegreeCompatibility
import Kneser.CommonQuadraticBaseline

/-! One shared actual exponential preparation gives one normalized
reflected inverse coordinate, with all finite-order compact uniform
expansions. Its preparation degrees agree by genuine inverse telescoping. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Kneser.ReflectedCommonPreparedFamily

open Filter Set Metric Kneser.ExponentialUnfolding Kneser.ParabolicExponentialOrbit
open Kneser.ExponentialRootPolynomial Kneser.ReflectedEvenOrbitDiscs
open Kneser.ExponentialPreparedHigher Kneser.HigherOrderCutoff Kneser.AsymptoticBalance
open Kneser.ReflectedHigherPreparedCoordinate
open Kneser.CommonPreparedFamily (Prepared)
open scoped Topology BigOperators

def familyCoefficient (U H A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (n j : ℕ) (v : ℂ) : ℂ :=
  preparedCoefficient U H n (e n) A B (Γ n) v j

def normalizedCoordinate (U H A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (u v : ℂ) (s : ℝ) : ℂ :=
  preparedSeries U H 1 (e 1) A B (Γ 1) u s - preparedSeries U H 1 (e 1) A B (Γ 1) v s

def normalizedPolynomial (U H A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (n m : ℕ) (u v : ℂ) (s : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (m + 1), s ^ j *
    (familyCoefficient U H A B e Γ n j u - familyCoefficient U H A B e Γ n j v)

theorem normalizedPolynomial_eq_difference (U H A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (n m : ℕ) (u v s : ℂ) :
    normalizedPolynomial U H A B e Γ n m u v s =
      coordinatePolynomial (fun s => ReflectedHigherModelTime.modelTime U H n (e n) s u)
        (shiftedTerm A B (Γ n) (n + 1) u) m s -
      coordinatePolynomial (fun s => ReflectedHigherModelTime.modelTime U H n (e n) s v)
        (shiftedTerm A B (Γ n) (n + 1) v) m s := by
  simp only [normalizedPolynomial, coordinatePolynomial, familyCoefficient, preparedCoefficient,
    mul_sub, Finset.sum_sub_distrib]

def CompactAllFiniteExpansions (U H A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∀ n : ℕ, m * m + m + 1 ≤ n + 1 →
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ S : Set ℂ, IsCompact S →
      (∀ u ∈ S, R₀ + 1 ≤ (inverseCoordinate u).re) →
      (∀ u ∈ S, ∀ j ≤ m, Summable (fun k => ‖termCoefficient
        (shiftedTerm A B (Γ n) (n + 1) u) j k‖)) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ S, ∀ v ∈ S,
        ‖normalizedCoordinate U H A B e Γ u v s -
          normalizedPolynomial U H A B e Γ n m u v s‖ ≤
            C * s ^ ((m : ℝ) + gamma m (n + 1))

/-- One constant and one positive-parameter threshold work for every pair
of initial points in the chosen compact set. -/
theorem compactAllFiniteExpansions_of_common_preparations
    (U H A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F : ℂ × ℂ → ℂ)
    (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (hU : AnalyticAt ℂ U 0) (hU0 : U 0 = 0)
    (hH : AnalyticAt ℂ H 0) (hHne : H 0 ≠ 0)
    (hA : AnalyticAt ℂ A 0) (hB : AnalyticAt ℂ B 0) (hA0 : A 0 = 0) (hB0 : B 0 = 0)
    (hK : ContinuousAt (fun p : ℂ × ℂ => K p.1 p.2) 0) (hK0 : K 0 0 ≠ 0)
    (hfactor : ∀ᶠ s in 𝓝 (0 : ℂ), ∀ u,
      unfolding s u - u = rootPolynomial A B s u * K s u)
    (hprepared : ∀ n, Prepared A B F n (e n) (Γ n)) :
    CompactAllFiniteExpansions U H A B e Γ := by
  intro m hm n hN
  obtain ⟨he, hΓ, hΓeven, hprep⟩ := hprepared n
  obtain ⟨_hebase, hΓbase, _hΓbaseeven, hprepbase⟩ := hprepared 1
  obtain ⟨Rexp, hRexp, hexp⟩ := prepared_compact_higher_expansion U H A B K (Γ n)
    n (e n) hU hU0 hH hHne he hA hB hA0 hB0 hΓ (fun x u => hΓeven (x, u))
    hK hK0 hfactor m hm hN
  obtain ⟨Rcomp, hRcomp, hcomp⟩ := ReflectedPreparedDegreeCompatibility.exists_actual_normalized_compatibility U H A B K
    F (Γ n) (Γ 1) n 1 (e n) (e 1) hK hK0 hfactor hΓ hΓbase hprep hprepbase
  let R₀ : ℝ := max Rexp Rcomp
  have hR₀ : 0 < R₀ := hRexp.trans_le (le_max_left _ _)
  refine ⟨R₀, hR₀, ?_⟩
  intro S hS hpetal
  have hpetalExp : ∀ u ∈ S, Rexp + 1 ≤ (inverseCoordinate u).re := by
    intro u hu
    have hh : Rexp ≤ R₀ := le_max_left _ _
    linarith [hpetal u hu]
  obtain ⟨hsum, C, hC, hrem⟩ := hexp S hS hpetalExp
  have hune : ∀ u ∈ S, u ≠ 0 := by
    intro u hu heq
    have hh := hpetal u hu
    simp only [heq, inverseCoordinate, div_zero, Complex.zero_re] at hh
    linarith
  have hi : ContinuousOn inverseCoordinate S := by
    intro u hu
    exact (continuousAt_const.div continuousAt_id (hune u hu)).continuousWithinAt
  obtain ⟨Z₁, hZ₁⟩ := hS.exists_bound_of_continuousOn hi
  let Z : ℝ := max Z₁ 0
  have hZ : 0 ≤ Z := le_max_right _ _
  have hZu : ∀ u ∈ S, ‖inverseCoordinate u‖ ≤ Z :=
    fun u hu => (hZ₁ u hu).trans (le_max_left _ _)
  have hcompat := hcomp R₀ (le_max_right _ _) Z hZ
  refine ⟨hsum, 2 * C, by positivity, ?_⟩
  filter_upwards [hrem, hcompat] with s hs hcs u hu v hv
  have heq := hcs u v (hpetal u hu) (hZu u hu) (hpetal v hv) (hZu v hv)
  change ReflectedHigherPreparedCoordinate.preparedSeries U H n (e n) A B (Γ n) u s -
      ReflectedHigherPreparedCoordinate.preparedSeries U H n (e n) A B (Γ n) v s =
        normalizedCoordinate U H A B e Γ u v s at heq
  rw [← heq, normalizedPolynomial_eq_difference]
  have hr :
      ReflectedHigherPreparedCoordinate.preparedSeries U H n (e n) A B (Γ n) u s -
          ReflectedHigherPreparedCoordinate.preparedSeries U H n (e n) A B (Γ n) v s -
        (coordinatePolynomial (fun s => ReflectedHigherModelTime.modelTime U H n (e n) s u)
            (shiftedTerm A B (Γ n) (n + 1) u) m s -
          coordinatePolynomial (fun s => ReflectedHigherModelTime.modelTime U H n (e n) s v)
            (shiftedTerm A B (Γ n) (n + 1) v) m s) =
      (ReflectedHigherPreparedCoordinate.preparedSeries U H n (e n) A B (Γ n) u s -
        coordinatePolynomial (fun s => ReflectedHigherModelTime.modelTime U H n (e n) s u)
          (shiftedTerm A B (Γ n) (n + 1) u) m s) -
      (ReflectedHigherPreparedCoordinate.preparedSeries U H n (e n) A B (Γ n) v s -
        coordinatePolynomial (fun s => ReflectedHigherModelTime.modelTime U H n (e n) s v)
          (shiftedTerm A B (Γ n) (n + 1) v) m s) := by ring
  rw [hr]
  exact (norm_sub_le _ _).trans ((add_le_add (hs u hu) (hs v hv)).trans_eq (by ring))


def CoefficientConsistent (U H A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∀ n₁ n₂ : ℕ,
    m * m + m + 1 ≤ n₁ + 1 → m * m + m + 1 ≤ n₂ + 1 →
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ u v : ℂ,
      R₀ + 1 ≤ (inverseCoordinate u).re → R₀ + 1 ≤ (inverseCoordinate v).re →
      ∀ j ≤ m,
        familyCoefficient U H A B e Γ n₁ j u - familyCoefficient U H A B e Γ n₁ j v =
          familyCoefficient U H A B e Γ n₂ j u - familyCoefficient U H A B e Γ n₂ j v

theorem coefficientConsistent_of_compact_expansions (U H A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (hexp : CompactAllFiniteExpansions U H A B e Γ) : CoefficientConsistent U H A B e Γ := by
  intro m hm n₁ n₂ hN₁ hN₂
  obtain ⟨R₁, hR₁, hExp₁⟩ := hexp m hm n₁ hN₁
  obtain ⟨R₂, hR₂, hExp₂⟩ := hexp m hm n₂ hN₂
  let R₀ : ℝ := max R₁ R₂
  refine ⟨R₀, hR₁.trans_le (le_max_left _ _), ?_⟩
  intro u v hu hv
  let S : Set ℂ := {u, v}
  have hS : IsCompact S := ((Set.finite_singleton v).insert u).isCompact
  have hpetal₁ : ∀ w ∈ S, R₁ + 1 ≤ (inverseCoordinate w).re := by
    intro w hw
    have hh : R₁ ≤ R₀ := le_max_left _ _
    rcases Set.mem_insert_iff.mp hw with hwu | hwv
    · subst w; linarith
    · have hwv' : w = v := Set.mem_singleton_iff.mp hwv
      subst w; linarith
  have hpetal₂ : ∀ w ∈ S, R₂ + 1 ≤ (inverseCoordinate w).re := by
    intro w hw
    have hh : R₂ ≤ R₀ := le_max_right _ _
    rcases Set.mem_insert_iff.mp hw with hwu | hwv
    · subst w; linarith
    · have hwv' : w = v := Set.mem_singleton_iff.mp hwv
      subst w; linarith
  obtain ⟨_hsum₁, C₁, hC₁, hRem₁⟩ := hExp₁ S hS hpetal₁
  obtain ⟨_hsum₂, C₂, hC₂, hRem₂⟩ := hExp₂ S hS hpetal₂
  have hrem₁ : ∀ᶠ s : ℝ in 𝓝[>] 0,
      ‖normalizedCoordinate U H A B e Γ u v s -
        AsymptoticCoefficientUniqueness.polynomial (fun j =>
          familyCoefficient U H A B e Γ n₁ j u - familyCoefficient U H A B e Γ n₁ j v) m s‖ ≤
          C₁ * s ^ ((m : ℝ) + gamma m (n₁ + 1)) := by
    filter_upwards [hRem₁] with s hs
    simpa only [normalizedPolynomial, AsymptoticCoefficientUniqueness.polynomial] using
      hs u (by simp [S]) v (by simp [S])
  have hrem₂ : ∀ᶠ s : ℝ in 𝓝[>] 0,
      ‖normalizedCoordinate U H A B e Γ u v s -
        AsymptoticCoefficientUniqueness.polynomial (fun j =>
          familyCoefficient U H A B e Γ n₂ j u - familyCoefficient U H A B e Γ n₂ j v) m s‖ ≤
          C₂ * s ^ ((m : ℝ) + gamma m (n₂ + 1)) := by
    filter_upwards [hRem₂] with s hs
    simpa only [normalizedPolynomial, AsymptoticCoefficientUniqueness.polynomial] using
      hs u (by simp [S]) v (by simp [S])
  exact AsymptoticCoefficientUniqueness.coefficients_unique_of_common_expansions
    (normalizedCoordinate U H A B e Γ u v) _ _ m C₁ C₂ (gamma m (n₁ + 1)) (gamma m (n₂ + 1))
    hC₁ hC₂ (gamma_pos m (n₁ + 1) hN₁) (gamma_pos m (n₂ + 1) hN₂) hrem₁ hrem₂


end Kneser.ReflectedCommonPreparedFamily

end
