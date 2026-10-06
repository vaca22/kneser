import Kneser.HigherMovingPreparationCompatibility
import Kneser.ActualBilateralHigherPreparation

/-! Both actual Fatou coordinates have all finite parameter expansions on
one fixed overlap gate. Higher preparation degree changes only the later
finite petal transport, not the spatial gate or the baseline coordinate.
Every coefficient includes the genuine moving initial point, and every
orbit coefficient sum is absolutely convergent. -/

set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace Kneser.HigherGateTransport

open Filter Set Metric Kneser.ExponentialUnfolding Kneser.ParabolicExponentialOrbit
open Kneser.RepellingExponentialOrbit Kneser.ParabolicFatouHolomorphic
open Kneser.ActualBilateralGate Kneser.ActualGateAbel Kneser.HigherGateSeeds
open Kneser.HigherMovingPreparationCompatibility Kneser.CommonPreparedFamily
open Kneser.CommonQuadraticBaseline Kneser.HigherOrderCutoff Kneser.AsymptoticBalance
open Kneser.ReflectedOrbitChainCoefficient
open scoped Topology BigOperators

def forwardCoefficient (U H A B : ℂ → ℂ)
    (n : ℕ) (e : Fin (2 * n) → ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (N L : ℕ) (u : ℂ) (j : ℕ) : ℂ :=
  HigherMovingPreparedCoordinate.movingCoefficient U H n e A B Γ (forwardSeed N L) u j

def backwardCoefficient (U H A B : ℂ → ℂ)
    (n : ℕ) (e : Fin (2 * n) → ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (N L : ℕ) (u : ℂ) (j : ℕ) : ℂ :=
  -ReflectedHigherMovingPreparedCoordinate.movingCoefficient U H n e A B Γ (backwardSeed N L) u j

def polynomial (c : ℂ → ℕ → ℂ) (m : ℕ) (u v : ℂ) (s : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (m + 1), (s : ℂ) ^ j * (c u j - c v j)

theorem normalized_remainder_bound (f P : ℂ → ℂ) (C t : ℝ)
    (u v : ℂ) (hu : ‖f u - P u‖ ≤ C * t) (hv : ‖f v - P v‖ ≤ C * t) :
    ‖(f u - f v) - (P u - P v)‖ ≤ (2 * C) * t := by
  have he : (f u - f v) - (P u - P v) = (f u - P u) - (f v - P v) := by ring
  rw [he]
  exact (norm_sub_le _ _).trans ((add_le_add hu hv).trans_eq (by ring))

theorem polynomial_difference (c : ℂ → ℕ → ℂ) (m : ℕ) (u v : ℂ) (s : ℝ) :
    polynomial c m u v s =
      (∑ j ∈ Finset.range (m + 1), (s : ℂ) ^ j * c u j) -
        (∑ j ∈ Finset.range (m + 1), (s : ℂ) ^ j * c v j) := by
  simp only [polynomial, mul_sub, Finset.sum_sub_distrib]

theorem polynomial_neg (c : ℂ → ℕ → ℂ) (m : ℕ) (u v : ℂ) (s : ℝ) :
    polynomial (fun u j => -c u j) m u v s = -polynomial c m u v s := by
  simp only [polynomial, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The original finite entry length `N` and its gate are fixed before the
requested Taylor order. The later length `L` is chosen before the compact
source set. Uniform constants and parameter neighborhoods precede both
source points. -/
def FixedGateAllFiniteExpansions (U H A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ) (N : ℕ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∀ n : ℕ, m * m + m + 1 ≤ n + 1 →
    ∃ L : ℕ, ∀ S : Set ℂ, IsCompact S → S ⊆ gate 64 N →
      (∀ u ∈ S, ∀ j ≤ m, Summable (fun k => ‖termCoefficient
        (HigherMovingOrbitDiscs.descendedTerm A B (Γ n) (n + 1) (forwardSeed N L) u) j k‖)) ∧
      (∀ u ∈ S, ∀ j ≤ m, Summable (fun k => ‖termCoefficient
        (ReflectedHigherMovingPreparedCoordinate.shiftedTerm A B (Γ n) (n + 1)
          (backwardSeed N L) u) j k‖)) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ S, ∀ v ∈ S,
        ‖(ActualBilateralGate.forwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N u s -
          ActualBilateralGate.forwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N v s) -
          polynomial (forwardCoefficient U H A B n (e n) (Γ n) N L) m u v s‖ ≤
          C * s ^ ((m : ℝ) + gamma m (n + 1)) ∧
        ‖(ActualBilateralGate.backwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N u s -
          ActualBilateralGate.backwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N v s) -
          polynomial (backwardCoefficient U H A B n (e n) (Γ n) N L) m u v s‖ ≤
          C * s ^ ((m : ℝ) + gamma m (n + 1))

theorem fixedGateAllFiniteExpansions_of_actual
    (U H A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F : ℂ × ℂ → ℂ)
    (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (hdata : ActualPreparationData U H (first (e 1)) (second (e 1)) A B K F (Γ 1))
    (hprep : ∀ n, Prepared A B F n (e n) (Γ n))
    (R : ℝ) (hR : 64 ≤ R)
    (hlocal : LocalAbelData U H (first (e 1)) (second (e 1)) A B (Γ 1) R)
    (N : ℕ) (hN : R + 64 + 4 ≤ 3 * (N : ℝ) / 4) :
    FixedGateAllFiniteExpansions U H A B e Γ N := by
  obtain ⟨hU, hU0, _hUd, hH, hHne, _hHlog, hA, hB, hA0, hB0,
    _he₁, _he₂, _hF, _hΓ₁, _hEven₁, hK0, hK, _hq, _hroots, hfactor, _hp₁, _hresidue⟩ := hdata
  have hKne : K 0 0 ≠ 0 := by rw [hK0]; norm_num
  have hN64 : (130 : ℝ) ≤ 3 * (N : ℝ) / 4 := by linarith
  intro m hm n hn
  obtain ⟨he, hΓ, hEven, hp⟩ := hprep n
  obtain ⟨he₁, hΓ₁, _hEven₁, hp₁⟩ := hprep 1
  obtain ⟨Ra, hRa, ha⟩ := HigherMovingPreparedCoordinate.exists_moving_higher_expansion
    U H A B K (Γ n) n (e n) hU hU0 hH hHne he hA hB hA0 hB0 hΓ
      (fun x v => hEven (x, v)) hK hKne hfactor m hm hn
  obtain ⟨Rr, hRr, hr⟩ := ReflectedHigherMovingPreparedCoordinate.exists_moving_higher_expansion
    U H A B K (Γ n) n (e n) hU hU0 hH hHne he hA hB hA0 hB0 hΓ
      (fun x v => hEven (x, v)) hK hKne hfactor m hm hn
  obtain ⟨Rca, hRca, hca⟩ := PreparedDegreeCompatibility.exists_actual_normalized_compatibility
    U H A B K F (Γ n) (Γ 1) n 1 (e n) (e 1) hK hKne hfactor hΓ hΓ₁ hp hp₁
  obtain ⟨Rcr, hRcr, hcr⟩ := ReflectedPreparedDegreeCompatibility.exists_actual_normalized_compatibility
    U H A B K F (Γ n) (Γ 1) n 1 (e n) (e 1) hK hKne hfactor hΓ hΓ₁ hp hp₁
  let T : ℝ := max Ra (max Rr (max Rca Rcr))
  have hTa : Ra ≤ T := le_max_left _ _
  have hTr : Rr ≤ T := (le_max_left _ _).trans (le_max_right _ _)
  have hTca : Rca ≤ T := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hTcr : Rcr ≤ T := ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hT : 0 < T := hRa.trans_le hTa
  obtain ⟨L, hL⟩ := exists_nat_gt (2 * (T + 2))
  have hLT : T + 2 ≤ 64 + (L : ℝ) / 2 := by linarith
  refine ⟨L, ?_⟩
  intro S hS hSgate
  have hWa : ∀ u ∈ S, AnalyticAt ℂ (forwardSeed N L) (0, u) :=
    fun u _ => forwardSeed_analytic N L u
  have hWr : ∀ u ∈ S, AnalyticAt ℂ (backwardSeed N L) (0, u) :=
    fun u hu => backwardSeed_analytic N L hN64 u (hSgate hu)
  have hda : ∀ u ∈ S, T + 2 ≤ (inverseCoordinate (forwardSeed N L (0, u))).re :=
    fun u hu => hLT.trans (forwardSeed_depth N L hN64 u (hSgate hu))
  have hdr : ∀ u ∈ S, T + 2 ≤ (inverseCoordinate (backwardSeed N L (0, u))).re :=
    fun u hu => hLT.trans (backwardSeed_depth N L hN64 u (hSgate hu))
  obtain ⟨hsuma, Ca, hCa, hEa⟩ := ha (forwardSeed N L) S hS hWa
    (fun u hu => by linarith [hda u hu])
  obtain ⟨hsumr, Cr, hCr, hEr⟩ := hr (backwardSeed N L) S hS hWr
    (fun u hu => by linarith [hdr u hu])
  have hcompa := moving_normalized_compatibility
    (PreparedDegreeCompatibility.preparedSeries U H n (e n) A B (Γ n))
    (PreparedDegreeCompatibility.preparedSeries U H 1 (e 1) A B (Γ 1))
    T hT (hca T hTca) (forwardSeed N L) S hS hWa hda
  have hcompr := moving_normalized_compatibility
    (ReflectedHigherPreparedCoordinate.preparedSeries U H n (e n) A B (Γ n))
    (ReflectedHigherPreparedCoordinate.preparedSeries U H 1 (e 1) A B (Γ 1))
    T hT (hcr T hTcr) (backwardSeed N L) S hS hWr hdr
  have hbasea : ∀ u ∈ S, R + 2 ≤ (inverseCoordinate (forwardSeed N 0 (0, u))).re := by
    intro u hu
    have hh := gate_forward_entry u N (R + 1) (by linarith) (hSgate hu)
    have hh' : R + 1 + 1 < (inverseCoordinate (orbit u 0 N)).re := hh
    simp only [forwardSeed, orbit_zero]
    linarith
  have hbaser : ∀ u ∈ S, R + 2 ≤ (inverseCoordinate (backwardSeed N 0 (0, u))).re := by
    intro u hu
    have hh := gate_backward_entry u N (R + 1) (by linarith) (hSgate hu)
    have hh' : R + 1 + 1 < (inverseCoordinate (inverseOrbit (-u) 0 N)).re := hh
    simp only [backwardSeed, inverseOrbit_zero]
    linarith
  have habela := forward_iterated_abel_uniform
    (fun s u => PreparedActualFirstOrder.actualPreparedCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) u s)
    R hR hlocal.attracting (forwardSeed N 0) S hS
      (fun u _ => forwardSeed_analytic N 0 u) hbasea L
  have habelr := backward_iterated_abel_uniform
    (fun s v => ReflectedPreparedFirstOrder.actualInversePreparedCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) v s)
    R hR hlocal.repelling (backwardSeed N 0) S hS
      (fun u hu => backwardSeed_analytic N 0 hN64 u (hSgate hu)) hbaser L
  refine ⟨hsuma, hsumr, 2 * max Ca Cr, by positivity, ?_⟩
  filter_upwards [hEa, hEr, hcompa, hcompr, habela, habelr, self_mem_nhdsWithin] with
    s hea her hca' hcr' haba habr hsp u hu v hv
  have hsp' : 0 < s := hsp
  have ht : 0 ≤ s ^ ((m : ℝ) + gamma m (n + 1)) := (Real.rpow_pos_of_pos hsp' _).le
  have heqa :
      HigherMovingPreparedCoordinate.movingCoordinate U H n (e n) A B (Γ n) (forwardSeed N L) u s -
        HigherMovingPreparedCoordinate.movingCoordinate U H n (e n) A B (Γ n) (forwardSeed N L) v s =
      ActualBilateralGate.forwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N u s -
        ActualBilateralGate.forwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N v s := by
    rw [HigherMovingPreparedCoordinate.movingCoordinate_eq, HigherMovingPreparedCoordinate.movingCoordinate_eq,
      hca' u hu v hv, attracting_series_one, attracting_series_one]
    have hau := haba u hu
    have hav := haba v hv
    simp only [forwardSeed, orbit_zero] at hau hav ⊢
    rw [hau, hav]
    dsimp only [ActualBilateralGate.forwardCoordinate]
    ring
  have heqr :
      -(ReflectedHigherMovingPreparedCoordinate.movingCoordinate U H n (e n) A B (Γ n) (backwardSeed N L) u s -
        ReflectedHigherMovingPreparedCoordinate.movingCoordinate U H n (e n) A B (Γ n) (backwardSeed N L) v s) =
      ActualBilateralGate.backwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N u s -
        ActualBilateralGate.backwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N v s := by
    rw [ReflectedHigherMovingPreparedCoordinate.movingCoordinate_eq, ReflectedHigherMovingPreparedCoordinate.movingCoordinate_eq,
      hcr' u hu v hv, repelling_series_one, repelling_series_one]
    have hru := habr u hu
    have hrv := habr v hv
    simp only [backwardSeed, inverseOrbit_zero] at hru hrv ⊢
    rw [hru, hrv]
    dsimp only [ActualBilateralGate.backwardCoordinate]
    ring
  constructor
  · rw [← heqa, polynomial_difference]
    have he := normalized_remainder_bound
      (fun u => HigherMovingPreparedCoordinate.movingCoordinate U H n (e n) A B (Γ n) (forwardSeed N L) u s)
      (fun u => ∑ j ∈ Finset.range (m + 1), (s : ℂ) ^ j *
        HigherMovingPreparedCoordinate.movingCoefficient U H n (e n) A B (Γ n) (forwardSeed N L) u j)
      Ca (s ^ ((m : ℝ) + gamma m (n + 1))) u v (hea u hu) (hea v hv)
    exact he.trans (mul_le_mul_of_nonneg_right (by nlinarith [le_max_left Ca Cr]) ht)
  · rw [← heqr]
    change ‖-(_ - _) - polynomial (fun u j => -ReflectedHigherMovingPreparedCoordinate.movingCoefficient
      U H n (e n) A B (Γ n) (backwardSeed N L) u j) m u v s‖ ≤
        (2 * max Ca Cr) * s ^ ((m : ℝ) + gamma m (n + 1))
    rw [polynomial_neg, ← neg_sub, norm_neg, polynomial_difference]
    have he := normalized_remainder_bound
      (fun u => ReflectedHigherMovingPreparedCoordinate.movingCoordinate U H n (e n) A B (Γ n) (backwardSeed N L) u s)
      (fun u => ∑ j ∈ Finset.range (m + 1), (s : ℂ) ^ j *
        ReflectedHigherMovingPreparedCoordinate.movingCoefficient U H n (e n) A B (Γ n) (backwardSeed N L) u j)
      Cr (s ^ ((m : ℝ) + gamma m (n + 1))) u v (her u hu) (her v hv)
    have hmCr : 2 * Cr ≤ 2 * max Ca Cr := by nlinarith [le_max_right Ca Cr]
    have hle := he.trans (mul_le_mul_of_nonneg_right hmCr ht)
    simpa only [neg_sub_neg] using hle

/-- The fixed-gate endpoint is instantiated with constructed actual roots,
cofactor, logarithmic defect, and every genuine preparation degree. -/
theorem exists_actual_bilateral_fixed_gate_all_orders :
    ∃ U H A B : ℂ → ℂ, ∃ K : ℂ → ℂ → ℂ, ∃ F : ℂ × ℂ → ℂ,
    ∃ e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ, ∃ Γ : ℕ → ℂ × ℂ → ℂ,
    ∃ R : ℝ, ∃ N : ℕ,
      ActualPreparationData U H (first (e 1)) (second (e 1)) A B K F (Γ 1) ∧
      (∀ n, Prepared A B F n (e n) (Γ n)) ∧
      64 ≤ R ∧ R + 64 + 4 ≤ 3 * (N : ℝ) / 4 ∧
      FixedGateAllFiniteExpansions U H A B e Γ N := by
  obtain ⟨U, H, A, B, K, F, e, Γ, hdata, hprep, _ha, _hr, _hca, _hcr⟩ :=
    ActualBilateralHigherPreparation.exists_actual_bilateral_common_all_orders
  obtain ⟨R₀, _hR₀, hlocal₀⟩ := local_abel_data_of_actual U H (first (e 1)) (second (e 1))
    A B K F (Γ 1) hdata
  let R : ℝ := max 64 R₀
  have hR : 64 ≤ R := le_max_left _ _
  have hlocal : LocalAbelData U H (first (e 1)) (second (e 1)) A B (Γ 1) R :=
    hlocal₀.mono (le_max_right _ _)
  obtain ⟨N, hN⟩ := exists_nat_gt (4 * (R + 64 + 4) / 3)
  have hN' : R + 64 + 4 ≤ 3 * (N : ℝ) / 4 := by linarith
  exact ⟨U, H, A, B, K, F, e, Γ, R, N, hdata, hprep, hR, hN',
    fixedGateAllFiniteExpansions_of_actual U H A B K F e Γ hdata hprep R hR hlocal N hN'⟩

end Kneser.HigherGateTransport
end
