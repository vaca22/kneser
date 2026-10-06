import Kneser.LensPreparedModelBridge
import Kneser.ActualHolomorphicGrowingLens
import Kneser.HigherGateSeeds
import Kneser.RealOrderedRootUniqueness

/-! The actual prepared finite-entry coordinates equal the genuine
infinite growing-lens orbit coordinates.  All finite entry lengths
cancel by actual telescoping and absolutely convergent tails. -/

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace Kneser.ActualLensPreparedCoordinateBridge

open Filter Set Metric Kneser.ActualLensModel Kneser.ActualLensBootstrap
open Kneser.ActualHolomorphicGrowingLens Kneser.ActualBilateralGate
open Kneser.ExponentialUnfolding Kneser.EvenPreparedOrbitDiscs
open Kneser.ActualInverseLensBootstrap Kneser.ActualInverseLensDynamics
open Kneser.GrowingBandGeometry Kneser.GrowingLensSpatialHolomorphy
open Kneser.PreparedActualFirstOrder Kneser.ExponentialModelTime
open Kneser.ActualReflectedLensModel Kneser.HigherGateSeeds
open scoped Topology BigOperators

theorem physical_inverse_add (s : ℝ) (u : ℂ) (N k : ℕ) :
    Kneser.ActualInverseLensBootstrap.inverseOrbit s
      (Kneser.ActualInverseLensBootstrap.inverseOrbit s u N) k =
      Kneser.ActualInverseLensBootstrap.inverseOrbit s u (N + k) := by
  induction k with
  | zero => simp
  | succ k ih => simp only [Kneser.ActualInverseLensBootstrap.inverseOrbit_succ,Nat.add_succ,ih]

theorem physical_shiftedTerm (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s : ℝ) (u : ℂ) (k : ℕ) :
    Kneser.ReflectedPreparedFirstOrder.shiftedTerm A B Γ 2 (-u) s k =
      descendedTerm A B Γ 2 (Kneser.ActualInverseLensBootstrap.inverseOrbit s u (k + 1)) s 0 := by
  unfold Kneser.ReflectedPreparedFirstOrder.shiftedTerm
    Kneser.ReflectedEvenOrbitDiscs.descendedTerm Kneser.ReflectedEvenOrbitDiscs.splitTerm
    descendedTerm splitTerm
  simp only [Kneser.AnalyticEvenDescent.square_sqrt,orbit_zero]
  rw [inverseOrbit_eq_reflected]

theorem forward_prepared_eq_lens (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (s a b θ : ℝ) (u : ℂ) (N : ℕ)
    (hmodel : ∀ v : ℂ, 0 < v.im → preparedModelTime U H e₁ e₂ s v =
      lensModel s a b θ (e₁ s) (e₂ s) v)
    (hupper : ∀ k : ℕ, 0 < (orbit u s k).im)
    (hsum : Summable (fun k => ‖descendedTerm A B Γ 2 u s k‖))
    (hstep : ∀ k : ℕ,
      lensModel s a b θ (e₁ s) (e₂ s) (unfolding s (orbit u s k)) -
        lensModel s a b θ (e₁ s) (e₂ s) (orbit u s k) - 1 =
        descendedTerm A B Γ 2 (orbit u s k) s 0) :
    forwardCoordinate U H e₁ e₂ A B Γ N u s =
      lensModel s a b θ (e₁ s) (e₂ s) u + ∑' k, descendedTerm A B Γ 2 u s k := by
  have hterm (k : ℕ) : descendedTerm A B Γ 2 (orbit u s k) s 0 = descendedTerm A B Γ 2 u s k := by
    simp only [descendedTerm,splitTerm,Kneser.AnalyticEvenDescent.square_sqrt,orbit_zero]
  have htail : (∑' k, descendedTerm A B Γ 2 (orbit u s N) s k) =
      ∑' k, descendedTerm A B Γ 2 u s (k + N) := by
    apply tsum_congr
    intro k
    simp only [descendedTerm,splitTerm,Kneser.AnalyticEvenDescent.square_sqrt]
    rw [← orbit_add,Nat.add_comm N k]
  have ht := finite_model_telescope (lensModel s a b θ (e₁ s) (e₂ s))
    (fun v => descendedTerm A B Γ 2 v s 0) u s N (fun k _ => hstep k)
  simp only [hterm] at ht
  have hh := hsum.of_norm.sum_add_tsum_nat_add N
  dsimp only [forwardCoordinate,actualPreparedCoordinate,Kneser.coordinateSeries]
  rw [hmodel _ (hupper N),htail]
  linear_combination ht + hh

theorem inverse_model_telescope (ψ f : ℂ → ℂ) (s : ℝ) (u : ℂ) (N : ℕ)
    (hstep : ∀ k < N,
      ψ (inverseStep s (Kneser.ActualInverseLensBootstrap.inverseOrbit s u k)) -
        ψ (Kneser.ActualInverseLensBootstrap.inverseOrbit s u k) + 1 =
        -f (Kneser.ActualInverseLensBootstrap.inverseOrbit s u (k + 1))) :
    ψ (Kneser.ActualInverseLensBootstrap.inverseOrbit s u N) - ψ u + N =
      -∑ k ∈ Finset.range N, f (Kneser.ActualInverseLensBootstrap.inverseOrbit s u (k + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hi := ih (fun k hk => hstep k (by omega))
    have hn := hstep N (by omega)
    rw [Finset.sum_range_succ,neg_add,← hi]
    rw [Kneser.ActualInverseLensBootstrap.inverseOrbit_succ,Nat.cast_add,Nat.cast_one]
    simp only [Kneser.ActualInverseLensBootstrap.inverseOrbit_succ] at hn
    linear_combination hn

theorem backward_prepared_eq_lens (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (s a b θ : ℝ) (u c : ℂ) (N : ℕ)
    (hmodel : ∀ v : ℂ, 0 < v.im →
      -preparedModelTime (-U) (-H) e₁ (-e₂) s (-v) = lensModel s a b θ (e₁ s) (e₂ s) v + c)
    (hupper : ∀ k : ℕ, 0 < (Kneser.ActualInverseLensBootstrap.inverseOrbit s u k).im)
    (hsum : Summable (fun k => ‖descendedTerm A B Γ 2
      (Kneser.ActualInverseLensBootstrap.inverseOrbit s u (k + 1)) s 0‖))
    (hstep : ∀ k : ℕ,
      lensModel s a b θ (e₁ s) (e₂ s)
        (inverseStep s (Kneser.ActualInverseLensBootstrap.inverseOrbit s u k)) -
      lensModel s a b θ (e₁ s) (e₂ s) (Kneser.ActualInverseLensBootstrap.inverseOrbit s u k) + 1 =
        -descendedTerm A B Γ 2 (Kneser.ActualInverseLensBootstrap.inverseOrbit s u (k + 1)) s 0) :
    backwardCoordinate U H e₁ e₂ A B Γ N u s =
      lensModel s a b θ (e₁ s) (e₂ s) u -
        ∑' k, descendedTerm A B Γ 2 (Kneser.ActualInverseLensBootstrap.inverseOrbit s u (k + 1)) s 0 + c := by
  let v := Kneser.ActualInverseLensBootstrap.inverseOrbit s u N
  have he : Kneser.RepellingExponentialOrbit.inverseOrbit (-u) (s : ℂ) N = -v := by
    dsimp [v]
    rw [inverseOrbit_eq_reflected]
    simp
  have htail : (∑' k, Kneser.ReflectedPreparedFirstOrder.shiftedTerm A B Γ 2 (-v) s k) =
      ∑' k, descendedTerm A B Γ 2
        (Kneser.ActualInverseLensBootstrap.inverseOrbit s u ((k + N) + 1)) s 0 := by
    apply tsum_congr
    intro k
    rw [physical_shiftedTerm]
    dsimp [v]
    rw [physical_inverse_add]
    simp only [Nat.add_comm N k]
  have ht := inverse_model_telescope (lensModel s a b θ (e₁ s) (e₂ s))
    (fun v => descendedTerm A B Γ 2 v s 0) s u N (fun k _ => hstep k)
  have hh := hsum.of_norm.sum_add_tsum_nat_add N
  dsimp only [backwardCoordinate,Kneser.ReflectedPreparedFirstOrder.actualInversePreparedCoordinate,
    Kneser.coordinateSeries]
  rw [he,neg_add,htail,hmodel v (hupper N)]
  dsimp only [v] at *
  linear_combination ht - hh

/-- The genuine lens control discharges all orbit, half-plane, summability
and finite telescope hypotheses. Only the actual two model branch
identities remain as explicit inputs to this bridge. -/
theorem prepared_coordinates_of_lensControl (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (s a b θ Y η M P : ℝ) (hs : 0 < s) (hs1 : s < 1)
    (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P)
    (hmodel : ∀ u : ℂ, 0 < u.im →
      preparedModelTime U H e₁ e₂ s u = lensModel s a b θ (e₁ s) (e₂ s) u ∧
      -preparedModelTime (-U) (-H) e₁ (-e₂) s (-u) =
        lensModel s a b θ (e₁ s) (e₂ s) u + residueSum s a b * (Real.pi : ℂ) * Complex.I)
    (Z : ℂ) (hZ : Z ∈ strip θ Y) (hu : 0 < (bandChart a b θ Z).im) (N : ℕ) :
    forwardCoordinate U H e₁ e₂ A B Γ N (bandChart a b θ Z) s =
      Kneser.GrowingLensSpatialHolomorphy.attractingCoordinate A B Γ s a b θ (e₁ s) (e₂ s) Z ∧
    backwardCoordinate U H e₁ e₂ A B Γ N (bandChart a b θ Z) s =
      Kneser.GrowingLensSpatialHolomorphy.repellingCoordinate A B Γ s a b θ (e₁ s) (e₂ s) Z +
        residueSum s a b * (Real.pi : ℂ) * Complex.I := by
  let u := bandChart a b θ Z
  have hdF := (hc.true_orbits Z hZ).2.2.2.2.1
  have hdG := (hc.true_orbits Z hZ).2.2.2.2.2
  have hUF : ∀ k : ℕ, 0 < (orbit u s k).im := by
    intro k
    induction k with
    | zero => exact hu
    | succ k ih =>
      rw [orbit_succ]
      apply unfolding_im_pos s _ hs.le hs1
      · exact (hdF k).2.2.1.trans (by linarith [hc.radius_small])
      · exact ih
  have hUG : ∀ k : ℕ, 0 < (Kneser.ActualInverseLensBootstrap.inverseOrbit s u k).im := by
    intro k
    induction k with
    | zero => exact hu
    | succ k ih =>
      rw [Kneser.ActualInverseLensBootstrap.inverseOrbit_succ]
      exact inverseStep_im_pos s _ hs1 ih
  refine ⟨?_,?_⟩
  · exact forward_prepared_eq_lens U H e₁ e₂ A B Γ s a b θ u N
      (fun v hv => (hmodel v hv).1) hUF (hc.true_orbits Z hZ).1
      (fun k => hc.forward_nonreal_step _ ((hdF k).2.2.1.trans_lt (by linarith [hc.radius_pos]))
        (ne_of_gt (hUF k)))
  · exact backward_prepared_eq_lens U H e₁ e₂ A B Γ s a b θ u
      (residueSum s a b * (Real.pi : ℂ) * Complex.I) N
      (fun v hv => (hmodel v hv).2) hUG (hc.true_orbits Z hZ).2.1
      (fun k => by
        simpa only [Kneser.ActualInverseLensBootstrap.inverseOrbit_succ] using
          hc.inverse_nonreal_step _ (hdG k).2.2.1
            (ne_of_gt (hUG k)))

/-- A common actual threshold makes the bridge valid for ANY controlled
lens of this preparation. Its roots, height and inverse may therefore be
the witnesses already used by the global Fourier theorem. -/
theorem exists_actual_coordinate_bridge_threshold (U H e₁ e₂ A B : ℂ → ℂ)
    (K : ℂ → ℂ → ℂ) (F Γ : ℂ × ℂ → ℂ)
    (hdata : Kneser.ReflectedOrbitChainCoefficient.ActualPreparationData U H e₁ e₂ A B K F Γ) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1 / 2 ∧
      ∀ s a b θ Y η M P : ℝ, 0 < s → s < s₀ →
        LensControl e₁ e₂ A B Γ s a b θ Y η M P →
        ∀ Z : ℂ, Z ∈ strip θ Y → 0 < (bandChart a b θ Z).im → ∀ N : ℕ,
          forwardCoordinate U H e₁ e₂ A B Γ N (bandChart a b θ Z) s =
            Kneser.GrowingLensSpatialHolomorphy.attractingCoordinate A B Γ s a b θ (e₁ s) (e₂ s) Z ∧
          backwardCoordinate U H e₁ e₂ A B Γ N (bandChart a b θ Z) s =
            Kneser.GrowingLensSpatialHolomorphy.repellingCoordinate A B Γ s a b θ (e₁ s) (e₂ s) Z +
              residueSum s a b * (Real.pi : ℂ) * Complex.I := by
  obtain ⟨ηm,sm,hηm,_hηmq,hsm,hsmh,hmodels⟩ :=
    Kneser.LensPreparedModelBridge.exists_actual_upper_model_bridge U H e₁ e₂ A B K F Γ hdata
  obtain ⟨sr,hsr,_hsrh,hroots⟩ := Kneser.RealOrderedRootUniqueness.exists_uniform_ordered_root_smallness ηm hηm
  refine ⟨min sm sr,lt_min hsm hsr,(min_le_left _ _).trans hsmh,?_⟩
  intro s a b θ Y η M P hs hss hc Z hZ hu N
  obtain ⟨ha,hb⟩ := hroots s a b hs (hss.trans_le (min_le_right _ _))
    hc.left_neg hc.right_pos hc.left_fixed hc.right_fixed
  have hm := hmodels s a b θ hs (hss.trans_le (min_le_left _ _)) ha hb
    hc.left_neg hc.right_pos hc.left_fixed hc.right_fixed hc.theta_pos hc.theta_actual
  exact prepared_coordinates_of_lensControl U H e₁ e₂ A B Γ s a b θ Y η M P hs
    (by linarith [hss.trans_le ((min_le_left sm sr).trans hsmh)]) hc hm Z hZ hu N


/-- The same actual preparation constructs a growing lens on which both
finite-entry definitions agree with its genuine infinite orbit-series
coordinates, for EVERY entry length. No model or orbit premise remains. -/
theorem exists_actual_prepared_lens_coordinates (U H e₁ e₂ A B : ℂ → ℂ)
    (K : ℂ → ℂ → ℂ) (F Γ : ℂ × ℂ → ℂ)
    (hdata : Kneser.ReflectedOrbitChainCoefficient.ActualPreparationData U H e₁ e₂ A B K F Γ) :
    ∃ Y s₀ η M P : ℝ, 2 ≤ Y ∧ 0 < s₀ ∧ s₀ ≤ 1 / 2 ∧
      ∀ s : ℝ, 0 < s → s < s₀ → ∃ a b θ : ℝ,
        LensControl e₁ e₂ A B Γ s a b θ Y η M P ∧
        ∀ Z : ℂ, Z ∈ strip θ Y → 0 < (bandChart a b θ Z).im → ∀ N : ℕ,
          forwardCoordinate U H e₁ e₂ A B Γ N (bandChart a b θ Z) s =
            Kneser.GrowingLensSpatialHolomorphy.attractingCoordinate A B Γ s a b θ (e₁ s) (e₂ s) Z ∧
          backwardCoordinate U H e₁ e₂ A B Γ N (bandChart a b θ Z) s =
            Kneser.GrowingLensSpatialHolomorphy.repellingCoordinate A B Γ s a b θ (e₁ s) (e₂ s) Z +
              residueSum s a b * (Real.pi : ℂ) * Complex.I := by
  obtain ⟨Y,sl,η,M,P,hY,hsl,hslh,hlens⟩ := exists_actual_lens_control U H e₁ e₂ A B K F Γ hdata
  obtain ⟨ηm,sm,hηm,_hηmq,hsm,_hsmh,hmodels⟩ :=
    Kneser.LensPreparedModelBridge.exists_actual_upper_model_bridge U H e₁ e₂ A B K F Γ hdata
  obtain ⟨sr,hsr,_hsrh,hroots⟩ := Kneser.RealOrderedRootUniqueness.exists_uniform_ordered_root_smallness ηm hηm
  let s₀ := min sl (min sm sr)
  refine ⟨Y,s₀,η,M,P,hY,by dsimp [s₀]; positivity,(min_le_left _ _).trans hslh,?_⟩
  intro s hs hss
  obtain ⟨a,b,θ,hc⟩ := hlens s hs (hss.trans_le (min_le_left _ _))
  obtain ⟨ha,hb⟩ := hroots s a b hs
    (hss.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
    hc.left_neg hc.right_pos hc.left_fixed hc.right_fixed
  have hm := hmodels s a b θ hs (hss.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
    ha hb hc.left_neg hc.right_pos hc.left_fixed hc.right_fixed hc.theta_pos hc.theta_actual
  refine ⟨a,b,θ,hc,?_⟩
  intro Z hZ hu N
  exact prepared_coordinates_of_lensControl U H e₁ e₂ A B Γ s a b θ Y η M P hs
    (by linarith [hss.trans_le ((min_le_left sl _).trans hslh)]) hc hm Z hZ hu N

end Kneser.ActualLensPreparedCoordinateBridge
