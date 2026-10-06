import Kneser.FatouBasinExtension
import Kneser.ActualGateAbel
import Kneser.ActualQuantitativeGateTransition

/-!
The actual canonical parabolic Fatou coordinates extend by their genuine
orbit entry to open regular basins. The zero-parameter transition and its
real normalization anchor are identified with those same global coordinates.
-/

set_option autoImplicit false
noncomputable section
namespace Kneser.CanonicalBasinExtension

open Filter Set Metric Kneser.FatouBasinExtension
open Kneser.ParabolicExponentialOrbit Kneser.ParabolicFatouHolomorphic
open Kneser.ParabolicCoordinateJacobian Kneser.RepellingExponentialOrbit
open Kneser.ActualDeepCoordinateData Kneser.ActualGateAbel
open Kneser.ActualQuantitativeGateTransition Kneser.ActualBilateralGate
open Kneser.PreparedActualFirstOrder Kneser.ReflectedPreparedFirstOrder
open scoped Topology

structure CanonicalSeedData (R : ℝ) : Prop where
  depth : 64 ≤ R
  attracting_map : MapsTo parabolicMap (petal R) (petal R)
  repelling_map : MapsTo parabolicInverse (petal R) (petal R)
  attracting_abel : ∀ u ∈ petal R, attractingCoordinate (parabolicMap u) = attractingCoordinate u + 1
  repelling_abel : ∀ v ∈ petal R, repellingCoordinate (parabolicInverse v) = repellingCoordinate v + 1
  attracting_jacobian : ∀ u ∈ petal R, AnalyticAt ℂ attractingCoordinate u ∧ deriv attractingCoordinate u ≠ 0
  repelling_jacobian : ∀ v ∈ petal R, AnalyticAt ℂ repellingCoordinate v ∧ deriv repellingCoordinate v ≠ 0

def globalAttracting (R : ℝ) : ℂ → ℂ := extend parabolicMap attractingCoordinate (petal R)

def globalReflected (R : ℝ) : ℂ → ℂ := extend parabolicInverse repellingCoordinate (petal R)

def globalRepelling (R : ℝ) (u : ℂ) : ℂ := -globalReflected R (-u)

theorem canonical_seed_of_deep
    (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (R : ℝ)
    (hd : DeepCoordinateData U H e₁ e₂ A B Γ R)
    (hl : LocalAbelData U H e₁ e₂ A B Γ R) : CanonicalSeedData (R + 2) := by
  have hsub : petal (R + 2) ⊆ petal (R + 1) := fun u hu => by
    change R + 2 < _ at hu
    change R + 1 < _
    linarith
  have hsub₀ : petal (R + 2) ⊆ petal R := fun u hu => by
    change R + 2 < _ at hu
    change R < _
    linarith
  have hma : MapsTo parabolicMap (petal (R + 2)) (petal (R + 2)) := by
    simpa using mapsTo_iterate_petal (R := R + 2) (by linarith [hd.depth]) 1
  have hmr : MapsTo parabolicInverse (petal (R + 2)) (petal (R + 2)) := by
    simpa using mapsTo_inverse_iterate_petal (R := R + 2) (by linarith [hd.depth]) 1
  refine ⟨by linarith [hd.depth], hma, hmr, ?_, ?_, ?_, ?_⟩
  · intro u hu
    have hh := hl.attracting_zero u (by change R + 2 < _ at hu; exact hu.le)
    have ha := hd.attracting_canonical u (hsub hu)
    have hb := hd.attracting_canonical (parabolicMap u) (hsub (hma hu))
    have heq : ExponentialUnfolding.unfolding 0 u = parabolicMap u := by
      simp [ExponentialUnfolding.unfolding, parabolicMap]
    rw [heq] at hh
    simpa only [ha, hb] using hh
  · intro v hv
    have hh := hl.repelling_zero v (by change R + 2 < _ at hv; exact hv.le)
    have ha := hd.repelling_canonical v (hsub hv)
    have hb := hd.repelling_canonical (parabolicInverse v) (hsub (hmr hv))
    simpa only [reflectedInverse_zero, ha, hb] using hh
  · intro u hu
    have h := hd.attracting_jacobian.2 u (hsub₀ hu)
    exact ⟨h.1, h.2.1⟩
  · intro v hv
    have h := hd.repelling_jacobian.2 v (hsub₀ hv)
    exact ⟨h.1, h.2.1⟩

theorem exists_actual_canonical_seed : ∃ R : ℝ, CanonicalSeedData R := by
  obtain ⟨U, H, e₁, e₂, A, B, K, F, Γ, _hdata, R, hd, hl⟩ := exists_actual_deep_abel_data
  exact ⟨R + 2, canonical_seed_of_deep U H e₁ e₂ A B Γ R hd hl⟩

theorem parabolicMap_analytic_jacobian (u : ℂ) :
    AnalyticAt ℂ parabolicMap u ∧ deriv parabolicMap u ≠ 0 := by
  have hd : HasDerivAt parabolicMap (Complex.exp u) u := by
    change HasDerivAt (fun z : ℂ => Complex.exp z - 1) (Complex.exp u) u
    exact (Complex.hasDerivAt_exp u).sub_const 1
  exact ⟨(differentiable_parabolicMap.analyticAt u), by rw [hd.deriv]; exact Complex.exp_ne_zero u⟩

theorem global_attracting_data (R : ℝ) (hs : CanonicalSeedData R) :
    IsOpen (basin parabolicMap (petal R)) ∧
    (∀ u ∈ basin parabolicMap (petal R),
      AnalyticAt ℂ (globalAttracting R) u ∧ deriv (globalAttracting R) u ≠ 0) ∧
    (∀ u ∈ basin parabolicMap (petal R),
      parabolicMap u ∈ basin parabolicMap (petal R) ∧
        globalAttracting R (parabolicMap u) = globalAttracting R u + 1) ∧
    basin parabolicMap (petal R) = {u | ∃ n : ℕ, (parabolicMap^[n]) u ∈ petal R} := by
  exact ⟨basin_isOpen _ _ (petal_isOpen (by linarith [hs.depth])),
    extend_analytic_jacobian _ _ _ (petal_isOpen (by linarith [hs.depth]))
      hs.attracting_map hs.attracting_abel hs.attracting_jacobian,
    extend_abel _ _ _ hs.attracting_map hs.attracting_abel parabolicMap_analytic_jacobian,
    basin_eq_eventual_entry _ _ parabolicMap_analytic_jacobian⟩

theorem global_reflected_data (R : ℝ) (hs : CanonicalSeedData R) :
    IsOpen (basin parabolicInverse (petal R)) ∧
    ∀ v ∈ basin parabolicInverse (petal R),
      AnalyticAt ℂ (globalReflected R) v ∧ deriv (globalReflected R) v ≠ 0 := by
  exact ⟨basin_isOpen _ _ (petal_isOpen (by linarith [hs.depth])),
    extend_analytic_jacobian _ _ _ (petal_isOpen (by linarith [hs.depth]))
      hs.repelling_map hs.repelling_abel hs.repelling_jacobian⟩

theorem inverse_gate_entry (R : ℝ) (N : ℕ) (u : ℂ)
    (hpoint : inverseOrbit (-u) 0 N ∈ petal R)
    (hg : 64 * ((N : ℝ) + 1) ≤ |(inverseCoordinate (-u)).im|) :
    Entry parabolicInverse (petal R) (-u) N := by
  have ha := FiniteGateJacobian.analyticAt_inverseOrbit_spatial_of_gate (-u) N hg N le_rfl
  have hd := FiniteGateJacobian.hasDerivAt_inverseOrbit_spatial_of_gate (-u) N hg N le_rfl
  have hn := FiniteGateJacobian.inverseOrbitSpatialJacobian_ne_zero_of_gate (-u) N hg N le_rfl
  rw [RepellingFatouCoordinate.inverseOrbit_zero_parameter] at hpoint
  have he : (fun v : ℂ => inverseOrbit v 0 N) = parabolicInverse^[N] := by
    funext v
    exact RepellingFatouCoordinate.inverseOrbit_zero_parameter v N
  rw [he] at ha hd
  exact ⟨hpoint, ha, by rw [hd.deriv]; exact hn⟩

theorem forward_zero_eq_global
    (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (R R₀ : ℝ) (N : ℕ)
    (hs : CanonicalSeedData R₀) (hRR : R₀ ≤ R)
    (hb : BilateralGateData U H e₁ e₂ A B Γ R 64 N)
    (u : ℂ) (hu : u ∈ gate 64 N) :
    forwardCoordinate U H e₁ e₂ A B Γ N u 0 = globalAttracting R₀ u := by
  have hentry := gate_forward_entry u N R hb.length hu
  have hp : (parabolicMap^[N]) u ∈ petal R₀ := by
    rw [← unfolding_orbit_zero_eq_iterate]
    change R₀ < _
    change R + 1 < _ at hentry
    linarith
  have he : Entry parabolicMap (petal R₀) u N :=
    ⟨hp, iterate_analytic_jacobian _ parabolicMap_analytic_jacobian u N⟩
  have hglobal := extend_eq_transport _ _ _ hs.attracting_map hs.attracting_abel u N he
  rw [(hb.canonical u hu).1]
  simpa only [globalAttracting, transport, unfolding_orbit_zero_eq_iterate] using hglobal.symm

theorem backward_zero_eq_global
    (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (R R₀ : ℝ) (N : ℕ)
    (hs : CanonicalSeedData R₀) (hRR : R₀ ≤ R)
    (hb : BilateralGateData U H e₁ e₂ A B Γ R 64 N)
    (u : ℂ) (hu : u ∈ gate 64 N) :
    backwardCoordinate U H e₁ e₂ A B Γ N u 0 = globalRepelling R₀ u := by
  have hentry := gate_backward_entry u N R hb.length hu
  have hp : inverseOrbit (-u) 0 N ∈ petal R₀ := by
    change R₀ < _
    change R + 1 < _ at hentry
    linarith
  have he := inverse_gate_entry R₀ N u hp (reflected_gate u N hu)
  have hglobal := extend_eq_transport _ _ _ hs.repelling_map hs.repelling_abel (-u) N he
  rw [(hb.canonical u hu).2]
  dsimp [globalRepelling, globalReflected]
  rw [hglobal]
  dsimp [transport]
  rw [← RepellingFatouCoordinate.inverseOrbit_zero_parameter]
  ring

theorem anchor_zero_eq_global
    (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (R R₀ : ℝ)
    (N M : ℕ) (Y : ℝ) (V : ℝ → ℂ → ℂ)
    (hs : CanonicalSeedData R₀) (hRR : R₀ ≤ R)
    (hd : DeepCoordinateData U H e₁ e₂ A B Γ R)
    (ht : ActualTransitionData U H e₁ e₂ A B Γ R N M Y V) :
    ActualNormalizationAnchorExpansion.anchorValue U H e₁ e₂ A B Γ M 0 =
      globalAttracting R₀ RealNormalizationAnchor.normalizationAnchor := by
  let u := RealNormalizationAnchor.normalizationAnchor
  have hp : (parabolicMap^[M]) u ∈ petal R₀ := by
    rw [← unfolding_orbit_zero_eq_iterate]
    have h := ht.anchor_entry
    change R₀ < _
    change R + 1 < _ at h
    linarith
  have he : Entry parabolicMap (petal R₀) u M :=
    ⟨hp, iterate_analytic_jacobian _ parabolicMap_analytic_jacobian u M⟩
  have hglobal := extend_eq_transport _ _ _ hs.attracting_map hs.attracting_abel u M he
  dsimp [ActualNormalizationAnchorExpansion.anchorValue]
  rw [hd.attracting_canonical _ ht.anchor_entry]
  simpa only [globalAttracting, transport, unfolding_orbit_zero_eq_iterate, u] using hglobal.symm

theorem transition_zero_eq_global
    (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (R R₀ : ℝ)
    (N M : ℕ) (Y : ℝ) (V : ℝ → ℂ → ℂ)
    (hs : CanonicalSeedData R₀) (hRR : R₀ ≤ R)
    (hd : DeepCoordinateData U H e₁ e₂ A B Γ R)
    (ht : ActualTransitionData U H e₁ e₂ A B Γ R N M Y V)
    (w : ℂ) (hw : w ∈ ball (0 : ℂ) 4) :
    transitionValue U H e₁ e₂ A B Γ N M Y V 0 w =
      globalAttracting R₀ (chartPoint Y (V 0 w)) -
        globalAttracting R₀ RealNormalizationAnchor.normalizationAnchor ∧
    globalRepelling R₀ (chartPoint Y (V 0 w)) =
      FullCanonicalImageGate.canonicalGateInZeta N (chartCenter Y) + w := by
  have hz64 : V 0 w ∈ closedBall (0 : ℂ) 64 :=
    closedBall_subset_closedBall (by norm_num) (ht.inverse_zero w hw).1
  have hu := chartPoint_in_gate N Y ht.height (V 0 w) hz64
  constructor
  · dsimp only [transitionValue, attractingChart]
    rw [forward_zero_eq_global U H e₁ e₂ A B Γ R R₀ N hs hRR ht.bilateral _ hu,
      anchor_zero_eq_global U H e₁ e₂ A B Γ R R₀ N M Y V hs hRR hd ht]
  · have hb := backward_zero_eq_global U H e₁ e₂ A B Γ R R₀ N hs hRR ht.bilateral _ hu
    have hi := (ht.inverse_zero w hw).2
    dsimp only [repellingChart] at hi
    rw [hb] at hi
    exact (sub_eq_iff_eq_add.mp hi).trans (by ring)

end Kneser.CanonicalBasinExtension
end
