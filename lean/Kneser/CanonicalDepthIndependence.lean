import Kneser.CanonicalBasinExtension

/-!
The genuine global parabolic coordinates and their regular basins are
independent of the depth used to start orbit transport. Linear inverse-
coordinate drift supplies every deeper entry, for both actual maps.
-/

set_option autoImplicit false
noncomputable section
namespace Kneser.CanonicalDepthIndependence

open Set Complex Kneser.FatouBasinExtension Kneser.CanonicalBasinExtension
open Kneser.ParabolicExponentialOrbit Kneser.ParabolicFatouHolomorphic
open Kneser.RepellingExponentialOrbit

theorem attracting_deeper_entry (R S : ℝ) (hR : 64 ≤ R) (u : ℂ) (hu : u ∈ petal R) :
    ∃ k : ℕ, (parabolicMap^[k]) u ∈ petal S := by
  obtain ⟨k, hk⟩ := exists_nat_gt (2 * S)
  have hdrift := iterate_inverse_re u (by change R < _ at hu; linarith) k
  refine ⟨k, ?_⟩
  change S < _
  change R < _ at hu
  linarith

theorem reflected_deeper_entry (R S : ℝ) (hR : 64 ≤ R) (v : ℂ) (hv : v ∈ petal R) :
    ∃ k : ℕ, (parabolicInverse^[k]) v ∈ petal S := by
  obtain ⟨k, hk⟩ := exists_nat_gt (2 * S)
  have hdrift := RepellingFatouCoordinate.inverse_iterate_re v R hR
    (by change R < _ at hv; exact hv.le) k
  refine ⟨k, ?_⟩
  change S < _
  linarith

theorem parabolicInverse_petal_analytic_jacobian (R : ℝ) (hR : 64 ≤ R)
    (v : ℂ) (hv : v ∈ petal R) :
    AnalyticAt ℂ parabolicInverse v ∧ deriv parabolicInverse v ≠ 0 := by
  have hre : 0 < (inverseCoordinate v).re := by change R < _ at hv; linarith
  have hnorm := ParabolicExponentialOrbit.norm_le_two_div_re v hre
  have hsmall : ‖v‖ < 1 := by
    have hb : 2 / (inverseCoordinate v).re ≤ 1 / 32 :=
      (div_le_iff₀ hre).mpr (by change R < _ at hv; linarith)
    linarith
  have hslit : 1 - v ∈ slitPlane := by
    apply mem_slitPlane_iff.mpr
    left
    simp only [sub_re, one_re]
    linarith [re_le_norm v]
  have ha : AnalyticAt ℂ parabolicInverse v := by
    exact ((analyticAt_const.sub analyticAt_id).clog hslit).neg
  have hd := hasDerivAt_parabolicInverse v hsmall
  exact ⟨ha, by rw [hd.deriv]; exact one_div_ne_zero (slitPlane_ne_zero hslit)⟩

theorem attracting_basins_equal (R S : ℝ)
    (hR : CanonicalSeedData R) (hS : CanonicalSeedData S) :
    basin parabolicMap (petal R) = basin parabolicMap (petal S) := by
  apply Set.Subset.antisymm
  · exact basin_subset_of_eventual_entry _ _ _ hR.attracting_map
      (fun z _ => parabolicMap_analytic_jacobian z) (attracting_deeper_entry R S hR.depth)
  · exact basin_subset_of_eventual_entry _ _ _ hS.attracting_map
      (fun z _ => parabolicMap_analytic_jacobian z) (attracting_deeper_entry S R hS.depth)

theorem reflected_basins_equal (R S : ℝ)
    (hR : CanonicalSeedData R) (hS : CanonicalSeedData S) :
    basin parabolicInverse (petal R) = basin parabolicInverse (petal S) := by
  apply Set.Subset.antisymm
  · exact basin_subset_of_eventual_entry _ _ _ hR.repelling_map
      (parabolicInverse_petal_analytic_jacobian R hR.depth) (reflected_deeper_entry R S hR.depth)
  · exact basin_subset_of_eventual_entry _ _ _ hS.repelling_map
      (parabolicInverse_petal_analytic_jacobian S hS.depth) (reflected_deeper_entry S R hS.depth)

theorem globalAttracting_equal (R S : ℝ)
    (hR : CanonicalSeedData R) (hS : CanonicalSeedData S) : globalAttracting R = globalAttracting S := by
  funext z
  classical
  by_cases hz : z ∈ basin parabolicMap (petal R)
  · exact extend_seed_agree _ _ _ _ hR.attracting_map hS.attracting_map
      hR.attracting_abel hS.attracting_abel z hz (by rwa [← attracting_basins_equal R S hR hS])
  · have hzS : z ∉ basin parabolicMap (petal S) := by rwa [← attracting_basins_equal R S hR hS]
    simp only [globalAttracting, extend, hz, hzS, dite_false]

theorem globalReflected_equal (R S : ℝ)
    (hR : CanonicalSeedData R) (hS : CanonicalSeedData S) : globalReflected R = globalReflected S := by
  funext z
  classical
  by_cases hz : z ∈ basin parabolicInverse (petal R)
  · exact extend_seed_agree _ _ _ _ hR.repelling_map hS.repelling_map
      hR.repelling_abel hS.repelling_abel z hz (by rwa [← reflected_basins_equal R S hR hS])
  · have hzS : z ∉ basin parabolicInverse (petal S) := by rwa [← reflected_basins_equal R S hR hS]
    simp only [globalReflected, extend, hz, hzS, dite_false]

theorem globalRepelling_equal (R S : ℝ)
    (hR : CanonicalSeedData R) (hS : CanonicalSeedData S) : globalRepelling R = globalRepelling S := by
  funext u
  simp only [globalRepelling, globalReflected_equal R S hR hS]

end Kneser.CanonicalDepthIndependence
end
