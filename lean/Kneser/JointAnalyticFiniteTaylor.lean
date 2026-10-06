import Kneser.FiniteTaylorImplicitInverse
import Kneser.CauchyHigherTaylor

/-! Joint analyticity supplies actual uniform integer Taylor remainders
and spatial holomorphy of all coefficients.  Both are derived on a
smaller product neighborhood by Cauchy's estimates and compact bounds. -/

set_option autoImplicit false
noncomputable section

namespace Kneser.JointAnalyticFiniteTaylor

open Filter Set Metric
open scoped Topology BigOperators
open Kneser.FiniteExpansionHolomorphy

def coefficient (W : ℂ × ℂ → ℂ) (j : ℕ) (z : ℂ) : ℂ :=
  Kneser.CauchyHigherTaylor.coefficient (fun s : ℂ => W (s, z)) j

theorem coefficient_zero (W : ℂ × ℂ → ℂ) (z : ℂ) : coefficient W 0 z = W (0, z) := by
  simp [coefficient, Kneser.CauchyHigherTaylor.coefficient]

theorem exists_uniform_finite_taylor (W : ℂ × ℂ → ℂ) (z₀ : ℂ)
    (hW : AnalyticAt ℂ W (0, z₀)) (m : ℕ) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, 0 ≤ C ∧
      (∀ j ≤ m, AnalyticOnNhd ℂ (coefficient W j) (ball z₀ r)) ∧
      (∀ s : ℂ, ‖s‖ ≤ r / 2 → ∀ z ∈ closedBall z₀ r,
        ‖W (s, z) - complexPolynomial (coefficient W) m s z‖ ≤ C * ‖s‖ ^ (m + 1)) := by
  obtain ⟨R, hR, ha⟩ := hW.exists_ball_analyticOnNhd
  let r := R / 4
  have hr : 0 < r := by dsimp [r]; positivity
  have hrR : r < R := by dsimp [r]; linarith
  have hpoint (s z : ℂ) (hs : s ∈ closedBall (0 : ℂ) r) (hz : z ∈ closedBall z₀ r) :
      (s, z) ∈ ball (0, z₀) R := by
    rw [mem_ball, Prod.dist_eq]
    exact max_lt_iff.mpr ⟨(show dist s 0 ≤ r from hs).trans_lt hrR,
      (show dist z z₀ ≤ r from hz).trans_lt hrR⟩
  let K : Set (ℂ × ℂ) := closedBall (0 : ℂ) r ×ˢ closedBall z₀ r
  have hK : IsCompact K := (isCompact_closedBall (0 : ℂ) r).prod (isCompact_closedBall z₀ r)
  have hKsub : K ⊆ ball (0, z₀) R := fun p hp => hpoint p.1 p.2 hp.1 hp.2
  obtain ⟨M₀, hM₀⟩ := hK.exists_bound_of_continuousOn (ha.continuousOn.mono hKsub)
  let M := max M₀ 0
  have hM : 0 ≤ M := le_max_right _ _
  have hbound (s z : ℂ) (hs : s ∈ closedBall (0 : ℂ) r) (hz : z ∈ closedBall z₀ r) :
      ‖W (s, z)‖ ≤ M := (hM₀ (s, z) ⟨hs, hz⟩).trans (le_max_left _ _)
  have hcurve (z : ℂ) (hz : z ∈ closedBall z₀ r) :
      DiffContOnCl ℂ (fun s : ℂ => W (s, z)) (ball (0 : ℂ) r) := by
    apply DifferentiableOn.diffContOnCl
    intro s hs
    have hsclosed : s ∈ closedBall (0 : ℂ) r := closure_ball_subset_closedBall hs
    have hh : AnalyticAt ℂ (fun s : ℂ => W (s, z)) s :=
      (ha (s, z) (hpoint s z hsclosed hz)).comp_of_eq
        (analyticAt_id.prod analyticAt_const) rfl
    exact hh.differentiableAt.differentiableWithinAt
  have hrem (j : ℕ) (s z : ℂ) (hs : ‖s‖ ≤ r / 2) (hz : z ∈ closedBall z₀ r) :
      ‖W (s, z) - complexPolynomial (coefficient W) j s z‖ ≤
        (2 * M / r ^ (j + 1)) * ‖s‖ ^ (j + 1) := by
    have hh := Kneser.CauchyHigherTaylor.norm_remainder_le (fun s : ℂ => W (s, z)) r M
      (j + 1) s hr hM (hcurve z hz)
      (fun s hs => hbound s z (sphere_subset_closedBall hs) hz) hs
    convert hh using 1
    · rfl
    · ring
  have hcoeff : ∀ j ≤ m, AnalyticOnNhd ℂ (coefficient W j) (ball z₀ r) := by
    apply coefficients_analyticOnNhd (fun s : ℝ => fun z : ℂ => W ((s : ℂ), z))
      (coefficient W) m (ball z₀ r) isOpen_ball
    · intro S _ hSsub
      have he : ∀ᶠ s : ℝ in 𝓝[>] 0, s ≤ r :=
        ((eventually_lt_nhds hr).mono fun _ hs => hs.le).filter_mono nhdsWithin_le_nhds
      filter_upwards [he, self_mem_nhdsWithin] with s hs hsp
      change 0 < s at hsp
      intro z hz
      have hsc : (s : ℂ) ∈ closedBall (0 : ℂ) r := by
        simpa [mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsp] using hs
      exact (ha ((s : ℂ), z) (hpoint _ _ hsc (ball_subset_closedBall (hSsub hz)))).comp_of_eq
        (analyticAt_const.prod analyticAt_id) rfl
    · intro j _ S _ hSsub
      refine ⟨2 * M / r ^ (j + 1), ?_⟩
      have he : ∀ᶠ s : ℝ in 𝓝[>] 0, s ≤ r / 2 :=
        ((eventually_lt_nhds (by positivity : (0 : ℝ) < r / 2)).mono fun _ hs => hs.le).filter_mono
          nhdsWithin_le_nhds
      filter_upwards [he, self_mem_nhdsWithin] with s hs hsp
      change 0 < s at hsp
      intro z hz
      have hnorm : ‖(s : ℂ)‖ = s := by simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsp]
      simpa only [hnorm] using hrem j (s : ℂ) z (by rwa [hnorm])
        (ball_subset_closedBall (hSsub hz))
  exact ⟨r, hr, 2 * M / r ^ (m + 1), by positivity, hcoeff, fun s hs z hz => hrem m s z hs hz⟩

end Kneser.JointAnalyticFiniteTaylor

end
