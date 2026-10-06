import Kneser.LocalPeriodicStrip
import Kneser.AllOrderGateFirstCoefficient

/-! True finite coefficient packets preserve the Fatou translation law
at every order.  The same analytic periodic strip lift has integer
remainders uniformly across all integer cells. -/

set_option autoImplicit false
noncomputable section
namespace Kneser.AllOrderPeriodicPacket

open Filter Set Metric Kneser.LocalPeriodicStrip Kneser.AllOrderCompactGate
open Kneser.AllOrderGateFourier Kneser.FiniteExpansionHolomorphy
open Kneser.AllOrderGateFirstCoefficient
open scoped Topology BigOperators

theorem periodize_analytic_of_ball_three (f : ℂ → ℂ)
    (ha : AnalyticOnNhd ℂ f (ball (0 : ℂ) 3))
    (hp : ∀ z ∈ ball (0 : ℂ) 2, f (z + 1) = f z) :
    AnalyticOnNhd ℂ (periodize f) strip := by
  intro w hw
  have hg := periodize_germ f hp w hw
  have hred := ball_subset_ball (by norm_num : (2 : ℝ) ≤ 3) (reduced_mem_ball w hw)
  have hf := (ha _ hred).comp_of_eq (f := fun z : ℂ => z - (cell w : ℂ))
    (analyticAt_id.sub analyticAt_const) rfl
  exact hf.congr hg.symm

theorem lift_analytic_of_ball_three (T : ℂ → ℂ)
    (ha : AnalyticOnNhd ℂ T (ball (0 : ℂ) 3))
    (hp : ∀ z ∈ ball (0 : ℂ) 2, T (z + 1) = T z + 1) :
    AnalyticOnNhd ℂ (lift T) strip := by
  have hperiod : ∀ z ∈ ball (0 : ℂ) 2, (T (z + 1) - (z + 1)) = T z - z := by
    intro z hz
    rw [hp z hz]
    ring
  have hh := periodize_analytic_of_ball_three (fun z => T z - z)
    (fun z hz => (ha z hz).sub analyticAt_id) hperiod
  intro z hz
  have he : lift T = (fun w => w + periodize (fun v => T v - v) w) :=
    funext (lift_eq_periodize_displacement T)
  rw [he]
  exact analyticAt_id.add (hh z hz)

theorem coefficient_translation (T : ℝ → ℂ → ℂ) (b : ℕ → ℂ → ℂ) (m : ℕ)
    (hb : FinitePacket T b m (ball (0 : ℂ) 3))
    (hp : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ z ∈ ball (0 : ℂ) 2, T s (z + 1) = T s z + 1) :
    ∀ z ∈ ball (0 : ℂ) 2, ∀ j ≤ m, b j (z + 1) = b j z + if j = 0 then 1 else 0 := by
  intro z hz
  have hn : ‖z‖ < 2 := by simpa only [mem_ball, dist_zero_right] using hz
  have hnorm := norm_add_le z (1 : ℂ)
  rw [norm_one] at hnorm
  have hz3 : z ∈ ball (0 : ℂ) 3 := ball_subset_ball (by norm_num) hz
  have hz13 : z + 1 ∈ ball (0 : ℂ) 3 := by
    simp only [mem_ball, dist_zero_right]
    linarith
  obtain ⟨C, hC, hc⟩ := (finitePacket_pointwise T b m _ hb (z + 1) hz13).2
  obtain ⟨D, hD, hd⟩ := (finitePacket_pointwise T b m _ hb z hz3).2
  let d : ℕ → ℂ := fun j => b j z + if j = 0 then 1 else 0
  have hpoly (s : ℂ) : scalarPolynomial d m s = scalarPolynomial (fun j => b j z) m s + 1 := by
    simp [scalarPolynomial, d, mul_add, Finset.sum_add_distrib]
  have hd' : ∀ᶠ s : ℝ in 𝓝[>] 0,
      ‖T s (z + 1) - scalarPolynomial d m (s : ℂ)‖ ≤ D * s ^ (m + 1) := by
    filter_upwards [hp, hd] with s hs hds
    rw [hs z hz, hpoly]
    simpa only [add_sub_add_right_eq_sub] using hds
  exact Kneser.FiniteLocalExpansionGluing.coefficients_unique_integer
    (fun s => T s (z + 1)) (fun j => b j (z + 1)) d m C D hC hD hc hd'

def stripCoefficient (b : ℕ → ℂ → ℂ) (j : ℕ) : ℂ → ℂ :=
  if j = 0 then lift (b 0) else periodize (b j)

theorem stripCoefficient_apply (b : ℕ → ℂ → ℂ) (j : ℕ) (z : ℂ) :
    stripCoefficient b j z = b j (reduced z) + if j = 0 then (cell z : ℂ) else 0 := by
  by_cases hj : j = 0
  · subst j
    simp [stripCoefficient, lift]
  · simp [stripCoefficient, hj, periodize]

theorem strip_polynomial (b : ℕ → ℂ → ℂ) (m : ℕ) (s z : ℂ) :
    complexPolynomial (stripCoefficient b) m s z = complexPolynomial b m s (reduced z) + (cell z : ℂ) := by
  simp [complexPolynomial, stripCoefficient_apply, mul_add, Finset.sum_add_distrib]

theorem finitePacket_lift (T : ℝ → ℂ → ℂ) (b : ℕ → ℂ → ℂ) (m : ℕ)
    (hb : FinitePacket T b m (ball (0 : ℂ) 3))
    (hp : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ z ∈ ball (0 : ℂ) 2, T s (z + 1) = T s z + 1) :
    FinitePacket (fun s => lift (T s)) (stripCoefficient b) m strip := by
  have hc := coefficient_translation T b m hb hp
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    by_cases hj0 : j = 0
    · subst j
      simp only [stripCoefficient, if_pos rfl]
      apply lift_analytic_of_ball_three (b 0) (hb.1 0 (Nat.zero_le m))
      intro z hz
      simpa using hc z hz 0 (Nat.zero_le m)
    · simp only [stripCoefficient, if_neg hj0]
      apply periodize_analytic_of_ball_three (b j) (hb.1 j hj)
      intro z hz
      simpa only [hj0, if_false, add_zero] using hc z hz j hj
  · intro z hz
    simp only [stripCoefficient, ite_true, lift]
    rw [hb.2.1 _ (ball_subset_ball (by norm_num) (reduced_mem_ball z hz))]
  · intro K _hK hK
    have hsub : closedBall (0 : ℂ) 2 ⊆ ball (0 : ℂ) 3 := by
      intro z hz
      exact (show dist z 0 ≤ 2 from hz).trans_lt (by norm_num)
    obtain ⟨C, hC, he⟩ := hb.2.2 _ (isCompact_closedBall _ _) hsub
    refine ⟨C, hC, ?_⟩
    filter_upwards [he] with s hs z hz
    rw [strip_polynomial]
    simpa only [lift, add_sub_add_right_eq_sub] using
      hs (reduced z) (ball_subset_closedBall (reduced_mem_ball z (hK hz)))

end Kneser.AllOrderPeriodicPacket
