import Kneser.ExponentialModelTime
import Kneser.JointAnalyticDivision

/-!
The canonical slope in the logarithmic model is jointly analytic in the
splitting parameter and the spatial variable.  Uniform parameter discs then
follow on a neighbourhood of each attracting-side spatial point.
-/

noncomputable section

namespace Kneser.UniformModelTime

open Kneser.ExponentialModelTime Kneser.ExponentialPreparedModel
open Kneser.JointAnalyticDivision Kneser.AnalyticEvenDescent
open Filter Set Metric
open scoped Topology

def splitModel (U H e₁ e₂ : ℂ → ℂ) (p : ℂ × ℂ) : ℂ :=
  dslope (fun x => modelNumerator U H x p.2) 0 p.1 +
    polynomialCorrection e₁ e₂ (p.1 ^ 2) p.2

theorem quotient_on_hyperplane (B : Pair → ℂ) (u : ℂ) :
    quotient B (0, u) = partialFirst B (0, u) := by
  simp [quotient, scaleFirst_apply, intervalIntegral.integral_const]

theorem partialFirst_eq_deriv {B : Pair → ℂ} {u : ℂ}
    (hB : DifferentiableAt ℂ B (0, u)) :
    partialFirst B (0, u) = deriv (fun x : ℂ => B (x, u)) 0 := by
  have hc : HasDerivAt (fun x : ℂ => (x, u)) ((1 : ℂ), 0) 0 :=
    (hasDerivAt_id (0 : ℂ)).prodMk (hasDerivAt_const 0 u)
  have h := hB.hasFDerivAt.comp_hasDerivAt_of_eq 0 hc rfl
  exact h.deriv.symm

/-- The actual coordinate quotient agrees with the canonical derivative
slope on one joint neighbourhood, including the dividing hyperplane. -/
theorem eventually_dslope_eq_quotient {B : Pair → ℂ}
    (hB : AnalyticAt ℂ B 0) (hzero : ∀ u, B (0, u) = 0) :
    ∀ᶠ p in 𝓝 (0 : Pair), dslope (fun x => B (x, p.2)) 0 p.1 = quotient B p := by
  filter_upwards [eventually_coordinate_factor hB, hB.eventually_analyticAt] with p hp hpa
  by_cases hx : p.1 = 0
  · have hpa' : DifferentiableAt ℂ B (0, p.2) := by
      simpa only [← hx, Prod.mk.eta] using hpa.differentiableAt
    have hp0 : p = (0, p.2) := Prod.ext hx rfl
    rw [hp0, dslope_same, quotient_on_hyperplane, partialFirst_eq_deriv hpa']
  · rw [dslope_of_ne _ hx, slope_def_field, hzero, sub_zero]
    rw [hzero, sub_zero] at hp
    rw [hp]
    field_simp
    ring

theorem analyticAt_joint_dslope {B : Pair → ℂ}
    (hB : AnalyticAt ℂ B 0) (hzero : ∀ u, B (0, u) = 0) :
    AnalyticAt ℂ (fun p : Pair => dslope (fun x => B (x, p.2)) 0 p.1) 0 := by
  have heq : (quotient B) =ᶠ[𝓝 (0 : Pair)]
      (fun p : Pair => dslope (fun x => B (x, p.2)) 0 p.1) :=
    (eventually_dslope_eq_quotient hB hzero).mono (fun _ hp => hp.symm)
  exact (analyticAt_quotient hB).congr heq

set_option maxHeartbeats 1000000 in
/-- The filled logarithmic model is jointly analytic in `x` and `u`. -/
theorem analyticAt_splitModel {U H e₁ e₂ : ℂ → ℂ}
    (hU : AnalyticAt ℂ U 0) (hU0 : U 0 = 0)
    (hH : AnalyticAt ℂ H 0) (hHne : H 0 ≠ 0)
    (he₁ : AnalyticAt ℂ e₁ 0) (he₂ : AnalyticAt ℂ e₂ 0)
    (u : ℂ) (hu : u.re < 0) :
    AnalyticAt ℂ (splitModel U H e₁ e₂) (0, u) := by
  let B : Pair → ℂ := fun p => modelNumerator U H p.1 (u + p.2)
  have hT : AnalyticAt ℂ (fun p : Pair => (p.1, u + p.2)) 0 :=
    analyticAt_fst.prod (analyticAt_const.add analyticAt_snd)
  have hBa : AnalyticAt ℂ B 0 :=
    (analyticAt_modelNumerator_pair hU hU0 hH hHne u hu).comp_of_eq
      (f := fun p : Pair => (p.1, u + p.2)) hT (by simp)
  have hDa := analyticAt_joint_dslope hBa (fun v => modelNumerator_zero U H (u + v))
  have hS : AnalyticAt ℂ (fun p : Pair => (p.1, p.2 - u)) (0, u) :=
    analyticAt_fst.prod (analyticAt_snd.sub analyticAt_const)
  have hlog : AnalyticAt ℂ
      (fun p : Pair => dslope (fun x => modelNumerator U H x p.2) 0 p.1) (0, u) := by
    have h : AnalyticAt ℂ
        (fun p : Pair => dslope (fun x => B (x, p.2 - u)) 0 p.1) (0, u) :=
      hDa.comp_of_eq (f := fun p : Pair => (p.1, p.2 - u)) hS (by simp)
    simpa only [B, ← add_sub_assoc, add_sub_cancel_left] using h
  have hs : AnalyticAt ℂ (fun p : Pair => p.1 ^ 2) (0, u) := analyticAt_fst.pow 2
  have hP : AnalyticAt ℂ
      (fun p : Pair => polynomialCorrection e₁ e₂ (p.1 ^ 2) p.2) (0, u) := by
    exact ((he₁.comp_of_eq hs (by simp)).mul analyticAt_snd).add
      ((he₂.comp_of_eq hs (by simp)).mul (analyticAt_snd.pow 2))
  exact hlog.add hP

theorem splitModel_even (U H e₁ e₂ : ℂ → ℂ) (x u : ℂ) :
    splitModel U H e₁ e₂ (-x, u) = splitModel U H e₁ e₂ (x, u) := by
  rw [splitModel, splitModel, neg_sq,
    dslope_odd_even (modelNumerator_zero U H u) (fun z => modelNumerator_odd U H z u)]

theorem splitModel_sqrt (U H e₁ e₂ : ℂ → ℂ) (s u : ℂ) :
    splitModel U H e₁ e₂ (Complex.sqrt s, u) = preparedModelTime U H e₁ e₂ s u := by
  simp only [splitModel, square_sqrt, preparedModelTime, logarithmicModel]

/-- Joint analyticity before even descent provides parameter discs and
boundary bounds which are uniform on a spatial neighbourhood. -/
theorem exists_uniform_even_disc_bounds {Q : Pair → ℂ} (u₀ : ℂ)
    (hQ : AnalyticAt ℂ Q (0, u₀))
    (hEven : ∀ x u, Q (-x, u) = Q (x, u)) :
    ∃ r ρ M : ℝ, 0 < r ∧ 0 < ρ ∧ 0 ≤ M ∧
      ∀ u ∈ ball u₀ ρ,
        DiffContOnCl ℂ (fun s => Q (Complex.sqrt s, u)) (ball 0 r) ∧
        (∀ s ∈ closedBall (0 : ℂ) r, ‖Q (Complex.sqrt s, u)‖ ≤ M) := by
  let M : ℝ := ‖Q (0, u₀)‖ + 1
  have hbound : ∀ᶠ p in 𝓝 ((0 : ℂ), u₀), ‖Q p‖ < M :=
    hQ.continuousAt.norm.eventually (gt_mem_nhds (by dsimp [M]; linarith))
  obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.mp
    (hQ.eventually_analyticAt.and hbound)
  let r : ℝ := η ^ 2 / 4
  let ρ : ℝ := η / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  refine ⟨r, ρ, M, hr, hρ, by dsimp [M]; positivity, ?_⟩
  intro u hu
  have hnear : ∀ s ∈ closedBall (0 : ℂ) r,
      dist (Complex.sqrt s, u) ((0 : ℂ), u₀) < η := by
    intro s hs
    have hs' : ‖s‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hs
    have hx2 : ‖Complex.sqrt s‖ ^ 2 = ‖s‖ := by
      rw [← norm_pow, square_sqrt]
    have hx : ‖Complex.sqrt s‖ ≤ η / 2 := by
      dsimp [r] at hs'
      nlinarith [norm_nonneg (Complex.sqrt s)]
    have hu' : dist u u₀ < η / 2 := hu
    rw [Prod.dist_eq, dist_zero_right]
    exact max_lt (by linarith) (by linarith)
  have ha : ∀ s ∈ closedBall (0 : ℂ) r,
      AnalyticAt ℂ (fun z => Q (Complex.sqrt z, u)) s := by
    intro s hs
    have hQa := (hball (hnear s hs)).1
    have hQu : AnalyticAt ℂ (fun x => Q (x, u)) (Complex.sqrt s) :=
      hQa.comp_of_eq (analyticAt_id.prod analyticAt_const) rfl
    by_cases hs0 : s = 0
    · subst s
      apply analyticAt_even_sqrt (f := fun x => Q (x, u)) (fun x => hEven x u)
      simpa only [Complex.sqrt_zero] using hQu
    · exact analyticAt_even_sqrt_of_ne (f := fun x => Q (x, u)) (fun x => hEven x u) hs0 hQu
  constructor
  · have hd : DifferentiableOn ℂ (fun s => Q (Complex.sqrt s, u)) (closedBall 0 r) :=
      fun s hs => (ha s hs).differentiableAt.differentiableWithinAt
    exact (hd.mono closure_ball_subset_closedBall).diffContOnCl
  · intro s hs
    exact (hball (hnear s hs)).2.le

/-- Uniform parameter discs and bounds for the canonical actual model,
with one radius and one constant for all nearby spatial initial points. -/
theorem exists_uniform_preparedModelTime_disc_bounds {U H e₁ e₂ : ℂ → ℂ}
    (hU : AnalyticAt ℂ U 0) (hU0 : U 0 = 0)
    (hH : AnalyticAt ℂ H 0) (hHne : H 0 ≠ 0)
    (he₁ : AnalyticAt ℂ e₁ 0) (he₂ : AnalyticAt ℂ e₂ 0)
    (u₀ : ℂ) (hu₀ : u₀.re < 0) :
    ∃ r ρ M : ℝ, 0 < r ∧ 0 < ρ ∧ 0 ≤ M ∧
      ∀ u ∈ ball u₀ ρ,
        DiffContOnCl ℂ (fun s => preparedModelTime U H e₁ e₂ s u) (ball 0 r) ∧
        (∀ s ∈ closedBall (0 : ℂ) r, ‖preparedModelTime U H e₁ e₂ s u‖ ≤ M) := by
  simpa only [splitModel_sqrt] using
    exists_uniform_even_disc_bounds u₀
      (analyticAt_splitModel hU hU0 hH hHne he₁ he₂ u₀ hu₀)
      (splitModel_even U H e₁ e₂)

/-- The same uniform model constants apply to each parameter boundary circle. -/
theorem exists_uniform_preparedModelTime_boundary_bounds {U H e₁ e₂ : ℂ → ℂ}
    (hU : AnalyticAt ℂ U 0) (hU0 : U 0 = 0)
    (hH : AnalyticAt ℂ H 0) (hHne : H 0 ≠ 0)
    (he₁ : AnalyticAt ℂ e₁ 0) (he₂ : AnalyticAt ℂ e₂ 0)
    (u₀ : ℂ) (hu₀ : u₀.re < 0) :
    ∃ r ρ M : ℝ, 0 < r ∧ 0 < ρ ∧ 0 ≤ M ∧
      ∀ u ∈ ball u₀ ρ,
        DiffContOnCl ℂ (fun s => preparedModelTime U H e₁ e₂ s u) (ball 0 r) ∧
        (∀ s ∈ sphere (0 : ℂ) r, ‖preparedModelTime U H e₁ e₂ s u‖ ≤ M) := by
  obtain ⟨r, ρ, M, hr, hρ, hM, h⟩ :=
    exists_uniform_preparedModelTime_disc_bounds hU hU0 hH hHne he₁ he₂ u₀ hu₀
  refine ⟨r, ρ, M, hr, hρ, hM, ?_⟩
  intro u hu
  refine ⟨(h u hu).1, ?_⟩
  intro s hs
  exact (h u hu).2 s (mem_closedBall.mpr (mem_sphere.mp hs).le)

/-- Compact sets of spatial initial points share a single model parameter
disc and a single bound.  The constants are obtained from a finite cover. -/
theorem exists_compact_preparedModelTime_disc_bounds {U H e₁ e₂ : ℂ → ℂ}
    (hU : AnalyticAt ℂ U 0) (hU0 : U 0 = 0)
    (hH : AnalyticAt ℂ H 0) (hHne : H 0 ≠ 0)
    (he₁ : AnalyticAt ℂ e₁ 0) (he₂ : AnalyticAt ℂ e₂ 0)
    (S : Set ℂ) (hS : IsCompact S) (hneg : ∀ u ∈ S, u.re < 0) :
    ∃ r M : ℝ, 0 < r ∧ 0 ≤ M ∧ ∀ u ∈ S,
      DiffContOnCl ℂ (fun s => preparedModelTime U H e₁ e₂ s u) (ball 0 r) ∧
      (∀ s ∈ closedBall (0 : ℂ) r, ‖preparedModelTime U H e₁ e₂ s u‖ ≤ M) := by
  classical
  rcases S.eq_empty_or_nonempty with hSE | hSN
  · subst S
    exact ⟨1, 0, by norm_num, by norm_num, by simp⟩
  have hloc : ∀ u : S, ∃ r ρ M : ℝ, 0 < r ∧ 0 < ρ ∧ 0 ≤ M ∧
      ∀ v ∈ ball (u : ℂ) ρ,
        DiffContOnCl ℂ (fun s => preparedModelTime U H e₁ e₂ s v) (ball 0 r) ∧
        (∀ s ∈ closedBall (0 : ℂ) r, ‖preparedModelTime U H e₁ e₂ s v‖ ≤ M) :=
    fun u => exists_uniform_preparedModelTime_disc_bounds hU hU0 hH hHne he₁ he₂
      u (hneg u u.property)
  choose r ρ M hr hρ hM hlocal using hloc
  have hcover : S ⊆ ⋃ u : S, ball (u : ℂ) (ρ u) := by
    intro u hu
    exact mem_iUnion.mpr ⟨⟨u, hu⟩, mem_ball_self (hρ ⟨u, hu⟩)⟩
  obtain ⟨t, htcover⟩ := hS.elim_finite_subcover
    (fun u : S => ball (u : ℂ) (ρ u)) (fun _ => isOpen_ball) hcover
  have ht : t.Nonempty := by
    obtain ⟨u, hu⟩ := hSN
    obtain ⟨v, hv, _⟩ := mem_iUnion₂.mp (htcover hu)
    exact ⟨v, hv⟩
  let r₀ : ℝ := t.inf' ht r
  let M₀ : ℝ := t.sup' ht M
  have hr₀ : 0 < r₀ := by
    exact (Finset.lt_inf'_iff ht).mpr (fun u _ => hr u)
  have hM₀ : 0 ≤ M₀ := by
    obtain ⟨u, hu⟩ := ht
    exact (hM u).trans (Finset.le_sup' M hu)
  refine ⟨r₀, M₀, hr₀, hM₀, ?_⟩
  intro u hu
  obtain ⟨v, hv, huv⟩ := mem_iUnion₂.mp (htcover hu)
  have hrv : r₀ ≤ r v := Finset.inf'_le r hv
  have hMv : M v ≤ M₀ := Finset.le_sup' M hv
  refine ⟨((hlocal v u huv).1.mono (ball_subset_ball hrv)), ?_⟩
  intro s hs
  exact ((hlocal v u huv).2 s (closedBall_subset_closedBall hrv hs)).trans hMv

theorem exists_compact_preparedModelTime_boundary_bounds {U H e₁ e₂ : ℂ → ℂ}
    (hU : AnalyticAt ℂ U 0) (hU0 : U 0 = 0)
    (hH : AnalyticAt ℂ H 0) (hHne : H 0 ≠ 0)
    (he₁ : AnalyticAt ℂ e₁ 0) (he₂ : AnalyticAt ℂ e₂ 0)
    (S : Set ℂ) (hS : IsCompact S) (hneg : ∀ u ∈ S, u.re < 0) :
    ∃ r M : ℝ, 0 < r ∧ 0 ≤ M ∧ ∀ u ∈ S,
      DiffContOnCl ℂ (fun s => preparedModelTime U H e₁ e₂ s u) (ball 0 r) ∧
      (∀ s ∈ sphere (0 : ℂ) r, ‖preparedModelTime U H e₁ e₂ s u‖ ≤ M) := by
  obtain ⟨r, M, hr, hM, h⟩ :=
    exists_compact_preparedModelTime_disc_bounds hU hU0 hH hHne he₁ he₂ S hS hneg
  refine ⟨r, M, hr, hM, ?_⟩
  intro u hu
  refine ⟨(h u hu).1, ?_⟩
  intro s hs
  exact (h u hu).2 s (mem_closedBall.mpr (mem_sphere.mp hs).le)

end Kneser.UniformModelTime

end
