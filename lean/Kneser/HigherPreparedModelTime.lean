import Kneser.ExponentialPreparedHigher
import Kneser.UniformModelTime
import Kneser.PreparedModelAtZero

/-! The actual logarithmic model with its constructed finite correction,
at every preparation order. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace Kneser.HigherPreparedModelTime

open Filter Set Metric Kneser.ExponentialPreparedHigher Kneser.ExponentialModelTime
open Kneser.ExponentialPreparedModel Kneser.ExponentialPreparedQuadratic
open Kneser.ExponentialMatrixDividedDifference Kneser.ExponentialUnfolding
open Kneser.PreparedTwoRootDivision Kneser.UniformModelTime
open Kneser.AnalyticEvenDescent
open scoped Topology BigOperators

def modelTime (U H : ℂ → ℂ) (m : ℕ) (e : Fin (2 * m) → ℂ → ℂ)
    (s u : ℂ) : ℂ := logarithmicModel U H s u + correction m e s u

def splitModelTime (U H : ℂ → ℂ) (m : ℕ) (e : Fin (2 * m) → ℂ → ℂ)
    (p : Pair) : ℂ :=
  dslope (fun x => modelNumerator U H x p.2) 0 p.1 + correction m e (p.1 ^ 2) p.2

theorem analyticAt_splitModelTime {U H : ℂ → ℂ} (m : ℕ)
    (e : Fin (2 * m) → ℂ → ℂ)
    (hU : AnalyticAt ℂ U 0) (hU0 : U 0 = 0)
    (hH : AnalyticAt ℂ H 0) (hHne : H 0 ≠ 0)
    (he : ∀ i, AnalyticAt ℂ (e i) 0) (u : ℂ) (hu : u.re < 0) :
    AnalyticAt ℂ (splitModelTime U H m e) (0, u) := by
  have hlog := analyticAt_splitModel hU hU0 hH hHne
    (show AnalyticAt ℂ (fun _ : ℂ => (0 : ℂ)) 0 from analyticAt_const)
    (show AnalyticAt ℂ (fun _ : ℂ => (0 : ℂ)) 0 from analyticAt_const) u hu
  have hlog' : AnalyticAt ℂ
      (fun p : Pair => dslope (fun x => modelNumerator U H x p.2) 0 p.1) (0, u) := by
    change AnalyticAt ℂ (fun p : Pair =>
      dslope (fun x => modelNumerator U H x p.2) 0 p.1 +
        ((0 : ℂ) * p.2 + (0 : ℂ) * p.2 ^ 2)) (0, u) at hlog
    simpa only [zero_mul, zero_add, add_zero] using hlog
  have hs : AnalyticAt ℂ (fun p : Pair => p.1 ^ 2) (0, u) := analyticAt_fst.pow 2
  apply hlog'.add
  apply Finset.analyticAt_fun_sum
  intro i hi
  exact ((he i).comp_of_eq (f := fun p : Pair => p.1 ^ 2) hs (by simp)).mul
    (analyticAt_snd.pow (i.val + 1))

theorem splitModelTime_even (U H : ℂ → ℂ) (m : ℕ)
    (e : Fin (2 * m) → ℂ → ℂ) (x u : ℂ) :
    splitModelTime U H m e (-x, u) = splitModelTime U H m e (x, u) := by
  rw [splitModelTime, splitModelTime, neg_sq,
    dslope_odd_even (modelNumerator_zero U H u) (fun x => modelNumerator_odd U H x u)]

theorem splitModelTime_sqrt (U H : ℂ → ℂ) (m : ℕ)
    (e : Fin (2 * m) → ℂ → ℂ) (s u : ℂ) :
    splitModelTime U H m e (Complex.sqrt s, u) = modelTime U H m e s u := by
  simp only [splitModelTime, square_sqrt, modelTime, logarithmicModel]

/-- Uniform genuine parameter discs around every fixed attracting point,
for the constructed polynomial of any finite preparation order. -/
theorem exists_uniform_modelTime_disc_bounds {U H : ℂ → ℂ} (m : ℕ)
    (e : Fin (2 * m) → ℂ → ℂ)
    (hU : AnalyticAt ℂ U 0) (hU0 : U 0 = 0)
    (hH : AnalyticAt ℂ H 0) (hHne : H 0 ≠ 0)
    (he : ∀ i, AnalyticAt ℂ (e i) 0) (u₀ : ℂ) (hu₀ : u₀.re < 0) :
    ∃ r ρ M : ℝ, 0 < r ∧ 0 < ρ ∧ 0 ≤ M ∧ ∀ u ∈ ball u₀ ρ,
      DiffContOnCl ℂ (fun s => modelTime U H m e s u) (ball 0 r) ∧
      (∀ s ∈ closedBall (0 : ℂ) r, ‖modelTime U H m e s u‖ ≤ M) := by
  obtain ⟨r, ρ, M, hr, hρ, hM, h⟩ := exists_uniform_even_disc_bounds u₀
    (analyticAt_splitModelTime m e hU hU0 hH hHne he u₀ hu₀)
    (splitModelTime_even U H m e)
  exact ⟨r, ρ, M, hr, hρ, hM, fun u hu => by
    simpa only [splitModelTime_sqrt] using h u hu⟩

theorem modelTime_one_step (U H : ℂ → ℂ) (m : ℕ)
    (e : Fin (2 * m) → ℂ → ℂ)
    (hH : ∀ x, Complex.log (rootMultiplier U x) = x * H x)
    (x u F : ℂ) (hx : x ≠ 0) (hHx : H x ≠ 0) (hHnx : H (-x) ≠ 0)
    (hf : unfolding (x ^ 2) u - u = rootProduct U x u * symmetricCofactor U x u)
    (hF : F =
      Complex.log (1 + (u - U (-x)) * symmetricCofactor U x u) / Complex.log (rootMultiplier U x) +
      Complex.log (1 + (u - U x) * symmetricCofactor U x u) / Complex.log (rootMultiplier U (-x)) - 1)
    (ha : 0 < (U x - u).re) (hb : 0 < (U (-x) - u).re)
    (hra : 0 < (1 + (u - U (-x)) * symmetricCofactor U x u).re)
    (hrb : 0 < (1 + (u - U x) * symmetricCofactor U x u).re) :
    modelTime U H m e (x ^ 2) (unfolding (x ^ 2) u) - modelTime U H m e (x ^ 2) u - 1 =
      F + correction m e (x ^ 2) (unfolding (x ^ 2) u) - correction m e (x ^ 2) u := by
  have hlog := preparedModelTime_one_step U H (fun _ => 0) (fun _ => 0) hH
    x u F hx hHx hHnx hf hF ha hb hra hrb
  simp only [preparedModelTime, polynomialCorrection, zero_mul, zero_add, add_zero, sub_zero] at hlog
  dsimp [modelTime]
  linear_combination hlog

/-- The exact parabolic finite model holds for every constructed correction. -/
theorem modelTime_zero_eq_model (U H : ℂ → ℂ) (m : ℕ)
    (e : Fin (2 * m) → ℂ → ℂ)
    (hU : AnalyticAt ℂ U 0) (hU0 : U 0 = 0) (hUd : deriv U 0 ≠ 0)
    (hroots : ∀ᶠ x in 𝓝 0, unfolding (x ^ 2) (U x) = U x)
    (hH : AnalyticAt ℂ H 0)
    (hHlog : ∀ x, Complex.log (rootMultiplier U x) = x * H x)
    (u : ℂ) (hu : u.re < 0) :
    modelTime U H m e 0 u = ParabolicFatouCoordinate.model u + correction m e 0 u := by
  rw [modelTime, logarithmicModel, Complex.sqrt_zero, dslope_same,
    PreparedModelAtZero.deriv_modelNumerator_zero_eq_model U H hU hU0 hUd hroots hH hHlog u hu]

theorem exists_compact_modelTime_disc_bounds {U H : ℂ → ℂ} (n : ℕ)
    (e : Fin (2 * n) → ℂ → ℂ)
    (hU : AnalyticAt ℂ U 0) (hU0 : U 0 = 0)
    (hH : AnalyticAt ℂ H 0) (hHne : H 0 ≠ 0)
    (he : ∀ i, AnalyticAt ℂ (e i) 0)
    (S : Set ℂ) (hS : IsCompact S) (hneg : ∀ u ∈ S, u.re < 0) :
    ∃ r M : ℝ, 0 < r ∧ 0 ≤ M ∧ ∀ u ∈ S,
      DiffContOnCl ℂ (fun s => modelTime U H n e s u) (ball 0 r) ∧
      (∀ s ∈ closedBall (0 : ℂ) r, ‖modelTime U H n e s u‖ ≤ M) := by
  classical
  rcases S.eq_empty_or_nonempty with hSE | hSN
  · subst S
    exact ⟨1, 0, by norm_num, by norm_num, by simp⟩
  have hloc : ∀ u : S, ∃ r ρ M : ℝ, 0 < r ∧ 0 < ρ ∧ 0 ≤ M ∧
      ∀ v ∈ ball (u : ℂ) ρ,
        DiffContOnCl ℂ (fun s => modelTime U H n e s v) (ball 0 r) ∧
        (∀ s ∈ closedBall (0 : ℂ) r, ‖modelTime U H n e s v‖ ≤ M) :=
    fun u => exists_uniform_modelTime_disc_bounds n e hU hU0 hH hHne he
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


end Kneser.HigherPreparedModelTime

end
