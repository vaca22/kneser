import Kneser.ActualBilateralGate
import Kneser.FullCanonicalImageGate
import Kneser.QuantitativeGateTransition
import Kneser.ActualNormalizationAnchorExpansion
import Kneser.ActualGateAbel

/-!
# Actual quantitative transition on a whole Fourier gate

A true high reciprocal-coordinate disc supplies the complete spatial and
uniform analytic input. The moving repelling inverse and attracting
transition are constructed by the quantitative inverse theorem. The true
real anchor is transported separately and then subtracted.
-/

set_option autoImplicit false
noncomputable section

namespace Kneser.ActualQuantitativeGateTransition

open Filter Set Metric Kneser.ActualBilateralGate Kneser.ActualDeepCoordinateData
open Kneser.ParabolicExponentialOrbit Kneser.ParabolicCoordinateJacobian
open Kneser.FullCanonicalImageGate Kneser.PreparedActualFirstOrder Kneser.ReflectedOrbitChainCoefficient
open Kneser.ActualGateAbel
open Kneser.QuantitativeGateTransition Kneser.QuantitativeHornExpansion
open scoped Topology

def chartCenter (Y : ℝ) : ℂ := Complex.I * (Y : ℂ)
def chartPoint (Y : ℝ) (z : ℂ) : ℂ := inverseCoordinate (chartCenter Y + z)

def repellingChart (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (N : ℕ) (Y : ℝ) (s : ℝ) (z : ℂ) : ℂ :=
  backwardCoordinate U H e₁ e₂ A B Γ N (chartPoint Y z) s - canonicalGateInZeta N (chartCenter Y)

def attractingChart (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (N : ℕ) (Y : ℝ) (s : ℝ) (z : ℂ) : ℂ :=
  forwardCoordinate U H e₁ e₂ A B Γ N (chartPoint Y z) s

def repellingChartCoefficient (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (N : ℕ) (Y : ℝ) (z : ℂ) : ℂ :=
  backwardCoefficient U H e₁ e₂ A B Γ N (chartPoint Y z)

def attractingChartCoefficient (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (N : ℕ) (Y : ℝ) (z : ℂ) : ℂ :=
  forwardCoefficient U H e₁ e₂ A B Γ N (chartPoint Y z)

theorem chartPoint_in_gate (N : ℕ) (Y : ℝ)
    (hY : 64 * ((N : ℝ) + 1) + 64 ≤ Y) (z : ℂ)
    (hz : z ∈ closedBall (0 : ℂ) 64) : chartPoint Y z ∈ gate 64 N := by
  have hzc : chartCenter Y + z ∈ closedBall (chartCenter Y) 64 := by
    simpa [mem_closedBall, dist_eq_norm] using hz
  have hi := Kneser.FiniteZetaGateProjection.height_on_closedBall Y 64
    (64 * ((N : ℝ) + 1)) hY (by positivity) (chartCenter Y + z) hzc
  have hn : ‖z‖ ≤ 64 := by simpa [mem_closedBall, dist_zero_right] using hz
  change |(inverseCoordinate (inverseCoordinate (chartCenter Y + z))).re| ≤ 64 ∧
    64 * ((N : ℝ) + 1) ≤ |(inverseCoordinate (inverseCoordinate (chartCenter Y + z))).im|
  rw [Kneser.ParabolicOverlapGate.inverseCoordinate_involutive]
  exact ⟨by simpa [chartCenter] using (Complex.abs_re_le_norm z).trans hn, hi⟩

theorem chart_argument_ne_zero (N : ℕ) (Y : ℝ)
    (hY : 64 * ((N : ℝ) + 1) + 64 ≤ Y) (z : ℂ)
    (hz : z ∈ closedBall (0 : ℂ) 64) : chartCenter Y + z ≠ 0 := by
  have h := (chartPoint_in_gate N Y hY z hz).2
  rw [chartPoint, Kneser.ParabolicOverlapGate.inverseCoordinate_involutive] at h
  intro he
  rw [he] at h
  norm_num at h
  linarith [Nat.cast_nonneg (α := ℝ) N]

theorem chartPoint_analytic (N : ℕ) (Y : ℝ)
    (hY : 64 * ((N : ℝ) + 1) + 64 ≤ Y) (z : ℂ)
    (hz : z ∈ closedBall (0 : ℂ) 64) : AnalyticAt ℂ (chartPoint Y) z := by
  have ha : AnalyticAt ℂ inverseCoordinate (chartCenter Y + z) :=
    (analyticAt_const.div analyticAt_id (chart_argument_ne_zero N Y hY z hz))
  exact ha.comp_of_eq (analyticAt_const.add analyticAt_id) rfl

/-- The entire true reciprocal-coordinate disc is a compact subset of the
actual overlap gate; no gate-containment hypothesis is required. -/
theorem chart_compact_gate (N : ℕ) (Y : ℝ)
    (hY : 64 * ((N : ℝ) + 1) + 64 ≤ Y) :
    IsCompact ((chartPoint Y) '' closedBall (0 : ℂ) 64) ∧
      ((chartPoint Y) '' closedBall (0 : ℂ) 64) ⊆ gate 64 N := by
  refine ⟨(isCompact_closedBall (0 : ℂ) 64).image_of_continuousOn
    (fun z hz => (chartPoint_analytic N Y hY z hz).continuousAt.continuousWithinAt), ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  exact chartPoint_in_gate N Y hY z hz

theorem exists_disc_norm_bound (f : ℂ → ℂ)
    (ha : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) 64)) :
    ∃ M ≥ 0, ∀ z ∈ closedBall (0 : ℂ) 64, ‖f z‖ ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) 64).exists_bound_of_continuousOn ha.continuousOn
  exact ⟨max M 0, le_max_right _ _, fun z hz => (hM z hz).trans (le_max_left _ _)⟩

/-- Every input of the quantitative inverse/transition theorem is derived
from actual bilateral data and the true canonical spatial Jacobian bound. -/
theorem quantitative_transition_of_data
    (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (R Y : ℝ) (N : ℕ)
    (hdata : BilateralGateData U H e₁ e₂ A B Γ R 64 N)
    (hY : 64 * ((N : ℝ) + 1) + 64 ≤ Y)
    (hgeometry : ∀ z ∈ ball (chartCenter Y) 32,
      AnalyticAt ℂ (canonicalGateInZeta N) z ∧
        ‖deriv (canonicalGateInZeta N) z - 1‖ ≤ 1 / 4) :
    ∃ V : ℝ → ℂ → ℂ, ∃ C ≥ 0,
      (∀ w ∈ ball (0 : ℂ) 4,
        V 0 w ∈ closedBall (0 : ℂ) 16 ∧ repellingChart U H e₁ e₂ A B Γ N Y 0 (V 0 w) = w) ∧
      AnalyticOnNhd ℂ (V 0) (ball (0 : ℂ) 4) ∧
      (∀ᶠ s : ℝ in 𝓝[>] 0,
        (∀ w ∈ ball (0 : ℂ) 4,
          V s w ∈ closedBall (0 : ℂ) 16 ∧ repellingChart U H e₁ e₂ A B Γ N Y s (V s w) = w) ∧
        AnalyticOnNhd ℂ (V s) (ball (0 : ℂ) 4) ∧
        (∀ w ∈ ball (0 : ℂ) 4,
          ‖attractingChart U H e₁ e₂ A B Γ N Y s (V s w) -
              attractingChart U H e₁ e₂ A B Γ N Y 0 (V 0 w) -
            (s : ℂ) * (attractingChartCoefficient U H e₁ e₂ A B Γ N Y (V 0 w) -
              (deriv (attractingChart U H e₁ e₂ A B Γ N Y 0) (V 0 w) /
                deriv (repellingChart U H e₁ e₂ A B Γ N Y 0) (V 0 w)) *
                repellingChartCoefficient U H e₁ e₂ A B Γ N Y (V 0 w))‖ ≤ C * s ^ (6 / 5 : ℝ))) := by
  let F := repellingChart U H e₁ e₂ A B Γ N Y
  let Q := attractingChart U H e₁ e₂ A B Γ N Y
  let D := repellingChartCoefficient U H e₁ e₂ A B Γ N Y
  let E := attractingChartCoefficient U H e₁ e₂ A B Γ N Y
  have hqa (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) 64) := chartPoint_analytic N Y hY z hz
  have hgate (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) 64) := chartPoint_in_gate N Y hY z hz
  have hF0a : AnalyticOnNhd ℂ (F 0) (closedBall (0 : ℂ) 64) := by
    intro z hz
    exact ((hdata.spatial _ (hgate z hz)).2.2.1.comp_of_eq (hqa z hz) rfl).sub analyticAt_const
  have hQ0a : AnalyticOnNhd ℂ (Q 0) (closedBall (0 : ℂ) 64) := by
    intro z hz
    exact ((hdata.spatial _ (hgate z hz)).1).comp_of_eq (hqa z hz) rfl
  have hDa : AnalyticOnNhd ℂ D (closedBall (0 : ℂ) 64) := by
    intro z hz
    exact ((hdata.coefficient _ (hgate z hz)).2).comp_of_eq (hqa z hz) rfl
  have hEa : AnalyticOnNhd ℂ E (closedBall (0 : ℂ) 64) := by
    intro z hz
    exact ((hdata.coefficient _ (hgate z hz)).1).comp_of_eq (hqa z hz) rfl
  have hdisc (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) 64)) :
      DiffContOnCl ℂ f (ball (0 : ℂ) 64) :=
    hf.differentiableOn.mono closure_ball_subset_closedBall |>.diffContOnCl
  have hF0eq (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) 64) :
      F 0 z = canonicalGateInZeta N (chartCenter Y + z) - canonicalGateInZeta N (chartCenter Y) := by
    have h := (hdata.canonical _ (hgate z hz)).2
    dsimp [F, repellingChart]
    rw [h]
    rw [canonicalGateInZeta_eq N (chartCenter Y + z)]
    rfl
  have hF0 : ApproximatesLinearOn (F 0) (ContinuousLinearMap.id ℂ ℂ)
      (ball (0 : ℂ) 32) (1 / 4) := by
    apply FullCanonicalImageGate.approximation_of_deriv_bound (F 0)
    · intro z hz
      exact hF0a z (by
        have hn : ‖z‖ < 32 := by simpa [mem_ball, dist_zero_right] using hz
        simp only [mem_closedBall, dist_zero_right]; linarith)
    · intro z hz
      have hz' : chartCenter Y + z ∈ ball (chartCenter Y) 32 := by
        simpa [mem_ball, dist_eq_norm] using hz
      have heq : F 0 =ᶠ[𝓝 z] (fun w => canonicalGateInZeta N (chartCenter Y + w) -
          canonicalGateInZeta N (chartCenter Y)) := by
        have hnh : ∀ᶠ w in 𝓝 z, w ∈ ball (0 : ℂ) 32 := isOpen_ball.mem_nhds hz
        exact hnh.mono fun w hw => hF0eq w (by
          have hn : ‖w‖ < 32 := by simpa [mem_ball, dist_zero_right] using hw
          simp only [mem_closedBall, dist_zero_right]; linarith)
      have hder := (((hgeometry _ hz').1.hasStrictDerivAt.hasDerivAt.comp z
        ((hasDerivAt_id z).const_add (chartCenter Y))).sub_const (canonicalGateInZeta N (chartCenter Y))).deriv
      simp only [Function.comp_def, mul_one] at hder
      rw [heq.deriv_eq, hder]
      exact (hgeometry _ hz').2
  obtain ⟨hPc, hPgate⟩ := chart_compact_gate N Y hY
  have hFa : ∀ᶠ s : ℝ in 𝓝[>] 0, DiffContOnCl ℂ (F s) (ball (0 : ℂ) 64) := by
    filter_upwards [hdata.positive _ hPc hPgate] with s hs
    apply hdisc
    intro z hz
    exact ((hs _ (mem_image_of_mem (chartPoint Y) hz)).2.comp_of_eq (hqa z hz) rfl).sub analyticAt_const
  obtain ⟨C, hC, hUniform⟩ := hdata.uniform _ hPc hPgate
  have hUF : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ z ∈ closedBall (0 : ℂ) 64,
      ‖F s z - F 0 z - (s : ℂ) * D z‖ ≤ C * s ^ (6 / 5 : ℝ) := by
    filter_upwards [hUniform] with s hs
    intro z hz
    convert (hs _ (mem_image_of_mem (chartPoint Y) hz)).2 using 1
    congr 1
    dsimp [F, D, repellingChart, repellingChartCoefficient]
    ring
  have hUQ : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ z ∈ closedBall (0 : ℂ) 64,
      ‖Q s z - Q 0 z - (s : ℂ) * E z‖ ≤ C * s ^ (6 / 5 : ℝ) := by
    filter_upwards [hUniform] with s hs
    intro z hz
    exact (hs _ (mem_image_of_mem (chartPoint Y) hz)).1
  obtain ⟨MF, hMF, hFb⟩ := exists_disc_norm_bound _ hF0a
  obtain ⟨MD, hMD, hDb⟩ := exists_disc_norm_bound _ hDa
  obtain ⟨MA, hMA, hAb⟩ := exists_disc_norm_bound _ hQ0a
  obtain ⟨ME, hME, hEb⟩ := exists_disc_norm_bound _ hEa
  obtain ⟨V, CG, hCG, hV0, hVa0, hV⟩ := exists_quantitative_transition F Q D E
    16 (6 / 5) C C MF MD MA ME (by norm_num) (by norm_num) (by norm_num)
    hC hC hMF hMD hMA hME (by rw [hF0eq 0 (by simp)]; simp) (by simpa only [show (2 : ℝ) * 16 = 32 by norm_num] using hF0)
    (by simpa only [show (4 : ℝ) * 16 = 64 by norm_num] using hdisc _ hF0a) (by simpa only [show (4 : ℝ) * 16 = 64 by norm_num] using hFa)
    (by simpa only [show (4 : ℝ) * 16 = 64 by norm_num] using hdisc _ hDa) (by simpa only [show (4 : ℝ) * 16 = 64 by norm_num] using hdisc _ hQ0a)
    (by simpa only [show (4 : ℝ) * 16 = 64 by norm_num] using hdisc _ hEa) (by simpa only [show (4 : ℝ) * 16 = 64 by norm_num] using hFb)
    (by simpa only [show (4 : ℝ) * 16 = 64 by norm_num] using hDb) (by simpa only [show (4 : ℝ) * 16 = 64 by norm_num] using hAb) (by simpa only [show (4 : ℝ) * 16 = 64 by norm_num] using hEb)
    (by simpa only [show (4 : ℝ) * 16 = 64 by norm_num] using hUF) (by simpa only [show (4 : ℝ) * 16 = 64 by norm_num] using hUQ)
  refine ⟨V, CG, hCG, ?_, ?_, ?_⟩
  · simpa only [show (16 : ℝ) / 4 = 4 by norm_num, F] using hV0
  · simpa only [show (16 : ℝ) / 4 = 4 by norm_num] using hVa0
  · simpa only [show (16 : ℝ) / 4 = 4 by norm_num, F, Q, D, E] using hV

def transitionValue (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (N M : ℕ) (Y : ℝ) (V : ℝ → ℂ → ℂ) (s : ℝ) (w : ℂ) : ℂ :=
  attractingChart U H e₁ e₂ A B Γ N Y s (V s w) -
    ActualNormalizationAnchorExpansion.anchorValue U H e₁ e₂ A B Γ M s

def transitionCorrection (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (N M : ℕ) (Y : ℝ) (V : ℝ → ℂ → ℂ) (w : ℂ) : ℂ :=
  attractingChartCoefficient U H e₁ e₂ A B Γ N Y (V 0 w) -
    (deriv (attractingChart U H e₁ e₂ A B Γ N Y 0) (V 0 w) /
      deriv (repellingChart U H e₁ e₂ A B Γ N Y 0) (V 0 w)) *
        repellingChartCoefficient U H e₁ e₂ A B Γ N Y (V 0 w) -
    ActualNormalizationAnchorExpansion.anchorCoefficient U H e₁ e₂ A B Γ M

/-- The complete actual analytic input needed by the Fourier theorem.
Every field is obtained from one preparation and genuine moving inverses. -/
structure ActualTransitionData (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (R : ℝ) (N M : ℕ) (Y : ℝ) (V : ℝ → ℂ → ℂ) : Prop where
  length_margin : R + 72 ≤ 3 * (N : ℝ) / 4
  geometry : ∀ z ∈ ball (chartCenter Y) 32,
    AnalyticAt ℂ (canonicalGateInZeta N) z ∧ ‖deriv (canonicalGateInZeta N) z - 1‖ ≤ 1 / 4
  bilateral : BilateralGateData U H e₁ e₂ A B Γ R 64 N
  height : 64 * ((N : ℝ) + 1) + 64 ≤ Y
  inverse_zero : ∀ w ∈ ball (0 : ℂ) 4,
    V 0 w ∈ closedBall (0 : ℂ) 16 ∧ repellingChart U H e₁ e₂ A B Γ N Y 0 (V 0 w) = w
  inverse_zero_analytic : AnalyticOnNhd ℂ (V 0) (ball (0 : ℂ) 4)
  inverse_positive : ∀ᶠ s : ℝ in 𝓝[>] 0,
    (∀ w ∈ ball (0 : ℂ) 4,
      V s w ∈ closedBall (0 : ℂ) 16 ∧ repellingChart U H e₁ e₂ A B Γ N Y s (V s w) = w) ∧
    AnalyticOnNhd ℂ (V s) (ball (0 : ℂ) 4)
  transition_zero : AnalyticOnNhd ℂ (transitionValue U H e₁ e₂ A B Γ N M Y V 0) (ball (0 : ℂ) 4)
  transition_positive : ∀ᶠ s : ℝ in 𝓝[>] 0,
    AnalyticOnNhd ℂ (transitionValue U H e₁ e₂ A B Γ N M Y V s) (ball (0 : ℂ) 4)
  correction_analytic : AnalyticOnNhd ℂ (transitionCorrection U H e₁ e₂ A B Γ N M Y V) (ball (0 : ℂ) 4)
  uniform : ∃ C ≥ 0, ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ w ∈ ball (0 : ℂ) 4,
    ‖transitionValue U H e₁ e₂ A B Γ N M Y V s w -
        transitionValue U H e₁ e₂ A B Γ N M Y V 0 w -
      (s : ℂ) * transitionCorrection U H e₁ e₂ A B Γ N M Y V w‖ ≤ C * s ^ (6 / 5 : ℝ)
  anchor_entry : ExponentialUnfolding.orbit RealNormalizationAnchor.normalizationAnchor 0 M ∈
    ParabolicFatouHolomorphic.petal (R + 1)

/-- Actual fixed chart derivatives have the physical Jacobian ratio: the
nonzero reciprocal-coordinate chain factor cancels. -/
theorem chart_derivative_ratio
    (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (R Y : ℝ) (N : ℕ)
    (hd : BilateralGateData U H e₁ e₂ A B Γ R 64 N)
    (hY : 64 * ((N : ℝ) + 1) + 64 ≤ Y) (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) 64) :
    deriv (repellingChart U H e₁ e₂ A B Γ N Y 0) z ≠ 0 ∧
    deriv (attractingChart U H e₁ e₂ A B Γ N Y 0) z /
      deriv (repellingChart U H e₁ e₂ A B Γ N Y 0) z =
    deriv (fun u => forwardCoordinate U H e₁ e₂ A B Γ N u 0) (chartPoint Y z) /
      deriv (fun u => backwardCoordinate U H e₁ e₂ A B Γ N u 0) (chartPoint Y z) := by
  have hg := chartPoint_in_gate N Y hY z hz
  have hs := hd.spatial _ hg
  let d : ℂ := 2 / (chartCenter Y + z) ^ 2
  have hdne : d ≠ 0 := div_ne_zero (by norm_num) (pow_ne_zero 2 (chart_argument_ne_zero N Y hY z hz))
  have hq : HasDerivAt (chartPoint Y) d z := by
    rw [HasDerivAt, HasDerivAtFilter, hasFDerivAtFilter_iff_isLittleO]
    simpa [chartPoint, Function.comp_def, d] using
      ((hasDerivAt_inverseCoordinate _ (chart_argument_ne_zero N Y hY z hz)).comp z
        ((hasDerivAt_id z).const_add (chartCenter Y))).hasFDerivAt.isLittleO
  have ha := (hs.1.hasStrictDerivAt.hasDerivAt.comp z hq).deriv
  have hb := ((hs.2.2.1.hasStrictDerivAt.hasDerivAt.comp z hq).sub_const
    (canonicalGateInZeta N (chartCenter Y))).deriv
  change deriv (attractingChart U H e₁ e₂ A B Γ N Y 0) z =
    deriv (fun u => forwardCoordinate U H e₁ e₂ A B Γ N u 0) (chartPoint Y z) * d at ha
  change deriv (repellingChart U H e₁ e₂ A B Γ N Y 0) z =
    deriv (fun u => backwardCoordinate U H e₁ e₂ A B Γ N u 0) (chartPoint Y z) * d at hb
  refine ⟨by rw [hb]; exact mul_ne_zero hs.2.2.2 hdne, ?_⟩
  rw [ha, hb]
  field_simp

/-- Actual full transition data, including the separately transported true
normalization anchor, are derived from the common deep coordinate data. -/
theorem exists_transition_data_of_deep
    (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (R : ℝ)
    (hd : DeepCoordinateData U H e₁ e₂ A B Γ R) :
    ∃ (N M : ℕ) (Y : ℝ) (V : ℝ → ℂ → ℂ),
      ActualTransitionData U H e₁ e₂ A B Γ R N M Y V := by
  obtain ⟨N, Y, _Vbase, hN, hY, hgeometry, _hbasea, _hbase, _hsegment⟩ :=
    exists_whole_canonical_image_gate (4 * (R + 72) / 3)
  have hmargin : R + 72 ≤ 3 * (N : ℝ) / 4 := by linarith
  have hlength : R + 64 + 2 ≤ 3 * (N : ℝ) / 4 := by linarith
  have hdata := bilateral_gate_data_of_deep U H e₁ e₂ A B Γ R hd N hlength
  obtain ⟨V, C, hC, hV0, hVa0, hV⟩ := quantitative_transition_of_data
    U H e₁ e₂ A B Γ R Y N hdata hY hgeometry
  obtain ⟨M, hentry, _hanchor0, hanchor⟩ :=
    ActualNormalizationAnchorExpansion.exists_anchor_expansion_of_deep U H e₁ e₂ A B Γ R hd
  let T := fun s w => attractingChart U H e₁ e₂ A B Γ N Y s (V s w)
  let D := fun w => attractingChartCoefficient U H e₁ e₂ A B Γ N Y (V 0 w) -
    (deriv (attractingChart U H e₁ e₂ A B Γ N Y 0) (V 0 w) /
      deriv (repellingChart U H e₁ e₂ A B Γ N Y 0) (V 0 w)) *
      repellingChartCoefficient U H e₁ e₂ A B Γ N Y (V 0 w)
  obtain ⟨CG, hCG, hCGbound⟩ := uniform_subtract_normalization T D (ball (0 : ℂ) 4)
    (6 / 5) C (ActualNormalizationAnchorExpansion.anchorValue U H e₁ e₂ A B Γ M)
    (ActualNormalizationAnchorExpansion.anchorCoefficient U H e₁ e₂ A B Γ M) hC
    (hV.mono fun s hs => hs.2.2) hanchor
  have hclosed (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) 16) : z ∈ closedBall (0 : ℂ) 64 := by
    have hn : ‖z‖ ≤ 16 := by simpa [mem_closedBall, dist_zero_right] using hz
    simp only [mem_closedBall, dist_zero_right]; linarith
  have hAa0 : AnalyticOnNhd ℂ (attractingChart U H e₁ e₂ A B Γ N Y 0) (closedBall (0 : ℂ) 64) := by
    intro z hz
    exact (hdata.spatial _ (chartPoint_in_gate N Y hY z hz)).1.comp_of_eq (chartPoint_analytic N Y hY z hz) rfl
  have hFa0 : AnalyticOnNhd ℂ (repellingChart U H e₁ e₂ A B Γ N Y 0) (closedBall (0 : ℂ) 64) := by
    intro z hz
    exact ((hdata.spatial _ (chartPoint_in_gate N Y hY z hz)).2.2.1.comp_of_eq
      (chartPoint_analytic N Y hY z hz) rfl).sub analyticAt_const
  have hDa : AnalyticOnNhd ℂ (repellingChartCoefficient U H e₁ e₂ A B Γ N Y) (closedBall (0 : ℂ) 64) := by
    intro z hz
    exact (hdata.coefficient _ (chartPoint_in_gate N Y hY z hz)).2.comp_of_eq (chartPoint_analytic N Y hY z hz) rfl
  have hEa : AnalyticOnNhd ℂ (attractingChartCoefficient U H e₁ e₂ A B Γ N Y) (closedBall (0 : ℂ) 64) := by
    intro z hz
    exact (hdata.coefficient _ (chartPoint_in_gate N Y hY z hz)).1.comp_of_eq (chartPoint_analytic N Y hY z hz) rfl
  have hT0 : AnalyticOnNhd ℂ (transitionValue U H e₁ e₂ A B Γ N M Y V 0) (ball (0 : ℂ) 4) := by
    intro w hw
    exact ((hAa0 _ (hclosed _ (hV0 w hw).1)).comp_of_eq (hVa0 w hw) rfl).sub analyticAt_const
  have hD : AnalyticOnNhd ℂ (transitionCorrection U H e₁ e₂ A B Γ N M Y V) (ball (0 : ℂ) 4) := by
    intro w hw
    have hz := hclosed _ (hV0 w hw).1
    have hne := (chart_derivative_ratio U H e₁ e₂ A B Γ R Y N hdata hY _ hz).1
    have hraw := (hEa _ hz).sub (((hAa0 _ hz).deriv.div (hFa0 _ hz).deriv hne).mul (hDa _ hz))
    exact (hraw.comp_of_eq (hVa0 w hw) rfl).sub analyticAt_const
  obtain ⟨hPc, hPg⟩ := chart_compact_gate N Y hY
  have hTpos : ∀ᶠ s : ℝ in 𝓝[>] 0,
      AnalyticOnNhd ℂ (transitionValue U H e₁ e₂ A B Γ N M Y V s) (ball (0 : ℂ) 4) := by
    filter_upwards [hV, hdata.positive _ hPc hPg] with s hs hp
    intro w hw
    have hz := hclosed _ (hs.1 w hw).1
    have ha := (hp _ (mem_image_of_mem (chartPoint Y) hz)).1
    have hchart := ha.comp_of_eq (chartPoint_analytic N Y hY _ hz) rfl
    exact (hchart.comp_of_eq (hs.2.1 w hw) rfl).sub analyticAt_const
  refine ⟨N, M, Y, V, hmargin, hgeometry, hdata, hY, hV0, hVa0, hV.mono (fun s hs => ⟨hs.1, hs.2.1⟩),
    hT0, hTpos, hD, ⟨CG, hCG, ?_⟩, hentry⟩
  simpa only [T, D, transitionValue, transitionCorrection] using hCGbound

/-- Unconditional construction from the true exponential preparation. All
actual analytic, inverse, compact gate, and normalization inputs are outputs. -/
theorem exists_actual_transition_data :
    ∃ U H e₁ e₂ A B : ℂ → ℂ, ∃ K : ℂ → ℂ → ℂ, ∃ F Γ : ℂ × ℂ → ℂ,
      ActualPreparationData U H e₁ e₂ A B K F Γ ∧
        ∃ R : ℝ, DeepCoordinateData U H e₁ e₂ A B Γ R ∧
          ∃ (N M : ℕ) (Y : ℝ) (V : ℝ → ℂ → ℂ),
            ActualTransitionData U H e₁ e₂ A B Γ R N M Y V := by
  obtain ⟨U, H, e₁, e₂, A, B, K, F, Γ, hdata, R, hd⟩ := exists_actual_deep_coordinate_data
  obtain ⟨N, M, Y, V, ht⟩ := exists_transition_data_of_deep U H e₁ e₂ A B Γ R hd
  exact ⟨U, H, e₁, e₂, A, B, K, F, Γ, hdata, R, hd, N, M, Y, V, ht⟩

/-- The true preparation, local Abel identities, compact coordinate data,
and quantitative transition use the same witnesses and depth. -/
theorem exists_actual_deep_abel_transition_data :
    ∃ U H e₁ e₂ A B : ℂ → ℂ, ∃ K : ℂ → ℂ → ℂ, ∃ F Γ : ℂ × ℂ → ℂ,
      ActualPreparationData U H e₁ e₂ A B K F Γ ∧
        ∃ R : ℝ, DeepCoordinateData U H e₁ e₂ A B Γ R ∧
          LocalAbelData U H e₁ e₂ A B Γ R ∧
          ∃ (N M : ℕ) (Y : ℝ) (V : ℝ → ℂ → ℂ),
            ActualTransitionData U H e₁ e₂ A B Γ R N M Y V := by
  obtain ⟨U, H, e₁, e₂, A, B, K, F, Γ, hdata, R, hd, hl⟩ := exists_actual_deep_abel_data
  obtain ⟨N, M, Y, V, ht⟩ := exists_transition_data_of_deep U H e₁ e₂ A B Γ R hd
  exact ⟨U, H, e₁, e₂, A, B, K, F, Γ, hdata, R, hd, hl, N, M, Y, V, ht⟩

end Kneser.ActualQuantitativeGateTransition

end
