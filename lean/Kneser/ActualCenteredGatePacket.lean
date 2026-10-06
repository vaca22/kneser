import Kneser.ActualHigherFinitePacket
import Kneser.ActualQuantitativeGateTransition

/-! Actual finite packets in a centered reciprocal chart.  Spatial
normalization is performed at the same physical point for every parameter;
no absolute parameter expansion of a preparation constant is asserted. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Kneser.ActualCenteredGatePacket

open Filter Set Metric Kneser.ActualBilateralGate
open Kneser.ActualQuantitativeGateTransition Kneser.ActualHigherFinitePacket
open Kneser.FiniteExpansionHolomorphy Kneser.ParabolicExponentialOrbit
open Kneser.CommonQuadraticBaseline
open scoped Topology BigOperators

def centeredRepelling (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (N : ℕ) (Y : ℝ) (s : ℝ) (z : ℂ) : ℂ :=
  repellingChart U H e₁ e₂ A B Γ N Y s z - repellingChart U H e₁ e₂ A B Γ N Y s 0

def centeredAttracting (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (N : ℕ) (Y : ℝ) (s : ℝ) (z : ℂ) : ℂ :=
  attractingChart U H e₁ e₂ A B Γ N Y s z - attractingChart U H e₁ e₂ A B Γ N Y s 0

theorem strict_point_interior_gate (N : ℕ) (u : ℂ) (hne : u ≠ 0)
    (hre : |(inverseCoordinate u).re| < 64)
    (him : 64 * ((N : ℝ) + 1) < |(inverseCoordinate u).im|) :
    u ∈ interior (gate 64 N) := by
  have hi : ContinuousAt inverseCoordinate u := continuousAt_const.div continuousAt_id hne
  have hnear : ∀ᶠ v in 𝓝 u,
      |(inverseCoordinate v).re| < 64 ∧ 64 * ((N : ℝ) + 1) < |(inverseCoordinate v).im| :=
    (((Complex.continuous_re.continuousAt.comp hi).abs.eventually (gt_mem_nhds hre)).and
      ((Complex.continuous_im.continuousAt.comp hi).abs.eventually (lt_mem_nhds him)))
  apply mem_interior_iff_mem_nhds.mpr
  exact Filter.mem_of_superset hnear fun v hv => ⟨hv.1.le, hv.2.le⟩

theorem chartPoint_in_interior (N : ℕ) (Y : ℝ)
    (hY : 64 * ((N : ℝ) + 1) + 64 ≤ Y) (z : ℂ)
    (hz : z ∈ closedBall (0 : ℂ) 56) : chartPoint Y z ∈ interior (gate 64 N) := by
  have hz64 : z ∈ closedBall (0 : ℂ) 64 := closedBall_subset_closedBall (by norm_num) hz
  have hY64 : 64 * ((N : ℝ) + 1) + 64 ≤ Y := by linarith
  have ha : chartCenter Y + z ≠ 0 := chart_argument_ne_zero N Y hY64 z hz64
  have hne : chartPoint Y z ≠ 0 := div_ne_zero (by norm_num) ha
  have he : inverseCoordinate (chartPoint Y z) = chartCenter Y + z := by
    exact Kneser.ParabolicOverlapGate.inverseCoordinate_involutive _
  have hn : ‖z‖ ≤ 56 := by simpa only [mem_closedBall, dist_zero_right] using hz
  apply strict_point_interior_gate N _ hne
  · rw [he]
    simpa [chartCenter] using (Complex.abs_re_le_norm z).trans_lt (by linarith : ‖z‖ < 64)
  · rw [he]
    have hl : -56 ≤ z.im := (abs_le.mp ((Complex.abs_im_le_norm z).trans hn)).1
    have hb : 64 * ((N : ℝ) + 1) < (chartCenter Y + z).im := by
      simp only [chartCenter, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_add]
      linarith
    exact hb.trans_le (le_abs_self _)

theorem polynomial_pullback (c : ℕ → ℂ → ℂ) (m : ℕ) (q : ℂ → ℂ) (s z : ℂ) :
    complexPolynomial (fun j z => c j (q z)) m s z = complexPolynomial c m s (q z) := rfl

/-- The packet retains the actual two families, the same orbit coefficients,
and every lower compact-uniform remainder after chart pullback. -/
theorem centered_packet_of_packet (U H A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (N m n L : ℕ) (Y : ℝ)
    (hY : 64 * ((N : ℝ) + 1) + 64 ≤ Y)
    (hp : Packet U H A B e Γ N m n L (chartPoint Y 0)) :
    NormalizedFiniteData
      (centeredAttracting U H (first (e 1)) (second (e 1)) A B (Γ 1) N Y)
      (fun j z => Kneser.HigherGateTransport.forwardCoefficient U H A B n (e n) (Γ n) N L (chartPoint Y z) j -
        Kneser.HigherGateTransport.forwardCoefficient U H A B n (e n) (Γ n) N L (chartPoint Y 0) j)
      (fun z => attractingChartCoefficient U H (first (e 1)) (second (e 1)) A B (Γ 1) N Y z -
        attractingChartCoefficient U H (first (e 1)) (second (e 1)) A B (Γ 1) N Y 0)
      m (ball (0 : ℂ) 56) ∧
    NormalizedFiniteData
      (centeredRepelling U H (first (e 1)) (second (e 1)) A B (Γ 1) N Y)
      (fun j z => Kneser.HigherGateTransport.backwardCoefficient U H A B n (e n) (Γ n) N L (chartPoint Y z) j -
        Kneser.HigherGateTransport.backwardCoefficient U H A B n (e n) (Γ n) N L (chartPoint Y 0) j)
      (fun z => repellingChartCoefficient U H (first (e 1)) (second (e 1)) A B (Γ 1) N Y z -
        repellingChartCoefficient U H (first (e 1)) (second (e 1)) A B (Γ 1) N Y 0)
      m (ball (0 : ℂ) 56) := by
  have hy : 64 * ((N : ℝ) + 1) + 64 ≤ Y := by linarith
  have hmap : MapsTo (chartPoint Y) (closedBall (0 : ℂ) 56) (interior (gate 64 N)) :=
    fun z hz => chartPoint_in_interior N Y hY z hz
  have hqa : AnalyticOnNhd ℂ (chartPoint Y) (closedBall (0 : ℂ) 56) :=
    fun z hz => chartPoint_analytic N Y hy z (closedBall_subset_closedBall (by norm_num) hz)
  have pullback (f : ℝ → ℂ → ℂ) (c : ℕ → ℂ → ℂ) (d : ℂ → ℂ)
      (h : NormalizedFiniteData f c d m (interior (gate 64 N))) :
      NormalizedFiniteData (fun s z => f s (chartPoint Y z))
        (fun j z => c j (chartPoint Y z)) (fun z => d (chartPoint Y z)) m (ball (0 : ℂ) 56) := by
    refine ⟨?_, ?_, ?_⟩
    · intro j hj z hz
      exact (h.1 j hj _ (hmap (ball_subset_closedBall hz))).comp_of_eq
        (hqa z (ball_subset_closedBall hz)) rfl
    · intro z hz
      exact h.2.1 _ (hmap (ball_subset_closedBall hz))
    · intro j hj K hK hKU
      have hmK : K ⊆ closedBall (0 : ℂ) 56 := hKU.trans ball_subset_closedBall
      have hKi : IsCompact ((chartPoint Y) '' K) :=
        hK.image_of_continuousOn (hqa.continuousOn.mono hmK)
      have hKsub : (chartPoint Y) '' K ⊆ interior (gate 64 N) := by
        rintro _ ⟨z, hz, rfl⟩
        exact hmap (hmK hz)
      obtain ⟨C, hC, hb⟩ := h.2.2 j hj _ hKi hKsub
      exact ⟨C, hC, hb.mono fun s hs z hz => hs _ (mem_image_of_mem _ hz)⟩
  have ha := pullback _ _ _ hp.1
  have hr := pullback _ _ _ hp.2.1
  constructor
  · exact ha
  · convert hr using 1 <;> try rfl
    funext s z
    simp only [centeredRepelling, repellingChart]
    ring

end Kneser.ActualCenteredGatePacket
