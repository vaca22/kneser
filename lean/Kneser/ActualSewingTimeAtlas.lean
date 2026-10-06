import Kneser.FourierSewingTimeAtlas
import Kneser.ActualGlobalSewingIdentification
import Kneser.ActualSewnAllOrders

/-! The same actual preparation, multiplier roots, growing inverse and
Fourier sewing corrections supply the complete time atlas.  Its half-
plane width and small derivative budget are proved from the genuine
parameter limit.  Physical inverse charts are not extended beyond their
proved regular domains by this certificate. -/

set_option autoImplicit false
noncomputable section
namespace Kneser.ActualSewingTimeAtlas

open Filter Set Metric Complex MeasureTheory
open Kneser.WeightedFourier Kneser.FourierSewing
open Kneser.ActualNormalizedSewing Kneser.ActualGlobalSewingIdentification
open Kneser.ReflectedOrbitChainCoefficient Kneser.CommonQuadraticBaseline
open Kneser.ActualAllOrderUpperHornBaseline Kneser.ActualHolomorphicGrowingLens
open Kneser.GrowingBandGeometry Kneser.GrowingLensSpatialHolomorphy
open Kneser.ActualGrowingCoordinateInverse Kneser.ActualNormalizedGrowingTransition
open Kneser.NormalizedGrowingFourier Kneser.GateFourierDerivative
open Kneser.ActualBandTimeConfluence Kneser.RealNormalizationAnchor
open Kneser.ActualSewnAllOrders
open scoped Topology Interval

/-- Every clause refers to the same Q, P and normalizing translation.
The genuine Fourier integrals and Lambda comparison remain attached to
the atlas, rather than being supplied by an independent sewing witness. -/
def GeometricSewingWitness (h Y : ℝ) (T : ℂ → ℂ) : Prop :=
  3 < sewingWidth h Y 64 1 ∧
  ∃ Q P : Space, ∃ ζ : ℂ,
    Q ∈ Negative ∧ ‖Q‖ ≤ 1 ∧ (∀ n : ℤ, n < 0 → P n = 0) ∧ ‖P‖ ≤ 1 ∧
    ‖ζ‖ ≤ normalizationConstant Y 64 1 4 * lambda h ∧ ‖ζ‖ ≤ 1 ∧
    TimeAtlas (sewingWidth h Y 64 1) h T Q P (gateFourierCoefficient 0 0 T) ζ ∧
    (∀ z : ℂ, |z.im| ≤ sewingWidth h Y 64 1 →
      T (lowerMap (sewingWidth h Y 64 1) Q z) =
        upperMap (sewingWidth h Y 64 1) P (gateFourierCoefficient 0 0 T) z) ∧
    (∀ n : ℕ, 1 ≤ n →
      translatedCoefficient (sewingWidth h Y 64 1) h P (gateFourierCoefficient 0 0 T) ζ n =
        ∫ x : ℝ in (0 : ℝ)..1,
          sewnDisplacement (sewingWidth h Y 64 1) h P (gateFourierCoefficient 0 0 T) ζ (x : ℂ) *
            exp (-Kneser.fourierFrequency n * (x : ℂ))) ∧
    (∀ n : ℕ, 1 ≤ n →
      ‖translatedCoefficient (sewingWidth h Y 64 1) h P (gateFourierCoefficient 0 0 T) ζ n /
          (lambda h : ℂ) ^ n - gateFourierCoefficient n 0 T * hornPhase (gateFourierCoefficient 0 0 T) n‖ ≤
        comparisonConstant Y 64 1 4 n * lambda h)

theorem geometric_witness_of_sewing_witness (h Y : ℝ) (T : ℂ → ℂ)
    (hH : 3 < sewingWidth h Y 64 1) (hw : SewingWitness h Y T) :
    GeometricSewingWitness h Y T := by
  obtain ⟨Q, P, ζ, hQ, hQn, hP, hPn, hζ, hζ1, hroot, _hzero, hseam, hint, hcmp⟩ := hw
  have hseam' : ∀ z : ℂ, |z.im| ≤ sewingWidth h Y 64 1 →
      T (lowerMap (sewingWidth h Y 64 1) Q z) =
        upperMap (sewingWidth h Y 64 1) P (gateFourierCoefficient 0 0 T) z := hseam
  exact ⟨hH, Q, P, ζ, hQ, hQn, hP, hPn, hζ, hζ1,
    time_atlas_of_fourier_data _ h hH T Q P _ ζ hQ hQn hP hPn hseam' hroot,
    hseam', hint, hcmp⟩

/-- The actual global family has a genuine geometric sewing atlas at
every sufficiently small positive parameter, on the same witnesses. -/
def GeometricFamily (U H A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F : ℂ × ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ) : Prop :=
  ∃ R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P : ℝ, ∃ N M M₀ : ℕ,
  ∃ Vold V : ℝ → ℂ → ℂ, ∃ p r G : ℂ → ℂ,
    BaselineData U H A B K F e Γ R Rₛ Y₁ Y₀ Mh Ch N M M₀ Yg Vold V p r G ∧
    ∀ᶠ s : ℝ in 𝓝[>] 0, ∃ a b θ : ℝ, ∃ Vg : ℂ → ℂ,
      LensControl (first (e 1)) (second (e 1)) A B (Γ 1) s a b θ Y η Mg P ∧
      AnalyticOnNhd ℂ Vg (strip θ (3*Y+boundaryMargin P)) ∧
      (∀ w ∈ strip θ (3*Y+boundaryMargin P), Vg w ∈ strip θ (3*Y) ∧
        repellingCoordinate A B (Γ 1) s a b θ (first (e 1) s) (second (e 1) s) (Vg w) = w) ∧
      let T := transition A B (Γ 1) s a b θ realAnchor ((a+b)/2) (first (e 1) s) (second (e 1) s) Vg
      GeometricSewingWitness (height θ) (boundaryLoss Y P) T ∧
      (∀ n : ℤ, n ≠ 0 →
        gateFourierCoefficient n 0 (actualTransition U H A B e Γ N M Yg V s) *
            exp (-Kneser.fourierFrequency n * gateFourierCoefficient 0 0
              (actualTransition U H A B e Γ N M Yg V s)) =
          gateFourierCoefficient n 0 T * exp (-Kneser.fourierFrequency n * gateFourierCoefficient 0 0 T)) ∧
      lambda (height θ) = Kneser.ActualLambdaFlatness.lambdaFactor s a

theorem geometric_family_of_sewn_family
    (U H A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F : ℂ × ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (hf : SewnFamily U H A B K F e Γ) : GeometricFamily U H A B K F e Γ := by
  obtain ⟨R, Rₛ, Y₁, Y₀, Mh, Ch, Yg, Y, η, Mg, P, N, M, M₀, Vold, V, p, r, G, hbase, he⟩ := hf
  let C : ℝ := max (2 * (boundaryLoss Y P + 70)) 1 + 1
  have hC : 0 < C := by dsimp [C]; linarith [le_max_right (2 * (boundaryLoss Y P + 70)) 1]
  have ht := actual_theta_uniform_small U H (first (e 1)) (second (e 1)) A B K F (Γ 1)
    hbase.actual (2 * Real.pi / C) (by positivity)
  refine ⟨R, Rₛ, Y₁, Y₀, Mh, Ch, Yg, Y, η, Mg, P, N, M, M₀, Vold, V, p, r, G, hbase, ?_⟩
  filter_upwards [he, ht] with s hs htheta
  obtain ⟨a, b, θ, Vg, hc, hVa, hVs, hw, hgauge, hscale⟩ := hs
  have hh := (htheta a b hc.left_neg hc.right_pos hc.left_fixed hc.right_fixed).2
  rw [← hc.theta_actual] at hh
  have hheight : C < height θ := (lt_div_iff₀ hc.theta_pos).mpr
    (by have hi := (lt_div_iff₀ hC).mp hh; nlinarith)
  have hH : 3 < sewingWidth (height θ) (boundaryLoss Y P) 64 1 := by
    have hCle : 2 * (boundaryLoss Y P + 70) < C := by
      dsimp [C]
      linarith [le_max_left (2 * (boundaryLoss Y P + 70)) 1]
    unfold sewingWidth bandWidth
    linarith
  exact ⟨a, b, θ, Vg, hc, hVa, hVs,
    geometric_witness_of_sewing_witness _ _ _ hH hw, hgauge, hscale⟩

theorem exists_actual_geometric_sewing_family :
    ∃ U H A B : ℂ → ℂ, ∃ K : ℂ → ℂ → ℂ, ∃ F : ℂ × ℂ → ℂ,
    ∃ e : (n : ℕ) → Fin (2*n) → ℂ → ℂ, ∃ Γ : ℕ → ℂ × ℂ → ℂ,
      GeometricFamily U H A B K F e Γ := by
  obtain ⟨U, H, A, B, K, F, e, Γ, hf⟩ := exists_actual_global_sewn_horn_family
  exact ⟨U, H, A, B, K, F, e, Γ, geometric_family_of_sewn_family U H A B K F e Γ hf⟩

/-- This pointwise bridge uses the Q, P and shift already selected for the
all-order coefficient theorem. It makes no new sewing choice. -/
theorem time_atlas_of_fiber_data (A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (T : ℝ → ℂ → ℂ) (Y η Mg P₀ s : ℝ) (w : Fiber)
    (hd : FiberData A B e Γ T Y η Mg P₀ s w)
    (hH : 3 < sewingWidth (height w.theta) (boundaryLoss Y P₀) 64 1) :
    TimeAtlas (sewingWidth (height w.theta) (boundaryLoss Y P₀) 64 1) (height w.theta)
      (globalTransition A B e Γ s w) w.negative w.positive
      (gateFourierCoefficient 0 0 (globalTransition A B e Γ s w)) w.shift := by
  let H := sewingWidth (height w.theta) (boundaryLoss Y P₀) 64 1
  let t₀ := gateFourierCoefficient 0 0 (globalTransition A B e Γ s w)
  have hroot : (normalizingCentre (height w.theta) t₀ + w.shift) +
      evaluate H w.positive (normalizingCentre (height w.theta) t₀ + w.shift) =
        normalizingCentre (height w.theta) t₀ := by
    have hz := hd.normalized
    change sewnCoordinate H (height w.theta) w.positive t₀ w.shift 0 = 0 at hz
    simp only [sewnCoordinate, add_zero] at hz
    unfold normalizingCentre at *
    linear_combination hz
  exact time_atlas_of_fourier_data H (height w.theta) hH _ w.negative w.positive t₀ w.shift
    hd.negative_support hd.negative_norm hd.positive_support hd.positive_norm hd.sewing_identity hroot

/-- The same selected fibers supporting every coefficient order have
the genuine half-plane atlas throughout a positive parameter germ. -/
theorem all_orders_data_time_atlas
    (U H A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F : ℂ × ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ : ℝ) (N M M₀ : ℕ)
    (Vold V : ℝ → ℂ → ℂ) (p r G : ℂ → ℂ) (W : ℝ → Fiber)
    (hd : AllOrdersData U H A B K F e Γ R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ N M M₀ Vold V p r G W) :
    ∀ᶠ s : ℝ in 𝓝[>] 0,
      3 < sewingWidth (height (W s).theta) (boundaryLoss Y P₀) 64 1 ∧
      TimeAtlas (sewingWidth (height (W s).theta) (boundaryLoss Y P₀) 64 1)
        (height (W s).theta) (globalTransition A B e Γ s (W s))
        (W s).negative (W s).positive
        (gateFourierCoefficient 0 0 (globalTransition A B e Γ s (W s))) (W s).shift := by
  let C : ℝ := max (2 * (boundaryLoss Y P₀ + 70)) 1 + 1
  have hC : 0 < C := by dsimp [C]; linarith [le_max_right (2 * (boundaryLoss Y P₀ + 70)) 1]
  have ht := actual_theta_uniform_small U H (first (e 1)) (second (e 1)) A B K F (Γ 1)
    hd.baseline.actual (2 * Real.pi / C) (by positivity)
  filter_upwards [hd.actual_fibers, ht] with s hs htheta
  have hc := hs.control
  have hh := (htheta _ _ hc.left_neg hc.right_pos hc.left_fixed hc.right_fixed).2
  rw [← hc.theta_actual] at hh
  have hheight : C < height (W s).theta := (lt_div_iff₀ hc.theta_pos).mpr
    (by have hi := (lt_div_iff₀ hC).mp hh; nlinarith)
  have hH : 3 < sewingWidth (height (W s).theta) (boundaryLoss Y P₀) 64 1 := by
    have hCle : 2 * (boundaryLoss Y P₀ + 70) < C := by
      dsimp [C]
      linarith [le_max_left (2 * (boundaryLoss Y P₀ + 70)) 1]
    unfold sewingWidth bandWidth
    linarith
  exact ⟨hH, time_atlas_of_fiber_data A B e Γ _ Y η Mg P₀ s (W s) hs hH⟩

/-- No fresh chart or coefficient witnesses are used: the all-order
endpoint and its actual geometric time atlas belong to the same family. -/
theorem exists_actual_all_orders_time_atlas :
    ∃ U H A B : ℂ → ℂ, ∃ K : ℂ → ℂ → ℂ, ∃ F : ℂ × ℂ → ℂ,
    ∃ e : (n : ℕ) → Fin (2*n) → ℂ → ℂ, ∃ Γ : ℕ → ℂ × ℂ → ℂ,
    ∃ R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ : ℝ, ∃ N M M₀ : ℕ,
    ∃ Vold V : ℝ → ℂ → ℂ, ∃ p r G : ℂ → ℂ, ∃ W : ℝ → Fiber,
      AllOrdersData U H A B K F e Γ R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ N M M₀ Vold V p r G W ∧
      ∀ᶠ s : ℝ in 𝓝[>] 0,
        3 < sewingWidth (height (W s).theta) (boundaryLoss Y P₀) 64 1 ∧
        TimeAtlas (sewingWidth (height (W s).theta) (boundaryLoss Y P₀) 64 1)
          (height (W s).theta) (globalTransition A B e Γ s (W s))
          (W s).negative (W s).positive
          (gateFourierCoefficient 0 0 (globalTransition A B e Γ s (W s))) (W s).shift := by
  obtain ⟨U,H,A,B,K,F,e,Γ,R,Rₛ,Y₁,Y₀,Mh,Ch,Yg,Y,η,Mg,P₀,N,M,M₀,Vold,V,p,r,G,W,hd⟩ :=
    exists_actual_sewn_all_orders
  exact ⟨U,H,A,B,K,F,e,Γ,R,Rₛ,Y₁,Y₀,Mh,Ch,Yg,Y,η,Mg,P₀,N,M,M₀,Vold,V,p,r,G,W,hd,
    all_orders_data_time_atlas U H A B K F e Γ R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ N M M₀ Vold V p r G W hd⟩

end Kneser.ActualSewingTimeAtlas
end
