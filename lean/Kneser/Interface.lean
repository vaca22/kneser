import Kneser.GluedOriginalResult

/-!
# Readable interface to the sewn tetration family

This module is the human-readable entry point of the project. It packages the
*actual* construction behind the low-level endpoints

* `Kneser.OriginalMainResult.exists_actual_original_first_order_result`,
* `Kneser.GluedOriginalResult.exists_actual_glued_original_result`,
* `Kneser.ActualPhysicalSewnCoefficients.exists_actual_physical_sewn_coefficients`

(which quantify over roughly thirty auxiliary objects) into one bundled structure
`Kneser.Interface.SewnTetrationFamily`, and states the main results in a few lines.

## The mathematics

For a small parameter `s > 0` the real base is `b(s) = exp((1-s)/e)`, so that
`1 < b(s) < exp(1/e)` and `x ↦ b(s)^x` has two real fixed points
`L₁(s) < e < L₂(s)` with multipliers `λᵢ(s) = log b(s) · Lᵢ(s)`.
A structure `F : SewnTetrationFamily` provides, for every `s ∈ (0, s₀)`:

* an open domain `F.domain s ∋ 0` and a holomorphic function `F.K s` on it with
  `K(0) = 1` and `K(z+1) = b(s)^{K(z)}` (the domain is stable under `z ↦ z+1`);
  this is the two-sided glued function (upper physical chart and entire
  repelling chart);
* an integer period line `[J(s), J(s)+1] ⊆ F.domain s` and the genuine Fourier
  integrals `τₙ(s)` of `Ψₛ(K(z)) - z` on it, where `Ψₛ` is the principal
  Koenigs–Abel coordinate at the attracting fixed point `L₁(s)`;
* the multiplier parameter `p(s) = -log λ₁(s) · log λ₂(s)`, extended to an analytic
  germ with `p(0) = 0`, `p'(0) = 2`;
* the sewing scale `Λ(s) = exp(4π² / log λ₁(s))`, which is flat at `0`;
* the canonical global upper horn map `G` (`G(z+1) = G(z)+1`, `G(z) - z → 0` in
  the upper direction), its baseline coefficients `Bₙ` (Fourier coefficient of
  `G - id` times the anchor phase), and the explicit first coefficient
  `κₙ = dₙ / (2tₙ) - π i n d₀`, built from the parabolic transition `T₀` and the
  explicit first-order correction `D`;
* for every mode `n ≥ 1` with `Bₙ ≠ 0`: a coherent all-orders expansion
  `log(τₙ(s)/Λ(s)ⁿ/Bₙ) = Σ_{j ≤ m} αₙ,ⱼ p(s)ʲ + O(|p(s)|^{m+1})` with `αₙ,₁ = κₙ`,
  in particular `log(τₙ(s)/Λ(s)ⁿ/Bₙ) = κₙ p(s) + O(|p(s)|²)`.

The field `realized` records that all of these readable objects are literally
the objects of the low-level construction (`GluedResultData`), so nothing is
re-chosen in this file.

## What is NOT covered

* The constructed glued function is **not** identified with the independently
  defined classical Kneser tetration (Kneser uniformization identity).
* No full complex-parameter continuation or global single-valuedness statement.
* No certificate that a specific mode is nonzero: in particular `B₁ ≠ 0` and the
  numerical certificates of the manuscript are not formalized. Logarithmic
  statements are only asserted for modes with `Bₙ ≠ 0`.
* Remainder constants may depend on the mode `n`; no uniformity in `n` is claimed.
* The explicit absolute orbit-series formula of the correction `D` is not
  restated here; `D` is pinned by `realized` to
  `Kneser.ActualRealNormalizedFirstCoefficient.physicalCorrection`.
-/

set_option autoImplicit false
noncomputable section
namespace Kneser.Interface

open Filter Set Complex
open scoped Topology Real

/-- The real base `b(s) = exp((1-s)/e)` of the tetration family. -/
def tetrationBase (s : ℝ) : ℝ := Real.exp ((1 - s) / Real.exp 1)

/-- The multiplier of `x ↦ b(s)^x` at a fixed point `L`, namely `log b(s) · L`. -/
def fixedPointMultiplier (s L : ℝ) : ℝ := Real.log (tetrationBase s) * L

/-- The principal Koenigs–Abel coordinate of `x ↦ b(s)^x` at the attracting fixed
point `L`: `Ψ(x) = log(Φ(x)/Φ(1)) / log λ`, where `Φ` is the Koenigs linearizer
`Φ(x) = lim λ⁻ᵏ (Eᵏ(x) - L)` (written as an explicit telescoping series in
`Kneser.PositiveKoenigsOrbit.koenigsValue`). -/
def koenigsAbelLift (s L : ℝ) (x : ℂ) : ℂ :=
  Kneser.ActualBaseTetration.originalAbelLift s (L / Real.exp 1 - 1) x

/-- Fourier coefficient of `T - id` on the horizontal unit segment at height `y`:
`∫₀¹ (T(x+iy) - (x+iy)) e^{-2πin(x+iy)} dx`. -/
def gateCoefficient (T : ℂ → ℂ) (y : ℝ) (n : ℤ) : ℂ :=
  ∫ x : ℝ in (0:ℝ)..1, (T ((x:ℂ) + I * y) - ((x:ℂ) + I * y)) *
    cexp (-(2 * π * I * n) * ((x:ℂ) + I * y))

/-- Fourier coefficient of a correction `D` on the horizontal unit segment at height `y`. -/
def correctionCoefficient (D : ℂ → ℂ) (y : ℝ) (n : ℤ) : ℂ :=
  ∫ x : ℝ in (0:ℝ)..1, D ((x:ℂ) + I * y) * cexp (-(2 * π * I * n) * ((x:ℂ) + I * y))

/-- The genuine period-line Fourier coefficient of a function `K` lifted by `Ψ`:
`∫₀¹ (Ψ(K(J+x)) - (J+x)) e^{-2πin(J+x)} dx`. -/
def periodLineCoefficient (Ψ K : ℂ → ℂ) (J : ℕ) (n : ℤ) : ℂ :=
  ∫ x : ℝ in (0:ℝ)..1, (Ψ (K ((J:ℂ) + x)) - ((J:ℂ) + x)) *
    cexp (-(2 * π * I * n) * ((J:ℂ) + x))

/-- The actual sewn tetration family, with its multiplier parameter, sewing scale,
canonical horn baseline and explicit first-order coefficient. Every field is
proved for the project's construction (see `exists_sewnTetrationFamily`). -/
structure SewnTetrationFamily where
  /-- The parameter range is `(0, s₀)`. -/
  s₀ : ℝ
  s₀_pos : 0 < s₀
  /-- On the parameter range the base lies strictly between `1` and `exp(1/e)`. -/
  base_range : ∀ s ∈ Ioo 0 s₀, 1 < tetrationBase s ∧ tetrationBase s < Real.exp (1 / Real.exp 1)
  /-- The attracting and repelling real fixed points of `x ↦ b(s)^x`. -/
  L₁ : ℝ → ℝ
  L₂ : ℝ → ℝ
  fixed_points : ∀ s ∈ Ioo 0 s₀, L₁ s < Real.exp 1 ∧ Real.exp 1 < L₂ s ∧
    (tetrationBase s : ℂ) ^ (L₁ s : ℂ) = L₁ s ∧ (tetrationBase s : ℂ) ^ (L₂ s : ℂ) = L₂ s
  /-- The multiplier parameter, an analytic germ with `p(0)=0`, `p'(0)=2`. -/
  p : ℂ → ℂ
  p_analytic : AnalyticAt ℂ p 0
  p_zero : p 0 = 0
  p_deriv : HasDerivAt p 2 0
  p_eq : ∀ s ∈ Ioo 0 s₀, p s =
    ((-Real.log (fixedPointMultiplier s (L₁ s)) * Real.log (fixedPointMultiplier s (L₂ s)) : ℝ) : ℂ)
  /-- The glued tetration `K_s` on its open domain. -/
  domain : ℝ → Set ℂ
  K : ℝ → ℂ → ℂ
  domain_open : ∀ s ∈ Ioo 0 s₀, IsOpen (domain s)
  zero_mem : ∀ s ∈ Ioo 0 s₀, (0:ℂ) ∈ domain s
  holomorphic : ∀ s ∈ Ioo 0 s₀, AnalyticOnNhd ℂ (K s) (domain s)
  K_zero : ∀ s ∈ Ioo 0 s₀, K s 0 = 1
  K_succ : ∀ s ∈ Ioo 0 s₀, ∀ z ∈ domain s,
    z + 1 ∈ domain s ∧ K s (z + 1) = (tetrationBase s : ℂ) ^ K s z
  /-- The integer period line `[J(s), J(s)+1]` lies in the domain. -/
  J : ℝ → ℕ
  period_line : ∀ s ∈ Ioo 0 s₀, ∀ x ∈ Icc (0:ℝ) 1, (J s : ℂ) + x ∈ domain s
  /-- The genuine Fourier integrals of the Koenigs–Abel lift of `K_s`. -/
  τ : ℝ → ℤ → ℂ
  τ_eq : ∀ s n, τ s n = periodLineCoefficient (koenigsAbelLift s (L₁ s)) (K s) (J s) n
  /-- The sewing scale `Λ(s) = exp(4π²/log λ₁(s))`, flat at `0`. -/
  Λ : ℝ → ℝ
  Λ_eq : ∀ s ∈ Ioo 0 s₀, Λ s = Real.exp (4 * π ^ 2 / Real.log (fixedPointMultiplier s (L₁ s)))
  Λ_flat : ∀ m : ℕ, ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < Λ s ∧ Λ s ≤ s ^ m
  /-- The canonical global upper horn map `G`. -/
  G : ℂ → ℂ
  G_periodic : ∀ z, G (z + 1) = G z + 1
  G_upper : ∃ Y₀ C : ℝ, AnalyticOnNhd ℂ G {z | Y₀ < z.im} ∧
    ∀ z : ℂ, Y₀ < z.im → ‖G z - z‖ ≤ C / (z.im - Y₀)
  /-- Height of the horn gate and the anchor phase `α`. -/
  hornHeight : ℝ
  hornPhase : ℂ
  /-- The horn baseline `Bₙ = ĝₙ · e^{2πinα}`. -/
  B : ℕ → ℂ
  B_eq : ∀ n, B n = gateCoefficient G hornHeight n * cexp (2 * π * I * n * hornPhase)
  /-- Parabolic transition `T₀` at `s = 0` and the explicit first-order correction `D`. -/
  T₀ : ℂ → ℂ
  D : ℂ → ℂ
  mode_nonzero_iff : ∀ n : ℕ, 1 ≤ n → (gateCoefficient T₀ 0 n ≠ 0 ↔ B n ≠ 0)
  /-- The explicit first coefficient `κₙ = dₙ/(2tₙ) - π i n d₀`. -/
  κ : ℕ → ℂ
  κ_eq : ∀ n : ℕ, κ n = correctionCoefficient D 0 n / (2 * gateCoefficient T₀ 0 n) -
    π * I * n * correctionCoefficient D 0 0
  /-- First order: `log(τₙ/Λⁿ/Bₙ) = κₙ p + O(|p|²)`. -/
  first_order : ∀ n : ℕ, 1 ≤ n → B n ≠ 0 → ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s : ℝ in 𝓝[>] 0,
    ‖log (τ s n / (Λ s : ℂ) ^ n / B n) - κ n * p s‖ ≤ C * ‖p s‖ ^ 2
  /-- All orders, with one coherent coefficient sequence `α` and `α 1 = κₙ`. -/
  all_orders : ∀ n : ℕ, 1 ≤ n → B n ≠ 0 → ∃ α : ℕ → ℂ, α 0 = 0 ∧ α 1 = κ n ∧
    ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s : ℝ in 𝓝[>] 0,
      ‖log (τ s n / (Λ s : ℂ) ^ n / B n) - ∑ j ∈ Finset.range (m + 1), α j * p s ^ j‖ ≤
        C * ‖p s‖ ^ (m + 1)
  /-- Provenance: every readable object above is the corresponding object of the
  low-level construction certified by `GluedResultData`. -/
  realized : ∃ (U H A₁ A₂ : ℂ → ℂ) (Kp : ℂ → ℂ → ℂ) (Fp : ℂ × ℂ → ℂ)
      (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
      (R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ : ℝ) (N M M₀ : ℕ) (Vold V : ℝ → ℂ → ℂ) (r : ℂ → ℂ)
      (W : ℝ → Kneser.ActualSewnAllOrders.Fiber) (S : ℝ → ℂ → ℂ),
    Kneser.GluedOriginalResult.GluedResultData U H A₁ A₂ Kp Fp e Γ
      R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ N M M₀ Vold V p r G W J S ∧
    (∀ s, K s = Kneser.GluedOriginalResult.gluedOriginal A₁ A₂ e Γ Y P₀ s (W s) (S s)) ∧
    (∀ s, domain s = Kneser.ActualGluedPhysicalSewing.gluedDomain A₁ A₂ e Γ Y P₀ s (W s)) ∧
    (∀ s, L₁ s = Real.exp 1 * (1 + (W s).left) ∧ L₂ s = Real.exp 1 * (1 + (W s).right)) ∧
    (∀ s, Λ s = Kneser.ActualSewnAllOrders.scale W s) ∧
    T₀ = Kneser.ActualAllOrderUpperHornBaseline.actualTransition U H A₁ A₂ e Γ N M Yg V 0 ∧
    D = Kneser.ActualRealNormalizedFirstCoefficient.physicalCorrection U H A₁ A₂ e Γ N M Yg V ∧
    hornHeight = (Kneser.CanonicalUpperHornCharts.imageCenter Rₛ Yg).im ∧
    hornPhase = Kneser.CanonicalBasinExtension.globalAttracting Rₛ
      Kneser.RealNormalizationAnchor.normalizationAnchor

/-! ## Proof: the readable family is the actual construction -/

section Proofs

open Kneser.GluedOriginalResult Kneser.ActualBaseTetration Kneser.ActualGluedPhysicalSewing
open Kneser.ActualSewnAllOrders Kneser.ActualPhysicalSewnCoefficients
open Kneser.ActualAllOrderUpperHornBaseline Kneser.GateFourierDerivative
open Kneser.AllOrderParameterExpansion Kneser.CanonicalUpperHornCharts
open Kneser.CanonicalBasinExtension Kneser.RealNormalizationAnchor

theorem tetrationBase_eq_base (s : ℝ) : tetrationBase s = base s := rfl

theorem cpow_tetrationBase (s : ℝ) (x : ℂ) :
    (tetrationBase s : ℂ) ^ x = originalExponential s x := by
  have hb : (tetrationBase s : ℂ) ≠ 0 := by exact_mod_cast (base_pos s).ne'
  rw [cpow_def_of_ne_zero hb, originalExponential, ofReal_log (base_pos s).le]
  rfl

theorem fixedPointMultiplier_original (s a : ℝ) :
    fixedPointMultiplier s (Real.exp 1 * (1 + a)) = Kneser.PositiveKoenigsOrbit.multiplier s a := by
  unfold fixedPointMultiplier Kneser.PositiveKoenigsOrbit.multiplier
  rw [tetrationBase_eq_base, log_base]
  field_simp

theorem koenigsAbelLift_original (s a : ℝ) :
    koenigsAbelLift s (Real.exp 1 * (1 + a)) = originalAbelLift s a := by
  unfold koenigsAbelLift
  rw [mul_div_cancel_left₀ _ (Real.exp_ne_zero 1), add_sub_cancel_left]

theorem gateCoefficient_eq (T : ℂ → ℂ) (y : ℝ) (n : ℤ) :
    gateCoefficient T y n = gateFourierCoefficient n y T := rfl

theorem correctionCoefficient_eq (D : ℂ → ℂ) (y : ℝ) (n : ℤ) :
    correctionCoefficient D y n = gateCorrectionCoefficient n y D := rfl

theorem periodLineCoefficient_glued (A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (Y P₀ s : ℝ) (w : Fiber) (S : ℂ → ℂ) (J : ℕ) (n : ℤ) :
    gluedOriginalCoefficient A B e Γ Y P₀ s w S J n =
      periodLineCoefficient (koenigsAbelLift s (Real.exp 1 * (1 + w.left)))
        (gluedOriginal A B e Γ Y P₀ s w S) J n := by
  rw [koenigsAbelLift_original]
  rfl

/-- The project's construction yields a `SewnTetrationFamily`. -/
theorem exists_sewnTetrationFamily : Nonempty SewnTetrationFamily := by
  obtain ⟨U,H,A₁,A₂,Kp,Fp,e,Γ,R,Rₛ,Y₁,Y₀,Mh,Ch,Yg,Y,η,Mg,P₀,N,M,M₀,Vold,V,p,r,G,W,J,S,hd⟩ :=
    exists_actual_glued_original_result
  have hall := hd.physical_coefficients.all_orders
  have hbase := hall.baseline
  let T := actualTransition U H A₁ A₂ e Γ N M Yg V
  let y := (imageCenter Rₛ Yg).im
  let α := globalAttracting Rₛ normalizationAnchor
  let K : ℝ → ℂ → ℂ := fun s => gluedOriginal A₁ A₂ e Γ Y P₀ s (W s) (S s)
  let dom : ℝ → Set ℂ := fun s => gluedDomain A₁ A₂ e Γ Y P₀ s (W s)
  let L₁ : ℝ → ℝ := fun s => Real.exp 1 * (1 + (W s).left)
  let L₂ : ℝ → ℝ := fun s => Real.exp 1 * (1 + (W s).right)
  let τ : ℝ → ℤ → ℂ := fun s n => gluedOriginalCoefficient A₁ A₂ e Γ Y P₀ s (W s) (S s) (J s) n
  let Bc : ℕ → ℂ := fun n => gateCoefficient G y n * cexp (2 * π * I * n * α)
  let κ : ℕ → ℂ := fun n => physicalKappa U H A₁ A₂ e Γ N M Yg V n
  have hev : ∀ᶠ s : ℝ in 𝓝[>] 0, s < 1 ∧
      GluedBaseFiberData A₁ A₂ e Γ Y P₀ s (W s) (S s) ∧
      FiberData A₁ A₂ e Γ T Y η Mg P₀ s (W s) ∧
      (p s = (-Real.log (Kneser.PositiveKoenigsOrbit.multiplier s (W s).left) *
        Real.log (Kneser.PositiveKoenigsOrbit.multiplier s (W s).right) : ℝ)) ∧
      ∀ x ∈ Icc (0:ℝ) 1, (J s : ℂ) + x ∈ dom s := by
    have hlt : ∀ᶠ s : ℝ in 𝓝[>] 0, s < 1 :=
      (eventually_lt_nhds (by norm_num : (0:ℝ) < 1)).filter_mono nhdsWithin_le_nhds
    filter_upwards [hlt, hd.glued, hall.actual_fibers,
      Kneser.MainResult.actual_sewn_multiplier_parameter U H A₁ A₂ Kp Fp e Γ
        R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ N M M₀ Vold V p r G W hall,
      hd.actual_line] with s h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, fun x hx => (h5 x hx).1⟩
  obtain ⟨s₀, hs₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  have hP : ∀ s ∈ Ioo 0 s₀, _ := fun s hs => hsub hs
  -- the normalized coefficient at positive parameters and at zero
  have hpos : ∀ n : ℕ, ∀ s : ℝ, s ≠ 0 →
      normalizedGluedCoefficient A₁ A₂ e Γ T Y P₀ W S J n s = τ s n / (scale W s : ℂ) ^ n := by
    intro n s hs
    simp only [normalizedGluedCoefficient, hs, ite_false, τ]
  have hzero : ∀ n : ℕ, 1 ≤ n → normalizedGluedCoefficient A₁ A₂ e Γ T Y P₀ W S J n 0 = Bc n := by
    intro n hn
    rw [hd.canonical_baseline n hn]
    simp only [Bc, gateCoefficient_eq, Kneser.fourierFrequency, Int.cast_natCast, y, α]
  have hBc : ∀ n : ℕ, 1 ≤ n → (Bc n ≠ 0 ↔ gateFourierCoefficient n y G ≠ 0) := by
    intro n _
    simp only [Bc, gateCoefficient_eq, ne_eq, mul_eq_zero, Complex.exp_ne_zero, or_false]
  have hgt : ∀ᶠ s : ℝ in 𝓝[>] 0, s ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact ne_of_gt hs
  refine ⟨{
    s₀ := s₀
    s₀_pos := hs₀
    base_range := fun s hs => base_subcritical s hs.1 (hP s hs).1
    L₁ := L₁
    L₂ := L₂
    fixed_points := ?_
    p := p
    p_analytic := hbase.parameter_analytic
    p_zero := hbase.parameter_zero
    p_deriv := hbase.parameter_derivative
    p_eq := ?_
    domain := dom
    K := K
    domain_open := fun s hs => (hP s hs).2.1.domain_open
    zero_mem := fun s hs => (hP s hs).2.1.zero_mem
    holomorphic := fun s hs => (hP s hs).2.1.analytic
    K_zero := fun s hs => (hP s hs).2.1.normalized
    K_succ := ?_
    J := J
    period_line := fun s hs => (hP s hs).2.2.2.2
    τ := τ
    τ_eq := fun s n => periodLineCoefficient_glued A₁ A₂ e Γ Y P₀ s (W s) (S s) (J s) n
    Λ := scale W
    Λ_eq := ?_
    Λ_flat := hall.flat
    G := G
    G_periodic := hbase.global_translation
    G_upper := ?_
    hornHeight := y
    hornPhase := α
    B := Bc
    B_eq := fun n => rfl
    T₀ := T 0
    D := Kneser.ActualRealNormalizedFirstCoefficient.physicalCorrection U H A₁ A₂ e Γ N M Yg V
    mode_nonzero_iff := ?_
    κ := κ
    κ_eq := ?_
    first_order := ?_
    all_orders := ?_
    realized := ⟨U,H,A₁,A₂,Kp,Fp,e,Γ,R,Rₛ,Y₁,Y₀,Mh,Ch,Yg,Y,η,Mg,P₀,N,M,M₀,Vold,V,r,W,S,
      hd, fun s => rfl, fun s => rfl, fun s => ⟨rfl, rfl⟩, fun s => rfl, rfl, rfl, rfl, rfl⟩ }⟩
  · -- fixed points
    intro s hs
    have hc := (hP s hs).2.2.1.control
    have he := Real.exp_pos 1
    refine ⟨?_, ?_, ?_, ?_⟩
    · show Real.exp 1 * (1 + (W s).left) < Real.exp 1
      nlinarith [hc.left_neg]
    · show Real.exp 1 < Real.exp 1 * (1 + (W s).right)
      nlinarith [hc.right_pos]
    · rw [cpow_tetrationBase]
      have h := actual_affine_conjugacy s (W s).left
      rw [hc.left_fixed] at h
      have hL : ((L₁ s : ℝ) : ℂ) = originalCoordinate ((W s).left : ℂ) := by
        simp only [L₁, originalCoordinate]
        push_cast
        ring
      rw [hL]
      exact h.symm
    · rw [cpow_tetrationBase]
      have h := actual_affine_conjugacy s (W s).right
      rw [hc.right_fixed] at h
      have hL : ((L₂ s : ℝ) : ℂ) = originalCoordinate ((W s).right : ℂ) := by
        simp only [L₂, originalCoordinate]
        push_cast
        ring
      rw [hL]
      exact h.symm
  · -- multiplier parameter
    intro s hs
    rw [(hP s hs).2.2.2.1]
    simp only [L₁, L₂, fixedPointMultiplier_original]
  · -- tetration equation
    intro s hs z hz
    obtain ⟨hz1, hK⟩ := (hP s hs).2.1.tetration z hz
    exact ⟨hz1, by rw [cpow_tetrationBase]; exact hK⟩
  · -- sewing scale
    intro s hs
    have hf := (hP s hs).2.2.1
    show Kneser.FourierSewing.lambda (Kneser.GrowingBandGeometry.height (W s).theta) = _
    rw [hf.actual_scale]
    simp only [L₁, fixedPointMultiplier_original, Kneser.ActualLambdaFlatness.lambdaFactor,
      Kneser.ActualLambdaFlatness.attractingMultiplier, Kneser.PositiveKoenigsOrbit.multiplier]
  · -- canonical horn bounds
    refine ⟨Y₀ + Mh + 18, Ch, ?_, ?_⟩
    · exact hbase.global_analytic.mono (fun z (hz : Y₀ + Mh + 18 < z.im) =>
        show Y₀ + Mh + 2 < z.im by linarith)
    · intro z hz
      have h17 := hbase.height
      have hM := hbase.margin_nonneg
      have hC := hbase.bound_nonneg
      refine (hbase.global_bound z hz).trans ?_
      have h1 : 0 < z.im - (Y₀ + Mh + 18) := by linarith
      have h2 : z.im - (Y₀ + Mh + 18) ≤ z.im - Mh - 17 := by linarith
      exact div_le_div_of_nonneg_left hC h1 h2
  · -- nonzero modes
    intro n hn
    rw [gateCoefficient_eq, hBc n hn]
    exact Kneser.MainResult.actual_nonzero_mode_iff_canonical U H A₁ A₂ Kp Fp e Γ
      R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ N M M₀ Vold V p r G W hall n hn
  · -- explicit first coefficient
    intro n
    simp only [κ, physicalKappa, Kneser.hornKappa, gateCoefficient_eq, correctionCoefficient_eq,
      Int.cast_natCast]
    rfl
  · -- first order
    intro n hn hB
    obtain ⟨C, hC, hb⟩ := hd.first_order n hn ((hBc n hn).1 hB)
    refine ⟨C, hC, ?_⟩
    filter_upwards [hb, hgt] with s hs hs0
    rwa [hpos n s hs0, hzero n hn] at hs
  · -- all orders
    intro n hn hB
    obtain ⟨a, ha0, ha1, hexp⟩ := hd.coefficients n hn ((hBc n hn).1 hB)
    refine ⟨a, ha0, ha1, fun m => ?_⟩
    obtain ⟨_, C, hC, hb⟩ := hexp m
    refine ⟨C, hC, ?_⟩
    filter_upwards [hb, hgt] with s hs hs0
    rw [hpos n s hs0, hzero n hn] at hs
    simpa only [Kneser.AllOrderGateFourier.scalarPolynomial, mul_comm] using hs

/-- **Main theorem (headline form).** There is a sewn tetration family: for every
small `s > 0` the glued function satisfies `K(0)=1` and `K(z+1)=b(s)^{K(z)}` on its
open domain, the multiplier parameter has `p(0)=0`, `p'(0)=2`, and every nonzero
horn mode obeys `log(τₙ(s)/Λ(s)ⁿ/Bₙ) = κₙ p(s) + O(|p(s)|²)`. -/
theorem exists_sewn_tetration :
    ∃ F : SewnTetrationFamily,
      (∀ s ∈ Ioo 0 F.s₀, F.K s 0 = 1 ∧
        ∀ z ∈ F.domain s, z + 1 ∈ F.domain s ∧ F.K s (z + 1) = (tetrationBase s : ℂ) ^ F.K s z) ∧
      F.p 0 = 0 ∧ HasDerivAt F.p 2 0 ∧
      ∀ n : ℕ, 1 ≤ n → F.B n ≠ 0 → ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s : ℝ in 𝓝[>] 0,
        ‖log (F.τ s n / (F.Λ s : ℂ) ^ n / F.B n) - F.κ n * F.p s‖ ≤ C * ‖F.p s‖ ^ 2 := by
  obtain ⟨F⟩ := exists_sewnTetrationFamily
  exact ⟨F, fun s hs => ⟨F.K_zero s hs, F.K_succ s hs⟩, F.p_zero, F.p_deriv, F.first_order⟩

/-- **Main theorem (all orders).** For the same kind of family, every nonzero horn mode
has one coherent coefficient sequence `α` with `α 1 = κₙ` and
`log(τₙ(s)/Λ(s)ⁿ/Bₙ) = Σ_{j=1}^m αⱼ p(s)ʲ + O(|p(s)|^{m+1})` for every finite `m`. -/
theorem exists_sewn_tetration_all_orders :
    ∃ F : SewnTetrationFamily, ∀ n : ℕ, 1 ≤ n → F.B n ≠ 0 →
      ∃ α : ℕ → ℂ, α 0 = 0 ∧ α 1 = F.κ n ∧ ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s : ℝ in 𝓝[>] 0,
        ‖log (F.τ s n / (F.Λ s : ℂ) ^ n / F.B n) - ∑ j ∈ Finset.range (m + 1), α j * F.p s ^ j‖ ≤
          C * ‖F.p s‖ ^ (m + 1) := by
  obtain ⟨F⟩ := exists_sewnTetrationFamily
  exact ⟨F, F.all_orders⟩

end Proofs

end Kneser.Interface
