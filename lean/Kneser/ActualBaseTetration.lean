import Kneser.ActualPhysicalSewnCoefficients

/-! The same physical sewing family in the paper's original variable.
The real base is exp((1-s)/e), the original map is its actual complex
exponential, and x=e(1+u) is the proved affine conjugacy. The open
physical domain is retained, while normalization, tetration and true
normalized Koenigs Fourier integrals are transported exactly. -/

set_option autoImplicit false
noncomputable section
namespace Kneser.ActualBaseTetration

open Filter Set Metric Complex
open Kneser.ActualSewnAllOrders Kneser.ActualFiberKoenigsUniformization
open Kneser.ActualPhysicalSewnCoefficients Kneser.ActualRegularTimeLift
open Kneser.PositiveKoenigsOrbit Kneser.ExponentialUnfolding
open Kneser.GateFourierDerivative Kneser.RealNormalizationAnchor
open Kneser.CommonQuadraticBaseline Kneser.ActualAllOrderUpperHornBaseline
open Kneser.AllOrderParameterExpansion
open scoped Topology Interval

def base (s : ℝ) : ℝ := Real.exp ((1-s)/Real.exp 1)

def originalExponential (s : ℝ) (x : ℂ) : ℂ :=
  Complex.exp ((Real.log (base s):ℂ)*x)

def originalCoordinate (u : ℂ) : ℂ := (Real.exp 1:ℂ)*(1+u)

def unfoldedCoordinate (x : ℂ) : ℂ := x/(Real.exp 1:ℂ)-1

theorem base_pos (s : ℝ) : 0<base s := Real.exp_pos _

theorem log_base (s : ℝ) : Real.log (base s)=(1-s)/Real.exp 1 := Real.log_exp _

theorem base_zero : base 0=Real.exp (1/Real.exp 1) := by simp only [base,sub_zero]

theorem base_subcritical (s : ℝ) (hs : 0<s) (hs1 : s<1) :
    1<base s ∧ base s<Real.exp (1/Real.exp 1) := by
  refine ⟨?_,?_⟩
  · simpa only [Real.exp_zero,base] using Real.exp_lt_exp.mpr
      (show 0<(1-s)/Real.exp 1 from div_pos (by linarith) (Real.exp_pos 1))
  · unfold base
    exact Real.exp_lt_exp.mpr (div_lt_div_of_pos_right (by linarith) (Real.exp_pos 1))

theorem affine_left_inverse (u : ℂ) : unfoldedCoordinate (originalCoordinate u)=u := by
  unfold unfoldedCoordinate originalCoordinate
  have he : (Real.exp 1:ℂ)≠0 := by exact_mod_cast ne_of_gt (Real.exp_pos 1)
  field_simp
  ring

theorem affine_right_inverse (x : ℂ) : originalCoordinate (unfoldedCoordinate x)=x := by
  unfold unfoldedCoordinate originalCoordinate
  have he : (Real.exp 1:ℂ)≠0 := by exact_mod_cast ne_of_gt (Real.exp_pos 1)
  field_simp
  ring

theorem original_anchor : originalCoordinate (realAnchor:ℂ)=1 := by
  unfold originalCoordinate realAnchor
  push_cast
  rw [show (1:ℂ)+(Complex.exp (-1)-1)=Complex.exp (-1) by ring,
    ←Complex.exp_add]
  norm_num

theorem actual_affine_conjugacy (s : ℝ) (u : ℂ) :
    originalCoordinate (unfolding s u)=originalExponential s (originalCoordinate u) := by
  unfold originalCoordinate originalExponential unfolding
  rw [log_base]
  push_cast
  rw [show (1:ℂ)+(Complex.exp (-(s:ℂ)+(1-(s:ℂ))*u)-1)=
    Complex.exp (-(s:ℂ)+(1-(s:ℂ))*u) by ring,←Complex.exp_add]
  congr 1
  field_simp [Complex.exp_ne_zero 1]
  ring

theorem actual_inverse_conjugacy (s : ℝ) (x : ℂ) :
    unfoldedCoordinate (originalExponential s x)=unfolding s (unfoldedCoordinate x) := by
  have hh := actual_affine_conjugacy s (unfoldedCoordinate x)
  rw [affine_right_inverse] at hh
  rw [←hh,affine_left_inverse]

def originalK (A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (Y P₀ s : ℝ) (w : Fiber) (z : ℂ) : ℂ :=
  originalCoordinate (physicalFunction A B e Γ Y P₀ s w z)

def originalKoenigs (s a : ℝ) (x : ℂ) : ℂ :=
  (Real.exp 1:ℂ)*koenigsValue s a (unfoldedCoordinate x)

def originalAbelLift (s a : ℝ) (x : ℂ) : ℂ :=
  log (originalKoenigs s a x/originalKoenigs s a 1)/(Real.log (multiplier s a):ℂ)

theorem original_koenigs_affine (s a : ℝ) (u : ℂ) :
    originalKoenigs s a (originalCoordinate u)=(Real.exp 1:ℂ)*koenigsValue s a u := by
  simp only [originalKoenigs,affine_left_inverse]

theorem original_koenigs_anchor (s a : ℝ) :
    originalKoenigs s a 1=(Real.exp 1:ℂ)*koenigsValue s a realAnchor := by
  rw [←original_anchor,original_koenigs_affine]

theorem original_lift_affine (s a : ℝ) (u : ℂ) :
    originalAbelLift s a (originalCoordinate u)=principalKoenigsLift s a realAnchor u := by
  have he : (Real.exp 1:ℂ)≠0 := by exact_mod_cast ne_of_gt (Real.exp_pos 1)
  unfold originalAbelLift principalKoenigsLift
  rw [original_koenigs_affine,original_koenigs_anchor,mul_div_mul_left _ _ he]

structure BaseFiberData (A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (Y P₀ s : ℝ) (w : Fiber) : Prop where
  physical : PhysicalFiberData A B e Γ Y P₀ s w
  domain_open : IsOpen (physicalDomain A B e Γ Y P₀ s w)
  zero_mem : (0:ℂ)∈physicalDomain A B e Γ Y P₀ s w
  analytic : AnalyticOnNhd ℂ (originalK A B e Γ Y P₀ s w) (physicalDomain A B e Γ Y P₀ s w)
  normalized : originalK A B e Γ Y P₀ s w 0=1
  tetration : ∀z∈physicalDomain A B e Γ Y P₀ s w,
    z+1∈physicalDomain A B e Γ Y P₀ s w ∧
      originalK A B e Γ Y P₀ s w (z+1)=originalExponential s (originalK A B e Γ Y P₀ s w z)
  koenigs_identity : ∀z∈physicalDomain A B e Γ Y P₀ s w,
    originalKoenigs s w.left (originalK A B e Γ Y P₀ s w z)=originalKoenigs s w.left 1*
      exp ((Real.log (multiplier s w.left):ℂ)*actualSewnCoordinate A B e Γ Y P₀ s w z)
  abel_time_germ : ∀ᶠz : ℂ in 𝓝 0, z∈physicalDomain A B e Γ Y P₀ s w ∧
    originalAbelLift s w.left (originalK A B e Γ Y P₀ s w z)=actualSewnCoordinate A B e Γ Y P₀ s w z

theorem base_fiber_of_physical_data (A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (Y P₀ s : ℝ) (w : Fiber) (hd : PhysicalFiberData A B e Γ Y P₀ s w) :
    BaseFiberData A B e Γ Y P₀ s w := by
  refine ⟨hd,hd.domain_open,hd.zero_mem,?_,?_,?_,?_,?_⟩
  · intro z hz
    exact analyticAt_const.mul (analyticAt_const.add (hd.analytic z hz))
  · unfold originalK
    rw [hd.normalized]
    exact original_anchor
  · intro z hz
    obtain ⟨hz1,he⟩ := hd.abel z hz
    refine ⟨hz1,?_⟩
    unfold originalK
    rw [he,actual_affine_conjugacy]
  · intro z hz
    rw [originalK,original_koenigs_affine,original_koenigs_anchor,hd.time_identity z hz]
    ring
  · filter_upwards [hd.logarithmic_time_germ] with z hz
    refine ⟨hz.1,?_⟩
    exact (original_lift_affine s w.left _).trans hz.2

def originalCoefficient (A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (Y P₀ s : ℝ) (w : Fiber) (J : ℕ) (n : ℤ) : ℂ :=
  ∫x : ℝ in (0:ℝ)..1,
    (originalAbelLift s w.left (originalK A B e Γ Y P₀ s w ((J:ℂ)+(x:ℂ)))-((J:ℂ)+(x:ℂ)))*
      exp (-Kneser.fourierFrequency n*((J:ℂ)+(x:ℂ)))

theorem original_coefficient_eq_physical (A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (Y P₀ s : ℝ) (w : Fiber) (J : ℕ) (n : ℤ) :
    originalCoefficient A B e Γ Y P₀ s w J n=physicalCoefficient A B e Γ Y P₀ s w J n := by
  unfold originalCoefficient physicalCoefficient originalK
  simp only [original_lift_affine]

def normalizedOriginalCoefficient (A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (T : ℝ → ℂ → ℂ) (Y P₀ : ℝ) (W : ℝ → Fiber) (J : ℝ → ℕ) (n : ℕ) (s : ℝ) : ℂ :=
  if s=0 then localHorn T n 0 else
    originalCoefficient A B e Γ Y P₀ s (W s) (J s) n/(scale W s:ℂ)^n

theorem normalized_original_eq_physical (A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (T : ℝ → ℂ → ℂ) (Y P₀ : ℝ) (W : ℝ → Fiber) (J : ℝ → ℕ) (n : ℕ) :
    normalizedOriginalCoefficient A B e Γ T Y P₀ W J n=
      normalizedPhysicalCoefficient A B e Γ T Y P₀ W J n := by
  funext s
  simp only [normalizedOriginalCoefficient,normalizedPhysicalCoefficient,original_coefficient_eq_physical]

theorem original_period_line_of_data (A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (Y P₀ s : ℝ) (w : Fiber) (J : ℕ) (hd : PeriodLineData A B e Γ Y P₀ s w J) :
    (∀x∈Icc (0:ℝ) 1, (J:ℂ)+(x:ℂ)∈physicalDomain A B e Γ Y P₀ s w ∧
      originalAbelLift s w.left (originalK A B e Γ Y P₀ s w ((J:ℂ)+(x:ℂ)))=
        actualSewnCoordinate A B e Γ Y P₀ s w ((J:ℂ)+(x:ℂ))) ∧
    ∀n : ℤ, originalCoefficient A B e Γ Y P₀ s w J n=
      gateFourierCoefficient n 0 (actualSewnCoordinate A B e Γ Y P₀ s w) := by
  refine ⟨?_,?_⟩
  · intro x hx
    exact ⟨hd.actual_domain x hx,(original_lift_affine s w.left _).trans (hd.exact_lift x hx)⟩
  · intro n
    exact (original_coefficient_eq_physical A B e Γ Y P₀ s w J n).trans (hd.coefficient n)

theorem base_family_of_physical_coefficients
    (U H A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F : ℂ × ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ : ℝ) (N M M₀ : ℕ)
    (Vold V : ℝ → ℂ → ℂ) (p r G : ℂ → ℂ) (W : ℝ → Fiber) (J : ℝ → ℕ)
    (hd : PhysicalCoefficientsData U H A B K F e Γ R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ N M M₀ Vold V p r G W J) :
    (∀ᶠs : ℝ in 𝓝[>] 0, BaseFiberData A B e Γ Y P₀ s (W s)) ∧
    (∀ᶠs : ℝ in 𝓝[>] 0, ∀n : ℤ,
      originalCoefficient A B e Γ Y P₀ s (W s) (J s) n=
        gateFourierCoefficient n 0 (actualSewnCoordinate A B e Γ Y P₀ s (W s))) ∧
    ∀n : ℕ, normalizedOriginalCoefficient A B e Γ (actualTransition U H A B e Γ N M Yg V) Y P₀ W J n=
      normalizedPhysicalCoefficient A B e Γ (actualTransition U H A B e Γ N M Yg V) Y P₀ W J n := by
  refine ⟨hd.physical.mono (fun s hs => base_fiber_of_physical_data A B e Γ Y P₀ s (W s) hs),?_,?_⟩
  · filter_upwards [hd.actual_line] with s hs
    exact (original_period_line_of_data A B e Γ Y P₀ s (W s) (J s) hs).2
  · intro n
    exact normalized_original_eq_physical A B e Γ _ Y P₀ W J n

end Kneser.ActualBaseTetration
end
