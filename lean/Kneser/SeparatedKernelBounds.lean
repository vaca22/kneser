import Kneser.SeparatedOrbitSums

/-!
Uniform rational and exponential residual budgets for a real orbit with
positive drift. Both bounds are independent of the initial real position.
The exponential cubic bound uses the actual small-scale regime theta ≤ 1.
-/

set_option autoImplicit false
noncomputable section
namespace Kneser.SeparatedKernelBounds

open Filter Set MeasureTheory Kneser.SeparatedOrbitSums
open scoped Topology BigOperators

def rationalMajorant (Y t : ℝ) : ℝ := (Y ^ 4)⁻¹ * (1 + (t / Y) ^ 2)⁻¹

theorem rationalMajorant_nonneg (Y t : ℝ) : 0 ≤ rationalMajorant Y t := by
  unfold rationalMajorant
  positivity

theorem rationalMajorant_antitone (Y : ℝ) (hY : 0 < Y) :
    AntitoneOn (rationalMajorant Y) (Ici 0) := by
  intro s hs t ht hst
  dsimp [rationalMajorant]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply inv_le_inv₀ (by positivity) (by positivity) |>.mpr
  have hdiv : s / Y ≤ t / Y := div_le_div_of_nonneg_right hst hY.le
  have hsdiv : 0 ≤ s / Y := div_nonneg hs hY.le
  nlinarith

theorem rational_kernel_le_majorant (Y t : ℝ) (hY : 0 < Y) :
    ((t ^ 2 + Y ^ 2) ^ 2)⁻¹ ≤ rationalMajorant Y t := by
  have hD : 0 < t ^ 2 + Y ^ 2 := by positivity
  have he : rationalMajorant Y t = (Y ^ 2 * (t ^ 2 + Y ^ 2))⁻¹ := by
    dsimp [rationalMajorant]
    field_simp
    ring
  rw [he]
  apply inv_le_inv₀ (by positivity) (by positivity) |>.mpr
  nlinarith [sq_nonneg t]

theorem sampled_majorant_integral (c Y : ℝ) (hc : 0 < c) (hY : 0 < Y) :
    IntegrableOn (fun t : ℝ => rationalMajorant Y (c * t)) (Ioi 0) ∧
      (∫ t : ℝ in Ioi 0, rationalMajorant Y (c * t)) = Real.pi / (2 * c * Y ^ 3) := by
  have hr : 0 < c / Y := div_pos hc hY
  have he (t : ℝ) : rationalMajorant Y (c * t) =
      (Y ^ 4)⁻¹ * (1 + ((c / Y) * t) ^ 2)⁻¹ := by
    dsimp [rationalMajorant]
    congr 2
    ring
  have hi : Integrable (fun t : ℝ => rationalMajorant Y (c * t)) := by
    simpa only [he] using (integrable_inv_one_add_mul_sq hr.ne').const_mul ((Y ^ 4)⁻¹)
  refine ⟨hi.integrableOn, ?_⟩
  simp_rw [he]
  rw [integral_const_mul, integral_comp_mul_left_Ioi (fun t : ℝ => (1 + t ^ 2)⁻¹) 0 hr]
  simp only [mul_zero, integral_Ioi_inv_one_add_sq, Real.arctan_zero, sub_zero, smul_eq_mul]
  field_simp <;> ring

theorem sampled_majorant_bound (c Y : ℝ) (hc : 0 < c) (hY : 1 ≤ Y) :
    Summable (fun k : ℕ => rationalMajorant Y (c * k)) ∧
      (∑' k : ℕ, rationalMajorant Y (c * k)) ≤ (1 + Real.pi / (2 * c)) / Y ^ 3 := by
  have hYpos : 0 < Y := by linarith
  have ha : AntitoneOn (fun t : ℝ => rationalMajorant Y (c * t)) (Ici 0) := by
    intro s hs t ht hst
    exact rationalMajorant_antitone Y hYpos (mul_nonneg hc.le hs) (mul_nonneg hc.le ht)
      (mul_le_mul_of_nonneg_left hst hc.le)
  have hn : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ rationalMajorant Y (c * t) :=
    fun t _ => rationalMajorant_nonneg Y (c * t)
  obtain ⟨hi, he⟩ := sampled_majorant_integral c Y hc hYpos
  refine ⟨ha.summable_of_integrableOn_Ioi_zero hi hn, ?_⟩
  have hh := ha.tsum_le_integral hi hn
  rw [he] at hh
  have hz : rationalMajorant Y (c * 0) = (Y ^ 4)⁻¹ := by simp [rationalMajorant]
  rw [hz] at hh
  have hp : (Y ^ 4)⁻¹ ≤ (Y ^ 3)⁻¹ := by
    apply inv_le_inv₀ (by positivity) (by positivity) |>.mpr
    nlinarith [mul_le_mul_of_nonneg_left hY (pow_nonneg hYpos.le 3)]
  calc
    _ ≤ (Y ^ 3)⁻¹ + Real.pi / (2 * c * Y ^ 3) := hh.trans (add_le_add hp le_rfl)
    _ = _ := by field_simp <;> ring

theorem rational_orbit_kernel_bound (x : ℕ → ℝ) (c Y : ℝ) (hc : 0 < c) (hY : 1 ≤ Y)
    (hstep : ∀ k, x k + c ≤ x (k + 1)) :
    Summable (fun k : ℕ => ((x k ^ 2 + Y ^ 2) ^ 2)⁻¹) ∧
      (∑' k : ℕ, ((x k ^ 2 + Y ^ 2) ^ 2)⁻¹) ≤ (2 + Real.pi / c) / Y ^ 3 := by
  have hYpos : 0 < Y := by linarith
  obtain ⟨hsample, hsample_bound⟩ := sampled_majorant_bound c Y hc hY
  obtain ⟨hsmajor, hmajor⟩ := sum_kernel_le_two_sampled x c hc (separation_of_step x c hstep)
    (rationalMajorant Y) (rationalMajorant_antitone Y hYpos)
    (fun t _ => rationalMajorant_nonneg Y t) hsample
  have hle : ∀ k : ℕ, ((x k ^ 2 + Y ^ 2) ^ 2)⁻¹ ≤ rationalMajorant Y |x k| := by
    intro k
    simpa only [sq_abs] using rational_kernel_le_majorant Y |x k| hYpos
  have hs : Summable (fun k : ℕ => ((x k ^ 2 + Y ^ 2) ^ 2)⁻¹) :=
    hsmajor.of_nonneg_of_le (fun k => by positivity) hle
  refine ⟨hs, ?_⟩
  calc
    _ ≤ ∑' k : ℕ, rationalMajorant Y |x k| := hs.tsum_le_tsum hle hsmajor
    _ ≤ 2 * ∑' k : ℕ, rationalMajorant Y (c * k) := hmajor
    _ ≤ 2 * ((1 + Real.pi / (2 * c)) / Y ^ 3) := mul_le_mul_of_nonneg_left hsample_bound (by norm_num)
    _ = _ := by field_simp <;> ring

theorem exponential_orbit_kernel_bound (x : ℕ → ℝ) (c θ : ℝ) (hc : 0 < c) (hθ : 0 < θ)
    (hstep : ∀ k, x k + c ≤ x (k + 1)) :
    Summable (fun k : ℕ => Real.exp (-2 * θ * |x k|)) ∧
      (∑' k : ℕ, Real.exp (-2 * θ * |x k|)) ≤ 2 / (1 - Real.exp (-2 * θ * c)) := by
  let f : ℝ → ℝ := fun t => Real.exp (-2 * θ * t)
  have hf : AntitoneOn f (Ici 0) := by
    intro s _ t _ hst
    apply Real.exp_le_exp.mpr
    nlinarith
  have hq : 0 ≤ Real.exp (-2 * θ * c) := (Real.exp_pos _).le
  have hqlt : Real.exp (-2 * θ * c) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith
  have he (k : ℕ) : f (c * k) = Real.exp (-2 * θ * c) ^ k := by
    rw [← Real.exp_nat_mul]
    dsimp [f]
    congr 1
    ring
  have hs : Summable (fun k : ℕ => f (c * k)) := by
    simpa only [he] using summable_geometric_of_lt_one hq hqlt
  obtain ⟨hsx, hx⟩ := sum_kernel_le_two_sampled x c hc (separation_of_step x c hstep)
    f hf (fun t _ => (Real.exp_pos _).le) hs
  refine ⟨hsx, ?_⟩
  simpa only [he, tsum_geometric_of_lt_one hq hqlt, div_eq_mul_inv] using hx

theorem exponential_cubic_orbit_bound (x : ℕ → ℝ) (c θ : ℝ)
    (hc : 0 < c) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hstep : ∀ k, x k + c ≤ x (k + 1)) :
    Summable (fun k : ℕ => θ ^ 4 * Real.exp (-2 * θ * |x k|)) ∧
      (∑' k : ℕ, θ ^ 4 * Real.exp (-2 * θ * |x k|)) ≤
        (Real.exp (2 * c) / c) * θ ^ 3 := by
  obtain ⟨hs, hb⟩ := exponential_orbit_kernel_bound x c θ hc hθ hstep
  let q : ℝ := Real.exp (-2 * θ * c)
  have hq : 0 < q := Real.exp_pos _
  have hqlt : q < 1 := by dsimp [q]; rw [Real.exp_lt_one_iff]; nlinarith
  have hden : 0 < 1 - q := by linarith
  have he : Real.exp (2 * θ * c) * q = 1 := by
    dsimp [q]
    rw [← Real.exp_add]
    have hz : 2 * θ * c + -2 * θ * c = 0 := by ring
    rw [hz, Real.exp_zero]
  have hmul := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (2 * θ * c)) hq.le
  rw [he] at hmul
  have hqlo : Real.exp (-2 * c) ≤ q := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hlo : 2 * θ * c * Real.exp (-2 * c) ≤ 1 - q := by
    have hm := mul_le_mul_of_nonneg_left hqlo (show 0 ≤ 2 * θ * c by positivity)
    nlinarith
  have hA : 0 ≤ (Real.exp (2 * c) / c) * θ ^ 3 := by positivity
  have hcancel : ((Real.exp (2 * c) / c) * θ ^ 3) *
      (2 * θ * c * Real.exp (-2 * c)) = 2 * θ ^ 4 := by
    rw [show -2 * c = -(2 * c) by ring, Real.exp_neg]
    field_simp <;> ring
  have hbound : θ ^ 4 * (2 / (1 - q)) ≤ (Real.exp (2 * c) / c) * θ ^ 3 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hden).mpr
    calc
      _ = ((Real.exp (2 * c) / c) * θ ^ 3) * (2 * θ * c * Real.exp (-2 * c)) := by
        rw [hcancel]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlo hA
  refine ⟨hs.mul_left (θ ^ 4), ?_⟩
  rw [tsum_mul_left]
  exact (mul_le_mul_of_nonneg_left hb (by positivity)).trans hbound

end Kneser.SeparatedKernelBounds
end
