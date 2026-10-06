import Kneser.FlatSewingLogTransfer

/-! Genuine normalized mode ratios preserve the coherent coefficient
sequence. The principal-logarithm identity is proved near the actual
limit one; it is not an unrestricted logarithm product rule. -/

set_option autoImplicit false
noncomputable section
namespace Kneser.ParameterModeRatios
open Filter Set Complex
open Kneser.AllOrderGateFourier Kneser.AllOrderParameterExpansion
open scoped Topology

theorem scalarPolynomial_sub_mul (a b : ℕ → ℂ) (c z : ℂ) (m : ℕ) :
    scalarPolynomial (fun j => a j-c*b j) m z =
      scalarPolynomial a m z-c*scalarPolynomial b m z := by
  simp only [scalarPolynomial,mul_sub,Finset.sum_sub_distrib,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem parameterExpansion_sub_mul (f g : ℝ → ℂ) (p : ℂ → ℂ)
    (a b : ℕ → ℂ) (c : ℂ) (m : ℕ)
    (hf : ParameterExpansion f p a m) (hg : ParameterExpansion g p b m) :
    ParameterExpansion (fun s => f s-c*g s) p (fun j => a j-c*b j) m := by
  obtain ⟨C,hC,he⟩ := hf.2
  obtain ⟨D,hD,hd⟩ := hg.2
  refine ⟨by change a 0-c*b 0=f 0-c*g 0; rw [hf.1,hg.1],C+‖c‖*D,by positivity,?_⟩
  filter_upwards [he,hd] with s hs ht
  rw [scalarPolynomial_sub_mul]
  have hid : f s-c*g s-(scalarPolynomial a m (p s)-c*scalarPolynomial b m (p s))=
      (f s-scalarPolynomial a m (p s))-c*(g s-scalarPolynomial b m (p s)) := by ring
  rw [hid]
  apply (norm_sub_le _ _).trans
  rw [norm_mul]
  exact (add_le_add hs (mul_le_mul_of_nonneg_left ht (norm_nonneg _))).trans_eq (by ring)

/-- Principal logarithms agree with the ratio logarithm on a genuine
neighborhood of the common limiting value one. -/
theorem eventually_log_div_pow (f g : ℝ → ℂ) (n : ℕ)
    (hf : Tendsto f (𝓝[>] 0) (𝓝 1)) (hg : Tendsto g (𝓝[>] 0) (𝓝 1)) :
    ∀ᶠ s : ℝ in 𝓝[>] 0,
      log (f s/(g s)^n)=log (f s)-(n:ℂ)*log (g s) := by
  have hfl : Tendsto (fun s => log (f s)) (𝓝[>] 0) (𝓝 0) := by
    convert (continuousAt_clog (x:=(1:ℂ)) one_mem_slitPlane).tendsto.comp hf using 1 <;>
      simp only [Function.comp_def,log_one]
  have hgl : Tendsto (fun s => log (g s)) (𝓝[>] 0) (𝓝 0) := by
    convert (continuousAt_clog (x:=(1:ℂ)) one_mem_slitPlane).tendsto.comp hg using 1 <;>
      simp only [Function.comp_def,log_one]
  have hd : Tendsto (fun s => log (f s)-(n:ℂ)*log (g s)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero,sub_zero] using hfl.sub (hgl.const_mul (n:ℂ))
  have hn : ∀ᶠ s : ℝ in 𝓝[>] 0,
      ‖log (f s)-(n:ℂ)*log (g s)‖<Real.pi :=
    hd.norm.eventually (gt_mem_nhds (by simpa only [norm_zero] using Real.pi_pos))
  filter_upwards [hn,hf.eventually_ne (by norm_num : (1:ℂ)≠0),
    hg.eventually_ne (by norm_num : (1:ℂ)≠0)] with s hs hfs hgs
  have hi := (abs_lt.mp ((abs_im_le_norm _).trans_lt hs))
  have he : exp (log (f s)-(n:ℂ)*log (g s))=f s/(g s)^n := by
    rw [exp_sub,exp_log hfs,exp_nat_mul,exp_log hgs]
  rw [←he]
  exact log_exp hi.1 hi.2.le

theorem all_orders_normalized_ratio (f g : ℝ → ℂ) (p : ℂ → ℂ)
    (a b : ℕ → ℂ) (n : ℕ) (hf0 : f 0≠0) (hg0 : g 0≠0)
    (hf : Tendsto f (𝓝[>] 0) (𝓝 (f 0)))
    (hg : Tendsto g (𝓝[>] 0) (𝓝 (g 0)))
    (ha : ∀ m, ParameterExpansion (fun s => log (f s/f 0)) p a m)
    (hb : ∀ m, ParameterExpansion (fun s => log (g s/g 0)) p b m) :
    ∀ m, ParameterExpansion
      (fun s => log ((f s/f 0)/(g s/g 0)^n)) p (fun j => a j-(n:ℂ)*b j) m := by
  have hfn : Tendsto (fun s => f s/f 0) (𝓝[>] 0) (𝓝 1) := by
    simpa only [div_self hf0] using hf.div_const (f 0)
  have hgn : Tendsto (fun s => g s/g 0) (𝓝[>] 0) (𝓝 1) := by
    simpa only [div_self hg0] using hg.div_const (g 0)
  have hid := eventually_log_div_pow _ _ n hfn hgn
  intro m
  obtain ⟨hzero,C,hC,he⟩ := parameterExpansion_sub_mul _ _ p a b (n:ℂ) m (ha m) (hb m)
  refine ⟨?_,C,hC,?_⟩
  · simpa only [div_self hf0,div_self hg0,one_pow,div_one,log_one,mul_zero,sub_zero] using hzero
  · filter_upwards [he,hid] with s hs hi
    simpa only [hi] using hs

end Kneser.ParameterModeRatios
end
