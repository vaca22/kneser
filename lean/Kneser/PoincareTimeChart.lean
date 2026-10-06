import Kneser.PoincareEntireExtension

/-! Entire exponential-time charts of a constructed Poincare function.
The unit Abel equation and the actual logarithmic imaginary period are
derived from its scaling equation. -/
set_option autoImplicit false
noncomputable section
namespace Kneser.PoincareTimeChart
open Filter Set Complex
open Kneser.PoincareEntireExtension
open scoped Topology

def chart (F : ℂ → ℂ) (μ : ℝ) (c w : ℂ) : ℂ :=
  F (c*exp (-(Real.log μ:ℂ)*w))

def imaginaryPeriod (μ : ℝ) : ℂ :=
  (2*(Real.pi:ℂ)*I)/(-(Real.log μ:ℂ))

theorem chart_analytic (F : ℂ → ℂ) (μ : ℝ) (c : ℂ)
    (hF : ∀ z, AnalyticAt ℂ F z) : ∀ w, AnalyticAt ℂ (chart F μ c) w := by
  intro w
  exact (hF _).comp (analyticAt_const.mul ((analyticAt_const.mul analyticAt_id).cexp))

theorem chart_abel (F f : ℂ → ℂ) (μ : ℝ) (hμ : 0<μ) (c : ℂ)
    (heq : ∀ z, F (z/(μ:ℂ))=f (F z)) (w : ℂ) :
    chart F μ c (w+1)=f (chart F μ c w) := by
  have hexp : exp (-(Real.log μ:ℂ))=(μ:ℂ)⁻¹ := by
    rw [exp_neg,←ofReal_exp,Real.exp_log hμ]
  have hid : -(Real.log μ:ℂ)*(w+1)=(-(Real.log μ:ℂ)*w)+(-(Real.log μ:ℂ)) := by ring
  unfold chart
  rw [hid,exp_add,hexp]
  rw [show c*(exp (-(Real.log μ:ℂ)*w)*(μ:ℂ)⁻¹)=
      (c*exp (-(Real.log μ:ℂ)*w))/(μ:ℂ) by ring,heq]

theorem chart_periodic (F : ℂ → ℂ) (μ : ℝ) (hlog : Real.log μ≠0) (c w : ℂ) :
    chart F μ c (w+imaginaryPeriod μ)=chart F μ c w := by
  have hn : -(Real.log μ:ℂ)≠0 := neg_ne_zero.mpr (by exact_mod_cast hlog)
  have hid : -(Real.log μ:ℂ)*(w+imaginaryPeriod μ)=
      (-(Real.log μ:ℂ)*w)+2*(Real.pi:ℂ)*I := by
    unfold imaginaryPeriod
    field_simp [show (Real.log μ:ℂ)≠0 by exact_mod_cast hlog]
    <;> ring
  unfold chart
  rw [hid,exp_periodic]

theorem exists_entire_time_chart (f H : ℂ → ℂ) (μ r : ℝ)
    (hμ : 0<μ) (hμ1 : μ<1) (hr : 0<r) (c : ℂ)
    (hf : ∀ z, AnalyticAt ℂ f z) (hH : AnalyticOnNhd ℂ H (Metric.ball 0 r))
    (heq : ∀ z∈Metric.ball 0 r, f (H ((μ:ℂ)*z))=H z) :
    ∃ F S : ℂ → ℂ,
      (∀ z, AnalyticAt ℂ F z) ∧ EqOn F H (Metric.ball 0 r) ∧
      (∀ w, S w=F (c*exp (-(Real.log μ:ℂ)*w))) ∧
      (∀ w, AnalyticAt ℂ S w) ∧ (∀ w, S (w+1)=f (S w)) ∧
      ∀ w, S (w+imaginaryPeriod μ)=S w := by
  obtain ⟨F,hFa,hFl,hFe⟩ := exists_entire_extension f H μ r hμ hμ1 hr hf hH heq
  exact ⟨F,chart F μ c,hFa,hFl,fun _ => rfl,chart_analytic F μ c hFa,
    chart_abel F f μ hμ c hFe,chart_periodic F μ (ne_of_lt (Real.log_neg hμ hμ1)) c⟩

end Kneser.PoincareTimeChart
end
