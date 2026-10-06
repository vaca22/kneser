import Kneser.HolomorphicInjectiveInverse
import Mathlib.Analysis.SpecificLimits.Normed

/-! An entire Poincare continuation constructed from a genuine local
inverse linearizing chart. Every value is a finite true iterate, and
independence of the finite entry index is proved from the local equation.
No continuation function or global functional equation is assumed. -/

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace Kneser.PoincareEntireExtension
open Filter Set Metric Complex
open scoped Topology

def term (f H : ℂ → ℂ) (μ : ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  (f^[N]) (H ((μ:ℂ)^N*z))

theorem scaled_mem_ball (μ r : ℝ) (hμ : 0≤μ) (hμ1 : μ≤1)
    (z : ℂ) (hz : z∈ball 0 r) : (μ:ℂ)*z∈ball 0 r := by
  rw [mem_ball_zero_iff] at hz ⊢
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hμ]
  exact (mul_le_of_le_one_left (norm_nonneg _) hμ1).trans_lt hz

theorem exists_entry (μ r : ℝ) (hμ : 0≤μ) (hμ1 : μ<1) (hr : 0<r) (z : ℂ) :
    ∃ N : ℕ, (μ:ℂ)^N*z∈ball 0 r := by
  have hm : ‖(μ:ℂ)‖<1 := by simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hμ] using hμ1
  have ht := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hm).mul_const z
  have he : ∀ᶠ N : ℕ in atTop, (μ:ℂ)^N*z∈ball 0 r := by
    have ht' : Tendsto (fun N : ℕ => (μ:ℂ)^N*z) atTop (𝓝 (0:ℂ)) := by
      simpa only [zero_mul] using ht
    exact ht'.eventually (ball_mem_nhds (0:ℂ) hr)
  exact he.exists

theorem term_succ (f H : ℂ → ℂ) (μ r : ℝ)
    (heq : ∀ z∈ball 0 r, f (H ((μ:ℂ)*z))=H z)
    (N : ℕ) (z : ℂ) (hz : (μ:ℂ)^N*z∈ball 0 r) :
    term f H μ (N+1) z=term f H μ N z := by
  unfold term
  rw [Function.iterate_succ_apply]
  have hid : (μ:ℂ)^(N+1)*z=(μ:ℂ)*((μ:ℂ)^N*z) := by rw [pow_succ]; ring
  rw [hid,heq _ hz]

theorem term_add (f H : ℂ → ℂ) (μ r : ℝ) (hμ : 0≤μ) (hμ1 : μ≤1)
    (heq : ∀ z∈ball 0 r, f (H ((μ:ℂ)*z))=H z)
    (N : ℕ) (z : ℂ) (hz : (μ:ℂ)^N*z∈ball 0 r) (k : ℕ) :
    (μ:ℂ)^(N+k)*z∈ball 0 r ∧ term f H μ (N+k) z=term f H μ N z := by
  induction k with
  | zero => simpa only [add_zero] using And.intro hz (rfl : term f H μ N z=term f H μ N z)
  | succ k ih =>
    have hm : (μ:ℂ)^(N+(k+1))*z∈ball 0 r := by
      have hh := scaled_mem_ball μ r hμ hμ1 _ ih.1
      convert hh using 1
      rw [Nat.add_succ,pow_succ]
      ring
    refine ⟨hm,?_⟩
    rw [Nat.add_succ,term_succ f H μ r heq (N+k) z ih.1,ih.2]

theorem term_eq_of_entries (f H : ℂ → ℂ) (μ r : ℝ) (hμ : 0≤μ) (hμ1 : μ≤1)
    (heq : ∀ z∈ball 0 r, f (H ((μ:ℂ)*z))=H z)
    (N M : ℕ) (z : ℂ) (hN : (μ:ℂ)^N*z∈ball 0 r) (hM : (μ:ℂ)^M*z∈ball 0 r) :
    term f H μ N z=term f H μ M z := by
  rcases le_total N M with h | h
  · obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le h
    exact (term_add f H μ r hμ hμ1 heq N z hN k).2.symm
  · obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le h
    exact (term_add f H μ r hμ hμ1 heq M z hM k).2

/-- The index is chosen only after its actual finite-entry property has
been proved. Invalid inputs have an explicit default and are unused. -/
def entryIndex (μ r : ℝ) (z : ℂ) : ℕ := by
  classical
  exact if h : ∃ N : ℕ, (μ:ℂ)^N*z∈ball 0 r then Classical.choose h else 0

def entire (f H : ℂ → ℂ) (μ r : ℝ) (z : ℂ) : ℂ :=
  term f H μ (entryIndex μ r z) z

theorem entryIndex_spec (μ r : ℝ) (hμ : 0≤μ) (hμ1 : μ<1) (hr : 0<r) (z : ℂ) :
    (μ:ℂ)^(entryIndex μ r z)*z∈ball 0 r := by
  classical
  have h := exists_entry μ r hμ hμ1 hr z
  simp only [entryIndex,dite_eq_left h]
  exact Classical.choose_spec h

theorem entire_eq_term (f H : ℂ → ℂ) (μ r : ℝ) (hμ : 0≤μ) (hμ1 : μ<1) (hr : 0<r)
    (heq : ∀ z∈ball 0 r, f (H ((μ:ℂ)*z))=H z)
    (N : ℕ) (z : ℂ) (hN : (μ:ℂ)^N*z∈ball 0 r) :
    entire f H μ r z=term f H μ N z := by
  exact term_eq_of_entries f H μ r hμ hμ1.le heq _ N z (entryIndex_spec μ r hμ hμ1 hr z) hN

theorem entire_eq_local (f H : ℂ → ℂ) (μ r : ℝ) (hμ : 0≤μ) (hμ1 : μ<1) (hr : 0<r)
    (heq : ∀ z∈ball 0 r, f (H ((μ:ℂ)*z))=H z) :
    EqOn (entire f H μ r) H (ball 0 r) := by
  intro z hz
  simpa only [term,pow_zero,one_mul,Function.iterate_zero,id_eq] using
    entire_eq_term f H μ r hμ hμ1 hr heq 0 z (by simpa only [pow_zero,one_mul] using hz)

theorem analyticAt_iterate (f : ℂ → ℂ) (hf : ∀ z, AnalyticAt ℂ f z) (N : ℕ) (z : ℂ) :
    AnalyticAt ℂ (f^[N]) z := by
  induction N with
  | zero => simpa only [Function.iterate_zero] using (analyticAt_id : AnalyticAt ℂ id z)
  | succ N ih =>
    have hh : AnalyticAt ℂ (fun w => f ((f^[N]) w)) z := (hf _).comp ih
    simpa only [←Function.iterate_succ_apply'] using hh

theorem entire_analytic (f H : ℂ → ℂ) (μ r : ℝ) (hμ : 0≤μ) (hμ1 : μ<1) (hr : 0<r)
    (hf : ∀ z, AnalyticAt ℂ f z) (hH : AnalyticOnNhd ℂ H (ball 0 r))
    (heq : ∀ z∈ball 0 r, f (H ((μ:ℂ)*z))=H z) :
    ∀ z, AnalyticAt ℂ (entire f H μ r) z := by
  intro z
  obtain ⟨N,hN⟩ := exists_entry μ r hμ hμ1 hr z
  have hscale : AnalyticAt ℂ (fun w : ℂ => (μ:ℂ)^N*w) z := analyticAt_const.mul analyticAt_id
  have hterm : AnalyticAt ℂ (term f H μ N) z :=
    (analyticAt_iterate f hf N _).comp ((hH _ hN).comp hscale)
  have hn : ∀ᶠ w : ℂ in 𝓝 z, (μ:ℂ)^N*w∈ball 0 r :=
    hscale.continuousAt.eventually (isOpen_ball.mem_nhds hN)
  exact hterm.congr (hn.mono fun w hw => (entire_eq_term f H μ r hμ hμ1 hr heq N w hw).symm)

theorem entire_functional_eq (f H : ℂ → ℂ) (μ r : ℝ) (hμ : 0<μ) (hμ1 : μ<1) (hr : 0<r)
    (heq : ∀ z∈ball 0 r, f (H ((μ:ℂ)*z))=H z) (z : ℂ) :
    entire f H μ r (z/(μ:ℂ))=f (entire f H μ r z) := by
  obtain ⟨N,hN⟩ := exists_entry μ r hμ.le hμ1 hr z
  have hμc : (μ:ℂ)≠0 := by exact_mod_cast ne_of_gt hμ
  have he : (μ:ℂ)^(N+1)*(z/(μ:ℂ))=(μ:ℂ)^N*z := by
    rw [pow_succ]
    field_simp
  have hNe : (μ:ℂ)^(N+1)*(z/(μ:ℂ))∈ball 0 r := by rwa [he]
  rw [entire_eq_term f H μ r hμ.le hμ1 hr heq (N+1) _ hNe,
    entire_eq_term f H μ r hμ.le hμ1 hr heq N _ hN]
  unfold term
  rw [he,Function.iterate_succ_apply']

theorem exists_entire_extension (f H : ℂ → ℂ) (μ r : ℝ) (hμ : 0<μ) (hμ1 : μ<1) (hr : 0<r)
    (hf : ∀ z, AnalyticAt ℂ f z) (hH : AnalyticOnNhd ℂ H (ball 0 r))
    (heq : ∀ z∈ball 0 r, f (H ((μ:ℂ)*z))=H z) :
    ∃ F : ℂ → ℂ, (∀ z, AnalyticAt ℂ F z) ∧ EqOn F H (ball 0 r) ∧
      ∀ z, F (z/(μ:ℂ))=f (F z) := by
  exact ⟨entire f H μ r,entire_analytic f H μ r hμ.le hμ1 hr hf hH heq,
    entire_eq_local f H μ r hμ.le hμ1 hr heq,entire_functional_eq f H μ r hμ hμ1 hr heq⟩

end Kneser.PoincareEntireExtension
end
