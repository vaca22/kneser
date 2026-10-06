import Kneser.PositiveLocalKoenigs

/-! A normalized Koenigs germ constructed from the genuine iterates of
an analytic contraction with a proved quadratic remainder bound. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
namespace Kneser.QuadraticLocalKoenigs
open Set Metric Filter Complex
open scoped Topology BigOperators

def approximation (f : ℂ → ℂ) (c : ℂ) (μ : ℝ) (u : ℂ) (n : ℕ) : ℂ :=
  ((μ:ℂ)^n)⁻¹*((f^[n]) u-c)
def increment (f : ℂ → ℂ) (c : ℂ) (μ : ℝ) (u : ℂ) (n : ℕ) : ℂ :=
  approximation f c μ u (n+1)-approximation f c μ u n
def value (f : ℂ → ℂ) (c : ℂ) (μ : ℝ) (u : ℂ) : ℂ :=
  u-c+∑' n, increment f c μ u n

theorem approximation_increment (f : ℂ → ℂ) (c : ℂ) (μ : ℝ) (u : ℂ) (n : ℕ) (hμ : μ≠0) :
    increment f c μ u n=((μ:ℂ)^(n+1))⁻¹*
      ((f^[n+1]) u-c-(μ:ℂ)*((f^[n]) u-c)) := by
  have hmc : (μ:ℂ)≠0 := by exact_mod_cast hμ
  unfold increment approximation
  rw [pow_succ]
  field_simp

theorem approximation_partial_sum (f : ℂ → ℂ) (c : ℂ) (μ : ℝ) (u : ℂ) (n : ℕ) :
    approximation f c μ u n=u-c+∑ k∈Finset.range n,increment f c μ u k := by
  induction n with
  | zero => simp [approximation]
  | succ n ih => rw [Finset.sum_range_succ,←add_assoc,←ih]; unfold increment; ring

theorem tendsto_approximation (f : ℂ → ℂ) (c : ℂ) (μ : ℝ) (u : ℂ)
    (hs : Summable (fun n => ‖increment f c μ u n‖)) :
    Tendsto (approximation f c μ u) atTop (𝓝 (value f c μ u)) := by
  have ht : Tendsto (fun n : ℕ => u-c+∑ k∈Finset.range n,increment f c μ u k) atTop (𝓝 (value f c μ u)) :=
    tendsto_const_nhds.add hs.of_norm.tendsto_sum_tsum_nat
  exact ht.congr' (Eventually.of_forall fun n => (approximation_partial_sum f c μ u n).symm)

theorem approximation_forward (f : ℂ → ℂ) (c : ℂ) (μ : ℝ) (u : ℂ) (n : ℕ) (hμ : μ≠0) :
    approximation f c μ (f u) n=(μ:ℂ)*approximation f c μ u (n+1) := by
  have hmc : (μ:ℂ)≠0 := by exact_mod_cast hμ
  unfold approximation
  rw [Function.iterate_succ_apply,pow_succ]
  field_simp

theorem increment_forward (f : ℂ → ℂ) (c : ℂ) (μ : ℝ) (u : ℂ) (n : ℕ) (hμ : μ≠0) :
    increment f c μ (f u) n=(μ:ℂ)*increment f c μ u (n+1) := by
  unfold increment
  rw [approximation_forward f c μ u (n+1) hμ,approximation_forward f c μ u n hμ]
  ring

theorem summable_forward (f : ℂ → ℂ) (c : ℂ) (μ : ℝ) (u : ℂ) (hμ : μ≠0)
    (hs : Summable (fun n => ‖increment f c μ u n‖)) :
    Summable (fun n => ‖increment f c μ (f u) n‖) := by
  simpa only [increment_forward f c μ u _ hμ,norm_mul] using
    ((summable_nat_add_iff 1).mpr hs).mul_left ‖(μ:ℂ)‖

theorem functional_eq (f : ℂ → ℂ) (c : ℂ) (μ : ℝ) (u : ℂ) (hμ : μ≠0)
    (hs : Summable (fun n => ‖increment f c μ u n‖)) : value f c μ (f u)=(μ:ℂ)*value f c μ u := by
  have ht := ((tendsto_approximation f c μ u hs).comp (tendsto_add_atTop_nat 1)).const_mul (μ:ℂ)
  exact tendsto_nhds_unique (tendsto_approximation f c μ (f u) (summable_forward f c μ u hμ hs))
    (ht.congr' (Eventually.of_forall fun n => (approximation_forward f c μ u n hμ).symm))

theorem local_orbit_geometric (f : ℂ → ℂ) (c : ℂ) (μ r δ : ℝ)
    (hμ : 0≤μ) (hr : 0≤r) (hr1 : r≤1) (hδ : 0<δ) (hμδ : μ+2*δ≤r)
    (hq : ∀ u∈ball c δ, ‖f u-c-(μ:ℂ)*(u-c)‖≤2*‖u-c‖^2) (u : ℂ) (hu : u∈ball c δ) :
    ∀ n : ℕ, ‖(f^[n]) u-c‖≤‖u-c‖*r^n := by
  have hun : ‖u-c‖<δ := by simpa only [mem_ball,dist_eq_norm] using hu
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : ‖(f^[n]) u-c‖<δ :=
      ih.trans_lt ((mul_le_mul_of_nonneg_left (pow_le_one₀ hr hr1) (norm_nonneg _)).trans_lt (by simpa using hun))
    have hb := hq _ (by simpa only [mem_ball,dist_eq_norm] using hn)
    have ht := norm_add_le (f ((f^[n]) u)-c-(μ:ℂ)*((f^[n]) u-c)) ((μ:ℂ)*((f^[n]) u-c))
    rw [sub_add_cancel,norm_mul,Complex.norm_of_nonneg hμ] at ht
    have hquad : ‖(f^[n]) u-c‖^2≤δ*‖(f^[n]) u-c‖ := by nlinarith [norm_nonneg ((f^[n]) u-c)]
    have hstep : ‖f ((f^[n]) u)-c‖≤r*‖(f^[n]) u-c‖ := by
      nlinarith [mul_le_mul_of_nonneg_right hμδ (norm_nonneg ((f^[n]) u-c))]
    rw [Function.iterate_succ_apply']
    exact hstep.trans ((mul_le_mul_of_nonneg_left ih hr).trans_eq (by rw [pow_succ]; ring))

theorem increment_norm_bound (f : ℂ → ℂ) (c : ℂ) (μ r δ : ℝ)
    (hμ : 0<μ) (hr : 0≤r) (hr1 : r≤1) (hδ : 0<δ) (hμδ : μ+2*δ≤r)
    (hq : ∀ u∈ball c δ, ‖f u-c-(μ:ℂ)*(u-c)‖≤2*‖u-c‖^2)
    (u : ℂ) (hu : u∈ball c δ) (n : ℕ) :
    ‖increment f c μ u n‖≤(2*‖u-c‖^2/μ)*(r^2/μ)^n := by
  have ho := local_orbit_geometric f c μ r δ hμ.le hr hr1 hδ hμδ hq u hu
  have hn : (f^[n]) u∈ball c δ := by
    rw [mem_ball,dist_eq_norm]
    exact (ho n).trans_lt ((mul_le_mul_of_nonneg_left (pow_le_one₀ hr hr1) (norm_nonneg _)).trans_lt
      (by simpa only [mem_ball,dist_eq_norm,mul_one] using hu))
  have hb := hq _ hn
  rw [approximation_increment f c μ u n (ne_of_gt hμ),norm_mul,norm_inv,norm_pow,Complex.norm_of_nonneg hμ.le]
  calc
    _ ≤ (μ^(n+1))⁻¹*(2*(‖u-c‖*r^n)^2) := by
      rw [Function.iterate_succ_apply']
      exact mul_le_mul_of_nonneg_left (hb.trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (ho n) 2) (by norm_num))) (by positivity)
    _ = _ := by
      rw [mul_pow,←pow_mul,Nat.mul_comm n 2,pow_mul,div_pow,pow_succ]
      field_simp

/-- The orbit sum itself is analytic and normalized, with no Koenigs germ
or invariant neighborhood assumed as an input. -/
theorem exists_normalized_local_koenigs (f : ℂ → ℂ) (c : ℂ) (μ q : ℝ)
    (hμ : 0<μ) (hμ1 : μ<1) (hq : 0<q)
    (hfa : AnalyticOnNhd ℂ f (ball c q)) (hfix : f c=c)
    (hquad : ∀ u∈ball c q, ‖f u-c-(μ:ℂ)*(u-c)‖≤2*‖u-c‖^2) :
    ∃ δ : ℝ, 0<δ ∧ δ≤q ∧
      AnalyticOnNhd ℂ (value f c μ) (ball c δ) ∧ value f c μ c=0 ∧ HasDerivAt (value f c μ) 1 c ∧
      ∀ u∈ball c δ, f u∈ball c δ ∧ value f c μ (f u)=(μ:ℂ)*value f c μ u ∧
        Summable (fun n => ‖increment f c μ u n‖) ∧
        Tendsto (approximation f c μ u) atTop (𝓝 (value f c μ u)) := by
  obtain ⟨r,δ₀,hr,hr1,_hmr,hrμ,hδ₀,_hδ₀1,hμδ₀⟩ := Kneser.PositiveLocalKoenigs.exists_contraction_rate μ hμ hμ1
  let δ := min q (δ₀/2)
  have hδ : 0<δ := lt_min hq (by positivity)
  have hδq : δ≤q := min_le_left _ _
  have hμδ : μ+2*δ≤r := by have hh := min_le_right q (δ₀/2); linarith
  have hlocal : ∀ u∈ball c δ, ‖f u-c-(μ:ℂ)*(u-c)‖≤2*‖u-c‖^2 :=
    fun u hu => hquad u (ball_subset_ball hδq hu)
  have ho := local_orbit_geometric f c μ r δ hμ.le hr.le hr1.le hδ hμδ hlocal
  let p := r^2/μ
  have hp : 0≤p := by dsimp [p]; positivity
  have hp1 : p<1 := (div_lt_one hμ).mpr hrμ
  have hs : ∀ u∈ball c δ, Summable (fun n => ‖increment f c μ u n‖) := by
    intro u hu
    exact ((summable_geometric_of_lt_one hp hp1).mul_left (2*‖u-c‖^2/μ)).of_nonneg_of_le
      (fun _ => norm_nonneg _) (increment_norm_bound f c μ r δ hμ hr.le hr1.le hδ hμδ hlocal u hu)
  have hiter : ∀ n : ℕ, ∀ u∈ball c δ, AnalyticAt ℂ (f^[n]) u := by
    intro n
    induction n with
    | zero => intro u hu; exact analyticAt_id
    | succ n ih =>
      intro u hu
      have hn : (f^[n]) u∈ball c q := by
        apply ball_subset_ball hδq
        rw [mem_ball,dist_eq_norm]
        exact (ho u hu n).trans_lt ((mul_le_mul_of_nonneg_left (pow_le_one₀ hr.le hr1.le) (norm_nonneg _)).trans_lt
          (by simpa only [mem_ball,dist_eq_norm,mul_one] using hu))
      have hh := (hfa _ hn).comp (f:=f^[n]) (ih u hu)
      simpa only [Function.iterate_succ'] using hh
  let C := 2*δ^2/μ
  have hmajor := (summable_geometric_of_lt_one hp hp1).mul_left C
  have hbound : ∀ n : ℕ, ∀ u∈ball c δ, ‖increment f c μ u n‖≤C*p^n := by
    intro n u hu
    have hn : ‖u-c‖≤δ := (by simpa only [mem_ball,dist_eq_norm] using hu : ‖u-c‖<δ).le
    exact (increment_norm_bound f c μ r δ hμ hr.le hr1.le hδ hμδ hlocal u hu n).trans
      (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hn 2) (by norm_num)) hμ.le) (by positivity))
  have hterms : ∀ n : ℕ, DifferentiableOn ℂ (fun u => increment f c μ u n) (ball c δ) := by
    intro n u hu
    exact (((analyticAt_const.mul ((hiter (n+1) u hu).sub analyticAt_const)).sub
      (analyticAt_const.mul ((hiter n u hu).sub analyticAt_const))).differentiableAt).differentiableWithinAt
  have hhol := Complex.differentiableOn_tsum_of_summable_norm hmajor hterms isOpen_ball hbound
  have hanalytic : AnalyticOnNhd ℂ (value f c μ) (ball c δ) := by
    intro u hu
    exact ((analyticAt_id.sub analyticAt_const).add (hhol.analyticAt (isOpen_ball.mem_nhds hu)))
  have hzero : value f c μ c=0 := by
    have hfiter : ∀ n : ℕ, (f^[n]) c=c := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [Function.iterate_succ_apply',ih,hfix]
    simp [value,increment,approximation,hfiter]
  have hbig : (fun u : ℂ => value f c μ u-(u-c))=O[𝓝 c] (fun u : ℂ => ‖u-c‖^2) := by
    apply Asymptotics.isBigO_iff.mpr
    refine ⟨2/μ*(1-p)⁻¹,?_⟩
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hδ : c∈ball c δ)] with u hu
    have hb := norm_tsum_le_tsum_norm (hs u hu)
    change ‖∑' n, increment f c μ u n‖≤_ at hb
    have hm := (hs u hu).tsum_le_tsum
      (increment_norm_bound f c μ r δ hμ hr.le hr1.le hδ hμδ hlocal u hu)
      ((summable_geometric_of_lt_one hp hp1).mul_left (2*‖u-c‖^2/μ))
    rw [tsum_mul_left,tsum_geometric_of_abs_lt_one (by rw [abs_of_nonneg hp]; exact hp1)] at hm
    simp only [value,add_sub_cancel_left,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖u-c‖)]
    exact hb.trans (hm.trans_eq (by ring))
  have hd : HasDerivAt (value f c μ) 1 c := by
    apply HasDerivAt.of_isLittleO
    simpa only [hzero,sub_zero,smul_eq_mul,mul_one] using
      hbig.trans_isLittleO (Asymptotics.isLittleO_pow_sub_sub c (m:=2) (by norm_num))
  refine ⟨δ,hδ,hδq,hanalytic,hzero,hd,?_⟩
  intro u hu
  have hin : f u∈ball c δ := by
    rw [mem_ball,dist_eq_norm]
    have h1 := ho u hu 1
    simp only [Function.iterate_one,pow_one] at h1
    exact h1.trans_lt ((mul_le_mul_of_nonneg_left hr1.le (norm_nonneg (u-c))).trans_lt
      (by simpa only [mem_ball,dist_eq_norm,mul_one] using hu))
  exact ⟨hin,functional_eq f c μ u (ne_of_gt hμ) (hs u hu),hs u hu,tendsto_approximation f c μ u (hs u hu)⟩

end Kneser.QuadraticLocalKoenigs
end
