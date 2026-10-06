import Kneser.ActualHolomorphicGrowingLens
import Kneser.ActualKoenigsUpperBranch

/-! The actual normalized Koenigs orbit sum is holomorphic and injective
on the genuine physical growing lens. The map and its normalization are
fixed by the actual exponential orbit, not by existential chart data. -/
set_option autoImplicit false
set_option maxHeartbeats 7000000
noncomputable section
namespace Kneser.GrowingLensKoenigs
open Set Metric Filter
open Kneser.ExponentialUnfolding Kneser.PositiveKoenigsOrbit Kneser.PositiveKoenigsPetal
open Kneser.ActualKoenigsEntryRealPhase Kneser.ActualKoenigsUpperBranch
open Kneser.ActualKoenigsGlobalRealPhase Kneser.ActualHolomorphicGrowingLens
open Kneser.GrowingLensEntry Kneser.GrowingBandGeometry
open Kneser.ReflectedOrbitChainCoefficient
open scoped Topology

def physicalLens (a b θ Y : ℝ) : Set ℂ := bandChart a b θ '' strip θ Y

theorem lensControl_forward_limit
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P : ℝ)
    (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P) (u : ℂ)
    (hu : u∈physicalLens a b θ Y) :
    Tendsto (orbit u s) atTop (𝓝 (a:ℂ)) := by
  obtain ⟨Z,hZ,rfl⟩ := hu
  have hd := (hc.true_orbits Z hZ).2.2.2.2.1
  exact true_forward_orbit_tendsto_root _ s a b θ (by linarith [hc.left_neg,hc.right_pos]) hc.theta_pos
    (fun k => ⟨(hd k).1,(hd k).2.1⟩) (fun k => (hd k).2.2.2.2)

theorem lensControl_unit_root_bound
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P : ℝ)
    (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P) (u : ℂ)
    (hu : u∈physicalLens a b θ Y) :
    ∀ k : ℕ, ‖orbit u s k-(a:ℂ)‖≤1 := by
  have hL := lensControl_forward_limit e₁ e₂ A B Γ s a b θ Y η M P hc u hu
  obtain ⟨Z,hZ,rfl⟩ := hu
  have hd := (hc.true_orbits Z hZ).2.2.2.2.1
  have hnorm : ∀ k, ‖orbit (bandChart a b θ Z) s k‖≤η/4 := fun k => (hd k).2.2.1
  have hrootnorm : ‖(a:ℂ)‖≤η/4 :=
    le_of_tendsto (continuous_norm.continuousAt.tendsto.comp hL) (Eventually.of_forall hnorm)
  intro k
  exact (norm_sub_le _ _).trans (by linarith [hnorm k,hrootnorm,hc.radius_small])

theorem koenigsValue_ne_zero_of_true_limit (s a : ℝ) (u : ℂ)
    (hs : 0≤s) (hs1 : s<1) (ha : -1<a) (ha0 : a≤0)
    (hfa : unfolding s a=(a:ℂ)) (hμ : 0<multiplier s a) (hμ1 : multiplier s a<1)
    (hlim : Tendsto (orbit u s) atTop (𝓝 (a:ℂ)))
    (hroots : ∀ k, orbit u s k≠(a:ℂ)) : koenigsValue s a u≠0 := by
  obtain ⟨_δ,_hδ,_hhol,_hz,hder,_hrest⟩ :=
    Kneser.PositiveLocalKoenigs.exists_actual_local_koenigs s a hs hs1 ha ha0 hfa hμ hμ1
  have hnear : ∀ᶠ v : ℂ in 𝓝 (a:ℂ), v≠(a:ℂ) → koenigsValue s a v≠0 := by
    simpa only [mem_compl_iff,mem_singleton_iff] using
      eventually_nhdsWithin_iff.mp (hder.eventually_ne (c:=(0:ℂ)) (by norm_num))
  obtain ⟨N,hN⟩ := (hlim.eventually hnear).exists
  have hKN := hN (hroots N)
  have hsum := actual_koenigs_sum_of_orbit_limit s a u hs hs1 ha ha0 hfa hμ hμ1 hlim
  intro he
  rw [koenigsValue_iterate s a u (ne_of_gt hμ) hsum N,he,mul_zero] at hKN
  exact hKN rfl

theorem koenigs_geometry_of_lensControl
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P : ℝ)
    (hs : 0<s) (hs1 : s<1)
    (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P) :
    AnalyticOnNhd ℂ (koenigsValue s a) (physicalLens a b θ Y) ∧
    InjOn (koenigsValue s a) (physicalLens a b θ Y) ∧
    ∀ u∈physicalLens a b θ Y, koenigsValue s a u≠0 ∧
      koenigsValue s a (unfolding s u)=(multiplier s a:ℂ)*koenigsValue s a u := by
  have ha := real_root_gt_neg_one s a hc.left_fixed
  have hμ : 0<multiplier s a := by unfold multiplier; exact mul_pos (by linarith) (by linarith)
  have hμ1 : multiplier s a<1 := by unfold multiplier; nlinarith [hc.left_neg]
  have hlimits := fun u hu => lensControl_forward_limit e₁ e₂ A B Γ s a b θ Y η M P hc u hu
  have hsums := fun u hu => actual_koenigs_sum_of_orbit_limit s a u hs.le hs1 ha hc.left_neg.le
    hc.left_fixed hμ hμ1 (hlimits u hu)
  refine ⟨fun u hu => analyticAt_koenigsValue_of_true_limit s a u hs.le hs1 ha hc.left_neg.le
    hc.left_fixed hμ hμ1 (hlimits u hu),?_,?_⟩
  · obtain ⟨δ,hδ,hinj⟩ := exists_local_koenigs_injective s a hs.le hs1 ha hc.left_neg.le hc.left_fixed hμ hμ1
    intro u hu v hv heq
    obtain ⟨N,huN,hvN⟩ := (((hlimits u hu).eventually (ball_mem_nhds (a:ℂ) hδ)).and
      ((hlimits v hv).eventually (ball_mem_nhds (a:ℂ) hδ))).exists
    have hKN : koenigsValue s a (orbit u s N)=koenigsValue s a (orbit v s N) := by
      rw [koenigsValue_iterate s a u (ne_of_gt hμ) (hsums u hu) N,
        koenigsValue_iterate s a v (ne_of_gt hμ) (hsums v hv) N,heq]
    have hN := hinj huN hvN hKN
    have hbu := lensControl_unit_root_bound e₁ e₂ A B Γ s a b θ Y η M P hc u hu
    have hbv := lensControl_unit_root_bound e₁ e₂ A B Γ s a b θ Y η M P hc v hv
    have hpull : ∀ n : ℕ, orbit u s n=orbit v s n → u=v := by
      intro n
      induction n with
      | zero => simpa only [orbit_zero] using (fun h : orbit u s 0=orbit v s 0 => h)
      | succ n ih =>
        intro he
        rw [orbit_succ,orbit_succ] at he
        exact ih (unfolding_injective_on_unit_root_ball s a _ _ hs.le hs1 (hbu n) (hbv n) he)
    exact hpull N hN
  · intro u hu
    have hn : ∀ k, orbit u s k≠(a:ℂ) := by
      obtain ⟨Z,hZ,rfl⟩ := hu
      exact fun k => ((hc.true_orbits Z hZ).2.2.2.2.1 k).1
    exact ⟨koenigsValue_ne_zero_of_true_limit s a u hs.le hs1 ha hc.left_neg.le hc.left_fixed hμ hμ1
      (hlimits u hu) hn,koenigsValue_functional_eq s a u (ne_of_gt hμ) (hsums u hu)⟩

/-- Actual preparation constructs the lens and the normalized true σ
map with holomorphy, injectivity and its genuine linearizing equation. -/
theorem exists_actual_growing_lens_koenigs
    (U H e₁ e₂ A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F Γ : ℂ × ℂ → ℂ)
    (hdata : ActualPreparationData U H e₁ e₂ A B K F Γ) :
    ∃ Y s₀ η M P : ℝ, 2≤Y ∧ 0<s₀ ∧ s₀≤1/2 ∧
      ∀ s : ℝ, 0<s → s<s₀ → ∃ a b θ : ℝ,
        LensControl e₁ e₂ A B Γ s a b θ Y η M P ∧
        AnalyticOnNhd ℂ (koenigsValue s a) (physicalLens a b θ Y) ∧
        InjOn (koenigsValue s a) (physicalLens a b θ Y) ∧
        ∀ u∈physicalLens a b θ Y, koenigsValue s a u≠0 ∧
          koenigsValue s a (unfolding s u)=(multiplier s a:ℂ)*koenigsValue s a u := by
  obtain ⟨Y,s₀,η,M,P,hY,hs₀,hs₀h,hall⟩ := exists_actual_lens_control U H e₁ e₂ A B K F Γ hdata
  refine ⟨Y,s₀,η,M,P,hY,hs₀,hs₀h,?_⟩
  intro s hs hss
  obtain ⟨a,b,θ,hc⟩ := hall s hs hss
  exact ⟨a,b,θ,hc,koenigs_geometry_of_lensControl e₁ e₂ A B Γ s a b θ Y η M P hs
    (by linarith [hss.trans_le hs₀h]) hc⟩

end Kneser.GrowingLensKoenigs
end
