import Kneser.ActualGrowingKoenigsIdentification
import Kneser.ActualNormalizationAnchorExpansion
import Kneser.RealOrderedRootUniqueness
import Kneser.ParabolicInitialPetal

/-! The paper's actual real normalization anchor is identified with the
same true Koenigs logarithm. A genuine buffered finite parabolic entry
supplies the positive-parameter entry, rather than being replaced by an
assumed equality of normalizations. -/
set_option autoImplicit false
set_option maxHeartbeats 9000000
noncomputable section
namespace Kneser.ActualAnchorKoenigsIdentification
open Set Metric Filter Complex
open Kneser.ExponentialUnfolding Kneser.PositiveKoenigsOrbit Kneser.PositiveKoenigsAbel
open Kneser.ActualKoenigsEntryRealPhase Kneser.ActualKoenigsGlobalRealPhase
open Kneser.ActualKoenigsRealPhase Kneser.ActualKoenigsIdentification
open Kneser.RealOrderedRootUniqueness Kneser.ReflectedOrbitChainCoefficient
open Kneser.RealNormalizationAnchor Kneser.ActualNormalizationAnchorExpansion
open Kneser.RealExponentialPetal Kneser.ApolloniusGeometry
open Kneser.ParabolicExponentialOrbit Kneser.ParabolicInitialPetal
open scoped Topology

theorem koenigsTime_iterate_real_left (s a r : ℝ)
    (hs : 0<s) (hs1 : s<1) (ha : -1<a) (ha0 : a≤0)
    (hfa : unfolding s a=(a:ℂ)) (hμ : 0<multiplier s a) (hμ1 : multiplier s a<1)
    (hr : r<a) (N : ℕ) :
    koenigsTime s a (orbit r s N)=koenigsTime s a r+(N:ℂ) := by
  have hleft := orbit_left_of_root s a r hs1 hfa hr
  induction N with
  | zero => simp
  | succ N ih =>
    have him := real_orbit_im_zero s r N
    have he : orbit r s N=((orbit r s N).re:ℂ) := by apply Complex.ext <;> simp [him]
    have hlim := real_left_orbit_limit s a (orbit r s N).re hs1 ha hfa hμ.le hμ1 (hleft N)
    have hsum := actual_koenigs_sum_of_orbit_limit s a (orbit r s N).re hs.le hs1 ha ha0 hfa hμ hμ1 hlim
    have hneg := koenigsValue_negative_left s a (orbit r s N).re hs.le hs1 ha ha0 hfa hμ hμ1 hsum hlim (hleft N)
    have hK : koenigsValue s a ((orbit r s N).re:ℂ)≠0 := by
      intro hz
      rw [hz,Complex.zero_re] at hneg
      linarith [hneg.2]
    have hh := koenigsTime_abel s a ((orbit r s N).re:ℂ) hμ hμ1 hsum hK
    rw [←he] at hh
    rw [orbit_succ,hh,ih]
    push_cast
    ring

/-- The finite entry is expressed by the true attracting cross ratio.
All root matching, summability and logarithm branches are conclusions of
actual preparation and the actual exponential map. -/
theorem exists_actual_anchor_koenigs_entry_threshold
    (U H e₁ e₂ A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F Γ : ℂ × ℂ → ℂ)
    (hdata : ActualPreparationData U H e₁ e₂ A B K F Γ) :
    ∃ R₀ s₀ : ℝ, 0<R₀ ∧ 0<s₀ ∧ s₀≤1/2 ∧
      ∀ s a b : ℝ, 0<s → s<s₀ → a<0 → 0<b →
        unfolding s a=(a:ℂ) → unfolding s b=(b:ℂ) →
        ∀ R : ℝ, R₀≤R → ∀ M : ℕ, realAnchor<a →
          ‖crossRatio a b (orbit normalizationAnchor s M)‖≤Real.exp (-((-Real.log (multiplier s a))*R)) →
          anchorValue U H e₁ e₂ A B Γ M s=
            koenigsTime s a realAnchor+modelConstant s a b (e₁ s) (e₂ s) := by
  obtain ⟨Q,R₀,s₀,hR₀,hs₀,hs₀h,hall⟩ := exists_actual_prepared_koenigs_identification U H e₁ e₂ A B K F Γ hdata
  refine ⟨R₀,s₀,hR₀,hs₀,hs₀h,?_⟩
  intro s a b hs hss ha0 hb0 hfa hfb R hR M har hentry
  obtain ⟨a',b',haa',ha',hb',hfa',hfb',hμ',hμ1',hid⟩ := hall s hs hss
  have hs1 : s<1 := by linarith [hss.trans_le hs₀h]
  obtain ⟨rfl,rfl⟩ := ordered_actual_roots_unique s a b a' b' hs1 ha0 hb0 ha' hb' hfa hfb hfa' hfb'
  have hleft := orbit_left_of_root s a normalizationAnchor hs1 hfa har
  have hscale := timeScale_eq_neg_log_multiplier Q s a b hs1 haa' (by linarith) hfa hfb
  have hq : ‖crossRatio a b (orbit normalizationAnchor s M)‖≤
      Real.exp (-(timeScale Q ((1-s)*(b-a))*R)) := by simpa only [hscale,multiplier] using hentry
  have he := (hid R hR (orbit normalizationAnchor s M) (hleft M) hq).2.2.2.2.2.2
  have hiter := koenigsTime_iterate_real_left s a realAnchor hs hs1 haa' ha'.le hfa hμ' hμ1' har M
  unfold anchorValue
  rw [he]
  simp only [normalizationAnchor]
  rw [hiter]
  ring

/-- A fixed buffered parabolic entry has a genuine positive-parameter
cross-ratio entry for every sufficiently small parameter and for every
actual ordered root pair. -/
theorem eventual_anchor_crossRatio_entry (R : ℝ) (hR : 0<R) (Rᵢ : ℝ)
    (hinit : ∀ Z : ℝ, 0≤Z → ∃ s₀ : ℝ, 0<s₀ ∧ s₀≤1/2 ∧
      ∀ s : ℝ, 0<s → s<s₀ → ∃ a b θ : ℝ, a<0 ∧ 0<b ∧ |a|<1/(4*(Z+1)) ∧
        |b|<1/(4*(Z+1)) ∧ 0<θ ∧ unfolding s a=(a:ℂ) ∧ unfolding s b=(b:ℂ) ∧
        θ= -Real.log ((1-s)*(1+a)) ∧
        ∀ u : ℂ, R+1≤(inverseCoordinate u).re → ‖inverseCoordinate u‖≤Z →
          ‖crossRatio a b u‖≤Real.exp (-(θ*R)) ∧
          ∀ k : ℕ, ‖orbit u s k-(a:ℂ)‖*‖orbit u s k-(b:ℂ)‖≤100/(R+(3/4)*(k:ℝ))^2)
    (M : ℕ) (hentry : R+2≤(inverseCoordinate (orbit normalizationAnchor 0 M)).re) :
    ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ a b : ℝ, a<0 → 0<b →
      unfolding s a=(a:ℂ) → unfolding s b=(b:ℂ) →
      realAnchor<a ∧
      ‖crossRatio a b (orbit normalizationAnchor s M)‖≤Real.exp (-((-Real.log (multiplier s a))*R)) := by
  let v₀ : ℂ := orbit normalizationAnchor 0 M
  have hv₀ : v₀≠0 := by
    intro hz
    change R+2≤(inverseCoordinate v₀).re at hentry
    rw [hz,inverseCoordinate,div_zero,Complex.zero_re] at hentry
    linarith
  have hv : ContinuousAt (fun s : ℝ => orbit normalizationAnchor (s:ℂ) M) 0 := by
    have hc := (Kneser.ParabolicOverlapGate.analyticAt_forward_orbit_joint normalizationAnchor 0 M).continuousAt
    have hp : ContinuousAt (fun s : ℝ => ((s:ℂ),normalizationAnchor)) 0 :=
      Complex.continuous_ofReal.continuousAt.prodMk continuousAt_const
    exact hc.comp (f:=fun s : ℝ => ((s:ℂ),normalizationAnchor)) hp
  have hζ : ContinuousAt (fun s : ℝ => inverseCoordinate (orbit normalizationAnchor s M)) 0 :=
    continuousAt_const.div hv hv₀
  let Z := ‖inverseCoordinate v₀‖+1
  have hZ : 0≤Z := by dsimp [Z]; positivity
  obtain ⟨s₁,hs₁,hs₁h,hroots⟩ := hinit Z hZ
  obtain ⟨s₂,hs₂,_hs₂h,hsmall⟩ := exists_uniform_ordered_root_smallness (-realAnchor/2) (by linarith [realAnchor_interval.2])
  have hdepth : ∀ᶠ s : ℝ in 𝓝[>] 0, R+1≤(inverseCoordinate (orbit normalizationAnchor s M)).re := by
    have hh := (Complex.continuous_re.continuousAt.comp hζ).eventually (lt_mem_nhds (show R+1<(inverseCoordinate v₀).re by change R+2≤_ at hentry; linarith))
    exact (hh.filter_mono nhdsWithin_le_nhds).mono (fun _ h => h.le)
  have hbound : ∀ᶠ s : ℝ in 𝓝[>] 0, ‖inverseCoordinate (orbit normalizationAnchor s M)‖≤Z := by
    have hh := hζ.norm.eventually (gt_mem_nhds (show ‖inverseCoordinate v₀‖<Z by dsimp [Z]; linarith))
    exact (hh.filter_mono nhdsWithin_le_nhds).mono (fun _ h => h.le)
  have hpos : ∀ᶠ s : ℝ in 𝓝[>] 0, 0<s := self_mem_nhdsWithin
  have hlim₁ : ∀ᶠ s : ℝ in 𝓝[>] 0, s<s₁ := (eventually_lt_nhds hs₁).filter_mono nhdsWithin_le_nhds
  have hlim₂ : ∀ᶠ s : ℝ in 𝓝[>] 0, s<s₂ := (eventually_lt_nhds hs₂).filter_mono nhdsWithin_le_nhds
  filter_upwards [hpos,hlim₁,hlim₂,hdepth,hbound] with s hs hss₁ hss₂ hd hb
  intro a b ha0 hb0 hfa hfb
  have hsa : s<1 := by linarith [hss₁.trans_le hs₁h]
  obtain ⟨a',b',θ,ha',hb',_has,_hbs,_hθ,hfa',hfb',hθeq,horbit⟩ := hroots s hs hss₁
  obtain ⟨rfl,rfl⟩ := ordered_actual_roots_unique s a b a' b' hsa ha0 hb0 ha' hb' hfa hfb hfa' hfb'
  obtain ⟨haSmall,_hbSmall⟩ := hsmall s a b hs hss₂ ha' hb' hfa' hfb'
  refine ⟨?_,?_⟩
  · have hh := (abs_lt.mp haSmall).1
    linarith [realAnchor_interval.2]
  · simpa only [hθeq,multiplier] using (horbit (orbit normalizationAnchor s M) hd hb).1

/-- The actual real-anchor value is identified with the actual Koenigs
normalization for every genuinely deep fixed entry length. The finite
positive-parameter entry and the logarithm branch are derived. -/
theorem exists_actual_anchor_koenigs_identification
    (U H e₁ e₂ A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F Γ : ℂ × ℂ → ℂ)
    (hdata : ActualPreparationData U H e₁ e₂ A B K F Γ) :
    ∃ D : ℝ, 64≤D ∧ ∀ M : ℕ,
      D+2≤(inverseCoordinate (orbit normalizationAnchor 0 M)).re →
      ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ a b : ℝ, a<0 → 0<b →
        unfolding s a=(a:ℂ) → unfolding s b=(b:ℂ) →
        anchorValue U H e₁ e₂ A B Γ M s=
          koenigsTime s a realAnchor+modelConstant s a b (e₁ s) (e₂ s) := by
  obtain ⟨R₀,s₀,hR₀,hs₀,_hs₀h,hid⟩ := exists_actual_anchor_koenigs_entry_threshold U H e₁ e₂ A B K F Γ hdata
  obtain ⟨Rᵢ,hRᵢ,hinit⟩ := exists_uniform_initial_parabolic_petals
  let D := max 64 (max R₀ Rᵢ)
  have hD : 64≤D := le_max_left _ _
  have hDR : R₀≤D := (le_max_left _ _).trans (le_max_right _ _)
  have hDᵢ : Rᵢ≤D := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨D,hD,?_⟩
  intro M hentry
  have he := eventual_anchor_crossRatio_entry D (by linarith) Rᵢ (hinit D hDᵢ) M hentry
  have hpos : ∀ᶠ s : ℝ in 𝓝[>] 0, 0<s := self_mem_nhdsWithin
  have hsmall : ∀ᶠ s : ℝ in 𝓝[>] 0, s<s₀ := (eventually_lt_nhds hs₀).filter_mono nhdsWithin_le_nhds
  filter_upwards [he,hpos,hsmall] with s hs hp hss
  intro a b ha hb hfa hfb
  obtain ⟨har,hq⟩ := hs a b ha hb hfa hfb
  exact hid s a b hp hss ha hb hfa hfb D hDR M har hq

end Kneser.ActualAnchorKoenigsIdentification
end
