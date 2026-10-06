import Kneser.ActualKoenigsJacobian
import Kneser.ActualRegularWelding

/-! The genuine regular attracting superfunction on its actual Koenigs
image domain. The domain is retained explicitly; no entire inverse or
continuation across an unspecified cut is assumed. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Kneser.ActualRegularKoenigsInverse
open Filter Set Metric Complex
open Kneser.ExponentialUnfolding Kneser.PositiveKoenigsOrbit Kneser.PositiveLocalKoenigs
open Kneser.ActualKoenigsJacobian Kneser.ActualKoenigsEntryRealPhase
open Kneser.ActualKoenigsGlobalRealPhase Kneser.ActualKoenigsUpperBranch
open Kneser.PositiveKoenigsPetal Kneser.HolomorphicInjectiveInverse
open Kneser.GrowingLensKoenigs Kneser.ActualRegularWelding
open Kneser.GrowingBandGeometry Kneser.ActualHolomorphicGrowingLens
open Kneser.GrowingLensSpatialHolomorphy Kneser.GrowingLensCoordinateRegularity
open Kneser.ActualGrowingKoenigsIdentification Kneser.ActualGrowingCoordinateInverse
open scoped Topology

def unitBasin (s a : ℝ) : Set ℂ := {u |
  Tendsto (fun k => orbit u s k) atTop (𝓝 (a:ℂ)) ∧
  ∀k : ℕ, ‖orbit u s k-(a:ℂ)‖<1}

theorem exists_local_unit_basin (s a : ℝ)
    (hs : 0≤s) (hs1 : s<1) (ha : -1<a) (ha0 : a≤0)
    (hfa : unfolding s a=(a:ℂ)) (hμ : 0<multiplier s a) (hμ1 : multiplier s a<1) :
    ∃δ : ℝ, 0<δ ∧ ball (a:ℂ) δ⊆unitBasin s a := by
  obtain ⟨r,δ,hr,hr1,_hmr,_hrμ,hδ,hδ1,hμδ⟩ := exists_contraction_rate _ hμ hμ1
  refine ⟨δ,hδ,?_⟩
  intro u hu
  have ho := local_orbit_geometric s a r δ hs hs1 ha ha0 hfa hμ hr.le hr1.le hδ hδ1 hμδ u hu
  have hun : ‖u-(a:ℂ)‖<δ := by simpa only [mem_ball,dist_eq_norm] using hu
  have hnormzero : Tendsto (fun k => ‖orbit u s k-(a:ℂ)‖) atTop (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _) ho (by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr.le hr1).const_mul ‖u-(a:ℂ)‖)
  refine ⟨tendsto_iff_norm_sub_tendsto_zero.mpr hnormzero,?_⟩
  intro k
  exact (ho k).trans_lt ((mul_le_mul_of_nonneg_left (pow_le_one₀ hr.le hr1.le) (norm_nonneg _)).trans_lt
    (by simpa using hun.trans_le hδ1))

theorem unit_basin_isOpen (s a : ℝ)
    (hs : 0≤s) (hs1 : s<1) (ha : -1<a) (ha0 : a≤0)
    (hfa : unfolding s a=(a:ℂ)) (hμ : 0<multiplier s a) (hμ1 : multiplier s a<1) :
    IsOpen (unitBasin s a) := by
  obtain ⟨δ,hδ,hlocal⟩ := exists_local_unit_basin s a hs hs1 ha ha0 hfa hμ hμ1
  rw [isOpen_iff_mem_nhds]
  intro u hu
  obtain ⟨N,hN⟩ := (hu.1.eventually (ball_mem_nhds (a:ℂ) hδ)).exists
  have hentry : ∀ᶠv : ℂ in 𝓝 u, orbit v s N∈ball (a:ℂ) δ :=
    (Kneser.PreparedSpatialHolomorphy.differentiable_orbit_spatial s N u).continuousAt.eventually (isOpen_ball.mem_nhds hN)
  have hfinite : ∀ᶠv : ℂ in 𝓝 u, ∀k∈Finset.range N, ‖orbit v s k-(a:ℂ)‖<1 := by
    apply (eventually_all_finset (Finset.range N)).mpr
    intro k _
    exact ((Kneser.PreparedSpatialHolomorphy.differentiable_orbit_spatial s k u).continuousAt.sub continuousAt_const).norm.eventually
      (gt_mem_nhds (hu.2 k))
  filter_upwards [hentry,hfinite] with v hv hbounds
  have hb := hlocal hv
  refine ⟨orbit_limit_from_entry s a v N hb.1,?_⟩
  intro k
  by_cases hk : k<N
  · exact hbounds k (Finset.mem_range.mpr hk)
  · have hh := hb.2 (k-N)
    rw [actual_orbit_add] at hh
    simpa only [show k-N+N=k by omega] using hh

theorem koenigs_unit_basin_data (s a : ℝ)
    (hs : 0≤s) (hs1 : s<1) (ha : -1<a) (ha0 : a≤0)
    (hfa : unfolding s a=(a:ℂ)) (hμ : 0<multiplier s a) (hμ1 : multiplier s a<1) :
    InjOn (koenigsValue s a) (unitBasin s a) ∧
    ∀u∈unitBasin s a, AnalyticAt ℂ (koenigsValue s a) u ∧ deriv (koenigsValue s a) u≠0 := by
  refine ⟨?_,?_⟩
  · obtain ⟨δ,hδ,hinj⟩ := exists_local_koenigs_injective s a hs hs1 ha ha0 hfa hμ hμ1
    intro u hu v hv heq
    obtain ⟨N,huN,hvN⟩ := ((hu.1.eventually (ball_mem_nhds (a:ℂ) hδ)).and
      (hv.1.eventually (ball_mem_nhds (a:ℂ) hδ))).exists
    have hsu := actual_koenigs_sum_of_orbit_limit s a u hs hs1 ha ha0 hfa hμ hμ1 hu.1
    have hsv := actual_koenigs_sum_of_orbit_limit s a v hs hs1 ha ha0 hfa hμ hμ1 hv.1
    have heN : koenigsValue s a (orbit u s N)=koenigsValue s a (orbit v s N) := by
      rw [koenigsValue_iterate s a u (ne_of_gt hμ) hsu N,koenigsValue_iterate s a v (ne_of_gt hμ) hsv N,heq]
    have hN := hinj huN hvN heN
    have hpull : ∀n : ℕ, orbit u s n=orbit v s n → u=v := by
      intro n
      induction n with
      | zero => simpa only [orbit_zero] using (fun h : orbit u s 0=orbit v s 0 => h)
      | succ n ih =>
        intro he
        rw [orbit_succ,orbit_succ] at he
        exact ih (unfolding_injective_on_unit_root_ball s a _ _ hs hs1 (hu.2 n).le (hv.2 n).le he)
    exact hpull N hN
  · intro u hu
    exact ⟨analyticAt_koenigsValue_of_true_limit s a u hs hs1 ha ha0 hfa hμ hμ1 hu.1,
      deriv_koenigsValue_ne_zero_of_true_limit s a u hs hs1 ha ha0 hfa hμ hμ1 hu.1⟩

theorem unit_basin_forward (s a : ℝ) (u : ℂ) (hu : u∈unitBasin s a) :
    unfolding s u∈unitBasin s a := by
  have he (k : ℕ) : orbit (unfolding s u) s k=orbit u s (k+1) := by
    have hh := actual_orbit_add u s 1 k
    simpa only [orbit_succ,orbit_zero,Nat.add_comm] using hh
  refine ⟨?_,?_⟩
  · simpa only [he] using ((tendsto_add_atTop_iff_nat 1).mpr hu.1)
  · intro k
    rw [he]
    exact hu.2 _

def koenigsArgument (s a r₀ : ℝ) (w : ℂ) : ℂ :=
  koenigsValue s a r₀ * Complex.exp ((Real.log (multiplier s a):ℂ)*w)

def regularTimeDomain (s a r₀ : ℝ) : Set ℂ :=
  koenigsArgument s a r₀ ⁻¹' (koenigsValue s a '' unitBasin s a)

def regularSuperfunction (s a r₀ : ℝ) (w : ℂ) : ℂ :=
  imageInverse (koenigsValue s a) (unitBasin s a) (koenigsArgument s a r₀ w)

def koenigsHeight (s a : ℝ) : ℝ := -2*Real.pi/Real.log (multiplier s a)

theorem analyticAt_koenigsArgument (s a r₀ : ℝ) (w : ℂ) :
    AnalyticAt ℂ (koenigsArgument s a r₀) w := by
  exact analyticAt_const.mul ((analyticAt_const.mul analyticAt_id).cexp)

theorem regular_domain_holomorphic (s a r₀ : ℝ)
    (hs : 0≤s) (hs1 : s<1) (ha : -1<a) (ha0 : a≤0)
    (hfa : unfolding s a=(a:ℂ)) (hμ : 0<multiplier s a) (hμ1 : multiplier s a<1) :
    IsOpen (regularTimeDomain s a r₀) ∧
    AnalyticOnNhd ℂ (regularSuperfunction s a r₀) (regularTimeDomain s a r₀) ∧
    ∀w∈regularTimeDomain s a r₀, regularSuperfunction s a r₀ w∈unitBasin s a ∧
      koenigsValue s a (regularSuperfunction s a r₀ w)=koenigsArgument s a r₀ w := by
  have hb := unit_basin_isOpen s a hs hs1 ha ha0 hfa hμ hμ1
  obtain ⟨hi,hF⟩ := koenigs_unit_basin_data s a hs hs1 ha ha0 hfa hμ hμ1
  have hV := analyticOnNhd_imageInverse _ _ hb hi hF
  refine ⟨(image_isOpen _ _ hb hF).preimage (continuous_iff_continuousAt.mpr (fun w => (analyticAt_koenigsArgument s a r₀ w).continuousAt)),?_,?_⟩
  · intro w hw
    exact (hV _ hw).comp (analyticAt_koenigsArgument s a r₀ w)
  · intro w hw
    exact imageInverse_spec _ _ _ hw

theorem koenigs_argument_add_one (s a r₀ : ℝ) (hμ : 0<multiplier s a) (w : ℂ) :
    koenigsArgument s a r₀ (w+1)=(multiplier s a:ℂ)*koenigsArgument s a r₀ w := by
  unfold koenigsArgument
  rw [mul_add,mul_one,Complex.exp_add,←Complex.ofReal_exp,Real.exp_log hμ]
  ring

theorem regular_superfunction_abel (s a r₀ : ℝ)
    (hs : 0≤s) (hs1 : s<1) (ha : -1<a) (ha0 : a≤0)
    (hfa : unfolding s a=(a:ℂ)) (hμ : 0<multiplier s a) (hμ1 : multiplier s a<1)
    (w : ℂ) (hw : w∈regularTimeDomain s a r₀) :
    w+1∈regularTimeDomain s a r₀ ∧
    regularSuperfunction s a r₀ (w+1)=unfolding s (regularSuperfunction s a r₀ w) := by
  obtain ⟨hi,_⟩ := koenigs_unit_basin_data s a hs hs1 ha ha0 hfa hμ hμ1
  have hv := (regular_domain_holomorphic s a r₀ hs hs1 ha ha0 hfa hμ hμ1).2.2 w hw
  have hfv := unit_basin_forward s a _ hv.1
  have hsum := actual_koenigs_sum_of_orbit_limit s a _ hs hs1 ha ha0 hfa hμ hμ1 hv.1.1
  have he := koenigsValue_functional_eq s a _ (ne_of_gt hμ) hsum
  rw [hv.2] at he
  rw [←koenigs_argument_add_one s a r₀ hμ w] at he
  have hw1 : w+1∈regularTimeDomain s a r₀ := ⟨_,hfv,he⟩
  refine ⟨hw1,?_⟩
  have hinv := imageInverse_left _ _ hi _ hfv
  rw [he] at hinv
  exact hinv

theorem koenigs_argument_imaginary_period (s a r₀ : ℝ)
    (hlog : Real.log (multiplier s a)≠0) (w : ℂ) :
    koenigsArgument s a r₀ (w+(koenigsHeight s a:ℂ)*Complex.I)=koenigsArgument s a r₀ w := by
  have he : (Real.log (multiplier s a):ℂ)*((koenigsHeight s a:ℂ)*Complex.I)=
      -1*(2*(Real.pi:ℂ)*Complex.I) := by
    unfold koenigsHeight
    push_cast
    field_simp [show (Real.log (multiplier s a):ℂ)≠0 by exact_mod_cast hlog]

  unfold koenigsArgument
  rw [mul_add,Complex.exp_add,he]
  have hp : Complex.exp (-1*(2*(Real.pi:ℂ)*Complex.I))=1 := by
    simpa using Complex.exp_int_mul_two_pi_mul_I (-1)
  rw [hp,mul_one]

theorem regular_superfunction_imaginary_period (s a r₀ : ℝ)
    (hlog : Real.log (multiplier s a)≠0) (w : ℂ) :
    (w+(koenigsHeight s a:ℂ)*Complex.I∈regularTimeDomain s a r₀ ↔ w∈regularTimeDomain s a r₀) ∧
    regularSuperfunction s a r₀ (w+(koenigsHeight s a:ℂ)*Complex.I)=regularSuperfunction s a r₀ w := by
  simp only [regularTimeDomain,mem_preimage,regularSuperfunction,
    koenigs_argument_imaginary_period s a r₀ hlog w]
  exact ⟨trivial,trivial⟩


theorem real_left_mem_unit_basin (s a r₀ : ℝ)
    (hs1 : s<1) (ha : -1<a) (hfa : unfolding s a=(a:ℂ))
    (hμ : 0<multiplier s a) (hμ1 : multiplier s a<1) (hr : r₀<a) (hd : a-r₀<1) :
    (r₀:ℂ)∈unitBasin s a := by
  refine ⟨real_left_orbit_limit s a r₀ hs1 ha hfa hμ.le hμ1 hr,?_⟩
  intro k
  exact ((real_left_orbit_distance s a r₀ hs1 ha hfa hμ.le hr k).2.2).trans_lt
    ((mul_le_mul_of_nonneg_left (pow_le_one₀ hμ.le hμ1.le) (by linarith)).trans_lt (by simpa using hd))

theorem regular_superfunction_anchor (s a r₀ : ℝ)
    (hs : 0≤s) (hs1 : s<1) (ha : -1<a) (ha0 : a≤0)
    (hfa : unfolding s a=(a:ℂ)) (hμ : 0<multiplier s a) (hμ1 : multiplier s a<1)
    (hr : r₀<a) (hd : a-r₀<1) :
    (0:ℂ)∈regularTimeDomain s a r₀ ∧ regularSuperfunction s a r₀ 0=(r₀:ℂ) ∧
    (koenigsHeight s a:ℂ)*Complex.I∈regularTimeDomain s a r₀ ∧
    regularSuperfunction s a r₀ ((koenigsHeight s a:ℂ)*Complex.I)=(r₀:ℂ) := by
  have hb := real_left_mem_unit_basin s a r₀ hs1 ha hfa hμ hμ1 hr hd
  obtain ⟨hi,_⟩ := koenigs_unit_basin_data s a hs hs1 ha ha0 hfa hμ hμ1
  have hz : (0:ℂ)∈regularTimeDomain s a r₀ := by
    exact ⟨r₀,hb,by simp [koenigsArgument]⟩
  have hzero : regularSuperfunction s a r₀ 0=(r₀:ℂ) := by
    simpa [regularSuperfunction,koenigsArgument] using imageInverse_left _ _ hi _ hb
  have hlog : Real.log (multiplier s a)≠0 := ne_of_lt (Real.log_neg hμ hμ1)
  have hper := regular_superfunction_imaginary_period s a r₀ hlog 0
  simp only [zero_add] at hper
  exact ⟨hz,hzero,hper.1.mpr hz,hper.2.trans hzero⟩

theorem lens_mem_unit_basin
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P : ℝ)
    (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P) (u : ℂ)
    (hu : u∈physicalLens a b θ Y) : u∈unitBasin s a := by
  refine ⟨lensControl_forward_limit e₁ e₂ A B Γ s a b θ Y η M P hc u hu,?_⟩
  obtain ⟨Z,hZ,rfl⟩ := hu
  intro k
  have hn := ((hc.true_orbits Z hZ).2.2.2.2.1 k).2.2.1
  have ha : ‖(a:ℂ)‖≤η/8 := by simpa only [Complex.norm_real,Real.norm_eq_abs] using hc.left_small
  exact (norm_sub_le _ _).trans_lt (by linarith [hn,ha,hc.radius_small])

theorem unit_basin_root (s a : ℝ) (hfa : unfolding s a=(a:ℂ)) : (a:ℂ)∈unitBasin s a := by
  have he : ∀k, orbit (a:ℂ) s k=(a:ℂ) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [orbit_succ,ih,hfa]
  refine ⟨?_,?_⟩
  · simpa only [he] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (a:ℂ)) atTop (𝓝 (a:ℂ)))
  · intro k
    simp only [he,sub_self,norm_zero]
    norm_num

theorem regular_superfunction_agrees_lens
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P r₀ : ℝ)
    (hs : 0<s) (hs1 : s<1) (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P)
    (hr₀ : r₀<a) (hd : a-r₀<1) (w : ℂ)
    (hw : w∈attractingImage A B Γ s a b θ Y r₀ (e₁ s) (e₂ s)) :
    w∈regularTimeDomain s a r₀ ∧
    regularSuperfunction s a r₀ w=regularAttractingInverse A B Γ s a b θ Y r₀ (e₁ s) (e₂ s) w := by
  have ha := real_root_gt_neg_one s a hc.left_fixed
  have hμ : 0<multiplier s a := by unfold multiplier; exact mul_pos (by linarith) (by linarith)
  have hμ1 : multiplier s a<1 := by unfold multiplier; nlinarith [hc.left_neg]
  obtain ⟨hi,_⟩ := koenigs_unit_basin_data s a hs.le hs1 ha hc.left_neg.le hc.left_fixed hμ hμ1
  have hb₀ := real_left_mem_unit_basin s a r₀ hs1 ha hc.left_fixed hμ hμ1 hr₀ hd
  have hKa : koenigsValue s a r₀≠0 := by
    intro he
    have hh := hi hb₀ (unit_basin_root s a hc.left_fixed)
      (by simpa only [koenigsValue_at_root s a hc.left_fixed] using he)
    have hrr : r₀=a := by exact_mod_cast hh
    linarith
  have hv := imageInverse_spec (normalizedAttracting A B Γ s a b θ r₀ (e₁ s) (e₂ s)) (strip θ (2*Y)) w hw
  have hu : regularAttractingInverse A B Γ s a b θ Y r₀ (e₁ s) (e₂ s) w∈unitBasin s a :=
    lens_mem_unit_basin e₁ e₂ A B Γ s a b θ Y η M P hc _
      ⟨_,inner_strip_subset θ Y (by linarith [hc.height_large]) hv.1,rfl⟩
  have hh := regular_attracting_inverse_koenigs e₁ e₂ A B Γ s a b θ Y η M P r₀ hs hs1 hc hr₀ w hw
  have he : koenigsValue s a (regularAttractingInverse A B Γ s a b θ Y r₀ (e₁ s) (e₂ s) w)=
      koenigsArgument s a r₀ w := by
    unfold koenigsArgument
    rw [hh]
    field_simp
  refine ⟨⟨_,hu,he⟩,?_⟩
  have hh := imageInverse_left _ _ hi _ hu
  rw [he] at hh
  exact hh

theorem regular_superfunction_actual_height
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P : ℝ)
    (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P) : koenigsHeight s a=height θ := by
  unfold koenigsHeight height
  rw [hc.theta_actual]
  ring

theorem actual_regular_transition_global
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P r₀ r : ℝ)
    (hs : 0<s) (hs1 : s<1) (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P)
    (hr₀ : r₀<a) (hd : a-r₀<1) (har : a<r) (hrb : r<b) (V : ℂ → ℂ)
    (hV : AnalyticOnNhd ℂ V (strip θ (3*Y+boundaryMargin P)))
    (hVs : ∀w∈strip θ (3*Y+boundaryMargin P), V w∈strip θ (3*Y) ∧
      repellingCoordinate A B Γ s a b θ (e₁ s) (e₂ s) (V w)=w)
    (w : ℂ) (hw : w∈Kneser.GrowingStripFourier.symmetricStrip (Kneser.NormalizedGrowingFourier.outerWidth θ Y P)) :
    let T := Kneser.ActualNormalizedGrowingTransition.transition A B Γ s a b θ r₀ r (e₁ s) (e₂ s) V
    T w∈regularTimeDomain s a r₀ ∧ T w-(height θ:ℂ)*Complex.I∈regularTimeDomain s a r₀ ∧
    regularSuperfunction s a r₀ (T w)=regularRepellingInverse A B Γ s a b θ r (e₁ s) (e₂ s) V w ∧
    regularSuperfunction s a r₀ (T w-(height θ:ℂ)*Complex.I)=regularRepellingInverse A B Γ s a b θ r (e₁ s) (e₂ s) V w := by
  dsimp only
  have hh := (actual_regular_inverse_charts e₁ e₂ A B Γ s a b θ Y η M P r₀ r hs1 hc har hrb V hV hVs).2.2.2 w hw
  have hR := regular_superfunction_agrees_lens e₁ e₂ A B Γ s a b θ Y η M P r₀ hs hs1 hc hr₀ hd _ hh.1
  have hlog : Real.log (multiplier s a)≠0 := by
    rw [←neg_ne_zero,hc.theta_actual.symm]
    exact ne_of_gt hc.theta_pos
  have hp := regular_superfunction_imaginary_period s a r₀ hlog
    (Kneser.ActualNormalizedGrowingTransition.transition A B Γ s a b θ r₀ r (e₁ s) (e₂ s) V w-(height θ:ℂ)*Complex.I)
  rw [regular_superfunction_actual_height e₁ e₂ A B Γ s a b θ Y η M P hc,sub_add_cancel] at hp
  exact ⟨hR.1,hp.1.mp hR.1,hR.2.trans hh.2,hp.2.symm.trans (hR.2.trans hh.2)⟩

theorem actual_anchor_domain_and_value
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P : ℝ)
    (hs : 0<s) (hs1 : s<1) (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P) :
    (0:ℂ)∈regularTimeDomain s a Kneser.RealNormalizationAnchor.realAnchor ∧
    regularSuperfunction s a Kneser.RealNormalizationAnchor.realAnchor 0=Kneser.RealNormalizationAnchor.realAnchor ∧
    (height θ:ℂ)*Complex.I∈regularTimeDomain s a Kneser.RealNormalizationAnchor.realAnchor ∧
    regularSuperfunction s a Kneser.RealNormalizationAnchor.realAnchor ((height θ:ℂ)*Complex.I)=Kneser.RealNormalizationAnchor.realAnchor := by
  have ha := real_root_gt_neg_one s a hc.left_fixed
  have hμ : 0<multiplier s a := by unfold multiplier; exact mul_pos (by linarith) (by linarith)
  have hμ1 : multiplier s a<1 := by unfold multiplier; nlinarith [hc.left_neg]
  have hr := Kneser.NormalizedGrowingFourier.actual_anchor_left_of_control e₁ e₂ A B Γ s a b θ Y η M P hc
  have hanchor : -1<Kneser.RealNormalizationAnchor.realAnchor := by
    unfold Kneser.RealNormalizationAnchor.realAnchor
    linarith [Real.exp_pos (-1)]
  have hd : a-Kneser.RealNormalizationAnchor.realAnchor<1 := by linarith [hc.left_neg]
  have hh := regular_superfunction_anchor s a Kneser.RealNormalizationAnchor.realAnchor hs.le hs1 ha hc.left_neg.le hc.left_fixed hμ hμ1 hr hd
  rwa [regular_superfunction_actual_height e₁ e₂ A B Γ s a b θ Y η M P hc] at hh

theorem actual_anchor_lens_agreement
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P : ℝ)
    (hs : 0<s) (hs1 : s<1) (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P)
    (w : ℂ) (hw : w∈attractingImage A B Γ s a b θ Y Kneser.RealNormalizationAnchor.realAnchor (e₁ s) (e₂ s)) :
    w∈regularTimeDomain s a Kneser.RealNormalizationAnchor.realAnchor ∧
    regularSuperfunction s a Kneser.RealNormalizationAnchor.realAnchor w=
      regularAttractingInverse A B Γ s a b θ Y Kneser.RealNormalizationAnchor.realAnchor (e₁ s) (e₂ s) w := by
  have hr := Kneser.NormalizedGrowingFourier.actual_anchor_left_of_control e₁ e₂ A B Γ s a b θ Y η M P hc
  have hanchor : -1<Kneser.RealNormalizationAnchor.realAnchor := by
    unfold Kneser.RealNormalizationAnchor.realAnchor
    linarith [Real.exp_pos (-1)]
  exact regular_superfunction_agrees_lens e₁ e₂ A B Γ s a b θ Y η M P _ hs hs1 hc hr (by linarith [hc.left_neg]) w hw

end Kneser.ActualRegularKoenigsInverse
end
