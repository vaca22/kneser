import Kneser.ActualBilateralGate
import Kneser.PreparedLocalAbel
import Kneser.ReflectedLocalAbel
import Mathlib.Analysis.Real.Pi.Bounds

/-!
The two coordinates of the same actual preparation satisfy genuine Abel
identities on compact overlap gates.  The inverse identity uses the proved
principal logarithm branch, not a formal inverse-map assumption.
-/

noncomputable section

namespace Kneser.ActualGateAbel

open Filter Set Metric Kneser.ExponentialUnfolding Kneser.ParabolicExponentialOrbit
open Kneser.RepellingExponentialOrbit Kneser.ReflectedOrbitChainCoefficient
open Kneser.PreparedActualFirstOrder Kneser.ReflectedPreparedFirstOrder
open Kneser.ParabolicFatouHolomorphic Kneser.ParabolicCoordinateJacobian
open Kneser.ActualDeepCoordinateData Kneser.ActualBilateralGate
open scoped Topology

def LocalAbel (Q : ℝ → ℂ → ℂ) (f : ℝ → ℂ → ℂ) (R : ℝ) : Prop :=
  ∀ v₀ : ℂ, R + 2 ≤ (inverseCoordinate v₀).re →
    ∃ ρ s₀ : ℝ, 0 < ρ ∧ 0 < s₀ ∧ ∀ s : ℝ, 0 < s → s < s₀ →
      ∀ v ∈ ball v₀ ρ, Q s (f s v) = Q s v + 1

structure LocalAbelData (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (R : ℝ) : Prop where
  attracting : LocalAbel (fun s u => actualPreparedCoordinate U H e₁ e₂ A B Γ u s)
    (fun s u => unfolding s u) R
  repelling : LocalAbel (fun s v => actualInversePreparedCoordinate U H e₁ e₂ A B Γ v s)
    (fun s v => reflectedInverse s v) R
  attracting_zero : ∀ u : ℂ, R + 2 ≤ (inverseCoordinate u).re →
    actualPreparedCoordinate U H e₁ e₂ A B Γ (unfolding 0 u) 0 =
      actualPreparedCoordinate U H e₁ e₂ A B Γ u 0 + 1
  repelling_zero : ∀ v : ℂ, R + 2 ≤ (inverseCoordinate v).re →
    actualInversePreparedCoordinate U H e₁ e₂ A B Γ (reflectedInverse 0 v) 0 =
      actualInversePreparedCoordinate U H e₁ e₂ A B Γ v 0 + 1

theorem local_abel_data_of_actual
    (U H e₁ e₂ A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F Γ : ℂ × ℂ → ℂ)
    (hdata : ActualPreparationData U H e₁ e₂ A B K F Γ) :
    ∃ R : ℝ, 0 < R ∧ LocalAbelData U H e₁ e₂ A B Γ R := by
  rcases hdata with ⟨hU, hU0, hUd, hH, hHne, hHlog, hA, hB, hA0, hB0, he₁, he₂,
    _hF, hΓ, hEven, hK0, hK, _hq, hroots, hfactor, hprepared, hresidue⟩
  have hcofactor := ExponentialMatrixDividedDifference.eventually_symmetricCofactor_factor
    hU hroots (PreparedLocalAbel.eventually_distinct_roots U hU hUd)
  obtain ⟨Ra, hRa, ha⟩ := PreparedLocalAbel.exists_local_prepared_abel
    U H e₁ e₂ A B K F Γ hU hU0 hH hHne hHlog hΓ.continuousAt hK
      (by rw [hK0]; norm_num) hfactor hcofactor hprepared hresidue
  obtain ⟨Rr, _hRr, hr⟩ := ReflectedLocalAbel.exists_local_inverse_prepared_abel
    U H e₁ e₂ A B K F Γ hU hU0 hH hHne hHlog hΓ.continuousAt hK
      (by rw [hK0]; norm_num) hfactor hcofactor hprepared hresidue
  obtain ⟨Rza, _hRza, hza⟩ := PreparedParabolicAbel.exists_prepared_parabolic_abel
    U H e₁ e₂ A B F Γ hU hU0 hH hHne hHlog he₁ he₂ hA hB hA0 hB0 hΓ
      (fun x v => hEven (x, v)) hcofactor hprepared hresidue
  obtain ⟨Rzr, _hRzr, hzr⟩ := ReflectedCanonicalAtZero.exists_reflected_parabolic_abel
    U H e₁ e₂ A B F Γ hU hU0 hH hHne hHlog he₁ he₂ hA hB hA0 hB0 hΓ
      (fun x v => hEven (x, v)) hcofactor hprepared hresidue
  let R := max Ra (max Rr (max Rza Rzr))
  have hRaR : Ra ≤ R := le_max_left _ _
  have hRrR : Rr ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have hRzaR : Rza ≤ R := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hRzrR : Rzr ≤ R := ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  refine ⟨R, hRa.trans_le hRaR, ?_, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨ρ, s₀, hρ, hs₀, h⟩ := ha v (by linarith)
    exact ⟨ρ, s₀, hρ, hs₀, fun s hs hss u hu => (h s hs hss u hu).2.2.2⟩
  · intro v hv
    obtain ⟨ρ, s₀, hρ, hs₀, h⟩ := hr v (by linarith)
    exact ⟨ρ, s₀, hρ, hs₀, fun s hs hss u hu => (h s hs hss u hu).2.2.2⟩
  · intro u hu
    exact (hza u (by linarith)).2.2.1
  · intro v hv
    exact (hzr v (by linarith)).2.2.1

theorem LocalAbelData.mono {U H e₁ e₂ A B : ℂ → ℂ} {Γ : ℂ × ℂ → ℂ} {R T : ℝ}
    (hd : LocalAbelData U H e₁ e₂ A B Γ R) (hRT : R ≤ T) :
    LocalAbelData U H e₁ e₂ A B Γ T := by
  exact ⟨fun u hu => hd.attracting u (by linarith),
    (fun v hv => hd.repelling v (by linarith)),
    (fun u hu => hd.attracting_zero u (by linarith)),
    (fun v hv => hd.repelling_zero v (by linarith))⟩

/-- Local parameter intervals and spatial neighborhoods give one interval
for a compact moving source set, using actual joint continuity. -/
theorem uniform_moving_local_property (P : ℝ → ℂ → Prop) (R : ℝ)
    (hP : ∀ v₀ : ℂ, R + 2 ≤ (inverseCoordinate v₀).re →
      ∃ ρ s₀ : ℝ, 0 < ρ ∧ 0 < s₀ ∧ ∀ s : ℝ, 0 < s → s < s₀ →
        ∀ v ∈ ball v₀ ρ, P s v)
    (W : ℂ × ℂ → ℂ) (S : Set ℂ) (hS : IsCompact S)
    (hW : ∀ u ∈ S, AnalyticAt ℂ W (0, u))
    (hw : ∀ u ∈ S, R + 2 ≤ (inverseCoordinate (W (0, u))).re) :
    ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ S, P s (W (s, u)) := by
  have hnear : ∀ᶠ s : ℝ in 𝓝 0, ∀ u ∈ S, 0 < s → P s (W (s, u)) := by
    apply hS.eventually_forall_of_forall_eventually
    intro u hu
    obtain ⟨ρ, s₀, hρ, hs₀, hlocal⟩ := hP _ (hw u hu)
    have hreal : ContinuousAt (fun p : ℝ × ℂ => W (p.1, p.2)) (0, u) :=
      (hW u hu).continuousAt.comp (f := fun p : ℝ × ℂ => ((p.1 : ℂ), p.2))
        ((Complex.continuous_ofReal.continuousAt.comp continuous_fst.continuousAt).prodMk continuous_snd.continuousAt)
    have hball := hreal.eventually (ball_mem_nhds _ hρ)
    have hsmall : ∀ᶠ p : ℝ × ℂ in 𝓝 (0, u), p.1 < s₀ :=
      continuous_fst.continuousAt.eventually (gt_mem_nhds hs₀)
    filter_upwards [hball, hsmall] with p hp hps hs
    exact hlocal p.1 hs hps _ hp
  have hpos : ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < s := self_mem_nhdsWithin
  filter_upwards [hnear.filter_mono nhdsWithin_le_nhds, hpos] with s hs hsp u hu
  exact hs u hu hsp

/-- The reflected principal inverse is the true backward branch on the
small actual gate, with logarithm branch conditions proved explicitly. -/
theorem reflectedInverse_forward (s u : ℂ) (hs : ‖s‖ ≤ 1 / 4) (hu : ‖u‖ ≤ 1 / 32) :
    reflectedInverse s (-unfolding s u) = -u := by
  have hsne : 1 - s ≠ 0 := by
    intro he
    rw [← sub_eq_zero.mp he] at hs
    norm_num at hs
  have hn : ‖1 - s‖ ≤ 1 + ‖s‖ := by
    simpa only [norm_one] using norm_sub_le (1 : ℂ) s
  have harg : ‖-s + (1 - s) * u‖ ≤ 1 / 2 := by
    have h := norm_add_le (-s) ((1 - s) * u)
    rw [norm_neg, norm_mul] at h
    have hm := mul_le_mul hn hu (norm_nonneg u) (by positivity : 0 ≤ 1 + ‖s‖)
    nlinarith
  have hi := Complex.abs_im_le_norm (-s + (1 - s) * u)
  have hlog := Complex.log_exp
    (show -Real.pi < (-s + (1 - s) * u).im by
      have h := (abs_le.mp (hi.trans harg)).1
      linarith [Real.pi_gt_three])
    (show (-s + (1 - s) * u).im ≤ Real.pi by
      have h := (abs_le.mp (hi.trans harg)).2
      linarith [Real.pi_gt_three])
  have he : 1 - -unfolding s u = Complex.exp (-s + (1 - s) * u) := by
    dsimp [unfolding]
    ring
  dsimp [reflectedInverse]
  rw [he, hlog]
  field_simp
  ring

theorem gate_length_mono {L : ℝ} {n N : ℕ} {u : ℂ} (hn : n ≤ N)
    (hu : u ∈ gate L N) : u ∈ gate L n := by
  refine ⟨hu.1, ?_⟩
  have h : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn
  linarith [hu.2]

theorem gate_norm_small {L : ℝ} (u : ℂ) (N : ℕ) (hu : u ∈ gate L N) : ‖u‖ ≤ 1 / 32 := by
  simpa only [Function.iterate_zero, id_eq] using
    ParabolicOverlapGate.finite_orbit_gate_norm parabolicMap
      Kneser.ParabolicExponentialOrbit.inverse_step_error_bound u N hu.2 0 (Nat.zero_le _)

def CompactGateAbel (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (L : ℝ) (N : ℕ) : Prop :=
  ∀ S : Set ℂ, IsCompact S → S ⊆ gate L N →
    ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ S,
      forwardCoordinate U H e₁ e₂ A B Γ N (unfolding s u) s =
        forwardCoordinate U H e₁ e₂ A B Γ N u s + 1 ∧
      backwardCoordinate U H e₁ e₂ A B Γ N (unfolding s u) s =
        backwardCoordinate U H e₁ e₂ A B Γ N u s + 1

theorem gate_abel_of_local_data
    (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (R L : ℝ)
    (hlocal : LocalAbelData U H e₁ e₂ A B Γ R) (n : ℕ)
    (hlen : R + L + 4 ≤ 3 * (n : ℝ) / 4) : CompactGateAbel U H e₁ e₂ A B Γ L (n + 1) := by
  intro S hS hgate
  have hNa : (R + 1) + L + 2 ≤ 3 * ((n + 1 : ℕ) : ℝ) / 4 := by push_cast; linarith
  have hNb : (R + 1) + L + 2 ≤ 3 * (n : ℝ) / 4 := by linarith
  have hA := uniform_moving_local_property
    (fun s v => actualPreparedCoordinate U H e₁ e₂ A B Γ (unfolding s v) s =
      actualPreparedCoordinate U H e₁ e₂ A B Γ v s + 1) R hlocal.attracting
    (fun p => orbit p.2 p.1 (n + 1)) S hS
    (fun u _ => ParabolicOverlapGate.analyticAt_forward_orbit_joint u 0 (n + 1))
    (fun u hu => by
      have h := gate_forward_entry u (n + 1) (R + 1) hNa (hgate hu)
      change R + 1 + 1 < _ at h
      linarith)
  have hB := uniform_moving_local_property
    (fun s v => actualInversePreparedCoordinate U H e₁ e₂ A B Γ (reflectedInverse s v) s =
      actualInversePreparedCoordinate U H e₁ e₂ A B Γ v s + 1) R hlocal.repelling
    (fun p => inverseOrbit (-p.2) p.1 n) S hS
    (fun u hu => analyticAt_backward_transport_joint u n (gate_length_mono (by omega) (hgate hu)))
    (fun u hu => by
      have h := gate_backward_entry u n (R + 1) hNb (gate_length_mono (by omega) (hgate hu))
      change R + 1 + 1 < _ at h
      linarith)
  have hpos : ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < s := self_mem_nhdsWithin
  have hsmall : ∀ᶠ s : ℝ in 𝓝[>] 0, s < 1 / 4 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hA, hB, hpos, hsmall] with s hsA hsB hsp hss u hu
  have hs : ‖(s : ℂ)‖ ≤ 1 / 4 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsp]
    exact hss.le
  have hbranch := reflectedInverse_forward (s : ℂ) u hs (gate_norm_small u (n + 1) (hgate hu))
  have hshift : inverseOrbit (-unfolding s u) s (n + 1) = inverseOrbit (-u) s n := by
    rw [← ReflectedLocalAbel.inverseOrbit_shift, hbranch]
  have ha := hsA u hu
  have hb := hsB u hu
  refine ⟨?_, ?_⟩
  · dsimp only [forwardCoordinate]
    rw [PreparedLocalAbel.orbit_shift, orbit_succ, ha]
    ring
  · dsimp only [backwardCoordinate]
    rw [hshift, inverseOrbit_succ, hb]
    ring

theorem gate_zero_abel_of_local_data
    (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (R L : ℝ)
    (hlocal : LocalAbelData U H e₁ e₂ A B Γ R) (n : ℕ)
    (hlen : R + L + 4 ≤ 3 * (n : ℝ) / 4) :
    ∀ u ∈ gate L (n + 1),
      forwardCoordinate U H e₁ e₂ A B Γ (n + 1) (unfolding 0 u) 0 =
        forwardCoordinate U H e₁ e₂ A B Γ (n + 1) u 0 + 1 ∧
      backwardCoordinate U H e₁ e₂ A B Γ (n + 1) (unfolding 0 u) 0 =
        backwardCoordinate U H e₁ e₂ A B Γ (n + 1) u 0 + 1 := by
  intro u hu
  have hNa : (R + 1) + L + 2 ≤ 3 * ((n + 1 : ℕ) : ℝ) / 4 := by push_cast; linarith
  have hNb : (R + 1) + L + 2 ≤ 3 * (n : ℝ) / 4 := by linarith
  have ha := hlocal.attracting_zero (orbit u 0 (n + 1))
    (by have h := gate_forward_entry u (n + 1) (R + 1) hNa hu; change R + 1 + 1 < _ at h; linarith)
  have hb := hlocal.repelling_zero (inverseOrbit (-u) 0 n)
    (by have h := gate_backward_entry u n (R + 1) hNb (gate_length_mono (by omega) hu)
        change R + 1 + 1 < _ at h; linarith)
  have hbranch := reflectedInverse_forward 0 u (by norm_num) (gate_norm_small u (n + 1) hu)
  have hshift : inverseOrbit (-unfolding 0 u) 0 (n + 1) = inverseOrbit (-u) 0 n := by
    rw [← ReflectedLocalAbel.inverseOrbit_shift, hbranch]
  refine ⟨?_, ?_⟩
  · dsimp only [forwardCoordinate]
    simp only [Complex.ofReal_zero]
    rw [PreparedLocalAbel.orbit_shift, orbit_succ, ha]
    ring
  · dsimp only [backwardCoordinate]
    simp only [Complex.ofReal_zero]
    rw [hshift, inverseOrbit_succ, hb]
    ring

/-- Same actual preparation, deep analytic data and both Abel identities,
at zero and on common compact positive-parameter intervals. -/
theorem exists_actual_deep_abel_data :
    ∃ U H e₁ e₂ A B : ℂ → ℂ, ∃ K : ℂ → ℂ → ℂ, ∃ F Γ : ℂ × ℂ → ℂ,
      ActualPreparationData U H e₁ e₂ A B K F Γ ∧
        ∃ R : ℝ, DeepCoordinateData U H e₁ e₂ A B Γ R ∧ LocalAbelData U H e₁ e₂ A B Γ R := by
  obtain ⟨U, H, e₁, e₂, A, B, K, F, Γ, hdata, R₁, hd⟩ := exists_actual_deep_coordinate_data
  obtain ⟨R₂, _hR₂, hl⟩ := local_abel_data_of_actual U H e₁ e₂ A B K F Γ hdata
  let R := max R₁ R₂
  exact ⟨U, H, e₁, e₂, A, B, K, F, Γ, hdata, R,
    hd.mono (le_max_left _ _), hl.mono (le_max_right _ _)⟩

theorem exists_actual_abel_bilateral_gate :
    ∃ U H e₁ e₂ A B : ℂ → ℂ, ∃ K : ℂ → ℂ → ℂ, ∃ F Γ : ℂ × ℂ → ℂ,
      ActualPreparationData U H e₁ e₂ A B K F Γ ∧
        ∃ R : ℝ, DeepCoordinateData U H e₁ e₂ A B Γ R ∧ LocalAbelData U H e₁ e₂ A B Γ R ∧
          ∀ L : ℝ, 0 < L → ∃ n : ℕ,
            BilateralGateData U H e₁ e₂ A B Γ R L (n + 1) ∧
            CompactGateAbel U H e₁ e₂ A B Γ L (n + 1) ∧
            ∀ u ∈ gate L (n + 1),
              forwardCoordinate U H e₁ e₂ A B Γ (n + 1) (unfolding 0 u) 0 =
                forwardCoordinate U H e₁ e₂ A B Γ (n + 1) u 0 + 1 ∧
              backwardCoordinate U H e₁ e₂ A B Γ (n + 1) (unfolding 0 u) 0 =
                backwardCoordinate U H e₁ e₂ A B Γ (n + 1) u 0 + 1 := by
  obtain ⟨U, H, e₁, e₂, A, B, K, F, Γ, hdata, R, hd, hl⟩ := exists_actual_deep_abel_data
  refine ⟨U, H, e₁, e₂, A, B, K, F, Γ, hdata, R, hd, hl, ?_⟩
  intro L _hL
  obtain ⟨n, hn⟩ := exists_nat_gt (4 * (R + L + 4) / 3)
  have hlen : R + L + 4 ≤ 3 * (n : ℝ) / 4 := by linarith
  have hN : R + L + 2 ≤ 3 * ((n + 1 : ℕ) : ℝ) / 4 := by push_cast; linarith
  exact ⟨n, bilateral_gate_data_of_deep U H e₁ e₂ A B Γ R hd (n + 1) hN,
    gate_abel_of_local_data U H e₁ e₂ A B Γ R L hl n hlen,
    gate_zero_abel_of_local_data U H e₁ e₂ A B Γ R L hl n hlen⟩

/-- Genuine Abel identities identify translation on an injective inverse
chart. The only chart conditions are the two inverse identities and the
membership of the actual next orbit point in the same injective chart. -/
theorem transition_translation_of_abel (P S f I : ℂ → ℂ) (V : Set ℂ) (z : ℂ)
    (hS : InjOn S V) (_hIz : I z ∈ V) (hIz1 : I (z + 1) ∈ V)
    (hf : f (I z) ∈ V) (hI : S (I z) = z) (hI1 : S (I (z + 1)) = z + 1)
    (hP : P (f (I z)) = P (I z) + 1) (hAbel : S (f (I z)) = S (I z) + 1) :
    P (I (z + 1)) = P (I z) + 1 ∧
      (P (I (z + 1)) - (z + 1)) = P (I z) - z := by
  have he : I (z + 1) = f (I z) := by
    apply hS hIz1 hf
    rw [hI1, hAbel, hI]
  rw [he, hP]
  exact ⟨rfl, by ring⟩

end Kneser.ActualGateAbel

end
