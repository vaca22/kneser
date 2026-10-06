import Kneser.ActualAnchorFixedEntry
import Kneser.ActualGateAbel
import Kneser.HigherGateSeeds

/-! Genuine finite entry times do not change the prepared attracting
coordinate transported back to its source. This applies in particular
to the real normalization anchor. The explicit first anchor correction
is independent of entry time by uniqueness of its actual right derivative. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace Kneser.ActualNormalizationEntryIndependence

open Filter Set Metric Kneser.ExponentialUnfolding Kneser.ParabolicExponentialOrbit
open Kneser.ActualBilateralGate Kneser.ActualGateAbel Kneser.PreparedActualFirstOrder
open Kneser.ActualDeepCoordinateData Kneser.ActualNormalizationAnchorExpansion
open Kneser.RealNormalizationAnchor Kneser.QuantitativeHornExpansion
open scoped Topology

theorem forward_entry_depth (u : ℂ) (R : ℝ) (hR : 64 ≤ R) (M k : ℕ)
    (hentry : R + 2 ≤ (inverseCoordinate (orbit u 0 M)).re) :
    R + 2 ≤ (inverseCoordinate (orbit u 0 (M + k))).re := by
  rw [Kneser.HigherGateSeeds.orbit_add, unfolding_orbit_zero_eq_iterate]
  have h := iterate_inverse_re (orbit u 0 M) (by linarith) k
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  linarith

theorem forward_entry_zero_step (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (R : ℝ) (hl : LocalAbelData U H e₁ e₂ A B Γ R) (u : ℂ) (M : ℕ)
    (hentry : R + 2 ≤ (inverseCoordinate (orbit u 0 M)).re) :
    forwardCoordinate U H e₁ e₂ A B Γ (M + 1) u 0 =
      forwardCoordinate U H e₁ e₂ A B Γ M u 0 := by
  have ha := hl.attracting_zero _ hentry
  simp only [forwardCoordinate, Complex.ofReal_zero, orbit_succ, ha, Nat.cast_add, Nat.cast_one]
  ring

theorem forward_entry_eventually_step (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (R : ℝ) (hl : LocalAbelData U H e₁ e₂ A B Γ R) (u : ℂ) (M : ℕ)
    (hentry : R + 2 ≤ (inverseCoordinate (orbit u 0 M)).re) :
    ∀ᶠ s : ℝ in 𝓝[>] 0, forwardCoordinate U H e₁ e₂ A B Γ (M + 1) u s =
      forwardCoordinate U H e₁ e₂ A B Γ M u s := by
  have he := uniform_moving_local_property
    (fun s v => actualPreparedCoordinate U H e₁ e₂ A B Γ (unfolding s v) s =
      actualPreparedCoordinate U H e₁ e₂ A B Γ v s + 1) R hl.attracting
    (fun p => orbit p.2 p.1 M) ({u} : Set ℂ) isCompact_singleton
    (fun v _ => Kneser.ParabolicOverlapGate.analyticAt_forward_orbit_joint v 0 M)
    (by intro v hv; rcases mem_singleton_iff.mp hv with rfl; exact hentry)
  filter_upwards [he] with s hs
  have ha := hs u (mem_singleton u)
  simp only [forwardCoordinate, orbit_succ, ha, Nat.cast_add, Nat.cast_one]
  ring

theorem forward_entry_zero_add (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (R : ℝ) (hR : 64 ≤ R) (hl : LocalAbelData U H e₁ e₂ A B Γ R) (u : ℂ) (M k : ℕ)
    (hentry : R + 2 ≤ (inverseCoordinate (orbit u 0 M)).re) :
    forwardCoordinate U H e₁ e₂ A B Γ (M + k) u 0 =
      forwardCoordinate U H e₁ e₂ A B Γ M u 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    exact (forward_entry_zero_step U H e₁ e₂ A B Γ R hl u (M + k)
      (forward_entry_depth u R hR M k hentry)).trans ih

theorem forward_entry_eventually_add (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (R : ℝ) (hR : 64 ≤ R) (hl : LocalAbelData U H e₁ e₂ A B Γ R) (u : ℂ) (M k : ℕ)
    (hentry : R + 2 ≤ (inverseCoordinate (orbit u 0 M)).re) :
    ∀ᶠ s : ℝ in 𝓝[>] 0, forwardCoordinate U H e₁ e₂ A B Γ (M + k) u s =
      forwardCoordinate U H e₁ e₂ A B Γ M u s := by
  induction k with
  | zero => exact Eventually.of_forall (fun _ => by simp)
  | succ k ih =>
    have hs := forward_entry_eventually_step U H e₁ e₂ A B Γ R hl u (M + k)
      (forward_entry_depth u R hR M k hentry)
    filter_upwards [hs, ih] with s hs hi
    exact hs.trans hi

theorem forward_entry_independent (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (R : ℝ) (hR : 64 ≤ R) (hl : LocalAbelData U H e₁ e₂ A B Γ R) (u : ℂ) (M M' : ℕ)
    (hentry : R + 2 ≤ (inverseCoordinate (orbit u 0 M)).re)
    (hentry' : R + 2 ≤ (inverseCoordinate (orbit u 0 M')).re) :
    forwardCoordinate U H e₁ e₂ A B Γ M u 0 = forwardCoordinate U H e₁ e₂ A B Γ M' u 0 ∧
    ∀ᶠ s : ℝ in 𝓝[>] 0, forwardCoordinate U H e₁ e₂ A B Γ M u s =
      forwardCoordinate U H e₁ e₂ A B Γ M' u s := by
  rcases le_total M M' with hle | hle
  · have h0 := forward_entry_zero_add U H e₁ e₂ A B Γ R hR hl u M (M' - M) hentry
    have he := forward_entry_eventually_add U H e₁ e₂ A B Γ R hR hl u M (M' - M) hentry
    rw [Nat.add_sub_of_le hle] at h0 he
    exact ⟨h0.symm, he.mono fun _ hs => hs.symm⟩
  · have h0 := forward_entry_zero_add U H e₁ e₂ A B Γ R hR hl u M' (M - M') hentry'
    have he := forward_entry_eventually_add U H e₁ e₂ A B Γ R hR hl u M' (M - M') hentry'
    rw [Nat.add_sub_of_le hle] at h0 he
    exact ⟨h0, he⟩

theorem anchorValue_entry_independent (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (R : ℝ) (hR : 64 ≤ R) (hl : LocalAbelData U H e₁ e₂ A B Γ R) (M M' : ℕ)
    (hentry : R + 2 ≤ (inverseCoordinate (orbit normalizationAnchor 0 M)).re)
    (hentry' : R + 2 ≤ (inverseCoordinate (orbit normalizationAnchor 0 M')).re) :
    anchorValue U H e₁ e₂ A B Γ M 0 = anchorValue U H e₁ e₂ A B Γ M' 0 ∧
    ∀ᶠ s : ℝ in 𝓝[>] 0, anchorValue U H e₁ e₂ A B Γ M s =
      anchorValue U H e₁ e₂ A B Γ M' s :=
  forward_entry_independent U H e₁ e₂ A B Γ R hR hl normalizationAnchor M M' hentry hentry'

theorem anchorCoefficient_entry_independent (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (R : ℝ) (hR : 64 ≤ R) (hl : LocalAbelData U H e₁ e₂ A B Γ R)
    (hd : DeepCoordinateData U H e₁ e₂ A B Γ R) (M M' : ℕ)
    (hentry : R + 2 ≤ (inverseCoordinate (orbit normalizationAnchor 0 M)).re)
    (hentry' : R + 2 ≤ (inverseCoordinate (orbit normalizationAnchor 0 M')).re) :
    anchorCoefficient U H e₁ e₂ A B Γ M = anchorCoefficient U H e₁ e₂ A B Γ M' := by
  have hM : orbit normalizationAnchor 0 M ∈ Kneser.ParabolicFatouHolomorphic.petal (R + 1) := by
    change R + 1 < _
    linarith
  have hM' : orbit normalizationAnchor 0 M' ∈ Kneser.ParabolicFatouHolomorphic.petal (R + 1) := by
    change R + 1 < _
    linarith
  have hder := (Kneser.ActualAnchorFixedEntry.anchor_expansion_of_entry
    U H e₁ e₂ A B Γ R hd M hM).hasDerivWithinAt (by norm_num : (1 : ℝ) < 6 / 5)
  have hder' := (Kneser.ActualAnchorFixedEntry.anchor_expansion_of_entry
    U H e₁ e₂ A B Γ R hd M' hM').hasDerivWithinAt (by norm_num : (1 : ℝ) < 6 / 5)
  obtain ⟨hzero, heq⟩ := anchorValue_entry_independent U H e₁ e₂ A B Γ R hR hl M M' hentry hentry'
  have hsame : HasDerivWithinAt (anchorValue U H e₁ e₂ A B Γ M)
      (anchorCoefficient U H e₁ e₂ A B Γ M') (Ioi 0) 0 :=
    (hder'.mono Ioi_subset_Ici_self).congr_of_eventuallyEq heq hzero
  exact ((hder.mono Ioi_subset_Ici_self).derivWithin (uniqueDiffWithinAt_Ioi 0)).symm.trans
    (hsame.derivWithin (uniqueDiffWithinAt_Ioi 0))

end Kneser.ActualNormalizationEntryIndependence

end
