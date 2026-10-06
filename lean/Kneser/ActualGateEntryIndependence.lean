import Kneser.ActualNormalizationEntryIndependence

/-! True forward and principal backward transports on one overlap gate
are independent of the finite depth used to enter the prepared petals.
Backward joint analyticity is derived from the actual gate geometry. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Kneser.ActualGateEntryIndependence

open Filter Set Metric Kneser.ExponentialUnfolding Kneser.ParabolicExponentialOrbit
open Kneser.RepellingExponentialOrbit Kneser.ActualBilateralGate Kneser.ActualGateAbel
open Kneser.ReflectedPreparedFirstOrder Kneser.ActualNormalizationEntryIndependence
open scoped Topology

theorem backward_entry_depth (u : ℂ) (R : ℝ) (hR : 64 ≤ R) (M k : ℕ)
    (hentry : R + 2 ≤ (inverseCoordinate (inverseOrbit (-u) 0 M)).re) :
    R + 2 ≤ (inverseCoordinate (inverseOrbit (-u) 0 (M + k))).re := by
  rw [Kneser.HigherGateSeeds.inverseOrbit_add,
    Kneser.RepellingFatouCoordinate.inverseOrbit_zero_parameter]
  have h := Kneser.RepellingFatouCoordinate.inverse_iterate_re
    (inverseOrbit (-u) 0 M) (R + 2) (by linarith) hentry k
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  linarith

theorem backward_entry_zero_step (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (R : ℝ) (hl : LocalAbelData U H e₁ e₂ A B Γ R) (u : ℂ) (M : ℕ)
    (hentry : R + 2 ≤ (inverseCoordinate (inverseOrbit (-u) 0 M)).re) :
    backwardCoordinate U H e₁ e₂ A B Γ (M + 1) u 0 =
      backwardCoordinate U H e₁ e₂ A B Γ M u 0 := by
  have ha := hl.repelling_zero _ hentry
  simp only [backwardCoordinate, Complex.ofReal_zero, inverseOrbit_succ, ha,
    Nat.cast_add, Nat.cast_one]
  ring

theorem backward_entry_eventually_step_of_gate (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (R : ℝ) (hl : LocalAbelData U H e₁ e₂ A B Γ R) (u : ℂ) (M : ℕ) (L : ℝ)
    (hu : u ∈ gate L M)
    (hentry : R + 2 ≤ (inverseCoordinate (inverseOrbit (-u) 0 M)).re) :
    ∀ᶠ s : ℝ in 𝓝[>] 0, backwardCoordinate U H e₁ e₂ A B Γ (M + 1) u s =
      backwardCoordinate U H e₁ e₂ A B Γ M u s := by
  have he := uniform_moving_local_property
    (fun s v => actualInversePreparedCoordinate U H e₁ e₂ A B Γ (reflectedInverse s v) s =
      actualInversePreparedCoordinate U H e₁ e₂ A B Γ v s + 1) R hl.repelling
    (fun p => inverseOrbit (-p.2) p.1 M) ({u} : Set ℂ) isCompact_singleton
    (by intro v hv; rcases mem_singleton_iff.mp hv with rfl
        exact analyticAt_backward_transport_joint _ M hu)
    (by intro v hv; rcases mem_singleton_iff.mp hv with rfl; exact hentry)
  filter_upwards [he] with s hs
  have ha := hs u (mem_singleton u)
  simp only [backwardCoordinate, inverseOrbit_succ, ha, Nat.cast_add, Nat.cast_one]
  ring

theorem backward_entry_zero_add (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (R : ℝ) (hR : 64 ≤ R) (hl : LocalAbelData U H e₁ e₂ A B Γ R) (u : ℂ) (M k : ℕ)
    (hentry : R + 2 ≤ (inverseCoordinate (inverseOrbit (-u) 0 M)).re) :
    backwardCoordinate U H e₁ e₂ A B Γ (M + k) u 0 =
      backwardCoordinate U H e₁ e₂ A B Γ M u 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    exact (backward_entry_zero_step U H e₁ e₂ A B Γ R hl u (M + k)
      (backward_entry_depth u R hR M k hentry)).trans ih

theorem backward_entry_eventually_add_of_gate (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (R : ℝ) (hR : 64 ≤ R) (hl : LocalAbelData U H e₁ e₂ A B Γ R) (u : ℂ) (M k : ℕ) (L : ℝ)
    (hu : u ∈ gate L (M + k))
    (hentry : R + 2 ≤ (inverseCoordinate (inverseOrbit (-u) 0 M)).re) :
    ∀ᶠ s : ℝ in 𝓝[>] 0, backwardCoordinate U H e₁ e₂ A B Γ (M + k) u s =
      backwardCoordinate U H e₁ e₂ A B Γ M u s := by
  revert hu
  induction k with
  | zero => exact fun _ => Eventually.of_forall (fun _ => by simp)
  | succ k ih =>
    intro hu
    have hug : u ∈ gate L (M + k) := gate_length_mono (by omega) hu
    have hs := backward_entry_eventually_step_of_gate U H e₁ e₂ A B Γ R hl u (M + k) L hug
      (backward_entry_depth u R hR M k hentry)
    filter_upwards [hs, ih hug] with s hs hi
    exact hs.trans hi

theorem backward_entry_independent_of_gate (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (R : ℝ) (hR : 64 ≤ R) (hl : LocalAbelData U H e₁ e₂ A B Γ R)
    (u : ℂ) (M M' : ℕ) (L : ℝ) (hu : u ∈ gate L (max M M'))
    (hentry : R + 2 ≤ (inverseCoordinate (inverseOrbit (-u) 0 M)).re)
    (hentry' : R + 2 ≤ (inverseCoordinate (inverseOrbit (-u) 0 M')).re) :
    backwardCoordinate U H e₁ e₂ A B Γ M u 0 = backwardCoordinate U H e₁ e₂ A B Γ M' u 0 ∧
    ∀ᶠ s : ℝ in 𝓝[>] 0, backwardCoordinate U H e₁ e₂ A B Γ M u s =
      backwardCoordinate U H e₁ e₂ A B Γ M' u s := by
  rcases le_total M M' with hle | hle
  · have hg : u ∈ gate L (M + (M' - M)) := by
      simpa only [Nat.add_sub_of_le hle, max_eq_right hle] using hu
    have h0 := backward_entry_zero_add U H e₁ e₂ A B Γ R hR hl u M (M' - M) hentry
    have he := backward_entry_eventually_add_of_gate U H e₁ e₂ A B Γ R hR hl u M (M' - M) L hg hentry
    rw [Nat.add_sub_of_le hle] at h0 he
    exact ⟨h0.symm, he.mono fun _ hs => hs.symm⟩
  · have hg : u ∈ gate L (M' + (M - M')) := by
      simpa only [Nat.add_sub_of_le hle, max_eq_left hle] using hu
    have h0 := backward_entry_zero_add U H e₁ e₂ A B Γ R hR hl u M' (M - M') hentry'
    have he := backward_entry_eventually_add_of_gate U H e₁ e₂ A B Γ R hR hl u M' (M - M') L hg hentry'
    rw [Nat.add_sub_of_le hle] at h0 he
    exact ⟨h0, he⟩

/-- Gate geometry supplies every entry and every backward analyticity
condition; the only coordinate input is the actual local Abel data. -/
theorem gate_coordinate_entry_independent (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (R : ℝ) (hR : 64 ≤ R) (hl : LocalAbelData U H e₁ e₂ A B Γ R)
    (L : ℝ) (M M' : ℕ)
    (hM : R + L + 3 ≤ 3 * (M : ℝ) / 4) (hM' : R + L + 3 ≤ 3 * (M' : ℝ) / 4)
    (u : ℂ) (hu : u ∈ gate L (max M M')) :
    (forwardCoordinate U H e₁ e₂ A B Γ M u 0 = forwardCoordinate U H e₁ e₂ A B Γ M' u 0 ∧
      backwardCoordinate U H e₁ e₂ A B Γ M u 0 = backwardCoordinate U H e₁ e₂ A B Γ M' u 0) ∧
    ∀ᶠ s : ℝ in 𝓝[>] 0,
      forwardCoordinate U H e₁ e₂ A B Γ M u s = forwardCoordinate U H e₁ e₂ A B Γ M' u s ∧
      backwardCoordinate U H e₁ e₂ A B Γ M u s = backwardCoordinate U H e₁ e₂ A B Γ M' u s := by
  have huM : u ∈ gate L M := gate_length_mono (le_max_left _ _) hu
  have huM' : u ∈ gate L M' := gate_length_mono (le_max_right _ _) hu
  have haf := gate_forward_entry u M (R + 1) (by linarith) huM
  have haf' := gate_forward_entry u M' (R + 1) (by linarith) huM'
  have har := gate_backward_entry u M (R + 1) (by linarith) huM
  have har' := gate_backward_entry u M' (R + 1) (by linarith) huM'
  change R + 1 + 1 < _ at haf haf' har har'
  obtain ⟨hfa, hfe⟩ := forward_entry_independent U H e₁ e₂ A B Γ R hR hl u M M' (by linarith) (by linarith)
  obtain ⟨hra, hre⟩ := backward_entry_independent_of_gate U H e₁ e₂ A B Γ R hR hl u M M' L hu
    (by linarith) (by linarith)
  exact ⟨⟨hfa, hra⟩, hfe.and hre⟩

end Kneser.ActualGateEntryIndependence

end
