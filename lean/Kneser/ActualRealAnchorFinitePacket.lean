import Kneser.ActualRealAnchorHigherGate
import Kneser.ActualAnchorFixedEntry
import Kneser.ActualQuantitativeGateTransition

/-! The actual real-anchor normalized coordinate has holomorphic orbit
coefficients, exact baseline and explicit first correction, with every
compact-uniform integer remainder. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Kneser.ActualRealAnchorFinitePacket

open Filter Set Kneser.ActualRealAnchorHigherGate Kneser.ActualHigherFinitePacket
open Kneser.FiniteExpansionHolomorphy Kneser.ActualBilateralGate
open Kneser.CommonQuadraticBaseline Kneser.ActualGateAbel Kneser.ActualDeepCoordinateData
open Kneser.ExponentialUnfolding Kneser.ParabolicExponentialOrbit
open Kneser.ReflectedOrbitChainCoefficient Kneser.RealNormalizationAnchor
open Kneser.ActualNormalizationAnchorExpansion Kneser.QuantitativeHornExpansion
open Kneser.FirstOrderFiniteConsistency Kneser.HigherOrderCutoff
open scoped Topology

def firstCorrection (U H A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ) (N M : ℕ) (u : ℂ) : ℂ :=
  forwardCoefficient U H (first (e 1)) (second (e 1)) A B (Γ 1) N u -
    anchorCoefficient U H (first (e 1)) (second (e 1)) A B (Γ 1) M

theorem real_anchor_packet (U H A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F : ℂ × ℂ → ℂ)
    (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (hdata : ActualPreparationData U H (first (e 1)) (second (e 1)) A B K F (Γ 1))
    (hprep : ∀ n, Kneser.CommonPreparedFamily.Prepared A B F n (e n) (Γ n))
    (R : ℝ) (hR : 64 ≤ R)
    (hlocal : LocalAbelData U H (first (e 1)) (second (e 1)) A B (Γ 1) R)
    (hdeep : DeepCoordinateData U H (first (e 1)) (second (e 1)) A B (Γ 1) R)
    (N M : ℕ) (hN : R + 64 + 4 ≤ 3 * (N : ℝ) / 4)
    (hg : BilateralGateData U H (first (e 1)) (second (e 1)) A B (Γ 1) R 64 N)
    (hentry : R + 2 ≤ (inverseCoordinate (orbit normalizationAnchor 0 M)).re)
    (m : ℕ) (hm : 1 ≤ m) :
    ∃ n L : ℕ,
      NormalizedFiniteData (normalizedCoordinate U H A B e Γ N M)
        (coefficient U H A B e Γ n N M L) (firstCorrection U H A B e Γ N M)
        m (interior (gate 64 N)) ∧
      ∀ u ∈ gate 64 N, ∀ j ≤ m + 1,
        Summable (fun k => ‖termCoefficient
          (Kneser.HigherMovingOrbitDiscs.descendedTerm A B (Γ n) (n + 1)
            (Kneser.HigherGateSeeds.forwardSeed N L) u) j k‖) ∧
        Summable (fun k => ‖termCoefficient
          (Kneser.HigherMovingOrbitDiscs.descendedTerm A B (Γ n) (n + 1) (anchorSeed M L) u) j k‖) := by
  let n := (m + 1) * (m + 1) + (m + 1)
  obtain ⟨L, hL⟩ := finite_real_anchor_expansion U H A B K F e Γ hdata hprep R hR hlocal N M hN hentry
    m n (by rfl)
  let f := normalizedCoordinate U H A B e Γ N M
  let c := coefficient U H A B e Γ n N M L
  have hreg (S : Set ℂ) (hS : IsCompact S) (hSg : S ⊆ gate 64 N) :
      ∀ᶠ s : ℝ in 𝓝[>] 0, AnalyticOnNhd ℂ (f s) S := by
    filter_upwards [hg.positive S hS hSg] with s hs u hu
    exact (hs u hu).1.sub analyticAt_const
  have hbounded (S : Set ℂ) (hS : IsCompact S) (hSg : S ⊆ gate 64 N) :
      ∀ᶠ s : ℝ in 𝓝[>] 0, ∃ M : ℝ, ∀ u ∈ S, ‖f s u‖ ≤ M := by
    filter_upwards [hreg S hS hSg] with s hs
    exact hS.exists_bound_of_continuousOn hs.continuousOn
  have hInt (S : Set ℂ) (hS : IsCompact S) (hSg : S ⊆ gate 64 N) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ S,
        ‖f s u - complexPolynomial c m (s : ℂ) u‖ ≤ C * s ^ (m + 1) := by
    obtain ⟨_hsum, C, hC, hb⟩ := hL S hS hSg
    obtain ⟨D, hD, hd⟩ := Kneser.AsymptoticCoefficientUniqueness.truncate_one_uniform f c m S C
      (Kneser.AsymptoticBalance.gamma (m + 1) (n + 1)) hC
      (Kneser.AsymptoticBalance.gamma_pos _ _ (by dsimp [n]; omega)) hb (hbounded S hS hSg)
    exact ⟨D, hD, by simpa only [show (m : ℝ) + 1 = ((m + 1 : ℕ) : ℝ) by norm_cast, Real.rpow_natCast,
      complexPolynomial, Kneser.AsymptoticCoefficientUniqueness.polynomial] using hd⟩
  have hall (j : ℕ) (hj : j ≤ m) (S : Set ℂ) (hS : IsCompact S) (hSg : S ⊆ gate 64 N) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ S,
        ‖f s u - complexPolynomial c j (s : ℂ) u‖ ≤ C * s ^ (j + 1) := by
    obtain ⟨C, hC, hb⟩ := hInt S hS hSg
    obtain ⟨D, hD, hd⟩ := Kneser.AsymptoticCoefficientUniqueness.truncate_uniform_integer f c m j hj S C hC
      (by simpa only [show (m : ℝ) + 1 = ((m + 1 : ℕ) : ℝ) by norm_cast, Real.rpow_natCast,
        complexPolynomial, Kneser.AsymptoticCoefficientUniqueness.polynomial] using hb) (hbounded S hS hSg)
    exact ⟨D, hD, by simpa only [show (j : ℝ) + 1 = ((j + 1 : ℕ) : ℝ) by norm_cast, Real.rpow_natCast,
      complexPolynomial, Kneser.AsymptoticCoefficientUniqueness.polynomial] using hd⟩
  have hca : ∀ j ≤ m, AnalyticOnNhd ℂ (c j) (interior (gate 64 N)) :=
    coefficients_analyticOnNhd f c m _ isOpen_interior
      (fun S hS hSg => hreg S hS (hSg.trans interior_subset))
      (fun j hj S hS hSg => by
        obtain ⟨C, _hC, hb⟩ := hall j hj S hS (hSg.trans interior_subset)
        exact ⟨C, hb⟩)
  have hanchor := Kneser.ActualAnchorFixedEntry.anchor_expansion_of_entry
    U H (first (e 1)) (second (e 1)) A B (Γ 1) R hdeep M
      (show orbit normalizationAnchor 0 M ∈ Kneser.ParabolicFatouHolomorphic.petal (R + 1) from by
        change R + 1 < _; linarith)
  have hlow (u : ℂ) (hu : u ∈ interior (gate 64 N)) : c 0 u = f 0 u ∧
      c 1 u = firstCorrection U H A B e Γ N M u := by
    have hsingleton : ({u} : Set ℂ) ⊆ gate 64 N := by simpa using interior_subset hu
    obtain ⟨C, hC, hb⟩ := hInt {u} isCompact_singleton hsingleton
    obtain ⟨D, hD, hd⟩ := hg.uniform {u} isCompact_singleton hsingleton
    obtain ⟨E, hE, he⟩ := Kneser.QuantitativeGateTransition.uniform_subtract_normalization
      (fun s u => forwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N u s)
      (forwardCoefficient U H (first (e 1)) (second (e 1)) A B (Γ 1) N)
      {u} (6 / 5) D (anchorValue U H (first (e 1)) (second (e 1)) A B (Γ 1) M)
      (anchorCoefficient U H (first (e 1)) (second (e 1)) A B (Γ 1) M) hD
      (hd.mono fun s hs v hv => (hs v hv).1) hanchor
    exact first_coefficients_of_integer_expansion (fun s => f s u) (fun j => c j u) m hm C hC
      (by simpa only [show (m : ℝ) + 1 = ((m + 1 : ℕ) : ℝ) by norm_cast, Real.rpow_natCast,
        complexPolynomial, Kneser.AsymptoticCoefficientUniqueness.polynomial] using hb.mono (fun s hs => hs u (by simp)))
      (firstCorrection U H A B e Γ N M u) (6 / 5) (by norm_num)
      ⟨E, hE, he.mono fun s hs => hs u (by simp)⟩
  refine ⟨n, L, ⟨hca, hlow, fun j hj S hS hSg => hall j hj S hS (hSg.trans interior_subset)⟩, ?_⟩
  intro u hu j hj
  exact (hL {u} isCompact_singleton (by simpa using hu)).1 u (by simp) j hj

end Kneser.ActualRealAnchorFinitePacket
