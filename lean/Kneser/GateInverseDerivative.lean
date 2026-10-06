import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# One-sided differentiation of a gate inverse and transition composition

The changing family needs only a uniform right-sided first expansion along
the moving branch. A genuine inverse-function theorem is applied to the fixed
spatial map at parameter zero. The derivative of the moving inverse is proved
from its inverse equation and continuity; it is not an assumption.
-/

set_option autoImplicit false
noncomputable section

namespace Kneser.GateInverseDerivative

open Filter
open scoped Topology

/-- The fixed map evaluated at a moving inverse has derivative minus the
parameter correction, using only a one-sided expansion of the changing map. -/
theorem hasDerivWithinAt_fixedMap_of_inverse_expansion
    (S : ℝ → ℂ → ℂ) (v : ℝ → ℂ) (D : ℂ → ℂ) (ε : ℝ → ℝ)
    (hInv : ∀ᶠ s in nhdsWithin 0 (Set.Ioi 0), S s (v s) = S 0 (v 0))
    (hD : Tendsto (fun s => D (v s)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (D (v 0))))
    (hε : Tendsto ε (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hRem : ∀ᶠ s in nhdsWithin 0 (Set.Ioi 0),
      ‖S s (v s) - S 0 (v s) - (s : ℂ) * D (v s)‖ ≤ |s| * ε s) :
    HasDerivWithinAt (fun s => S 0 (v s)) (-D (v 0)) (Set.Ici 0) 0 := by
  apply HasDerivWithinAt.Ici_of_Ioi
  rw [hasDerivWithinAt_iff_tendsto]
  apply squeeze_zero' (g := fun s => ε s + ‖D (v 0) - D (v s)‖)
  · exact Eventually.of_forall (fun s => mul_nonneg (inv_nonneg.mpr (norm_nonneg _))
      (norm_nonneg _))
  · filter_upwards [hInv, hRem, self_mem_nhdsWithin] with s hs hrem hpos
    have hsp : 0 < s := hpos
    have habs : 0 < |s| := abs_pos.mpr hsp.ne'
    have heq : S 0 (v s) - S 0 (v 0) - (s : ℂ) * (-D (v 0)) =
        -(S s (v s) - S 0 (v s) - (s : ℂ) * D (v s)) +
          (s : ℂ) * (D (v 0) - D (v s)) := by
      rw [hs]
      ring
    have hbound : ‖S 0 (v s) - S 0 (v 0) - (s : ℂ) * (-D (v 0))‖ ≤
        |s| * (ε s + ‖D (v 0) - D (v s)‖) := by
      rw [heq]
      calc
        _ ≤ ‖-(S s (v s) - S 0 (v s) - (s : ℂ) * D (v s))‖ +
            ‖(s : ℂ) * (D (v 0) - D (v s))‖ := norm_add_le _ _
        _ = ‖S s (v s) - S 0 (v s) - (s : ℂ) * D (v s)‖ +
            |s| * ‖D (v 0) - D (v s)‖ := by
          rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ |s| * ε s + |s| * ‖D (v 0) - D (v s)‖ := add_le_add hrem le_rfl
        _ = _ := by ring
    simp only [sub_zero, Complex.real_smul, Real.norm_eq_abs]
    calc
      _ ≤ |s|⁻¹ * (|s| * (ε s + ‖D (v 0) - D (v s)‖)) :=
        mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr habs.le)
      _ = _ := by field_simp
  · simpa using hε.add ((tendsto_const_nhds (x := D (v 0))).sub hD).norm

/-- Genuine inverse differentiation: the branch derivative is a conclusion
from its inverse equation, continuity, and the fixed map's nonzero derivative. -/
theorem hasDerivWithinAt_inverse_branch
    (S : ℝ → ℂ → ℂ) (v : ℝ → ℂ) (D : ℂ → ℂ) (ε : ℝ → ℝ) (B : ℂ)
    (hS0 : HasStrictDerivAt (S 0) B (v 0)) (hB : B ≠ 0)
    (hv : Tendsto v (nhdsWithin 0 (Set.Ioi 0)) (nhds (v 0)))
    (hInv : ∀ᶠ s in nhdsWithin 0 (Set.Ioi 0), S s (v s) = S 0 (v 0))
    (hD : Tendsto (fun s => D (v s)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (D (v 0))))
    (hε : Tendsto ε (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hRem : ∀ᶠ s in nhdsWithin 0 (Set.Ioi 0),
      ‖S s (v s) - S 0 (v s) - (s : ℂ) * D (v s)‖ ≤ |s| * ε s) :
    HasDerivWithinAt v (-D (v 0) / B) (Set.Ici 0) 0 := by
  let g := hS0.localInverse (S 0) B (v 0) hB
  have hg : HasDerivAt g B⁻¹ (S 0 (v 0)) := (hS0.to_localInverse hB).hasDerivAt
  have hw := (hasDerivWithinAt_fixedMap_of_inverse_expansion S v D ε hInv hD hε hRem).Ioi_of_Ici
  have hcomp := hg.comp_hasDerivWithinAt 0 hw
  have hleft : ∀ᶠ w in nhds (v 0), g (S 0 w) = w := hS0.eventually_left_inverse hB
  have hvEq : v =ᶠ[nhdsWithin 0 (Set.Ioi 0)] (fun s => g (S 0 (v s))) :=
    (hv.eventually hleft).mono (fun s hs => hs.symm)
  have hzero : v 0 = g (S 0 (v 0)) := hleft.self_of_nhds.symm
  have h := hcomp.congr_of_eventuallyEq hvEq hzero
  apply HasDerivWithinAt.Ici_of_Ioi
  apply h.congr_deriv
  simp only [div_eq_mul_inv, mul_comm]

/-- Differentiation of a moving composition from its uniform one-sided
parameter expansion and the fixed spatial derivative. -/
theorem hasDerivWithinAt_moving_composition
    (A : ℝ → ℂ → ℂ) (v : ℝ → ℂ) (D : ℂ → ℂ) (ε : ℝ → ℝ) (B dv : ℂ)
    (hA0 : HasDerivAt (A 0) B (v 0))
    (hv : HasDerivWithinAt v dv (Set.Ici 0) 0)
    (hD : Tendsto (fun s => D (v s)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (D (v 0))))
    (hε : Tendsto ε (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hRem : ∀ᶠ s in nhdsWithin 0 (Set.Ioi 0),
      ‖A s (v s) - A 0 (v s) - (s : ℂ) * D (v s)‖ ≤ |s| * ε s) :
    HasDerivWithinAt (fun s => A s (v s)) (D (v 0) + B * dv) (Set.Ici 0) 0 := by
  have hparam : HasDerivWithinAt (fun s => A s (v s) - A 0 (v s))
      (D (v 0)) (Set.Ioi 0) 0 := by
    rw [hasDerivWithinAt_iff_tendsto]
    apply squeeze_zero' (g := fun s => ε s + ‖D (v s) - D (v 0)‖)
    · exact Eventually.of_forall (fun s => mul_nonneg (inv_nonneg.mpr (norm_nonneg _))
        (norm_nonneg _))
    · filter_upwards [hRem, self_mem_nhdsWithin] with s hrem hpos
      have hsp : 0 < s := hpos
      have habs : 0 < |s| := abs_pos.mpr hsp.ne'
      have heq : A s (v s) - A 0 (v s) - (s : ℂ) * D (v 0) =
          (A s (v s) - A 0 (v s) - (s : ℂ) * D (v s)) +
            (s : ℂ) * (D (v s) - D (v 0)) := by ring
      have hbound : ‖A s (v s) - A 0 (v s) - (s : ℂ) * D (v 0)‖ ≤
          |s| * (ε s + ‖D (v s) - D (v 0)‖) := by
        rw [heq]
        calc
          _ ≤ ‖A s (v s) - A 0 (v s) - (s : ℂ) * D (v s)‖ +
              ‖(s : ℂ) * (D (v s) - D (v 0))‖ := norm_add_le _ _
          _ = ‖A s (v s) - A 0 (v s) - (s : ℂ) * D (v s)‖ +
              |s| * ‖D (v s) - D (v 0)‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          _ ≤ |s| * ε s + |s| * ‖D (v s) - D (v 0)‖ := add_le_add hrem le_rfl
          _ = _ := by ring
      simp only [sub_zero, sub_self, Complex.real_smul, Real.norm_eq_abs]
      calc
        _ ≤ |s|⁻¹ * (|s| * (ε s + ‖D (v s) - D (v 0)‖)) :=
          mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr habs.le)
        _ = _ := by field_simp
    · simpa using hε.add (hD.sub (tendsto_const_nhds (x := D (v 0)))).norm
  have hspatial := hA0.comp_hasDerivWithinAt 0 hv.Ioi_of_Ici
  have h := hparam.add hspatial
  apply HasDerivWithinAt.Ici_of_Ioi
  convert h using 1
  funext s
  dsimp
  ring

/-- Combining inverse differentiation and attracting composition gives the
paper's gate correction before subtraction of its normalization constant. -/
theorem hasDerivWithinAt_gate_composition
    (S A : ℝ → ℂ → ℂ) (v : ℝ → ℂ) (DS DA : ℂ → ℂ)
    (εS εA : ℝ → ℝ) (B A' : ℂ)
    (hS0 : HasStrictDerivAt (S 0) B (v 0)) (hB : B ≠ 0)
    (hA0 : HasDerivAt (A 0) A' (v 0))
    (hv : Tendsto v (nhdsWithin 0 (Set.Ioi 0)) (nhds (v 0)))
    (hInv : ∀ᶠ s in nhdsWithin 0 (Set.Ioi 0), S s (v s) = S 0 (v 0))
    (hDS : Tendsto (fun s => DS (v s)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (DS (v 0))))
    (hDA : Tendsto (fun s => DA (v s)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (DA (v 0))))
    (hεS : Tendsto εS (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hεA : Tendsto εA (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hRemS : ∀ᶠ s in nhdsWithin 0 (Set.Ioi 0),
      ‖S s (v s) - S 0 (v s) - (s : ℂ) * DS (v s)‖ ≤ |s| * εS s)
    (hRemA : ∀ᶠ s in nhdsWithin 0 (Set.Ioi 0),
      ‖A s (v s) - A 0 (v s) - (s : ℂ) * DA (v s)‖ ≤ |s| * εA s) :
    HasDerivWithinAt (fun s => A s (v s))
      (DA (v 0) - (A' / B) * DS (v 0)) (Set.Ici 0) 0 := by
  have hdv := hasDerivWithinAt_inverse_branch S v DS εS B hS0 hB hv hInv hDS hεS hRemS
  have h := hasDerivWithinAt_moving_composition A v DA εA A' (-DS (v 0) / B)
    hA0 hdv hDA hεA hRemA
  apply h.congr_deriv
  ring

/-- An ordinary uniform `o(s)` remainder establishes a right derivative. -/
theorem hasDerivWithinAt_of_first_remainder (f : ℝ → ℂ) (d : ℂ) (ε : ℝ → ℝ)
    (hε : Tendsto ε (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hRem : ∀ᶠ s in nhdsWithin 0 (Set.Ioi 0),
      ‖f s - f 0 - (s : ℂ) * d‖ ≤ |s| * ε s) :
    HasDerivWithinAt f d (Set.Ici 0) 0 := by
  apply HasDerivWithinAt.Ici_of_Ioi
  rw [hasDerivWithinAt_iff_tendsto]
  apply squeeze_zero' (g := ε)
  · exact Eventually.of_forall (fun s => mul_nonneg (inv_nonneg.mpr (norm_nonneg _))
      (norm_nonneg _))
  · filter_upwards [hRem, self_mem_nhdsWithin] with s hrem hpos
    have hsp : 0 < s := hpos
    have habs : 0 < |s| := abs_pos.mpr hsp.ne'
    simp only [sub_zero, Complex.real_smul, Real.norm_eq_abs]
    calc
      _ ≤ |s|⁻¹ * (|s| * ε s) :=
        mul_le_mul_of_nonneg_left hrem (inv_nonneg.mpr habs.le)
      _ = _ := by field_simp
  · exact hε

/-- The normalized gate map `A_s(v_s)-A_s(u*)` has exactly the correction in
Theorem D, with both derivatives deduced from first-order expansions. -/
theorem hasDerivWithinAt_normalized_gate_composition
    (S A : ℝ → ℂ → ℂ) (v : ℝ → ℂ) (uStar : ℂ) (DS DA : ℂ → ℂ)
    (εS εA εStar : ℝ → ℝ) (B A' : ℂ)
    (hS0 : HasStrictDerivAt (S 0) B (v 0)) (hB : B ≠ 0)
    (hA0 : HasDerivAt (A 0) A' (v 0))
    (hv : Tendsto v (nhdsWithin 0 (Set.Ioi 0)) (nhds (v 0)))
    (hInv : ∀ᶠ s in nhdsWithin 0 (Set.Ioi 0), S s (v s) = S 0 (v 0))
    (hDS : Tendsto (fun s => DS (v s)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (DS (v 0))))
    (hDA : Tendsto (fun s => DA (v s)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (DA (v 0))))
    (hεS : Tendsto εS (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hεA : Tendsto εA (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hεStar : Tendsto εStar (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hRemS : ∀ᶠ s in nhdsWithin 0 (Set.Ioi 0),
      ‖S s (v s) - S 0 (v s) - (s : ℂ) * DS (v s)‖ ≤ |s| * εS s)
    (hRemA : ∀ᶠ s in nhdsWithin 0 (Set.Ioi 0),
      ‖A s (v s) - A 0 (v s) - (s : ℂ) * DA (v s)‖ ≤ |s| * εA s)
    (hRemStar : ∀ᶠ s in nhdsWithin 0 (Set.Ioi 0),
      ‖A s uStar - A 0 uStar - (s : ℂ) * DA uStar‖ ≤ |s| * εStar s) :
    HasDerivWithinAt (fun s => A s (v s) - A s uStar)
      (DA (v 0) - DA uStar - (A' / B) * DS (v 0)) (Set.Ici 0) 0 := by
  have hgate := hasDerivWithinAt_gate_composition S A v DS DA εS εA B A'
    hS0 hB hA0 hv hInv hDS hDA hεS hεA hRemS hRemA
  have hstar := hasDerivWithinAt_of_first_remainder (fun s => A s uStar) (DA uStar)
    εStar hεStar hRemStar
  apply (hgate.sub hstar).congr_deriv
  ring

/-- A quantitative inverse remainder follows from the inverse equation and
explicit parameter, spatial, and correction remainders. -/
theorem norm_inverse_remainder_le
    (s εParam εSpatial εD : ℝ) (Ssv S0v S0v0 B Dv D0 v v0 : ℂ)
    (hB : B ≠ 0) (hInv : Ssv = S0v0)
    (hParam : ‖Ssv - S0v - (s : ℂ) * Dv‖ ≤ |s| * εParam)
    (hSpatial : ‖S0v - S0v0 - B * (v - v0)‖ ≤ |s| * εSpatial)
    (hD : ‖Dv - D0‖ ≤ εD) :
    ‖v - v0 + (s : ℂ) * (D0 / B)‖ ≤
      ‖B‖⁻¹ * (|s| * (εParam + εSpatial + εD)) := by
  have heq : v - v0 + (s : ℂ) * (D0 / B) = B⁻¹ *
      (-(Ssv - S0v - (s : ℂ) * Dv) -
        (S0v - S0v0 - B * (v - v0)) + (s : ℂ) * (D0 - Dv)) := by
    rw [hInv]
    field_simp
    ring
  have hsum : ‖-(Ssv - S0v - (s : ℂ) * Dv) -
      (S0v - S0v0 - B * (v - v0)) + (s : ℂ) * (D0 - Dv)‖ ≤
      |s| * (εParam + εSpatial + εD) := by
    calc
      _ ≤ ‖-(Ssv - S0v - (s : ℂ) * Dv) - (S0v - S0v0 - B * (v - v0))‖ +
          ‖(s : ℂ) * (D0 - Dv)‖ := norm_add_le _ _
      _ ≤ (‖-(Ssv - S0v - (s : ℂ) * Dv)‖ + ‖S0v - S0v0 - B * (v - v0)‖) +
          ‖(s : ℂ) * (D0 - Dv)‖ := add_le_add (norm_sub_le _ _) le_rfl
      _ = (‖Ssv - S0v - (s : ℂ) * Dv‖ + ‖S0v - S0v0 - B * (v - v0)‖) +
          |s| * ‖Dv - D0‖ := by
        rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_sub_rev D0 Dv]
      _ ≤ (|s| * εParam + |s| * εSpatial) + |s| * εD :=
        add_le_add (add_le_add hParam hSpatial)
          (mul_le_mul_of_nonneg_left hD (abs_nonneg s))
      _ = _ := by ring
  rw [heq, norm_mul, norm_inv]
  exact mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (norm_nonneg B))

/-- Quantitative composition on the gate: separate coordinate and inverse
remainders produce a uniform remainder for the actual normalized transition.
The same statement can be applied at every gate point with common constants. -/
theorem norm_normalized_composition_remainder_le
    (s εA εSpatial εDA εV εStar M : ℝ)
    (Asv A0v A0v0 DAv DA0 Asp v v0 dv AStarS AStar0 DAStar : ℂ)
    (hM : 0 ≤ M) (hAsp : ‖Asp‖ ≤ M)
    (hA : ‖Asv - A0v - (s : ℂ) * DAv‖ ≤ |s| * εA)
    (hSpatial : ‖A0v - A0v0 - Asp * (v - v0)‖ ≤ |s| * εSpatial)
    (hDA : ‖DAv - DA0‖ ≤ εDA)
    (hV : ‖v - v0 - (s : ℂ) * dv‖ ≤ |s| * εV)
    (hStar : ‖AStarS - AStar0 - (s : ℂ) * DAStar‖ ≤ |s| * εStar) :
    ‖(Asv - AStarS) - (A0v0 - AStar0) -
      (s : ℂ) * (DA0 + Asp * dv - DAStar)‖ ≤
      |s| * (εA + εSpatial + εDA + M * εV + εStar) := by
  have heq : (Asv - AStarS) - (A0v0 - AStar0) -
      (s : ℂ) * (DA0 + Asp * dv - DAStar) =
      (Asv - A0v - (s : ℂ) * DAv) +
        (A0v - A0v0 - Asp * (v - v0)) + (s : ℂ) * (DAv - DA0) +
        Asp * (v - v0 - (s : ℂ) * dv) - (AStarS - AStar0 - (s : ℂ) * DAStar) := by
    ring
  have hAspV : ‖Asp * (v - v0 - (s : ℂ) * dv)‖ ≤ M * (|s| * εV) := by
    rw [norm_mul]
    exact mul_le_mul hAsp hV (norm_nonneg _) hM
  have hSD : ‖(s : ℂ) * (DAv - DA0)‖ ≤ |s| * εDA := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hDA (abs_nonneg s)
  rw [heq]
  calc
    _ ≤ ‖(Asv - A0v - (s : ℂ) * DAv) +
          (A0v - A0v0 - Asp * (v - v0)) + (s : ℂ) * (DAv - DA0) +
          Asp * (v - v0 - (s : ℂ) * dv)‖ +
        ‖AStarS - AStar0 - (s : ℂ) * DAStar‖ := norm_sub_le _ _
    _ ≤ (‖(Asv - A0v - (s : ℂ) * DAv) +
          (A0v - A0v0 - Asp * (v - v0)) + (s : ℂ) * (DAv - DA0)‖ +
          ‖Asp * (v - v0 - (s : ℂ) * dv)‖) +
        ‖AStarS - AStar0 - (s : ℂ) * DAStar‖ :=
      add_le_add (norm_add_le _ _) le_rfl
    _ ≤ ((‖(Asv - A0v - (s : ℂ) * DAv) +
          (A0v - A0v0 - Asp * (v - v0))‖ + ‖(s : ℂ) * (DAv - DA0)‖) +
          ‖Asp * (v - v0 - (s : ℂ) * dv)‖) +
        ‖AStarS - AStar0 - (s : ℂ) * DAStar‖ :=
      add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl
    _ ≤ (((‖Asv - A0v - (s : ℂ) * DAv‖ +
          ‖A0v - A0v0 - Asp * (v - v0)‖) + ‖(s : ℂ) * (DAv - DA0)‖) +
          ‖Asp * (v - v0 - (s : ℂ) * dv)‖) +
        ‖AStarS - AStar0 - (s : ℂ) * DAStar‖ :=
      add_le_add (add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl) le_rfl
    _ ≤ (((|s| * εA + |s| * εSpatial) + |s| * εDA) + M * (|s| * εV)) +
        |s| * εStar :=
      add_le_add (add_le_add (add_le_add (add_le_add hA hSpatial) hSD) hAspV) hStar
    _ = _ := by ring

end Kneser.GateInverseDerivative

end
