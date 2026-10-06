import Kneser.ExponentialMultiplierParameter
import Kneser.GateFourierDerivative
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Gate coefficients in the actual exponential multiplier parameter

The multiplier parameter is constructed from the actual exponential cusp,
and its derivative is proved to be `2`. Its complex-valued restriction to
the right real ray is sufficient for the coefficient conversion.
-/

set_option autoImplicit false
noncomputable section

namespace Kneser.ActualParameterHornCoefficient

open Kneser.ExponentialCuspParameter Kneser.ExponentialMultiplierParameter
open Kneser.GateFourierDerivative
open Filter MeasureTheory
open scoped Topology

/-- A quotient of two germs vanishing at zero converges to the quotient of
their right derivatives when the denominator derivative is nonzero. -/
theorem tendsto_quotient_of_right_derivatives (f p : ℝ → ℂ) (df dp : ℂ)
    (hf : HasDerivWithinAt f df (Set.Ici 0) 0)
    (hp : HasDerivWithinAt p dp (Set.Ici 0) 0)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hdp : dp ≠ 0) :
    Tendsto (fun s => f s / p s) (𝓝[>] 0) (𝓝 (df / dp)) := by
  have hf' : HasDerivWithinAt f df (Set.Ioi 0) 0 := hf.mono Set.Ioi_subset_Ici_self
  have hp' : HasDerivWithinAt p dp (Set.Ioi 0) 0 := hp.mono Set.Ioi_subset_Ici_self
  have hflim : Tendsto (fun s : ℝ => f s / (s : ℂ)) (𝓝[>] 0) (𝓝 df) := by
    have h := (hasDerivWithinAt_iff_tendsto_slope' (by simp : (0 : ℝ) ∉ Set.Ioi 0)).mp hf'
    change Tendsto (fun s => slope f 0 s) (𝓝[>] 0) (𝓝 df) at h
    simpa only [slope_def_module, sub_zero, hf0, Complex.real_smul,
      Complex.ofReal_inv, div_eq_mul_inv, mul_comm] using h
  have hplim : Tendsto (fun s : ℝ => p s / (s : ℂ)) (𝓝[>] 0) (𝓝 dp) := by
    have h := (hasDerivWithinAt_iff_tendsto_slope' (by simp : (0 : ℝ) ∉ Set.Ioi 0)).mp hp'
    change Tendsto (fun s => slope p 0 s) (𝓝[>] 0) (𝓝 dp) at h
    simpa only [slope_def_module, sub_zero, hp0, Complex.real_smul,
      Complex.ofReal_inv, div_eq_mul_inv, mul_comm] using h
  apply (hflim.div hplim hdp).congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hs)
  exact div_div_div_cancel_right₀ hs0 (f s) (p s)

/-- The constructed complex multiplier parameter has right real-ray
derivative `2`; no parameter derivative is an assumption. -/
theorem exists_actual_parameter_right_derivative :
    ∃ V p : ℂ → ℂ, AnalyticAt ℂ V 0 ∧ V 0 = 0 ∧
      (∀ᶠ x in nhds 0, cuspParameter (V x) = x ^ 2) ∧
      AnalyticAt ℂ p 0 ∧ p 0 = 0 ∧
      HasDerivWithinAt (fun s : ℝ => p (s : ℂ)) 2 (Set.Ici 0) 0 ∧
      (∀ x, p (x ^ 2) = -Complex.log (1 + V x) * Complex.log (1 + V (-x))) := by
  obtain ⟨V, p, hVa, hV0, hVsquare, hpa, hp0, hpder, hproduct⟩ :=
    exists_analytic_multiplier_parameter
  refine ⟨V, p, hVa, hV0, hVsquare, hpa, hp0, ?_, hproduct⟩
  have hp' : HasDerivAt p 2 ((0 : ℝ) : ℂ) := by simpa using hpder
  exact hp'.comp_ofReal.hasDerivWithinAt

/-- Every Fourier mode has the paper's coefficient in the actual multiplier
parameter. Fourier derivatives and the multiplier derivative are conclusions
of this theorem, not inputs. -/
theorem exists_actual_parameter_gate_coefficient (n : ℤ) (Y : ℝ)
    (T : ℝ → ℂ → ℂ) (D : ℂ → ℂ) (ε : ℝ → ℝ) (B a : ℂ)
    (hInt : ∀ m s, IntervalIntegrable
      (fun x => (T s (gatePoint Y x) - gatePoint Y x) * gateWeight m Y x) volume 0 1)
    (hD : ∀ m, IntervalIntegrable
      (fun x => D (gatePoint Y x) * gateWeight m Y x) volume 0 1)
    (hε : Tendsto ε (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hUniform : ∀ᶠ s in nhdsWithin 0 (Set.Ioi 0), ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ‖T s (gatePoint Y x) - T 0 (gatePoint Y x) - (s : ℂ) * D (gatePoint Y x)‖ ≤
        |s| * ε s)
    (hn0 : gateFourierCoefficient n Y (T 0) = B)
    (h00 : gateFourierCoefficient 0 Y (T 0) = -a) (hB : B ≠ 0) :
    ∃ V p : ℂ → ℂ, AnalyticAt ℂ V 0 ∧ V 0 = 0 ∧
      (∀ᶠ x in nhds 0, cuspParameter (V x) = x ^ 2) ∧
      AnalyticAt ℂ p 0 ∧ p 0 = 0 ∧
      HasDerivWithinAt (fun s : ℝ => p (s : ℂ)) 2 (Set.Ici 0) 0 ∧
      (∀ x, p (x ^ 2) = -Complex.log (1 + V x) * Complex.log (1 + V (-x))) ∧
      derivWithin
        (fun s => Complex.log (Kneser.realNormalizedHornCoefficient n
          (fun t => gateFourierCoefficient n Y (T t))
          (fun t => gateFourierCoefficient 0 Y (T t)) s)) (Set.Ici 0) 0 /
        derivWithin (fun s : ℝ => p (s : ℂ)) (Set.Ici 0) 0 =
        Kneser.hornKappa n B (gateCorrectionCoefficient n Y D)
          (gateCorrectionCoefficient 0 Y D) ∧
      Tendsto
        (fun s : ℝ => Complex.log (Kneser.realNormalizedHornCoefficient n
          (fun t => gateFourierCoefficient n Y (T t))
          (fun t => gateFourierCoefficient 0 Y (T t)) s) / p (s : ℂ))
        (𝓝[>] 0) (𝓝 (Kneser.hornKappa n B (gateCorrectionCoefficient n Y D)
          (gateCorrectionCoefficient 0 Y D))) := by
  obtain ⟨V, p, hVa, hV0, hVsquare, hpa, hp0, hpder, hproduct⟩ :=
    exists_actual_parameter_right_derivative
  have hlog := hasDerivWithinAt_log_normalized_gateFourier n Y T D ε B a
    hInt hD hε hUniform hn0 h00 hB
  refine ⟨V, p, hVa, hV0, hVsquare, hpa, hp0, hpder, hproduct, ?_, ?_⟩
  · rw [hlog.derivWithin (uniqueDiffWithinAt_Ici 0),
      hpder.derivWithin (uniqueDiffWithinAt_Ici 0)]
    norm_num
  · have hlimit := tendsto_quotient_of_right_derivatives _ _ _ _ hlog hpder
      (Kneser.log_realNormalizedHornCoefficient_zero n _ _ B a hn0 h00 hB) hp0
      (by norm_num : (2 : ℂ) ≠ 0)
    simpa using hlimit

end Kneser.ActualParameterHornCoefficient

end
