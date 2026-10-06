import Kneser.EvenPreparedOrbitDiscs
import Kneser.ParabolicOrbitSum

/-!
Every coefficient of an actual prepared orbit term is estimated by Cauchy's
formula on the derived shrinking parameter discs.  This proves the precise
`k^(2j-2N)` decay and absolute convergence used in the higher-order argument.
Construction of a preparation of arbitrary order remains a separate task.
-/

noncomputable section

namespace Kneser.HigherPreparedDerivative

open Complex Metric Kneser.EvenPreparedOrbitDiscs

theorem norm_iteratedDeriv_term_le
    (term : ℂ → ℕ → ℂ) (c M : ℝ) (N j : ℕ) (hj : j ≤ N)
    (hc : 0 < c)
    (hdisc : ∀ k, DiffContOnCl ℂ (fun s => term s k)
      (ball 0 (c / ((k : ℝ) + 1) ^ 2)))
    (hbound : ∀ (k : ℕ) (s : ℂ), ‖s‖ ≤ c / ((k : ℝ) + 1) ^ 2 →
      ‖term s k‖ ≤ M / ((k : ℝ) + 1) ^ (2 * N)) (k : ℕ) :
    ‖iteratedDeriv j (fun s => term s k) 0‖ ≤
      ((j.factorial : ℝ) * M / c ^ j) / ((k : ℝ) + 1) ^ (2 * N - 2 * j) := by
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j
    (by positivity : 0 < c / ((k : ℝ) + 1) ^ 2) (hdisc k)
    (fun s hs => hbound k s (by
      have hn : ‖s‖ = c / ((k : ℝ) + 1) ^ 2 := by
        simpa only [mem_sphere, dist_zero_right] using hs
      exact hn.le))
  apply h.trans_eq
  have hexp : 2 * N = (2 * N - 2 * j) + 2 * j := by omega
  have hpow : ((k : ℝ) + 1) ^ (2 * N) =
      ((k : ℝ) + 1) ^ (2 * N - 2 * j) * ((k : ℝ) + 1) ^ (2 * j) := by
    conv_lhs => rw [hexp, pow_add]
  rw [div_pow, ← pow_mul, hpow]
  field_simp

theorem summable_norm_iteratedDeriv_term
    (term : ℂ → ℕ → ℂ) (c M : ℝ) (N j : ℕ) (hj : j + 1 ≤ N)
    (hc : 0 < c)
    (hdisc : ∀ k, DiffContOnCl ℂ (fun s => term s k)
      (ball 0 (c / ((k : ℝ) + 1) ^ 2)))
    (hbound : ∀ (k : ℕ) (s : ℂ), ‖s‖ ≤ c / ((k : ℝ) + 1) ^ 2 →
      ‖term s k‖ ≤ M / ((k : ℝ) + 1) ^ (2 * N)) :
    Summable (fun k => ‖iteratedDeriv j (fun s => term s k) 0‖) := by
  exact summable_norm_of_parabolic_bound _ ((j.factorial : ℝ) * M / c ^ j)
    (q := 2 * N - 2 * j) (by omega)
    (norm_iteratedDeriv_term_le term c M N j (by omega) hc hdisc hbound)

end Kneser.HigherPreparedDerivative

end
