import HardySpaceFormalization.HardySpaceDisc
import HardySpaceFormalization.poissonIntegral

/-!
# Outer functions on the unit disc

Garnett II.4 and II.5, printed page 70: the outer-function formula `O_k`, the outer predicate,
and the basic properties used in the canonical factorization. `O_k` is analytic and zero-free
on the disc, and `log |O_k|` is the Poisson integral of the boundary log-data `k`.
-/

open MeasureTheory Complex
open scoped PoissonIntegral


/-- The normalized **outer-function formula** with boundary log-data `k`. Its analytic
and boundary properties assume `Integrable k (circleMeasure 0 1)`. -/
noncomputable def outerFunction (k : ℂ → ℝ) (z : ℂ) : ℂ :=
  exp (∫ ζ, herglotzRieszKernel 0 z ζ * (k ζ) ∂circleMeasure 0 1)

/-- A function is an **outer function** on the unit disc if it agrees with an exponential
integral of integrable real boundary log-data up to some unimodular constant. -/
def IsOuterFunction (f : ℂ → ℂ) : Prop :=
  ∃ k : ℂ → ℝ, Integrable k (circleMeasure 0 1) ∧
    ∃ C : ℂ, ‖C‖ = 1 ∧ ∀ z ∈ unitDisc, f z = C * outerFunction k z

/-! ### The outer-function formula -/

/-- The outer-function formula never vanishes. -/
theorem outerFunction_ne_zero (k : ℂ → ℝ) (z : ℂ) : outerFunction k z ≠ 0 :=
  exp_ne_zero _

/-- The outer-function formula with integrable boundary log-data is analytic on the disc. -/
theorem analyticOn_outerFunction {k : ℂ → ℝ} (hk : Integrable k (circleMeasure 0 1)) :
    AnalyticOn ℂ (outerFunction k) unitDisc :=
  (analyticOnNhd_integral_herglotzRieszKernel_mul (c := 0) (R := 1)
    (circleMeasure_compl_sphere zero_le_one) hk.ofReal).cexp.analyticOn

/-- **Garnett II.4.** The modulus of `O_k` is the exponential of the Poisson integral of the
boundary log-data `k`, since the real part of the Herglotz--Riesz kernel is the Poisson kernel. -/
theorem norm_outerFunction {k : ℂ → ℝ} (hk : Integrable k (circleMeasure 0 1)) {z : ℂ}
    (hz : z ∈ unitDisc) :
    ‖outerFunction k z‖ = Real.exp (P[0; k ∂ᵥ circleMeasure 0 1] z) := by
  sorry

/-- **Garnett II.4.** `log |O_k|` is the Poisson integral of the boundary log-data `k`. -/
theorem log_norm_outerFunction {k : ℂ → ℝ} (hk : Integrable k (circleMeasure 0 1)) {z : ℂ}
    (hz : z ∈ unitDisc) :
    Real.log ‖outerFunction k z‖ = P[0; k ∂ᵥ circleMeasure 0 1] z := by
  rw [norm_outerFunction hk hz, Real.log_exp]

/-- The outer-function formula with integrable boundary log-data is an outer function. -/
theorem isOuterFunction_outerFunction {k : ℂ → ℝ} (hk : Integrable k (circleMeasure 0 1)) :
    IsOuterFunction (outerFunction k) :=
  ⟨k, hk, 1, by simp, fun z _ => by simp⟩

/-! ### Outer functions -/

/-- An outer function is analytic on the unit disc. -/
theorem IsOuterFunction.analyticOn {F : ℂ → ℂ} (hF : IsOuterFunction F) :
    AnalyticOn ℂ F unitDisc := by
  obtain ⟨k, hk, C, -, hF⟩ := hF
  exact ((analyticOn_outerFunction hk).const_smul (c := C)).congr fun z hz => hF z hz

/-- An outer function has no zeros in the unit disc. -/
theorem IsOuterFunction.ne_zero {F : ℂ → ℂ} (hF : IsOuterFunction F) {z : ℂ}
    (hz : z ∈ unitDisc) : F z ≠ 0 := by
  obtain ⟨k, -, C, hC, hF⟩ := hF
  rw [hF z hz]
  exact mul_ne_zero (norm_ne_zero_iff.mp (by simp [hC])) (outerFunction_ne_zero k z)

/-- **Garnett II.4.** The logarithm of the modulus of an outer function is the Poisson integral
of integrable boundary log-data. -/
theorem IsOuterFunction.exists_log_norm_eq {F : ℂ → ℂ} (hF : IsOuterFunction F) :
    ∃ k : ℂ → ℝ, Integrable k (circleMeasure 0 1) ∧
      ∀ z ∈ unitDisc, Real.log ‖F z‖ = P[0; k ∂ᵥ circleMeasure 0 1] z := by
  obtain ⟨k, hk, C, hC, hF⟩ := hF
  refine ⟨k, hk, fun z hz => ?_⟩
  rw [hF z hz, norm_mul, hC, one_mul, log_norm_outerFunction hk hz]
