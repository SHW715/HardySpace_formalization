import HardySpaceFormalization.HardySpaceDisc
import HardySpaceFormalization.poissonIntegral
import HardySpaceFormalization.NontangentialLimit
import HardySpaceFormalization.NevanlinnaClass

/-!
# Outer functions on the unit disc

Garnett II.4 and II.5, printed pages 64 and 70: the outer-function formula `O_k`, the outer
predicate, and the basic properties used in the canonical factorization. `O_k` is analytic and
zero-free on the disc, and `log |O_k|` is the Poisson integral of the boundary log-data `k`.
On the circle, `O_k` has nontangential limits of modulus `e^k` almost everywhere, and an outer
function is determined by its boundary modulus up to a unimodular constant.
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

/-- An outer function, extended by zero outside the disc, belongs to the Nevanlinna class:
`log⁺ |F| ≤ P[k⁺ dσ]`, a harmonic majorant, since `log |F| = P[k dσ]` and the Poisson kernel
is nonnegative on the circle. -/
theorem IsOuterFunction.memNevanlinnaDisc_indicator {F : ℂ → ℂ} (hF : IsOuterFunction F) :
    Nevanlinna.MemNevanlinnaDisc (unitDisc.indicator F) := by
  obtain ⟨k, hk, hlog⟩ := hF.exists_log_norm_eq
  have hσ : circleMeasure 0 1 (Metric.sphere 0 1)ᶜ = 0 := circleMeasure_compl_sphere zero_le_one
  have hkp : Integrable (fun ζ => max (k ζ) 0) (circleMeasure 0 1) := hk.pos_part
  refine (Nevanlinna.memNevanlinnaDisc_iff_hasHarmonicMajorant
      (hF.analyticOn.congr fun z hz => Set.indicator_of_mem hz F)
      fun z hz => Set.indicator_of_notMem hz F).mpr
    ⟨P[0; (fun ζ => max (k ζ) 0) ∂ᵥ circleMeasure 0 1],
      harmonicOnNhd_poissonIntegral_withDensityᵥ hσ hkp, fun z hz => ?_⟩
  have hae : ∀ᵐ ζ ∂circleMeasure 0 1, ζ ∈ Metric.sphere (0 : ℂ) 1 := ae_iff.2 hσ
  -- `P[k] ≤ P[k⁺]` and `0 ≤ P[k⁺]`, because the Poisson kernel is nonnegative on the circle.
  have hle : P[0; k ∂ᵥ circleMeasure 0 1] z ≤
      P[0; (fun ζ => max (k ζ) 0) ∂ᵥ circleMeasure 0 1] z := by
    rw [poissonIntegral_withDensityᵥ hσ hz hk, poissonIntegral_withDensityᵥ hσ hz hkp]
    refine integral_mono_ae (by simpa [smul_eq_mul] using integrable_poissonKernel_mul hσ hz hk)
      (by simpa [smul_eq_mul] using integrable_poissonKernel_mul hσ hz hkp) ?_
    filter_upwards [hae] with ζ hζ
    exact smul_le_smul_of_nonneg_left (le_max_left _ _) (poissonKernel_nonneg hz hζ)
  have hnonneg : 0 ≤ P[0; (fun ζ => max (k ζ) 0) ∂ᵥ circleMeasure 0 1] z := by
    rw [poissonIntegral_withDensityᵥ hσ hz hkp]
    refine integral_nonneg_of_ae ?_
    filter_upwards [hae] with ζ hζ
    exact smul_nonneg (poissonKernel_nonneg hz hζ) (le_max_right _ _)
  show ((Real.posLog ‖unitDisc.indicator F z‖ : ℝ) : WithBot ℝ) ≤
    ((P[0; (fun ζ => max (k ζ) 0) ∂ᵥ circleMeasure 0 1] z : ℝ) : WithBot ℝ)
  rw [Set.indicator_of_mem hz]
  exact WithBot.coe_le_coe.mpr (max_le hnonneg ((hlog z hz).le.trans hle))

/-! ### Boundary values -/

/-- **Garnett II.4.** The outer-function formula with integrable boundary log-data has
nontangential limits almost everywhere on the unit circle. -/
theorem ae_nontangentiallyConvergentAt_outerFunction {k : ℂ → ℝ}
    (hk : Integrable k (circleMeasure 0 1)) :
    ∀ᵐ ζ ∂circleMeasure 0 1, NontangentiallyConvergentAt (outerFunction k) ζ := by
  sorry

/-- **Garnett II.4.** The boundary values of `O_k` have modulus `e^k` almost everywhere. -/
theorem ae_norm_boundaryValue_outerFunction {k : ℂ → ℝ}
    (hk : Integrable k (circleMeasure 0 1)) :
    ∀ᵐ ζ ∂circleMeasure 0 1, ‖boundaryValue (outerFunction k) ζ‖ = Real.exp (k ζ) := by
  sorry

/-- **Garnett II.4.** An outer function is determined by the modulus of its boundary values, up
to a unimodular constant. -/
theorem IsOuterFunction.exists_eq_const_mul_of_ae_norm_boundaryValue_eq {F₁ F₂ : ℂ → ℂ}
    (h₁ : IsOuterFunction F₁) (h₂ : IsOuterFunction F₂)
    (h : ∀ᵐ ζ ∂circleMeasure 0 1, ‖boundaryValue F₁ ζ‖ = ‖boundaryValue F₂ ζ‖) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ z ∈ unitDisc, F₁ z = c * F₂ z := by
  sorry
