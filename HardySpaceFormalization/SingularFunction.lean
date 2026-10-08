import HardySpaceFormalization.HardySpaceDisc
import HardySpaceFormalization.NontangentialLimit

/-!
# Singular functions on the unit disc

Garnett II.5, formulas (5.8) and (5.9) and the four properties on printed page 70. The formula
`S_μ` is analytic and zero-free on the disc, `log |S_μ| = -P[μ]` there, and `S_μ(0) = e^{-μ(T)}`.
-/

open MeasureTheory Complex
open scoped PoissonIntegral

/-- The **singular-function formula** associated to a measure `μ`. Its singular-function
properties assume that `μ` is finite, carried by the unit circle, and singular to arclength. -/
noncomputable def singularFunction (μ : Measure ℂ) (z : ℂ) : ℂ :=
  exp (-(∫ ζ, herglotzRieszKernel 0 z ζ ∂μ))

/-- A function is a **singular function** on the unit disc if it agrees there with the
exponential integral of a finite positive singular boundary measure. The normalization
at the origin is fixed by the formula; values outside the disc are unrestricted. -/
def IsSingularFunction (S : ℂ → ℂ) : Prop :=
  ∃ μ : Measure ℂ, IsFiniteMeasure μ ∧
    μ (Metric.sphere 0 1)ᶜ = 0 ∧
    μ ⟂ₘ circleMeasure 0 1 ∧
    ∀ z ∈ unitDisc, S z = singularFunction μ z

/-! ### The singular-function formula -/

/-- The singular-function formula never vanishes. -/
theorem singularFunction_ne_zero (μ : Measure ℂ) (z : ℂ) : singularFunction μ z ≠ 0 :=
  exp_ne_zero _

/-- The singular-function formula of a finite measure carried by the unit circle is analytic
on the disc. -/
theorem analyticOn_singularFunction {μ : Measure ℂ} [IsFiniteMeasure μ]
    (hμ : μ (Metric.sphere 0 1)ᶜ = 0) : AnalyticOn ℂ (singularFunction μ) unitDisc :=
  (analyticOnNhd_integral_herglotzRieszKernel (c := 0) (R := 1) hμ).neg.cexp.analyticOn

/-- **Garnett II, (5.9).** The modulus of `S_μ` is the exponential of minus the Poisson
integral of `μ`, since the real part of the Herglotz--Riesz kernel is the Poisson kernel. -/
theorem norm_singularFunction {μ : Measure ℂ} [IsFiniteMeasure μ]
    (hμ : μ (Metric.sphere 0 1)ᶜ = 0) {z : ℂ} (hz : z ∈ unitDisc) :
    ‖singularFunction μ z‖ = Real.exp (-P[0; μ.toSignedMeasure] z) := by
  rw [singularFunction, Complex.norm_exp, neg_re, poissonIntegral_toSignedMeasure_apply,
    ← RCLike.re_to_complex, ← integral_re (integrable_herglotzRieszKernel hμ hz)]
  congr 3 with ζ
  simpa using (congrFun (poissonKernel_eq_re_herglotzRieszKernel (c := 0) (w := z)) ζ).symm

/-- **Garnett II, (5.9).** `log |S_μ| = -P[μ]` on the disc. -/
theorem log_norm_singularFunction {μ : Measure ℂ} [IsFiniteMeasure μ]
    (hμ : μ (Metric.sphere 0 1)ᶜ = 0) {z : ℂ} (hz : z ∈ unitDisc) :
    Real.log ‖singularFunction μ z‖ = -P[0; μ.toSignedMeasure] z := by
  rw [norm_singularFunction hμ hz, Real.log_exp]

/-- At the origin the Herglotz--Riesz kernel is `1` on the circle, so `S_μ(0) = e^{-μ(T)}`. -/
theorem singularFunction_zero {μ : Measure ℂ} [IsFiniteMeasure μ]
    (hμ : μ (Metric.sphere 0 1)ᶜ = 0) :
    singularFunction μ 0 = Real.exp (-μ.real Set.univ) := by
  have h : ∫ ζ, herglotzRieszKernel 0 0 ζ ∂μ = ∫ _ζ, (1 : ℂ) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [ae_iff.2 hμ] with ζ hζ
    have hζ0 : ζ ≠ 0 := by
      rintro rfl
      simp at hζ
    simp [herglotzRieszKernel_def, hζ0]
  rw [singularFunction, h, integral_const, ofReal_exp]
  simp

/-- The singular-function formula of a finite positive measure carried by the unit circle and
singular to arclength is a singular function. -/
theorem isSingularFunction_singularFunction {μ : Measure ℂ} [IsFiniteMeasure μ]
    (hμ : μ (Metric.sphere 0 1)ᶜ = 0) (hμσ : μ ⟂ₘ circleMeasure 0 1) :
    IsSingularFunction (singularFunction μ) :=
  ⟨μ, inferInstance, hμ, hμσ, fun _ _ => rfl⟩

/-! ### Singular functions -/

/-- A singular function is analytic on the unit disc. -/
theorem IsSingularFunction.analyticOn {S : ℂ → ℂ} (hS : IsSingularFunction S) :
    AnalyticOn ℂ S unitDisc := by
  obtain ⟨μ, hfin, hμ, -, hS⟩ := hS
  exact (analyticOn_singularFunction hμ).congr hS

/-- **Garnett II.5, property (i).** A singular function has no zeros in the disc. -/
theorem IsSingularFunction.ne_zero {S : ℂ → ℂ} (hS : IsSingularFunction S)
    {z : ℂ} (hz : z ∈ unitDisc) : S z ≠ 0 := by
  obtain ⟨μ, -, -, -, hS⟩ := hS
  rw [hS z hz]
  exact singularFunction_ne_zero μ z

/-- **Garnett II.5, property (ii).** A singular function has modulus at most one in the disc. -/
theorem IsSingularFunction.norm_le_one {S : ℂ → ℂ} (hS : IsSingularFunction S)
    {z : ℂ} (hz : z ∈ unitDisc) : ‖S z‖ ≤ 1 := by
  obtain ⟨μ, hfin, hμ, -, hS⟩ := hS
  rw [hS z hz, norm_singularFunction hμ hz, Real.exp_le_one_iff, neg_nonpos]
  exact poissonIntegral_toSignedMeasure_nonneg hμ hz

/-- **Garnett II.5, property (iii).** A singular function has nontangential limits of
modulus one almost everywhere on the unit circle. -/
theorem IsSingularFunction.ae_hasNontangentialLimit_norm_eq_one {S : ℂ → ℂ}
    (hS : IsSingularFunction S) :
    ∀ᵐ ζ ∂circleMeasure 0 1, ∃ L : ℂ, HasNontangentialLimit S ζ L ∧ ‖L‖ = 1 := by
  sorry

/-- **Garnett II.5, property (iv).** A singular function takes a positive real value at zero. -/
theorem IsSingularFunction.zero_pos {S : ℂ → ℂ} (hS : IsSingularFunction S) :
    (S 0).im = 0 ∧ 0 < (S 0).re := by
  obtain ⟨μ, hfin, hμ, -, hS⟩ := hS
  rw [hS 0 (Metric.mem_ball_self one_pos), singularFunction_zero hμ]
  exact ⟨ofReal_im _, by rw [ofReal_re]; exact Real.exp_pos _⟩

/-- The measure representation is equivalent to analyticity and Garnett's four properties
of a singular function (II.5, printed page 70). -/
theorem isSingularFunction_iff {S : ℂ → ℂ} :
    IsSingularFunction S ↔
      AnalyticOn ℂ S unitDisc ∧
      (∀ z ∈ unitDisc, S z ≠ 0) ∧
      (∀ z ∈ unitDisc, ‖S z‖ ≤ 1) ∧
      (∀ᵐ ζ ∂circleMeasure 0 1, ∃ L : ℂ, HasNontangentialLimit S ζ L ∧ ‖L‖ = 1) ∧
      (S 0).im = 0 ∧ 0 < (S 0).re := by
  sorry
