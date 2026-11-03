import HardySpaceFormalization.HardySpaceDisc
import HardySpaceFormalization.NontangentialLimit

open Metric HardySpace MeasureTheory Filter
open scoped ENNReal Topology PoissonIntegral

/-- A harmonic function in `h^∞` of the unit disc is the Poisson integral of an essentially
bounded function on the circle, which is its nontangential boundary value almost everywhere. -/
theorem InnerProductSpace.HarmonicOnNhd.exists_isAEBoundaryValue_of_hardyNorm_lt_top
    {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u (ball 0 1)) (hnorm : hardyNorm u ∞ < ∞) :
    ∃ U : ℂ → ℝ, MemLp U ∞ (circleMeasure 0 1) ∧ IsAEBoundaryValue (circleMeasure 0 1) u U ∧
      ∀ w ∈ ball 0 1, u w = P[0; U ∂ᵥcircleMeasure 0 1] w := by
  obtain ⟨U, hU, hrepr⟩ :=
    (harmonicOnNhd_hardyNorm_lt_top_iff_exists_memLp_eq_poissonIntegral
      ENNReal.one_lt_top).mp ⟨hu, hnorm⟩
  refine ⟨U, hU, ?_, hrepr⟩
  filter_upwards [isAEBoundaryValue_poissonIntegral (hU.integrable le_top)] with ζ hζ
  apply hasNontangentialLimit_iff_forall.mpr
  intro α hα
  apply ((hasNontangentialLimit_iff_forall.mp hζ) α hα).congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (hrepr z (mem_ball_zero_iff.mpr hz.1)).symm

/-- A bounded analytic function on the unit disc has an essentially bounded nontangential boundary
function, whose mean over the circle is the value at the origin. -/
theorem AnalyticOnNhd.exists_isAEBoundaryValue_of_bounded
    {f : ℂ → ℂ} {C : ℝ} (hf : AnalyticOnNhd ℂ f (ball 0 1))
    (hbound : ∀ z ∈ ball 0 1, ‖f z‖ ≤ C) :
    ∃ F : ℂ → ℂ, MemLp F ∞ (circleMeasure 0 1) ∧ IsAEBoundaryValue (circleMeasure 0 1) f F ∧
      ∫ ζ, F ζ ∂circleMeasure 0 1 = f 0 := by
  -- The real and imaginary parts are bounded harmonic functions, hence in `h^∞`.
  have hnorm (u : ℂ → ℝ) (hu : InnerProductSpace.HarmonicOnNhd u (ball 0 1))
      (hboundu : ∀ z ∈ ball 0 1, |u z| ≤ C) : hardyNorm u ∞ < ∞ := by
    rw [hardyNorm_top_eq_Sup_norm hu.continuousOn]
    refine lt_of_le_of_lt (iSup_le fun z => ?_) (ENNReal.ofReal_lt_top (r := C))
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (hboundu z z.property)
  have hre : InnerProductSpace.HarmonicOnNhd (fun z => (f z).re) (ball 0 1) :=
    fun z hz => (hf z hz).harmonicAt_re
  have him : InnerProductSpace.HarmonicOnNhd (fun z => (f z).im) (ball 0 1) :=
    fun z hz => (hf z hz).harmonicAt_im
  obtain ⟨U, hU, hUb, hUr⟩ := hre.exists_isAEBoundaryValue_of_hardyNorm_lt_top
    (hnorm _ hre fun z hz => (Complex.abs_re_le_norm (f z)).trans (hbound z hz))
  obtain ⟨V, hV, hVb, hVr⟩ := him.exists_isAEBoundaryValue_of_hardyNorm_lt_top
    (hnorm _ him fun z hz => (Complex.abs_im_le_norm (f z)).trans (hbound z hz))
  -- At the center the Poisson integral is the mean, since the kernel is `1` on the circle.
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have hmean (W : ℂ → ℝ) (hW : MemLp W ∞ (circleMeasure 0 1)) :
      P[0; W ∂ᵥcircleMeasure 0 1] 0 = ∫ ζ, W ζ ∂circleMeasure 0 1 := by
    rw [poissonIntegral_withDensityᵥ (circleMeasure_compl_sphere zero_le_one) h0
      (hW.integrable le_top)]
    apply integral_congr_ae
    filter_upwards [ae_mem_sphere_circleMeasure zero_le_one] with ζ hζ
    have hζ' : ‖ζ‖ = 1 := mem_sphere_zero_iff_norm.1 hζ
    simp [poissonKernel_def, hζ']
  refine ⟨fun ζ => (U ζ : ℂ) + (V ζ : ℂ) * Complex.I,
    hU.ofReal.add (hV.ofReal.mul_const _), ?_, ?_⟩
  · filter_upwards [hUb, hVb] with ζ hUζ hVζ
    have hlim := hUζ.ofReal.add (hVζ.ofReal.mul_const Complex.I)
    simpa only [HasNontangentialLimit, Complex.re_add_im] using hlim
  · rw [integral_add (hU.integrable le_top).ofReal ((hV.integrable le_top).ofReal.mul_const _),
      integral_mul_const, integral_complex_ofReal, integral_complex_ofReal, ← hmean U hU,
      ← hmean V hV, ← hUr 0 h0, ← hVr 0 h0]
    exact Complex.re_add_im (f 0)

/-- Bounded analytic functions have nontangential limits almost everywhere. -/
theorem AnalyticOnNhd.ae_nontangentiallyConvergentAt_of_bounded
    {f : ℂ → ℂ} {C : ℝ} (hf : AnalyticOnNhd ℂ f (ball 0 1))
    (hbound : ∀ z ∈ ball 0 1, ‖f z‖ ≤ C) :
    ∀ᵐ ζ ∂circleMeasure 0 1, NontangentiallyConvergentAt f ζ := by
  obtain ⟨F, -, hF, -⟩ := hf.exists_isAEBoundaryValue_of_bounded hbound
  filter_upwards [hF] with ζ hζ
  exact ⟨F ζ, hζ⟩

/-- The boundary function of a bounded analytic function on the unit disc is essentially
bounded. -/
theorem AnalyticOnNhd.memLp_boundaryValue_of_bounded
    {f : ℂ → ℂ} {C : ℝ} (hf : AnalyticOnNhd ℂ f (ball 0 1))
    (hbound : ∀ z ∈ ball 0 1, ‖f z‖ ≤ C) :
    MemLp (boundaryValue f) ∞ (circleMeasure 0 1) := by
  obtain ⟨F, hFm, hF, -⟩ := hf.exists_isAEBoundaryValue_of_bounded hbound
  exact hFm.ae_eq (hF.ae_eq_boundaryValue ae_nontangentially_neBot_circleMeasure)

/-- **Garnett I.5.3, disc case `p = ∞`**: An `H∞` function has nontangential limits almost everywhere. -/
theorem HardySpace.MemHpDisc.ae_nontangentiallyConvergentAt
    {f : ℂ → ℂ} (hf : MemHpDisc ∞ f) :
    ∀ᵐ ζ ∂circleMeasure 0 1, NontangentiallyConvergentAt f ζ := by
  have han : AnalyticOnNhd ℂ f (ball 0 1) :=
    isOpen_ball.analyticOn_iff_analyticOnNhd.mp hf.1
  apply han.ae_nontangentiallyConvergentAt_of_bounded (C := (hardyNorm f ∞).toReal)
  intro z hz
  have hle : ‖f z‖ₑ ≤ hardyNorm f ∞ := by
    rw [hardyNorm_top_eq_Sup_norm hf.1.continuousOn]
    exact le_iSup (fun w : unitDisc => ‖f w‖ₑ) ⟨z, hz⟩
  simpa using ENNReal.toReal_mono hf.2.1.ne hle

-- This is true for general `1 ≤ p ≤ ∞`, but in this project `p = ∞` case is enough

/-- The value at the origin of a bounded analytic function on the unit disc is the mean of its
boundary values over the unit circle. -/
theorem AnalyticOnNhd.integral_boundaryValue_eq_of_bounded
    {f : ℂ → ℂ} {C : ℝ} (hf : AnalyticOnNhd ℂ f (ball 0 1))
    (hbound : ∀ z ∈ ball 0 1, ‖f z‖ ≤ C) :
    ∫ ζ, boundaryValue f ζ ∂circleMeasure 0 1 = f 0 := by
  obtain ⟨F, -, hF, hF0⟩ := hf.exists_isAEBoundaryValue_of_bounded hbound
  rw [← integral_congr_ae (hF.ae_eq_boundaryValue ae_nontangentially_neBot_circleMeasure), hF0]

/-- The modulus at the origin of a bounded analytic function on the unit disc is at most the
mean of the moduli of its boundary values. -/
theorem AnalyticOnNhd.norm_le_integral_norm_boundaryValue_of_bounded
    {f : ℂ → ℂ} {C : ℝ} (hf : AnalyticOnNhd ℂ f (ball 0 1))
    (hbound : ∀ z ∈ ball 0 1, ‖f z‖ ≤ C) :
    ‖f 0‖ ≤ ∫ ζ, ‖boundaryValue f ζ‖ ∂circleMeasure 0 1 := by
  rw [← hf.integral_boundaryValue_eq_of_bounded hbound]
  exact norm_integral_le_integral_norm _
