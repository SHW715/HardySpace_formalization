import HardySpaceFormalization.HardySpaceDisc
import HardySpaceFormalization.NontangentialLimit

open Metric HardySpace MeasureTheory Filter
open scoped ENNReal Topology PoissonIntegral

/-- Bounded analytic functions have nontangential limits almost everywhere. -/
theorem AnalyticOnNhd.ae_nontangentiallyConvergentAt_of_bounded
    {f : ℂ → ℂ} {C : ℝ} (hf : AnalyticOnNhd ℂ f (ball 0 1))
    (hbound : ∀ z ∈ ball 0 1, ‖f z‖ ≤ C) :
    ∀ᵐ ζ ∂circleMeasure 0 1, NontangentiallyConvergentAt f ζ := by
  -- codex without review
  have hreal (u : ℂ → ℝ) (hu : InnerProductSpace.HarmonicOnNhd u (ball 0 1))
      (hboundu : ∀ z ∈ ball 0 1, |u z| ≤ C) :
      ∃ U : ℂ → ℝ, IsAEBoundaryValue (circleMeasure 0 1) u U := by
    have hnorm : hardyNorm u ∞ < ∞ := by
      rw [hardyNorm_top_eq_Sup_norm hu.continuousOn]
      refine lt_of_le_of_lt (iSup_le fun z => ?_) (ENNReal.ofReal_lt_top (r := C))
      rw [Real.enorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_ofReal (hboundu z z.property)
    obtain ⟨U, hU, hrepr⟩ :=
      (harmonicOnNhd_hardyNorm_lt_top_iff_exists_memLp_eq_poissonIntegral
        ENNReal.one_lt_top).mp ⟨hu, hnorm⟩
    refine ⟨U, ?_⟩
    filter_upwards [isAEBoundaryValue_poissonIntegral (hU.integrable le_top)] with ζ hζ
    apply hasNontangentialLimit_iff_forall.mpr
    intro α hα
    have hlim := (hasNontangentialLimit_iff_forall.mp hζ) α hα
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (hrepr z (mem_ball_zero_iff.mpr hz.1)).symm
  obtain ⟨U, hU⟩ := hreal (fun z => (f z).re)
    (fun z hz => (hf z hz).harmonicAt_re)
    (fun z hz => (Complex.abs_re_le_norm (f z)).trans (hbound z hz))
  obtain ⟨V, hV⟩ := hreal (fun z => (f z).im)
    (fun z hz => (hf z hz).harmonicAt_im)
    (fun z hz => (Complex.abs_im_le_norm (f z)).trans (hbound z hz))
  filter_upwards [hU, hV] with ζ hUζ hVζ
  refine ⟨(U ζ : ℂ) + (V ζ : ℂ) * Complex.I, ?_⟩
  have hlim := hUζ.ofReal.add (hVζ.ofReal.mul_const Complex.I)
  simpa only [HasNontangentialLimit, Complex.re_add_im] using hlim

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
