import HardySpaceFormalization.Nevanlinna_properties
import HardySpaceFormalization.OuterFunction
import HardySpaceFormalization.SingularFunction
import Mathlib.Analysis.Complex.AbsMax

/-!
# Canonical factorization in the Nevanlinna class

Garnett II.5.5: the canonical factorization predicate on the unit disc, existence of the
factorization for a nonzero Nevanlinna function, and its uniqueness.
-/

open MeasureTheory Complex
open scoped PoissonIntegral

namespace Nevanlinna

/-- `IsCanonicalFactorization f C F μ₁ μ₂` asserts that `f = C * B * F * S₁ / S₂` on the disc
is a canonical factorization in the sense of Garnett II.5.5, formula (5.10). The Blaschke
product `B` is formed from the zeros of `f`, which satisfy the Blaschke condition; `‖C‖ = 1`;
`F` is outer; and `Sⱼ = singularFunction μⱼ`, where `μ₁, μ₂` are finite positive measures
carried by the unit circle, singular to arclength and to each other. Values of `f` outside
the disc are unrestricted. -/
@[mk_iff]
structure IsCanonicalFactorization (f : ℂ → ℂ) (C : ℂ) (F : ℂ → ℂ) (μ₁ μ₂ : Measure ℂ) :
    Prop where
  blaschkeCondition : BlaschkeCondition (analyticOrderAt f)
  norm_C : ‖C‖ = 1
  isOuterFunction : IsOuterFunction F
  isFiniteMeasure₁ : IsFiniteMeasure μ₁
  isFiniteMeasure₂ : IsFiniteMeasure μ₂
  measure_compl_sphere₁ : μ₁ (Metric.sphere 0 1)ᶜ = 0
  measure_compl_sphere₂ : μ₂ (Metric.sphere 0 1)ᶜ = 0
  singular_circleMeasure₁ : μ₁ ⟂ₘ circleMeasure 0 1
  singular_circleMeasure₂ : μ₂ ⟂ₘ circleMeasure 0 1
  mutuallySingular : μ₁ ⟂ₘ μ₂
  eq_mul_div : ∀ z ∈ unitDisc, f z = C * BlaschkeProduct (analyticOrderAt f) z * F z *
    singularFunction μ₁ z / singularFunction μ₂ z

/-- **Garnett II.5.5 (existence).** A nonzero Nevanlinna function has a canonical
factorization `f = C * B * F * S₁ / S₂` on the disc. -/
theorem MemNevanlinnaDisc.exists_isCanonicalFactorization {f : ℂ → ℂ}
    (hf : MemNevanlinnaDisc f) (hf_ne : ∃ z ∈ unitDisc, f z ≠ 0) :
    ∃ (C : ℂ) (F : ℂ → ℂ) (μ₁ μ₂ : Measure ℂ), IsCanonicalFactorization f C F μ₁ μ₂ := by
  -- II.5.2: `f = B g` with `g` zero-free and `log |g|` the least harmonic majorant of `log |f|`.
  obtain ⟨g, hgN, hg_ne, hfg, hg_lhm⟩ := hf.exists_eq_blaschkeProduct_mul hf_ne
  -- (5.2), (5.3): that majorant is `P[k dσ + μs]`, with `k = log |f*|` and `μs ⟂ σ`.
  set k : ℂ → ℝ := fun ζ => Real.log ‖boundaryValue f ζ‖ with hk_def
  have hk : Integrable k (circleMeasure 0 1) := hf.integrable_log_norm_boundaryValue hf_ne
  obtain ⟨μs, hμs_circ, hμs_sing, hμs_lhm⟩ :=
    hf.exists_mutuallySingular_isLeastHarmonicMajorant hf_ne
  have hlog : ∀ z ∈ unitDisc, Real.log ‖g z‖ = P[0; k ∂ᵥ circleMeasure 0 1 + μs] z :=
    fun z hz => hg_lhm.unique hμs_lhm hz
  -- (5.7): `μs = μ₂ - μ₁` with `μ₂ = μs⁺`, `μ₁ = μs⁻`, both carried by the circle and `⟂ σ`.
  set μ₁ := μs.toJordanDecomposition.negPart with hμ₁
  set μ₂ := μs.toJordanDecomposition.posPart with hμ₂
  haveI : IsFiniteMeasure μ₁ := μs.toJordanDecomposition.negPart_finite
  haveI : IsFiniteMeasure μ₂ := μs.toJordanDecomposition.posPart_finite
  obtain ⟨hcirc₂, hcirc₁⟩ := SignedMeasure.totalVariation_apply_eq_zero_iff.mp hμs_circ
  obtain ⟨hsing₂, hsing₁⟩ :=
    SignedMeasure.mutuallySingular_toENNRealVectorMeasure_iff.mp hμs_sing
  -- `|g| = |O_k S₁ / S₂|` on the disc, by comparing `log |g| = P[k] + P[μ₂] - P[μ₁]`.
  have hQ_ne : ∀ z, outerFunction k z * singularFunction μ₁ z / singularFunction μ₂ z ≠ 0 :=
    fun z => div_ne_zero (mul_ne_zero (outerFunction_ne_zero k z)
      (singularFunction_ne_zero μ₁ z)) (singularFunction_ne_zero μ₂ z)
  have hnorm : ∀ z ∈ unitDisc,
      ‖g z‖ = ‖outerFunction k z * singularFunction μ₁ z / singularFunction μ₂ z‖ := by
    intro z hz
    have hσ : circleMeasure 0 1 (Metric.sphere 0 1)ᶜ = 0 := circleMeasure_compl_sphere zero_le_one
    have hsplit : P[0; k ∂ᵥ circleMeasure 0 1 + μs] z = P[0; k ∂ᵥ circleMeasure 0 1] z +
        (P[0; μ₂.toSignedMeasure] z - P[0; μ₁.toSignedMeasure] z) := by
      rw [poissonIntegral_add (integrable_poissonKernel_withDensityᵥ hσ hz hk)
          (integrable_poissonKernel_totalVariation hμs_circ hz),
        poissonIntegral_eq_posPart_sub_negPart
          (integrable_poissonKernel_totalVariation hμs_circ hz),
        poissonIntegral_toSignedMeasure_apply, poissonIntegral_toSignedMeasure_apply]
    rw [← Real.exp_log (norm_pos_iff.mpr (hg_ne z hz)), hlog z hz, hsplit, norm_div, norm_mul,
      norm_outerFunction hk hz, norm_singularFunction hcirc₁ hz, norm_singularFunction hcirc₂ hz,
      ← Real.exp_add, ← Real.exp_sub]
    congr 1
    ring
  -- `g / (O_k S₁ / S₂)` is analytic on the disc with modulus one, hence a unimodular constant
  -- by the maximum modulus principle. (Garnett takes a single-valued `log g` instead.)
  set u : ℂ → ℂ := fun z => g z / (outerFunction k z * singularFunction μ₁ z /
    singularFunction μ₂ z) with hu
  have hu_an : AnalyticOn ℂ u unitDisc :=
    hgN.1.div (((analyticOn_outerFunction hk).mul (analyticOn_singularFunction hcirc₁)).div
      (analyticOn_singularFunction hcirc₂) fun z _ => singularFunction_ne_zero μ₂ z)
      fun z _ => hQ_ne z
  have hu_norm : ∀ z ∈ unitDisc, ‖u z‖ = 1 := fun z hz => by
    rw [hu, norm_div, hnorm z hz, div_self (norm_ne_zero_iff.mpr (hQ_ne z))]
  have h0 : (0 : ℂ) ∈ unitDisc := Metric.mem_ball_self one_pos
  have hconst : Set.EqOn u (Function.const ℂ (u 0)) unitDisc :=
    eqOn_of_isPreconnected_of_isMaxOn_norm (convex_ball (0 : ℂ) 1).isPreconnected
      Metric.isOpen_ball hu_an.differentiableOn h0
      (isMaxOn_iff.mpr fun z hz => by simp [hu_norm z hz, hu_norm 0 h0])
  refine ⟨u 0, outerFunction k, μ₁, μ₂,
    { blaschkeCondition := hf.blaschkeCondition hf_ne
      norm_C := hu_norm 0 h0
      isOuterFunction := isOuterFunction_outerFunction hk
      isFiniteMeasure₁ := inferInstance
      isFiniteMeasure₂ := inferInstance
      measure_compl_sphere₁ := hcirc₁
      measure_compl_sphere₂ := hcirc₂
      singular_circleMeasure₁ := hsing₁
      singular_circleMeasure₂ := hsing₂
      mutuallySingular := μs.toJordanDecomposition.mutuallySingular.symm
      eq_mul_div := fun z hz => ?_ }⟩
  have hgz : g z = u 0 * (outerFunction k z * singularFunction μ₁ z / singularFunction μ₂ z) :=
    (div_eq_iff (hQ_ne z)).mp (hconst hz)
  rw [hfg z hz, hgz]
  ring

/-- **Garnett II.5.5 (uniqueness).** Two canonical factorizations of the same function have
the same singular measures, and their outer parts agree up to the unimodular constants:
`C * F = C' * F'` on the disc. Mutual singularity of `μ₁` and `μ₂` is what makes the singular
quotient `S₁ / S₂` unique. -/
theorem IsCanonicalFactorization.unique {f : ℂ → ℂ} {C C' : ℂ} {F F' : ℂ → ℂ}
    {μ₁ μ₂ ν₁ ν₂ : Measure ℂ} (h : IsCanonicalFactorization f C F μ₁ μ₂)
    (h' : IsCanonicalFactorization f C' F' ν₁ ν₂) :
    μ₁ = ν₁ ∧ μ₂ = ν₂ ∧ ∀ z ∈ unitDisc, C * F z = C' * F' z := by
  sorry

end Nevanlinna
