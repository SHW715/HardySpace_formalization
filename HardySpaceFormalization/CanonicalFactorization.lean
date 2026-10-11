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
  -- Claude without review
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
quotient `S₁ / S₂` unique.

Garnett determines `F` by the boundary modulus `|f*|` and `S₁, S₂` by the least harmonic majorant
of `log |f|`. Here both come from the measure `k dσ + μ₂ - μ₁` representing `log |C F S₁ / S₂|`:
it is determined by its Poisson integral, its singular part `μ₂ - μ₁` by the Lebesgue
decomposition, and `μ₁, μ₂` by the Jordan decomposition. No boundary values are needed. -/
theorem IsCanonicalFactorization.unique {f : ℂ → ℂ} {C C' : ℂ} {F F' : ℂ → ℂ}
    {μ₁ μ₂ ν₁ ν₂ : Measure ℂ} (h : IsCanonicalFactorization f C F μ₁ μ₂)
    (h' : IsCanonicalFactorization f C' F' ν₁ ν₂) :
    μ₁ = ν₁ ∧ μ₂ = ν₂ ∧ ∀ z ∈ unitDisc, C * F z = C' * F' z := by
  haveI := h.isFiniteMeasure₁
  haveI := h.isFiniteMeasure₂
  haveI := h'.isFiniteMeasure₁
  haveI := h'.isFiniteMeasure₂
  have h0 : (0 : ℂ) ∈ unitDisc := Metric.mem_ball_self one_pos
  have hS : MeasurableSet (Metric.sphere (0 : ℂ) 1)ᶜ := Metric.isClosed_sphere.measurableSet.compl
  have hσ : circleMeasure 0 1 (Metric.sphere 0 1)ᶜ = 0 := circleMeasure_compl_sphere zero_le_one
  -- Cancel `B`: it does not vanish on a punctured neighborhood of `0`, since its order there is
  -- the finite multiplicity of `f` at `0`, and the identity theorem spreads `G = G'` to the disc.
  set B := BlaschkeProduct (analyticOrderAt f) with hB
  have hBan : AnalyticOnNhd ℂ B unitDisc := analyticOnNhd_blaschkeProduct h.blaschkeCondition
  have hBne : ∀ᶠ z in nhdsWithin (0 : ℂ) {0}ᶜ, B z ≠ 0 := by
    refine (hBan 0 h0).eventually_eq_zero_or_eventually_ne_zero.resolve_left fun hB0 => ?_
    have hord := analyticOrderAt_blaschkeProduct h.blaschkeCondition h0
    rw [analyticOrderAt_eq_top.mpr hB0] at hord
    exact h.blaschkeCondition.ne_top h0 hord.symm
  have hGan : ∀ (c : ℂ) (G : ℂ → ℂ) (ρ₁ ρ₂ : Measure ℂ) [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂],
      IsOuterFunction G → ρ₁ (Metric.sphere 0 1)ᶜ = 0 → ρ₂ (Metric.sphere 0 1)ᶜ = 0 →
      AnalyticOnNhd ℂ (fun z => c * G z * singularFunction ρ₁ z / singularFunction ρ₂ z)
        unitDisc := by
    intro c G ρ₁ ρ₂ _ _ hG hρ₁ hρ₂
    exact Metric.isOpen_ball.analyticOn_iff_analyticOnNhd.mp
      (((analyticOn_const.mul hG.analyticOn).mul (analyticOn_singularFunction hρ₁)).div
        (analyticOn_singularFunction hρ₂) fun z _ => singularFunction_ne_zero ρ₂ z)
  have hdiff := (hGan C F μ₁ μ₂ h.isOuterFunction h.measure_compl_sphere₁
    h.measure_compl_sphere₂).sub (hGan C' F' ν₁ ν₂ h'.isOuterFunction h'.measure_compl_sphere₁
    h'.measure_compl_sphere₂)
  have hfreq : ∃ᶠ z in nhdsWithin (0 : ℂ) {0}ᶜ,
      (C * F z * singularFunction μ₁ z / singularFunction μ₂ z -
        C' * F' z * singularFunction ν₁ z / singularFunction ν₂ z) = 0 := by
    refine Filter.Eventually.frequently ?_
    filter_upwards [hBne, mem_nhdsWithin_of_mem_nhds (Metric.isOpen_ball.mem_nhds h0)]
      with z hBz hz
    have hBG : B z * (C * F z * singularFunction μ₁ z / singularFunction μ₂ z -
        C' * F' z * singularFunction ν₁ z / singularFunction ν₂ z) = 0 := by
      linear_combination (h.eq_mul_div z hz).symm.trans (h'.eq_mul_div z hz)
    exact (mul_eq_zero.mp hBG).resolve_left hBz
  have hG : ∀ z ∈ unitDisc, C * F z * singularFunction μ₁ z / singularFunction μ₂ z =
      C' * F' z * singularFunction ν₁ z / singularFunction ν₂ z := fun z hz =>
    sub_eq_zero.mp
      (hdiff.eqOn_zero_of_preconnected_of_frequently_eq_zero (convex_ball (0 : ℂ) 1).isPreconnected
        h0 hfreq hz)
  -- `log |G| = P[k dσ + μ₂ - μ₁]` and `log |G'| = P[k' dσ + ν₂ - ν₁]`, so the two measures agree.
  have hlogG : ∀ (c : ℂ) (G : ℂ → ℂ) (ρ₁ ρ₂ : Measure ℂ) [IsFiniteMeasure ρ₁]
      [IsFiniteMeasure ρ₂], ‖c‖ = 1 → IsOuterFunction G → ρ₁ (Metric.sphere 0 1)ᶜ = 0 →
      ρ₂ (Metric.sphere 0 1)ᶜ = 0 → ∃ l : ℂ → ℝ, ∀ z ∈ unitDisc,
        Real.log ‖c * G z * singularFunction ρ₁ z / singularFunction ρ₂ z‖ =
          P[0; l ∂ᵥ circleMeasure 0 1 + (ρ₂.toSignedMeasure - ρ₁.toSignedMeasure)] z := by
    intro c G ρ₁ ρ₂ _ _ hc hG hρ₁ hρ₂
    obtain ⟨l, hl, hlogF⟩ := hG.exists_log_norm_eq
    refine ⟨l, fun z hz => ?_⟩
    have hG0 : ‖G z‖ ≠ 0 := norm_ne_zero_iff.mpr (hG.ne_zero hz)
    have hS₁ : ‖singularFunction ρ₁ z‖ ≠ 0 := norm_ne_zero_iff.mpr (singularFunction_ne_zero ρ₁ z)
    have hS₂ : ‖singularFunction ρ₂ z‖ ≠ 0 := norm_ne_zero_iff.mpr (singularFunction_ne_zero ρ₂ z)
    rw [norm_div, norm_mul, norm_mul, hc, one_mul, Real.log_div (mul_ne_zero hG0 hS₁) hS₂,
      Real.log_mul hG0 hS₁, hlogF z hz, log_norm_singularFunction hρ₁ hz,
      log_norm_singularFunction hρ₂ hz,
      poissonIntegral_add (integrable_poissonKernel_withDensityᵥ hσ hz hl)
        ((integrable_poissonKernel_toSignedMeasure hρ₂ hz).sub_vectorMeasure
          (integrable_poissonKernel_toSignedMeasure hρ₁ hz)),
      poissonIntegral_toSignedMeasure_sub hρ₂ hρ₁ hz]
    ring
  obtain ⟨k, hlog⟩ := hlogG C F μ₁ μ₂ h.norm_C h.isOuterFunction h.measure_compl_sphere₁
    h.measure_compl_sphere₂
  obtain ⟨k', hlog'⟩ := hlogG C' F' ν₁ ν₂ h'.norm_C h'.isOuterFunction h'.measure_compl_sphere₁
    h'.measure_compl_sphere₂
  have hcarried : ∀ (l : ℂ → ℝ) (ρ₁ ρ₂ : Measure ℂ) [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂],
      ρ₁ (Metric.sphere 0 1)ᶜ = 0 → ρ₂ (Metric.sphere 0 1)ᶜ = 0 →
      SignedMeasure.totalVariation
        (l ∂ᵥ circleMeasure 0 1 + (ρ₂.toSignedMeasure - ρ₁.toSignedMeasure))
        (Metric.sphere 0 1)ᶜ = 0 := by
    intro l ρ₁ ρ₂ _ _ hρ₁ hρ₂
    have hd := (SignedMeasure.totalVariation_apply_eq_zero_iff_forall hS).mp
      (SignedMeasure.totalVariation_withDensityᵥ_apply_eq_zero (f := l) hS hσ)
    have hm := (SignedMeasure.totalVariation_apply_eq_zero_iff_forall hS).mp
      (totalVariation_toSignedMeasure_sub_eq_zero hρ₂ hρ₁)
    refine (SignedMeasure.totalVariation_apply_eq_zero_iff_forall hS).mpr fun A hA hAm => ?_
    rw [add_apply, hd A hA hAm, hm A hA hAm, add_zero]
  have heq : k ∂ᵥ circleMeasure 0 1 + (μ₂.toSignedMeasure - μ₁.toSignedMeasure) =
      k' ∂ᵥ circleMeasure 0 1 + (ν₂.toSignedMeasure - ν₁.toSignedMeasure) :=
    eq_of_eqOn_poissonIntegral one_pos
      (hcarried k μ₁ μ₂ h.measure_compl_sphere₁ h.measure_compl_sphere₂)
      (hcarried k' ν₁ ν₂ h'.measure_compl_sphere₁ h'.measure_compl_sphere₂)
      fun z hz => by rw [← hlog z hz, ← hlog' z hz, hG z hz]
  -- The singular parts `μ₂ - μ₁` and `ν₂ - ν₁` are the signed measures of the Jordan
  -- decompositions `(μ₂, μ₁)` and `(ν₂, ν₁)`; Lebesgue uniqueness identifies them.
  let jμ : JordanDecomposition ℂ :=
    { posPart := μ₂, negPart := μ₁, mutuallySingular := h.mutuallySingular.symm }
  let jν : JordanDecomposition ℂ :=
    { posPart := ν₂, negPart := ν₁, mutuallySingular := h'.mutuallySingular.symm }
  have hsing : ∀ j : JordanDecomposition ℂ, j.posPart ⟂ₘ circleMeasure 0 1 →
      j.negPart ⟂ₘ circleMeasure 0 1 →
      j.toSignedMeasure ⟂ᵥ (circleMeasure 0 1).toENNRealVectorMeasure := fun j hp hn =>
    SignedMeasure.mutuallySingular_toENNRealVectorMeasure_iff.mpr
      (by rw [JordanDecomposition.toJordanDecomposition_toSignedMeasure]; exact ⟨hp, hn⟩)
  have hj : jμ.toSignedMeasure = jν.toSignedMeasure :=
    (SignedMeasure.eq_singularPart _ k
        (hsing jμ h.singular_circleMeasure₂ h.singular_circleMeasure₁) (add_comm _ _)).trans
      ((congrArg (SignedMeasure.singularPart · (circleMeasure 0 1)) heq).trans
        (SignedMeasure.eq_singularPart _ k'
          (hsing jν h'.singular_circleMeasure₂ h'.singular_circleMeasure₁) (add_comm _ _)).symm)
  -- Jordan uniqueness gives `μⱼ = νⱼ`; dividing out the common singular factors gives `CF = C'F'`.
  have hjj := JordanDecomposition.toSignedMeasure_injective hj
  have hμ₂ : μ₂ = ν₂ := congrArg JordanDecomposition.posPart hjj
  have hμ₁ : μ₁ = ν₁ := congrArg JordanDecomposition.negPart hjj
  refine ⟨hμ₁, hμ₂, fun z hz => ?_⟩
  have hs : singularFunction ν₁ z / singularFunction ν₂ z ≠ 0 :=
    div_ne_zero (singularFunction_ne_zero ν₁ z) (singularFunction_ne_zero ν₂ z)
  have hGz := hG z hz
  rw [hμ₁, hμ₂] at hGz
  exact mul_right_cancel₀ hs (by linear_combination hGz)

/-- **Garnett II.5.5 (converse).** For a multiplicity `m` satisfying the Blaschke condition, an
outer function `F`, singular functions `S₁, S₂`, and any constant `C`, the function
`C * B * F * S₁ / S₂`, extended by zero outside the disc, belongs to the Nevanlinna class.
Garnett's normalization `|C| = 1` is not needed.

Garnett majorizes `log |f|` by a Poisson integral and applies Theorem 5.1. Here instead each factor
lies in `N` (`B, S₁ ∈ H^∞`, `F ∈ N`, and `1 / S₂ ∈ N` since `S₂` has no zeros), and `N` is closed
under scalar multiplication and products. -/
theorem memNevanlinnaDisc_indicator_mul_blaschkeProduct {m : ℂ → ℕ∞} (hm : BlaschkeCondition m)
    (C : ℂ) {F S₁ S₂ : ℂ → ℂ} (hF : IsOuterFunction F) (hS₁ : IsSingularFunction S₁)
    (hS₂ : IsSingularFunction S₂) :
    MemNevanlinnaDisc
      (unitDisc.indicator fun z => C * BlaschkeProduct m z * F z * S₁ z / S₂ z) := by
  have hB : MemNevanlinnaDisc (unitDisc.indicator (BlaschkeProduct m)) :=
    memNevanlinnaDisc_of_memHpDisc (by simp) (memHpDisc_blaschkeProduct hm)
  have hS₁N : MemNevanlinnaDisc (unitDisc.indicator S₁) :=
    memNevanlinnaDisc_of_memHpDisc (by simp) hS₁.memHpDisc_indicator
  have hS₂N : MemNevanlinnaDisc (unitDisc.indicator S₂)⁻¹ :=
    (memNevanlinnaDisc_of_memHpDisc (by simp) hS₂.memHpDisc_indicator).inv fun z hz => by
      rw [Set.indicator_of_mem hz]
      exact hS₂.ne_zero hz
  have heq : (unitDisc.indicator fun z => C * BlaschkeProduct m z * F z * S₁ z / S₂ z) =
      C • (unitDisc.indicator (BlaschkeProduct m) * unitDisc.indicator F *
        unitDisc.indicator S₁ * (unitDisc.indicator S₂)⁻¹) := by
    funext z
    by_cases hz : z ∈ unitDisc
    · simp only [Set.indicator_of_mem hz, Pi.smul_apply, Pi.mul_apply, Pi.inv_apply, smul_eq_mul]
      ring
    · simp [Set.indicator_of_notMem hz]
  rw [heq]
  exact (((hB.mul hF.memNevanlinnaDisc_indicator).mul hS₁N).mul hS₂N).smul C

end Nevanlinna
