import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.CircleAverage

open Complex MeasureTheory Metric Real
open scoped ENNReal

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The normalized angular measure on one full turn.  This is the measure used by
`circleAverage` before pushing forward by `circleMap`. -/
def angularMeasure : Measure ℝ :=
  ENNReal.ofReal (1 / (2 * π)) • volume.restrict (Set.Ico 0 (2 * π))

/-- The normalized measure on the circle with center `c` and signed radius `R`, obtained by
pushing normalized angular measure forward along `circleMap c R`. -/
def circleMeasure (c : ℂ) (R : ℝ) : Measure ℂ := Measure.map (circleMap c R) angularMeasure

-- # Note: this is duplicate with `circle_measure_isProbabilityMeasure` in `HardySpaceDisc.lean`
/-- Integration against `circleMeasure` is integration of the pullback along `circleMap` against
the normalized angular measure. -/
lemma integral_circleMeasure_eq_integral_angularMeasure
    {c : ℂ} {R : ℝ} {f : ℂ → E}
    (hf : AEStronglyMeasurable f (circleMeasure c R)) :
    ∫ z, f z ∂circleMeasure c R = ∫ θ, f (circleMap c R θ) ∂angularMeasure := by
  simpa [circleMeasure] using
    (integral_map (μ := angularMeasure) (φ := circleMap c R)
      (measurable_circleMap c R).aemeasurable hf)

/-- The normalized angular measure is a probability measure. -/
instance isProbabilityMeasure_angularMeasure :
    IsProbabilityMeasure angularMeasure := by
  unfold angularMeasure
  rw [isProbabilityMeasure_iff]
  rw [Measure.smul_apply, Measure.restrict_apply_univ, Real.volume_Ico]
  simp only [smul_eq_mul]
  rw [← ENNReal.ofReal_mul (by positivity)]
  have hreal : 1 / (2 * π) * (2 * π - 0) = 1 := by
    field_simp [Real.pi_ne_zero]; ring
  rw [hreal, ENNReal.ofReal_one]

/-- The circle measure is a probability measure. -/
instance isProbabilityMeasure_circleMeasure {c : ℂ} {R : ℝ} :
    IsProbabilityMeasure (circleMeasure c R) := by
  rw [circleMeasure]
  exact Measure.isProbabilityMeasure_map (measurable_circleMap c R).aemeasurable

omit [NormedSpace ℝ E] in
/-- Circle-integrability gives almost-everywhere strong measurability of the pullback to the
angular parameter measure. -/
lemma CircleIntegrable.aestronglyMeasurable_comp_circleMap_angularMeasure
    {c : ℂ} {R : ℝ} {f : ℂ → E} (hf : CircleIntegrable f c R) :
    AEStronglyMeasurable (fun θ : ℝ => f (circleMap c R θ)) angularMeasure := by
  have hIco :
      IntegrableOn (fun θ : ℝ => f (circleMap c R θ)) (Set.Ico 0 (2 * π)) volume := by
    rw [← intervalIntegrable_iff_integrableOn_Ico_of_le (by positivity)]
    exact hf
  unfold angularMeasure
  exact AEStronglyMeasurable.mono_ac Measure.smul_absolutelyContinuous
    hIco.aestronglyMeasurable

/-- On one half-open period, a nondegenerate circle parametrization is a measurable embedding. -/
lemma measurableEmbedding_circleMap_Ico {c : ℂ} {R : ℝ} (hR : R ≠ 0) :
    MeasurableEmbedding ((Set.Ico (0 : ℝ) (2 * π)).restrict (circleMap c R)) := by
  refine ContinuousOn.measurableEmbedding measurableSet_Ico
    (continuous_circleMap c R).continuousOn ?_
  exact injOn_circleMap_of_abs_sub_le' (c := c) (R := R) hR (by linarith)

omit [NormedSpace ℝ E] in
/-- Circle-integrability gives almost-everywhere strong measurability with respect to the
normalized circle measure. -/
lemma CircleIntegrable.aestronglyMeasurable_circleMeasure
    {c : ℂ} {R : ℝ} {f : ℂ → E} (hf : CircleIntegrable f c R) :
    AEStronglyMeasurable f (circleMeasure c R) := by
  -- codex without review
  by_cases hR : R = 0
  · subst R
    have hmap0 :
        Measure.map (Function.const ℝ c) angularMeasure = Measure.dirac c := by
      change Measure.map (fun _ : ℝ => c) angularMeasure = Measure.dirac c
      rw [Measure.map_const]
      simp [measure_univ]
    rw [circleMeasure, circleMap_zero_radius, hmap0]
    exact aestronglyMeasurable_dirac
  · let s : Set ℝ := Set.Ico 0 (2 * π)
    let μs : Measure s := Measure.comap ((↑) : s → ℝ) (volume.restrict s)
    have hsubtype_map : Measure.map ((↑) : s → ℝ) μs = volume.restrict s := by
      calc
        Measure.map ((↑) : s → ℝ) μs = (volume.restrict s).restrict s := by
          simpa [μs] using map_comap_subtype_coe (s := s) measurableSet_Ico
            (volume.restrict s)
        _ = volume.restrict s := by
          rw [Measure.restrict_restrict measurableSet_Ico]
          simp [s]
    have hIco :
        IntegrableOn (fun θ : ℝ => f (circleMap c R θ)) s volume := by
      change IntegrableOn (fun θ : ℝ => f (circleMap c R θ))
        (Set.Ico 0 (2 * π)) volume
      rw [← intervalIntegrable_iff_integrableOn_Ico_of_le (by positivity)]
      exact hf
    have hsub :
        AEStronglyMeasurable
          (fun θ : s => f (circleMap c R θ)) μs := by
      have hmap :
          AEStronglyMeasurable (fun θ : ℝ => f (circleMap c R θ))
            (Measure.map ((↑) : s → ℝ) μs) := by
        rw [hsubtype_map]
        exact hIco.aestronglyMeasurable
      exact ((MeasurableEmbedding.subtype_coe measurableSet_Ico).aestronglyMeasurable_map_iff).1
        hmap
    have hemb : MeasurableEmbedding (s.restrict (circleMap c R)) := by
      simpa [s] using measurableEmbedding_circleMap_Ico (c := c) (R := R) hR
    have hcircle_base :
        AEStronglyMeasurable f (Measure.map (s.restrict (circleMap c R)) μs) :=
      (hemb.aestronglyMeasurable_map_iff).2 hsub
    have hmap_base :
        Measure.map (circleMap c R) (volume.restrict s) =
          Measure.map (s.restrict (circleMap c R)) μs := by
      rw [← hsubtype_map]
      rw [Measure.map_map (measurable_circleMap c R) measurable_subtype_coe]
      rfl
    have hcircle_eq :
        circleMeasure c R =
          ENNReal.ofReal (1 / (2 * π)) • Measure.map (s.restrict (circleMap c R)) μs := by
      unfold circleMeasure angularMeasure
      rw [Measure.map_smul, hmap_base]
    exact AEStronglyMeasurable.mono_ac
      (by rw [hcircle_eq]; exact Measure.smul_absolutelyContinuous) hcircle_base

omit [NormedSpace ℝ E] in
/-- Circle-integrable functions are integrable against normalized circle measure. -/
lemma CircleIntegrable.integrable_circleMeasure
    {c : ℂ} {R : ℝ} {f : ℂ → E} (hf : CircleIntegrable f c R) :
    Integrable f (circleMeasure c R) := by
  apply (integrable_map_measure hf.aestronglyMeasurable_circleMeasure
    (measurable_circleMap c R).aemeasurable).2
  have hIco : IntegrableOn (fun θ : ℝ => f (circleMap c R θ))
      (Set.Ico 0 (2 * π)) volume := by
    rw [← intervalIntegrable_iff_integrableOn_Ico_of_le (by positivity)]
    exact hf
  exact hIco.smul_measure ENNReal.ofReal_ne_top

/-- `circleAverage` is integration with respect to the normalized circle measure. -/
lemma circleAverage_eq_integral_circleMeasure {c : ℂ} {R : ℝ} {f : ℂ → E}
    (hf : CircleIntegrable f c R) :
    circleAverage f c R = ∫ z, f z ∂circleMeasure c R := by
  rw [integral_circleMeasure_eq_integral_angularMeasure
    hf.aestronglyMeasurable_circleMeasure]
  unfold circleAverage angularMeasure
  rw [integral_smul_measure]
  rw [intervalIntegral.integral_of_le (by positivity)]
  rw [← integral_Ico_eq_integral_Ioc]
  congr 1
  rw [ENNReal.toReal_ofReal]
  · field_simp [Real.pi_ne_zero]
  · positivity

/-- The circle measure is supported on its circle. -/
lemma ae_mem_sphere_circleMeasure {c : ℂ} {R : ℝ} (hR : 0 ≤ R) :
    ∀ᵐ z ∂circleMeasure c R, z ∈ sphere c R :=
    (ae_map_iff (measurable_circleMap c R).aemeasurable
    (p := fun z => z ∈ sphere c R) Metric.isClosed_sphere.measurableSet).2 <|
      ae_of_all _ fun θ => circleMap_mem_sphere c hR θ


/-- The circle measure vanishes off its circle. -/
theorem circleMeasure_compl_sphere {c : ℂ} {R : ℝ} (hR : 0 ≤ R) : circleMeasure c R (sphere c R)ᶜ = 0 := by
  have h := ae_mem_sphere_circleMeasure (c := c) (R := R) hR
  rwa [ae_iff, ← Set.compl_setOf, Set.setOf_mem_eq] at h

/-- Continuous boundary data is integrable against the circle measure. -/
theorem ContinuousOn.integrable_circleMeasure {k : ℂ → ℝ} {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hk : ContinuousOn k (sphere c R)) : Integrable k (circleMeasure c R) := by
  have hae := ae_mem_sphere_circleMeasure (c := c) (R := R) hR
  have hmeas : AEStronglyMeasurable k (circleMeasure c R) := by
    rw [← Measure.restrict_eq_self_of_ae_mem hae]
    exact hk.aestronglyMeasurable Metric.isClosed_sphere.measurableSet
  obtain ⟨C, hC⟩ := (isCompact_sphere c R).exists_bound_of_continuousOn hk
  refine (integrable_const C).mono' hmeas ?_
  filter_upwards [hae] with z hz using hC z hz

/-- Continuous real boundary data belongs to every Lp space on the circle. -/
theorem ContinuousOn.memLp_circleMeasure {k : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hk : ContinuousOn k (sphere c R)) (hR : 0 ≤ R) (p : ℝ≥0∞) :
    MemLp k p (circleMeasure c R) := by
  obtain ⟨C, hC⟩ := (isCompact_sphere c R).exists_bound_of_continuousOn hk
  exact MemLp.of_bound (hk.integrable_circleMeasure hR).aestronglyMeasurable C
    ((ae_mem_sphere_circleMeasure hR).mono fun z hz => hC z hz)

/-- If `P * φ` is circle-integrable, then `φ` is integrable against the circle measure weighted by
the nonnegative density `P`. -/
lemma integrable_withDensity_circleMeasure_of_circleIntegrable
    {c : ℂ} {R : ℝ} {P φ : ℂ → ℝ}
    (hP_meas : AEMeasurable P (circleMeasure c R))
    (hP_nonneg : ∀ᵐ z ∂circleMeasure c R, 0 ≤ P z)
    (hPφ : CircleIntegrable (fun z : ℂ => P z * φ z) c R) :
    Integrable φ ((circleMeasure c R).withDensity fun z => ENNReal.ofReal (P z)) := by
  apply (integrable_withDensity_iff_integrable_smul₀' hP_meas.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).2
  refine hPφ.integrable_circleMeasure.congr ?_
  filter_upwards [hP_nonneg] with z hz
  simp [ENNReal.toReal_ofReal hz, smul_eq_mul]

/-- Integrating against a density with respect to circle measure is the same as taking the
circle average after multiplying by that density. -/
lemma integral_withDensity_circleMeasure_eq_circleAverage_mul
    {c : ℂ} {R : ℝ} {P φ : ℂ → ℝ}
    (hP_meas : AEMeasurable P (circleMeasure c R))
    (hP_nonneg : ∀ᵐ z ∂circleMeasure c R, 0 ≤ P z)
    (hPφ : CircleIntegrable (fun z : ℂ => P z * φ z) c R) :
    circleAverage (fun z : ℂ => P z * φ z) c R =
     ∫ z, φ z ∂((circleMeasure c R).withDensity fun z => ENNReal.ofReal (P z)) := by
  rw [circleAverage_eq_integral_circleMeasure hPφ,
    integral_withDensity_eq_integral_toReal_smul₀ hP_meas.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [hP_nonneg] with z hz
  simp [ENNReal.toReal_ofReal hz, smul_eq_mul]

/-- If a circle-density is nonnegative and has circle average one, then the corresponding weighted
circle measure is a probability measure. -/
lemma isProbabilityMeasure_withDensity_circleMeasure
    {c : ℂ} {R : ℝ} {P : ℂ → ℝ}
    (hP_nonneg : ∀ᵐ z ∂circleMeasure c R, 0 ≤ P z)
    (hP_int : CircleIntegrable P c R)
    (hP_avg : circleAverage P c R = 1) :
    IsProbabilityMeasure ((circleMeasure c R).withDensity fun z => ENNReal.ofReal (P z)) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hP_int.integrable_circleMeasure hP_nonneg,
    ← circleAverage_eq_integral_circleMeasure hP_int, hP_avg, ENNReal.ofReal_one]

end
