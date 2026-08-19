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


/-- If `P * φ` is circle-integrable, then `φ` is integrable against the circle measure weighted by
the nonnegative density `P`. -/
lemma integrable_withDensity_circleMeasure_of_circleIntegrable
    {c : ℂ} {R : ℝ} {P φ : ℂ → ℝ}
    (hP_nonneg : ∀ᵐ z ∂circleMeasure c R, 0 ≤ P z)
    (hPφ : CircleIntegrable (fun z : ℂ => P z * φ z) c R) :
    Integrable φ ((circleMeasure c R).withDensity fun z => ENNReal.ofReal (P z)) := by
  sorry

/-- Integrating against a density with respect to circle measure is the same as taking the
circle average after multiplying by that density. -/
lemma integral_withDensity_circleMeasure_eq_circleAverage_mul
    {c : ℂ} {R : ℝ} {P φ : ℂ → ℝ}
    (hP_nonneg : ∀ᵐ z ∂circleMeasure c R, 0 ≤ P z)
    (hPφ : CircleIntegrable (fun z : ℂ => P z * φ z) c R) :
    circleAverage (fun z : ℂ => P z * φ z) c R =
     ∫ z, φ z ∂((circleMeasure c R).withDensity fun z => ENNReal.ofReal (P z)) := by
  sorry

/-- If a circle-density is nonnegative and has circle average one, then the corresponding weighted
circle measure is a probability measure. -/
lemma isProbabilityMeasure_withDensity_circleMeasure
    {c : ℂ} {R : ℝ} {P : ℂ → ℝ}
    (hP_nonneg : ∀ᵐ z ∂circleMeasure c R, 0 ≤ P z)
    (hP_int : CircleIntegrable P c R)
    (hP_avg : circleAverage P c R = 1) :
    IsProbabilityMeasure ((circleMeasure c R).withDensity fun z => ENNReal.ofReal (P z)) := by
  sorry

end
