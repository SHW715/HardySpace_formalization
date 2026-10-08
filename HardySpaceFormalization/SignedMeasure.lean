import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic

/-!
# Jordan parts and variation of signed measures

General facts about finite signed measures that mathlib does not yet provide. The Jordan parts
are bounded by the variation. A difference of finite measures has null total variation wherever
both measures vanish. The Jordan parts inherit nullity and mutual singularity from the signed
measure; this is Garnett's remark after (5.7) that the singular parts `μ₁, μ₂` are positive
singular measures. Nothing here depends on the disc.
-/

open MeasureTheory Set
open scoped ENNReal

/-- Both parts of the Jordan decomposition of a signed measure are bounded by its variation. -/
theorem toJordanDecomposition_le_variation {α : Type*} [MeasurableSpace α] (μ : SignedMeasure α) :
    μ.toJordanDecomposition.posPart ≤ μ.variation ∧
      μ.toJordanDecomposition.negPart ≤ μ.variation := by
  -- Claude without review
  obtain ⟨i, hi₁, hi₂, hi₃, hpos, hneg⟩ := μ.toJordanDecomposition_spec
  constructor <;> refine Measure.le_intro fun E hE _ => ?_
  · calc μ.toJordanDecomposition.posPart E
        ≤ ‖μ (i ∩ E)‖ₑ := by
          rw [hpos, SignedMeasure.toMeasureOfZeroLE_apply _ hi₂ hi₁ hE, Real.enorm_eq_ofReal_abs,
            ← ENNReal.ofReal_eq_coe_nnreal]
          exact ENNReal.ofReal_le_ofReal (le_abs_self _)
      _ ≤ μ.variation (i ∩ E) := VectorMeasure.enorm_measure_le_variation _ _
      _ ≤ μ.variation E := measure_mono Set.inter_subset_right
  · calc μ.toJordanDecomposition.negPart E
        ≤ ‖μ (iᶜ ∩ E)‖ₑ := by
          rw [hneg, SignedMeasure.toMeasureOfLEZero_apply _ hi₃ hi₁.compl hE,
            Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_eq_coe_nnreal]
          exact ENNReal.ofReal_le_ofReal (neg_le_abs _)
      _ ≤ μ.variation (iᶜ ∩ E) := VectorMeasure.enorm_measure_le_variation _ _
      _ ≤ μ.variation E := measure_mono Set.inter_subset_right

/-- The total variation of a difference of finite measures vanishes on every set on which both
measures vanish. -/
theorem totalVariation_toSignedMeasure_sub_eq_zero {α : Type*} [MeasurableSpace α]
    {μ₁ μ₂ : Measure α} [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] {S : Set α}
    (h₁ : μ₁ S = 0) (h₂ : μ₂ S = 0) :
    (μ₁.toSignedMeasure - μ₂.toSignedMeasure).totalVariation S = 0 := by
  set μ := μ₁.toSignedMeasure - μ₂.toSignedMeasure
  have hvar : μ.variation ≤ μ₁ + μ₂ := by
    refine VectorMeasure.variation_le_of_forall_enorm_le fun E hE => ?_
    have habs : |μ₁.real E - μ₂.real E| ≤ μ₁.real E + μ₂.real E := by
      rw [abs_le]
      constructor <;> linarith [measureReal_nonneg (μ := μ₁) (s := E),
        measureReal_nonneg (μ := μ₂) (s := E)]
    simp only [μ, sub_apply, Measure.toSignedMeasure_apply_measurable hE,
      Real.enorm_eq_ofReal_abs, Measure.add_apply]
    grw [ENNReal.ofReal_le_ofReal habs]
    rw [ENNReal.ofReal_add measureReal_nonneg measureReal_nonneg, ofReal_measureReal,
      ofReal_measureReal]
  have hS : μ.variation S = 0 :=
    le_zero_iff.mp ((Measure.le_iff'.mp hvar S).trans (by simp [h₁, h₂]))
  obtain ⟨hpos, hneg⟩ := toJordanDecomposition_le_variation μ
  rw [SignedMeasure.totalVariation, Measure.add_apply,
    le_zero_iff.mp ((Measure.le_iff'.mp hpos S).trans hS.le),
    le_zero_iff.mp ((Measure.le_iff'.mp hneg S).trans hS.le), add_zero]

namespace MeasureTheory.SignedMeasure

variable {α : Type*} [MeasurableSpace α]

/-- A signed measure has null total variation on `S` if and only if both of its Jordan parts
vanish on `S`. -/
theorem totalVariation_apply_eq_zero_iff {s : SignedMeasure α} {S : Set α} :
    s.totalVariation S = 0 ↔
      s.toJordanDecomposition.posPart S = 0 ∧ s.toJordanDecomposition.negPart S = 0 := by
  rw [totalVariation, Measure.add_apply, add_eq_zero]

/-- A signed measure is mutually singular with a measure `μ` if and only if both of its Jordan
parts are. -/
theorem mutuallySingular_toENNRealVectorMeasure_iff {s : SignedMeasure α} {μ : Measure α} :
    s ⟂ᵥ μ.toENNRealVectorMeasure ↔
      s.toJordanDecomposition.posPart ⟂ₘ μ ∧ s.toJordanDecomposition.negPart ⟂ₘ μ := by
  rw [mutuallySingular_ennreal_iff, VectorMeasure.ennrealToMeasure_toENNRealVectorMeasure,
    totalVariation_mutuallySingular_iff]

end MeasureTheory.SignedMeasure
