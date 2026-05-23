import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp


noncomputable section

open scoped NNReal ENNReal

open MeasureTheory Set

variable {α ε ε' E F G 𝕜 : Type*} {m m0 : MeasurableSpace α} {p : ℝ≥0∞} {q : ℝ} {f : α → E}
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
  [NormedDivisionRing 𝕜] [Module 𝕜 F] [NormSMulClass 𝕜 F]
  {μ : Measure α} {f g : α → ε}




/-- Fixed `eLpNorm` where raised to the power `p` when `0 < p < 1`. -/
def eLpNormFixed {α ε : Type*} [ENorm ε] {_ : MeasurableSpace α}
    (f : α → ε) (p : ℝ≥0∞) (μ : Measure α := by volume_tac) : ℝ≥0∞ :=
  if p ∈ Ioo 0 1 then (eLpNorm f p μ) ^ p.toReal else eLpNorm f p μ


theorem eLpNormFixed_neg (f : α → F) (p : ℝ≥0∞) (μ : Measure α) :
    eLpNormFixed (-f) p μ = eLpNormFixed f p μ := by simp [eLpNormFixed, eLpNorm_neg]


def eLpFixedScalar (c : 𝕜) (p : ℝ≥0∞) : ℝ≥0∞ :=
  if p ∈ Ioo 0 1 then ‖c‖ₑ ^ p.toReal else ‖c‖ₑ


theorem eLpNormFixed_const_smul
    (c : 𝕜) (f : α → F) (p : ℝ≥0∞) (μ : Measure α) :
    eLpNormFixed (c • f) p μ = (eLpFixedScalar c p) * eLpNormFixed f p μ := by
  by_cases hp : p ∈ Ioo (0 : ℝ≥0∞) 1
  · simp [eLpNormFixed, eLpFixedScalar, hp, eLpNorm_const_smul, ENNReal.mul_rpow_of_nonneg]
  · simp [eLpNormFixed, eLpFixedScalar, hp, eLpNorm_const_smul]

theorem eLpNormFixed_eq_zero_iff
    [TopologicalSpace ε] [ENormedAddMonoid ε]
    {f : α → ε} (hf : AEStronglyMeasurable f μ) (h0 : p ≠ 0) :
    eLpNormFixed f p μ = 0 ↔ f =ᵐ[μ] 0 := by
  by_cases hp : p ∈ Ioo (0 : ℝ≥0∞) 1
  · have hp_ne_top : p ≠ ∞ := ne_of_lt (hp.2.trans ENNReal.one_lt_top)
    have hpt : 0 < p.toReal := ENNReal.toReal_pos h0 hp_ne_top
    simp only [eLpNormFixed, hp, if_true]
    constructor
    · intro h
      have he : eLpNorm f p μ = 0 := (ENNReal.rpow_eq_zero_iff_of_pos hpt).1 h
      exact (eLpNorm_eq_zero_iff hf h0).1 he
    · intro h
      have he : eLpNorm f p μ = 0 := (eLpNorm_eq_zero_iff hf h0).2 h
      exact (ENNReal.rpow_eq_zero_iff_of_pos hpt).2 he
  · simp only [eLpNormFixed, hp, if_false]
    exact eLpNorm_eq_zero_iff hf h0

theorem eLpNormFixed_add_le
    [TopologicalSpace ε] [ESeminormedAddMonoid ε]
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
     : eLpNormFixed (f + g) p μ ≤ eLpNormFixed f p μ + eLpNormFixed g p μ := by
  by_cases hp0 : p = 0
  · simp [eLpNormFixed, hp0]
  by_cases hp1 : 1 ≤ p
  · have hp_not_mem_Ioo : p ∉ Ioo (0 : ℝ≥0∞) 1 := by
      intro hp; exact (not_lt_of_ge hp1) hp.2
    simpa [eLpNormFixed, hp_not_mem_Ioo] using eLpNorm_add_le hf hg hp1
  · have hp_mem_Ioo : p ∈ Ioo (0 : ℝ≥0∞) 1 := by
      exact ⟨pos_iff_ne_zero.mpr hp0, lt_of_not_ge hp1⟩
    simp [eLpNormFixed, hp_mem_Ioo]
    -- The rest is given by codex
    have hp_ne_top : p ≠ ∞ := (ne_of_lt (hp_mem_Ioo.2.trans ENNReal.one_lt_top))
    have hq_pos : 0 < p.toReal := ENNReal.toReal_pos hp0 hp_ne_top
    have hq_le_one : p.toReal ≤ 1 := by
      exact (ENNReal.toReal_le_toReal hp_ne_top (by simp)).2 hp_mem_Ioo.2.le
    rw [eLpNorm_eq_eLpNorm' hp0 hp_ne_top,
      eLpNorm_eq_eLpNorm' hp0 hp_ne_top,
      eLpNorm_eq_eLpNorm' hp0 hp_ne_top]
    rw [← lintegral_rpow_enorm_eq_rpow_eLpNorm' (μ := μ) (f := f + g) hq_pos,
      ← lintegral_rpow_enorm_eq_rpow_eLpNorm' (μ := μ) (f := f) hq_pos,
      ← lintegral_rpow_enorm_eq_rpow_eLpNorm' (μ := μ) (f := g) hq_pos]
    calc
      (∫⁻ x, ‖(f + g) x‖ₑ ^ p.toReal ∂μ)
          ≤ ∫⁻ x, ‖f x‖ₑ ^ p.toReal + ‖g x‖ₑ ^ p.toReal ∂μ := by
        refine lintegral_mono ?_
        intro x
        have hnorm : ‖(f + g) x‖ₑ ≤ ‖f x‖ₑ + ‖g x‖ₑ := by
          simpa [Pi.add_apply] using enorm_add_le (f x) (g x)
        calc
          ‖(f + g) x‖ₑ ^ p.toReal
              ≤ (‖f x‖ₑ + ‖g x‖ₑ) ^ p.toReal := by
            exact ENNReal.rpow_le_rpow hnorm hq_pos.le
          _ ≤ ‖f x‖ₑ ^ p.toReal + ‖g x‖ₑ ^ p.toReal := by
            exact ENNReal.rpow_add_le_add_rpow (‖f x‖ₑ) (‖g x‖ₑ) hq_pos.le hq_le_one
      _ = (∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ) + ∫⁻ x, ‖g x‖ₑ ^ p.toReal ∂μ := by
        rw [lintegral_add_left' (hf.enorm.pow_const p.toReal)]

theorem eLpNormFixed_le_eLpNormFixed_of_exponent_le
    [TopologicalSpace ε] [ContinuousENorm ε]
    {f : α → ε} {p q : ℝ≥0∞} (hpq : p ≤ q) [Fact (1 ≤ p)] [IsProbabilityMeasure μ]
    (hf : AEStronglyMeasurable f μ) :
    eLpNormFixed f p μ ≤ eLpNormFixed f q μ := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hq1 : (1 : ℝ≥0∞) ≤ q := hp1.trans hpq
  have hp_not_mem_Ioo : p ∉ Ioo (0 : ℝ≥0∞) 1 := by
    intro hp
    exact (not_lt_of_ge hp1) hp.2
  have hq_not_mem_Ioo : q ∉ Ioo (0 : ℝ≥0∞) 1 := by
    intro hq
    exact (not_lt_of_ge hq1) hq.2
  simpa [eLpNormFixed, hp_not_mem_Ioo, hq_not_mem_Ioo] using
    eLpNorm_le_eLpNorm_of_exponent_le hpq hf
