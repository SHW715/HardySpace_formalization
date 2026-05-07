import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.Analysis.Analytic.Constructions
import HardySpaceFormalization.eLpNormFixed



/-!
# Classical Hardy space `H^p` on unit disc in ℂ


-/


noncomputable section

open scoped Real ENNReal
open MeasureTheory Real Complex


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The open unit disc in `ℂ`, represented as the metric ball of radius `1` around `0`. -/
def unitDisc : Set ℂ :=
  Metric.ball (0 : ℂ) 1

lemma radial_point_mem_unitDisc {r θ : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    r * exp (I * θ) ∈ unitDisc := by
  rw [unitDisc, Metric.mem_ball, dist_zero_right]
  calc
    ‖r * exp (I * θ)‖ = |r| := by simp
    _ = r := abs_of_nonneg hr0.le
    _ < 1 := hr1

namespace HardySpace

/-- The Hardy `p`-norm on the unit disc. -/
def hardyNorm {E : Type*} [NormedAddCommGroup E]
    (f : ℂ → E) (p : ℝ≥0∞) : ℝ≥0∞ :=
   ⨆ (r : ℝ) (_ : 0 < r ∧ r < 1),
    eLpNormFixed (fun (θ : ℝ) ↦ f (r * exp (I * θ))) p
   (ENNReal.ofReal (1 / (2 * π)) • volume.restrict (Set.Ico 0 (2 * π)))

/-- Hardy `∞`-norm on the unit disc is equal to the supremum norm on the disc. -/
lemma hardyNorm_top_eq_Sup_norm
    {f : ℂ → E} (hf : ContinuousOn f unitDisc) :
    hardyNorm f ∞ = ⨆ z : unitDisc, ENNReal.ofReal ‖f z.1‖ := by sorry

lemma hardyNorm_const_smul (c : ℂ) (f : ℂ → E) (p : ℝ≥0∞) :
    hardyNorm (c • f) p = eLpFixedScalar c p * hardyNorm f p := by
  simp [hardyNorm, ENNReal.mul_iSup]
  congr
  ext r
  congr
  ext hr
  simpa [Pi.smul_apply] using
    eLpNormFixed_const_smul c (fun θ : ℝ => f (r * exp (I * θ))) p
      (ENNReal.ofReal (π⁻¹ * 2⁻¹) • volume.restrict (Set.Ico 0 (2 * π)))

/-- Hardy norm satisfies triangle inequality. -/
lemma hardyNorm_add_le {p : ℝ≥0∞} {f g : ℂ → E}
    (hf_an : AnalyticOn ℂ f unitDisc) (hg_an : AnalyticOn ℂ g unitDisc) :
    hardyNorm (f + g) p ≤ hardyNorm f p + hardyNorm g p := by
  unfold hardyNorm
  -- This part is given by codex
  let μ : Measure ℝ := ENNReal.ofReal (1 / (2 * π)) • volume.restrict (Set.Ico 0 (2 * π))
  change
    (⨆ (r : ℝ) (_ : 0 < r ∧ r < 1), eLpNormFixed (fun θ : ℝ => _) p μ) ≤
        (⨆ (r : ℝ) (_ : 0 < r ∧ r < 1), eLpNormFixed (fun θ : ℝ => _) p μ) +
          (⨆ (r : ℝ) (_ : 0 < r ∧ r < 1), eLpNormFixed (fun θ : ℝ => _) p μ)
  refine iSup_le ?_
  intro r
  refine iSup_le ?_
  intro hr
  have hf_meas : AEStronglyMeasurable (fun θ : ℝ => f (r * exp (I * θ))) μ := by
    have hcont : Continuous (fun θ : ℝ => f (r * exp (I * θ))) := by
      simpa [Function.comp_def] using hf_an.continuousOn.comp_continuous (by fun_prop)
          (fun θ => radial_point_mem_unitDisc hr.1 hr.2)
    exact hcont.aestronglyMeasurable
  have hg_meas : AEStronglyMeasurable (fun θ : ℝ => g (r * exp (I * θ))) μ := by
    have hcont : Continuous (fun θ : ℝ => g (r * exp (I * θ))) := by
      simpa [Function.comp_def] using hg_an.continuousOn.comp_continuous (by fun_prop)
          (fun θ => radial_point_mem_unitDisc hr.1 hr.2)
    exact hcont.aestronglyMeasurable
  calc
    eLpNormFixed (fun θ : ℝ => (f + g) _) p μ
        ≤ eLpNormFixed (fun θ : ℝ => f _) p μ + eLpNormFixed (fun θ : ℝ => g _) p μ := by
         simpa [Pi.add_apply] using eLpNormFixed_add_le hf_meas hg_meas
    _ ≤ (⨆ (r : ℝ) (_ : 0 < r ∧ r < 1), eLpNormFixed (fun θ : ℝ => f _) p μ) +
        (⨆ (r : ℝ) (_ : 0 < r ∧ r < 1), eLpNormFixed (fun θ : ℝ => g _) p μ) := by
       have hf_le : eLpNormFixed (fun θ : ℝ => f (r * exp (I * θ))) p μ ≤
        ⨆ (r : ℝ) (_ : 0 < r ∧ r < 1), eLpNormFixed (fun θ : ℝ => f (r * exp (I * θ))) p μ := by
        exact (le_iSup (fun hr : 0 < r ∧ r < 1 => eLpNormFixed (fun θ : ℝ => f (r * exp (I * θ))) p μ) hr).trans
          (le_iSup (fun r : ℝ => ⨆ (_ : 0 < r ∧ r < 1), eLpNormFixed (fun θ : ℝ => f (r * exp (I * θ))) p μ) r)
       have hg_le : eLpNormFixed (fun θ : ℝ => g (r * exp (I * θ))) p μ ≤
        ⨆ (r : ℝ) (_ : 0 < r ∧ r < 1), eLpNormFixed (fun θ : ℝ => g (r * exp (I * θ))) p μ := by
         exact (le_iSup (fun hr : 0 < r ∧ r < 1 => eLpNormFixed (fun θ : ℝ => g (r * exp (I * θ))) p μ) hr).trans
          (le_iSup (fun r : ℝ => ⨆ (_ : 0 < r ∧ r < 1), eLpNormFixed (fun θ : ℝ => g (r * exp (I * θ))) p μ) r)
       exact add_le_add hf_le hg_le

/-- Membership in the Hardy space `H^p` on the unit disc. -/
def MemHpDisc
    (p : ℝ≥0∞) (f : ℂ → E) : Prop :=
  AnalyticOn ℂ f unitDisc ∧ hardyNorm f p < ∞ ∧ ∀ z ∉ unitDisc, f z = 0


lemma MemHpDisc.add {p : ℝ≥0∞} {f g : ℂ → E}
    (hf : MemHpDisc (E := E) p f) (hg : MemHpDisc (E := E) p g) :
    MemHpDisc (E := E) p (f + g) := by
    unfold MemHpDisc at *
    rcases hf with ⟨hf_an, ⟨hf_norm, hf_zero⟩⟩
    rcases hg with ⟨hg_an, ⟨hg_norm, hg_zero⟩⟩
    constructor
    . exact AnalyticOn.add hf_an hg_an
    . constructor
      . exact lt_of_le_of_lt (hardyNorm_add_le hf_an hg_an)
          (ENNReal.add_lt_top.2 ⟨hf_norm, hg_norm⟩)
      . intro z hz; simp [Pi.add_apply, hf_zero z hz, hg_zero z hz]

lemma MemHpDisc.zero {p : ℝ≥0∞} :
    MemHpDisc (E := E) p (0 : ℂ → E) := by
    unfold MemHpDisc
    constructor
    . exact analyticOn_const
    . constructor
      . unfold hardyNorm
        by_cases hp : p ∈ Set.Ioo (0 : ℝ≥0∞) 1
        · have hpt : 0 < p.toReal := ENNReal.toReal_pos hp.1.ne' (ne_of_lt (hp.2.trans ENNReal.one_lt_top))
          simp [eLpNormFixed, hp, ENNReal.zero_rpow_of_pos hpt]
        · simp [eLpNormFixed, hp]
      . intro z hz; rfl

lemma MemHpDisc.smul {p : ℝ≥0∞} (c : ℂ) {f : ℂ → E}
    (hf : MemHpDisc (E := E) p f) :
    MemHpDisc (E := E) p (c • f) := by
    unfold MemHpDisc at *
    rcases hf with ⟨hf_an, ⟨hf_norm, hf_zero⟩⟩
    constructor
    . exact AnalyticOn.const_smul hf_an
    . constructor
      . rw [hardyNorm_const_smul]
        have hscalar : eLpFixedScalar c p < ∞ := by
          by_cases hp : p ∈ Set.Ioo (0 : ℝ≥0∞) 1
          · simp [eLpFixedScalar, hp]
            exact ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg (by simp)
          · simp [eLpFixedScalar, hp]
        exact ENNReal.mul_lt_top hscalar hf_norm
      . intro z hz; simp [hf_zero z hz]


def HpDisc (p : ℝ≥0∞) : Submodule ℂ (ℂ → E) where
  carrier := {f : ℂ → E | MemHpDisc (E := E) p f}
  add_mem' := MemHpDisc.add
  zero_mem' := MemHpDisc.zero
  smul_mem' := MemHpDisc.smul

namespace HpDisc

instance instNorm (p : ℝ≥0∞) : Norm (HpDisc (E := E) p) where
  norm f := (hardyNorm (E := E) f.1 p).toReal

instance instDist (p : ℝ≥0∞) : Dist (HpDisc (E := E) p) where
  dist f g := ‖-f + g‖

instance instEDist (p : ℝ≥0∞) : EDist (HpDisc (E := E) p) where
  edist f g := hardyNorm (E := E) (f.1 - g.1) p

@[simp] lemma norm_def (p : ℝ≥0∞) (f : HpDisc (E := E) p) :
    ‖f‖ = (hardyNorm (E := E) f.1 p).toReal := by rfl

@[simp] lemma norm_zero (p : ℝ≥0∞) :
    ‖(0 : HpDisc (E := E) p)‖ = 0 := by
  by_cases hp : p ∈ Set.Ioo (0 : ℝ≥0∞) 1
  · have hpt : 0 < p.toReal := ENNReal.toReal_pos hp.1.ne' (ne_of_lt (hp.2.trans ENNReal.one_lt_top))
    simp [hardyNorm, eLpNormFixed, hp, ENNReal.zero_rpow_of_pos hpt]
  · simp [hardyNorm, eLpNormFixed, hp]

@[simp] lemma norm_neg (p : ℝ≥0∞) (f : HpDisc (E := E) p) :
    ‖-f‖ = ‖f‖ := by
  simp [hardyNorm]
  congr; ext r; congr; ext hr
  exact eLpNormFixed_neg (fun θ : ℝ => f.1 (r * exp (I * θ))) p
    (ENNReal.ofReal (π⁻¹ * 2⁻¹) • volume.restrict (Set.Ico 0 (2 * π)))

lemma norm_add_le (p : ℝ≥0∞)
    (f g : HpDisc (E := E) p) :
    ‖f + g‖ ≤ ‖f‖ + ‖g‖ := by
  rcases f.2 with ⟨hf_an, ⟨hf_norm, _⟩⟩
  rcases g.2 with ⟨hg_an, ⟨hg_norm, _⟩⟩
  rw [norm_def, norm_def, norm_def]
  exact ENNReal.toReal_le_add (hardyNorm_add_le hf_an hg_an) hf_norm.ne hg_norm.ne

lemma eq_zero_of_norm_eq_zero (p : ℝ≥0∞)
    {f : HpDisc (E := E) p} (h : ‖f‖ = 0) [Fact (1 ≤ p)] :
    f = 0 := by
  sorry

lemma dist_eq_norm (p : ℝ≥0∞) (f g : HpDisc (E := E) p) :
    dist f g = ‖-f + g‖ := by rfl

lemma dist_self (p : ℝ≥0∞) (f : HpDisc (E := E) p) :
    dist f f = 0 := by
  rw [dist_eq_norm, neg_add_cancel f]; simp only [norm_zero]

lemma dist_comm (p : ℝ≥0∞) (f g : HpDisc (E := E) p) :
    dist f g = dist g f := by
  simp_rw [dist_eq_norm]; simpa [add_comm] using (norm_neg p (-g + f))

lemma dist_triangle (p : ℝ≥0∞)
    (f g h : HpDisc (E := E) p) :
    dist f h ≤ dist f g + dist g h := by
  simp_rw [dist_eq_norm]
  have hfgh : -f + h = (-f + g) + (-g + h) := by abel
  rw [hfgh]; exact norm_add_le p (-f + g) (-g + h)

lemma eq_of_dist_eq_zero (p : ℝ≥0∞)
    {f g : HpDisc (E := E) p} (hfg : dist f g = 0) [Fact (1 ≤ p)] :
    f = g := by
  rw [dist_eq_norm] at hfg
  have hsub : g - f = 0 := by
    simpa [sub_eq_add_neg, add_comm] using (eq_zero_of_norm_eq_zero p hfg : -f + g = 0)
  simpa [eq_comm] using (sub_eq_zero.mp hsub : g = f)

instance instMetricSpace (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    MetricSpace (HpDisc (E := E) p) where
  dist := dist
  dist_self := dist_self p
  dist_comm := dist_comm p
  dist_triangle := dist_triangle p
  eq_of_dist_eq_zero := fun {x y} h => eq_of_dist_eq_zero p h

instance instNormedAddCommGroup (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    NormedAddCommGroup (HpDisc (E := E) p) where
  dist_eq := fun _ _ => rfl


end HpDisc
end HardySpace
