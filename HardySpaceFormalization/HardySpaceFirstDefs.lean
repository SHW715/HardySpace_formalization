import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.Analysis.Analytic.Constructions


--# This file is no longer useful at the moment as I'm changing the definition of `hardyNorm`

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

namespace HardySpace

def eLpNormFixed {α ε : Type*} [ENorm ε] {_ : MeasurableSpace α}
    (f : α → ε) (p : ℝ≥0∞) (μ : Measure α := by volume_tac) : ℝ≥0∞ :=
  if p ∈ Set.Ioo 0 1 then (eLpNorm f p μ) ^ p.toReal else eLpNorm f p μ


/-- The Hardy `p`-norm on the unit disc. -/
def hardyNorm2 {E : Type*} [NormedAddCommGroup E]
    (f : ℂ → E) (p : ℝ≥0∞) : ℝ≥0∞ :=
   ⨆ (r : ℝ) (_ : 0 < r ∧ r < 1),
    eLpNormFixed (fun (θ : ℝ) ↦ f (r * exp (I * θ))) p
   (ENNReal.ofReal (1 / (2 * π)) • volume.restrict (Set.Ico 0 (2 * π)))


-- I think it will be nice to split the case of `p = ∞` as otherwise, `∞.toReal = 0`
-- and we will have `hardyNorm f ∞` to be meaningless.

-- # I find out the original definition of Hardy space and Hardy norms are wrong!
lemma mul_cexp_I_mul_mem_unitDisc {r θ : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    r * exp (I * θ) ∈ unitDisc := by
  rw [unitDisc, Metric.mem_ball, dist_zero_right]
  calc
    ‖r * exp (I * θ)‖ = |r| := by simp
    _ = r := abs_of_nonneg hr0.le
    _ < 1 := hr1

def hardyNorm {E : Type*} [NormedAddCommGroup E]
    (f : unitDisc → E) (p : ℝ≥0∞) : ℝ≥0∞ :=
if p = 0 then 0
else if p = ∞ then ⨆ z : unitDisc, ENNReal.ofReal ‖f z‖
else ⨆ (r : ℝ) (hr : 0 < r ∧ r < 1),
    eLpNorm (fun θ : ℝ => f ⟨r * exp (I * θ),
       mul_cexp_I_mul_mem_unitDisc hr.1 hr.2⟩) p
      ((ENNReal.ofReal (1 / (2 * π))) • volume.restrict (Set.Ico 0 (2 * π)))
        ^ min p.toReal 1


/-- Membership in the Hardy space `H^p` on the unit disc. -/
def MemHpDisc2
    (p : ℝ≥0∞) (f : ℂ → E) : Prop :=
  AnalyticOn ℂ f unitDisc ∧ hardyNorm2 f p < ∞

-- # Modification of definition of Hardy space!
def MemHpDisc (p : ℝ≥0∞) (f : unitDisc → E) : Prop :=
  (∃ F : ℂ → E, AnalyticOn ℂ F unitDisc ∧
   ∀ z : unitDisc, F z.1 = f z) ∧ hardyNorm f p < ∞

/-- Membership in `H^∞`, the space of bounded analytic functions on unit disc. -/
abbrev MemHInfinityDisc (f : unitDisc → E) : Prop :=
  MemHpDisc ∞ f

/-- `H^p` space over unit disc. -/
def HpDisc (p : ℝ≥0∞) : Submodule ℂ (unitDisc → E) where
  carrier := {f : unitDisc → E | MemHpDisc (E := E) p f}
  add_mem' := by
     intro a b ha hb
     unfold MemHpDisc at *
     rw [Set.mem_setOf_eq] at *
     rcases ha with ⟨⟨Fa, ⟨hFa_ana, hFa_ext⟩⟩ , ha_norm⟩
     rcases hb with ⟨⟨Fb, ⟨hFb_ana, hFb_ext⟩⟩ , hb_norm⟩
     constructor
     . use Fa + Fb
       constructor
       . exact AnalyticOn.add hFa_ana hFb_ana
       . simp [hFa_ext, hFb_ext]
     . unfold hardyNorm at *
       by_cases hp : p = 0
       . simp [hp] at *
       . simp [hp] at ha_norm hb_norm ⊢
         by_cases hi : p = ∞
         . -- this part is partly given by codex
           simp [hi] at *
           refine lt_of_le_of_lt ?_ (ENNReal.add_lt_top.2 ⟨ha_norm, hb_norm⟩)
           calc
             (⨆ z : unitDisc, ‖a z + b z‖ₑ) ≤ ⨆ z : unitDisc, (‖a z‖ₑ + ‖b z‖ₑ) := by
               refine iSup_le ?_
               intro z
               have hz' : (‖a z + b z‖₊ : ℝ≥0∞) ≤ (‖a z‖₊ : ℝ≥0∞) + (‖b z‖₊ : ℝ≥0∞) := by
                   exact_mod_cast (nnnorm_add_le (a z) (b z))
               have hz : ‖a z + b z‖ₑ ≤ ‖a z‖ₑ + ‖b z‖ₑ := by simpa using hz'
               refine hz.trans ?_
               exact le_iSup (fun z : unitDisc => ‖a z‖ₑ + ‖b z‖ₑ) z
             _ ≤ (⨆ z : unitDisc, ‖a z‖ₑ) + ⨆ z : unitDisc, ‖b z‖ₑ := by
               refine iSup_le ?_
               intro z
               exact add_le_add (le_iSup (fun z : unitDisc => ‖a z‖ₑ) z)
                 (le_iSup (fun z : unitDisc => ‖b z‖ₑ) z)
         . simp [hi] at ha_norm hb_norm ⊢ ; by_cases hp1 : 1 ≤ p
           . have hmin : min p.toReal 1 = 1 := by
                refine min_eq_right ?_
                exact (ENNReal.toReal_le_toReal (by simp) hi).2 hp1
             simp [hmin] at *
             -- the rest is given by codex and I haven't review it yet
             let μ : Measure ℝ :=
               (ENNReal.ofReal (π⁻¹ * 2⁻¹)) • volume.restrict (Set.Ico 0 (2 * π))
             change
              (⨆ (r : ℝ) (hr : 0 < r ∧ r < 1), eLpNorm _ p μ) < ∞ at ⊢ ha_norm hb_norm
             refine lt_of_le_of_lt ?_ (ENNReal.add_lt_top.2 ⟨ha_norm, hb_norm⟩)
             refine iSup_le ?_; intro r
             refine iSup_le ?_; intro hr
             have ha_meas :
                 AEStronglyMeasurable
                   (fun θ : ℝ =>
                     a ⟨r * exp (I * θ), mul_cexp_I_mul_mem_unitDisc hr.1 hr.2⟩) μ := by
               have hcont : Continuous (fun θ : ℝ => Fa (r * exp (I * θ))) := by
                 simpa [Function.comp_def] using
                   hFa_ana.continuousOn.comp_continuous (by fun_prop)
                     (fun θ => mul_cexp_I_mul_mem_unitDisc hr.1 hr.2)
               have h_eq :
                   (fun θ : ℝ =>
                     a ⟨r * exp (I * θ), mul_cexp_I_mul_mem_unitDisc hr.1 hr.2⟩) =
                     fun θ : ℝ => Fa (r * exp (I * θ)) := by
                 funext θ
                 exact (hFa_ext (r * exp (I * θ))
                   (mul_cexp_I_mul_mem_unitDisc hr.1 hr.2)).symm
               simpa [h_eq] using hcont.aestronglyMeasurable
             have hb_meas :
                 AEStronglyMeasurable
                   (fun θ : ℝ =>
                     b ⟨r * exp (I * θ), mul_cexp_I_mul_mem_unitDisc hr.1 hr.2⟩) μ := by
               have hcont : Continuous (fun θ : ℝ => Fb (r * exp (I * θ))) := by
                 simpa [Function.comp_def] using
                   hFb_ana.continuousOn.comp_continuous (by fun_prop)
                     (fun θ => mul_cexp_I_mul_mem_unitDisc hr.1 hr.2)
               have h_eq :
                   (fun θ : ℝ =>
                     b ⟨r * exp (I * θ), mul_cexp_I_mul_mem_unitDisc hr.1 hr.2⟩) =
                     fun θ : ℝ => Fb (r * exp (I * θ)) := by
                 funext θ
                 exact (hFb_ext (r * exp (I * θ))
                   (mul_cexp_I_mul_mem_unitDisc hr.1 hr.2)).symm
               simpa [h_eq] using hcont.aestronglyMeasurable
             calc
               eLpNorm _ p μ ≤ eLpNorm _ p μ + eLpNorm _ p μ := by
                     simpa [Pi.add_apply] using eLpNorm_add_le ha_meas hb_meas hp1
               _ ≤ (⨆ (r : ℝ) (hr : 0 < r ∧ r < 1), eLpNorm _ p μ) +
                   ⨆ (r : ℝ) (hr : 0 < r ∧ r < 1), eLpNorm _ p μ := by
                exact add_le_add
                  ((le_iSup (fun hr : 0 < r ∧ r < 1 => eLpNorm _ p μ) hr).trans
                   (le_iSup (fun r : ℝ => ⨆ (hr : 0 < r ∧ r < 1), eLpNorm _ p μ) r))
                   ((le_iSup (fun hr : 0 < r ∧ r < 1 => eLpNorm _ p μ) hr).trans
                     (le_iSup (fun r : ℝ => ⨆ (hr : 0 < r ∧ r < 1), eLpNorm _ p μ) r))

           . have hmin : min p.toReal 1 = p.toReal := by
                refine min_eq_left ?_
                exact (ENNReal.toReal_le_toReal hi (by simp)).2 (le_of_not_ge hp1)
             simp [hmin] at *
             -- the rest is given by codex and I haven't review it yet
             let μ : Measure ℝ := (ENNReal.ofReal (π⁻¹ * 2⁻¹)) • volume.restrict (Set.Ico 0 (2 * π))
             change (⨆ (r : ℝ) (hr : 0 < r ∧ r < 1), eLpNorm _ p μ ^ p.toReal) < ∞
                  at ⊢ ha_norm hb_norm
             have hqpos : 0 < p.toReal := by
                 rw [ENNReal.toReal_pos_iff]
                 exact ⟨pos_iff_ne_zero.mpr hp, lt_top_iff_ne_top.mpr hi⟩
             let A : ℝ≥0∞ :=
                 ⨆ (r : ℝ) (hr : 0 < r ∧ r < 1),
                   eLpNorm
                     (fun θ : ℝ =>
                       a ⟨r * exp (I * θ), mul_cexp_I_mul_mem_unitDisc hr.1 hr.2⟩)
                     p μ ^ p.toReal
             let B : ℝ≥0∞ :=
                 ⨆ (r : ℝ) (hr : 0 < r ∧ r < 1),
                   eLpNorm
                     (fun θ : ℝ =>
                       b ⟨r * exp (I * θ), mul_cexp_I_mul_mem_unitDisc hr.1 hr.2⟩)
                     p μ ^ p.toReal
             let C : ℝ≥0∞ := LpAddConst p
             let M : ℝ≥0∞ := (C * (A ^ p.toReal⁻¹ + B ^ p.toReal⁻¹)) ^ p.toReal
             have hA_top : A < ∞ := by simpa [A] using ha_norm
             have hB_top : B < ∞ := by simpa [B] using hb_norm
             have hM_top : M < ∞ := by
                 refine ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg ?_
                 refine ne_of_lt (ENNReal.mul_lt_top (LpAddConst_lt_top p) ?_)
                 exact ENNReal.add_lt_top.2
                   ⟨ENNReal.rpow_lt_top_of_nonneg (by positivity) hA_top.ne,
                    ENNReal.rpow_lt_top_of_nonneg (by positivity) hB_top.ne⟩
             refine lt_of_le_of_lt ?_ hM_top
             refine iSup_le ?_
             intro r
             refine iSup_le ?_
             intro hr
             have ha_meas :
                   AEStronglyMeasurable
                     (fun θ : ℝ =>
                       a ⟨r * exp (I * θ), mul_cexp_I_mul_mem_unitDisc hr.1 hr.2⟩) μ := by
                 have hcont : Continuous (fun θ : ℝ => Fa (r * exp (I * θ))) := by
                   simpa [Function.comp_def] using
                     hFa_ana.continuousOn.comp_continuous (by fun_prop)
                       (fun θ => mul_cexp_I_mul_mem_unitDisc hr.1 hr.2)
                 have h_eq :
                     (fun θ : ℝ =>
                       a ⟨r * exp (I * θ), mul_cexp_I_mul_mem_unitDisc hr.1 hr.2⟩) =
                       fun θ : ℝ => Fa (r * exp (I * θ)) := by
                   funext θ
                   exact (hFa_ext (r * exp (I * θ))
                     (mul_cexp_I_mul_mem_unitDisc hr.1 hr.2)).symm
                 simpa [h_eq] using hcont.aestronglyMeasurable
             have hb_meas :
                   AEStronglyMeasurable
                     (fun θ : ℝ =>
                       b ⟨r * exp (I * θ), mul_cexp_I_mul_mem_unitDisc hr.1 hr.2⟩) μ := by
                 have hcont : Continuous (fun θ : ℝ => Fb (r * exp (I * θ))) := by
                   simpa [Function.comp_def] using
                     hFb_ana.continuousOn.comp_continuous (by fun_prop)
                       (fun θ => mul_cexp_I_mul_mem_unitDisc hr.1 hr.2)
                 have h_eq :
                     (fun θ : ℝ =>
                       b ⟨r * exp (I * θ), mul_cexp_I_mul_mem_unitDisc hr.1 hr.2⟩) =
                       fun θ : ℝ => Fb (r * exp (I * θ)) := by
                   funext θ
                   exact (hFb_ext (r * exp (I * θ))
                     (mul_cexp_I_mul_mem_unitDisc hr.1 hr.2)).symm
                 simpa [h_eq] using hcont.aestronglyMeasurable
             have ha_le :
                   eLpNorm
                       (fun θ : ℝ =>
                         a ⟨r * exp (I * θ), mul_cexp_I_mul_mem_unitDisc hr.1 hr.2⟩)
                       p μ ≤ A ^ p.toReal⁻¹ := by
                 refine (ENNReal.le_rpow_inv_iff hqpos).2 ?_
                 exact (le_iSup
                   (fun hr : 0 < r ∧ r < 1 =>
                     eLpNorm
                       (fun θ : ℝ =>
                         a ⟨r * exp (I * θ), mul_cexp_I_mul_mem_unitDisc hr.1 hr.2⟩)
                       p μ ^ p.toReal)
                   hr).trans
                   (le_iSup
                     (fun r : ℝ =>
                       ⨆ (hr : 0 < r ∧ r < 1),
                         eLpNorm
                           (fun θ : ℝ =>
                             a ⟨r * exp (I * θ), mul_cexp_I_mul_mem_unitDisc hr.1 hr.2⟩)
                           p μ ^ p.toReal)
                     r)
             have hb_le :
                   eLpNorm
                       (fun θ : ℝ =>
                         b ⟨r * exp (I * θ), mul_cexp_I_mul_mem_unitDisc hr.1 hr.2⟩)
                       p μ ≤ B ^ p.toReal⁻¹ := by
                 refine (ENNReal.le_rpow_inv_iff hqpos).2 ?_
                 exact (le_iSup
                   (fun hr : 0 < r ∧ r < 1 =>
                     eLpNorm
                       (fun θ : ℝ =>
                         b ⟨r * exp (I * θ), mul_cexp_I_mul_mem_unitDisc hr.1 hr.2⟩)
                       p μ ^ p.toReal)
                   hr).trans
                   (le_iSup
                     (fun r : ℝ =>
                       ⨆ (hr : 0 < r ∧ r < 1),
                         eLpNorm
                           (fun θ : ℝ =>
                             b ⟨r * exp (I * θ), mul_cexp_I_mul_mem_unitDisc hr.1 hr.2⟩)
                           p μ ^ p.toReal)
                     r)
             have hsum_le :
                   eLpNorm
                       (fun θ : ℝ =>
                         a ⟨r * exp (I * θ), mul_cexp_I_mul_mem_unitDisc hr.1 hr.2⟩ +
                           b ⟨r * exp (I * θ), mul_cexp_I_mul_mem_unitDisc hr.1 hr.2⟩)
                       p μ ≤ C * (A ^ p.toReal⁻¹ + B ^ p.toReal⁻¹) := by
                 calc
                   eLpNorm
                       (fun θ : ℝ =>
                         a ⟨r * exp (I * θ), mul_cexp_I_mul_mem_unitDisc hr.1 hr.2⟩ +
                           b ⟨r * exp (I * θ), mul_cexp_I_mul_mem_unitDisc hr.1 hr.2⟩)
                       p μ
                       ≤ C *
                         (eLpNorm
                             (fun θ : ℝ =>
                               a ⟨r * exp (I * θ), mul_cexp_I_mul_mem_unitDisc hr.1 hr.2⟩)
                             p μ +
                           eLpNorm
                             (fun θ : ℝ =>
                               b ⟨r * exp (I * θ), mul_cexp_I_mul_mem_unitDisc hr.1 hr.2⟩)
                             p μ) := by
                     simpa [C, Pi.add_apply] using eLpNorm_add_le' ha_meas hb_meas p
                   _ ≤ C * (A ^ p.toReal⁻¹ + B ^ p.toReal⁻¹) := by
                     exact mul_le_mul_right (add_le_add ha_le hb_le) C
             exact ENNReal.rpow_le_rpow hsum_le ENNReal.toReal_nonneg
  zero_mem' := by
    rw [Set.mem_setOf_eq]
    unfold MemHpDisc
    constructor
    . use 0; constructor
      . exact analyticOn_const
      . simp
    . unfold hardyNorm
      by_cases hp : p = 0
      . simp [hp]
      . simp [hp]; by_cases hi : p = ∞
        . simp [hi]
        . simp [hi]; rw [ENNReal.zero_rpow_of_pos ?_]; simp; simp;
          -- why I have to `simp` twice here
          rw [ENNReal.toReal_pos_iff]
          rw [← ne_eq p 0] at hp
          rw [← ne_eq p ⊤] at hi
          constructor
          . exact pos_of_ne_zero hp
          . exact Ne.lt_top' (id (Ne.symm hi))
  smul_mem' := by
     intro c f hf
     rw [Set.mem_setOf] at *
     unfold MemHpDisc at *
     rcases hf with ⟨⟨F, ⟨hF_an, hF_ext⟩⟩, hf_norm⟩
     constructor
     . use (c • F); constructor
       . exact AnalyticOn.const_smul hF_an
       . simp [hF_ext]
     . unfold hardyNorm at *
       by_cases hp : p = 0
       . simp [hp]
       . simp [hp] at hf_norm ⊢; by_cases hi : p = ∞
         . simp [hi] at hf_norm ⊢
           -- fill in using codex
           have hc_top : ‖c‖ₑ < ∞ := ENNReal.coe_lt_top
           refine lt_of_le_of_lt ?_ (ENNReal.mul_lt_top hc_top hf_norm)
           calc
             (⨆ z : unitDisc, ‖c • f z‖ₑ) = ⨆ z : unitDisc, ‖c‖ₑ * ‖f z‖ₑ := by
               congr with z; simp [enorm_smul]
             _ ≤ ‖c‖ₑ * ⨆ z : unitDisc, ‖f z‖ₑ := by
               refine iSup_le ?_
               intro z
               simpa using mul_le_mul_right (le_iSup (fun z : unitDisc => ‖f z‖ₑ) z) ‖c‖ₑ
         . simp [hi] at hf_norm ⊢; by_cases hp1 : 1 ≤ p
           . have hmin : min p.toReal 1 = 1 := by
                refine min_eq_right ?_
                exact (ENNReal.toReal_le_toReal (by simp) hi).2 hp1
             simp [hmin] at *
             -- the rest is given by codex and I haven't review it yet
             let μ : Measure ℝ := (ENNReal.ofReal (π⁻¹ * 2⁻¹)) • volume.restrict (Set.Ico 0 (2 * π))
             change (⨆ (r : ℝ) (hr : 0 < r ∧ r < 1), eLpNorm _ p μ) < ∞ at ⊢ hf_norm
             have hc_top : ‖c‖ₑ < ∞ := ENNReal.coe_lt_top
             refine lt_of_le_of_lt ?_ (ENNReal.mul_lt_top hc_top hf_norm)
             calc
                 (⨆ (r : ℝ) (hr : 0 < r ∧ r < 1),
                   eLpNorm
                     (fun θ : ℝ =>
                       c • f ⟨r * exp (I * θ), mul_cexp_I_mul_mem_unitDisc hr.1 hr.2⟩)
                     p μ)
                     ≤
                     ⨆ (r : ℝ) (hr : 0 < r ∧ r < 1),
                       ‖c‖ₑ *
                         eLpNorm
                           (fun θ : ℝ =>
                             f ⟨r * exp (I * θ), mul_cexp_I_mul_mem_unitDisc hr.1 hr.2⟩)
                           p μ := by
                   refine iSup_le ?_
                   intro r
                   refine iSup_le ?_
                   intro hr
                   calc
                     eLpNorm
                         (fun θ : ℝ =>
                           c • f ⟨r * exp (I * θ), mul_cexp_I_mul_mem_unitDisc hr.1 hr.2⟩)
                         p μ
                         ≤
                         ‖c‖ₑ *
                           eLpNorm
                             (fun θ : ℝ =>
                               f ⟨r * exp (I * θ), mul_cexp_I_mul_mem_unitDisc hr.1 hr.2⟩)
                             p μ := by
                       simpa [Pi.smul_apply] using
                         (le_of_eq
                           (eLpNorm_const_smul c
                             (fun θ : ℝ =>
                               f ⟨r * exp (I * θ), mul_cexp_I_mul_mem_unitDisc hr.1 hr.2⟩)
                             p μ))
                     _ ≤
                         ⨆ (r : ℝ) (hr : 0 < r ∧ r < 1),
                           ‖c‖ₑ *
                             eLpNorm
                               (fun θ : ℝ =>
                                 f ⟨r * exp (I * θ), mul_cexp_I_mul_mem_unitDisc hr.1 hr.2⟩)
                               p μ :=
                       (le_iSup
                         (fun hr : 0 < r ∧ r < 1 =>
                           ‖c‖ₑ *
                             eLpNorm
                               (fun θ : ℝ =>
                                 f ⟨r * exp (I * θ), mul_cexp_I_mul_mem_unitDisc hr.1 hr.2⟩)
                               p μ)
                         hr).trans
                         (le_iSup
                           (fun r : ℝ =>
                             ⨆ (hr : 0 < r ∧ r < 1),
                               ‖c‖ₑ *
                                 eLpNorm
                                   (fun θ : ℝ =>
                                     f ⟨r * exp (I * θ),
                                       mul_cexp_I_mul_mem_unitDisc hr.1 hr.2⟩)
                                   p μ)
                           r)
                 _ ≤
                     ‖c‖ₑ *
                       ⨆ (r : ℝ) (hr : 0 < r ∧ r < 1),
                         eLpNorm
                           (fun θ : ℝ =>
                             f ⟨r * exp (I * θ), mul_cexp_I_mul_mem_unitDisc hr.1 hr.2⟩)
                           p μ := by
                   refine iSup_le ?_
                   intro r
                   refine iSup_le ?_
                   intro hr
                   simpa using mul_le_mul_right
                     ((le_iSup
                       (fun hr : 0 < r ∧ r < 1 =>
                         eLpNorm
                           (fun θ : ℝ =>
                             f ⟨r * exp (I * θ), mul_cexp_I_mul_mem_unitDisc hr.1 hr.2⟩)
                           p μ)
                       hr).trans
                       (le_iSup
                         (fun r : ℝ =>
                           ⨆ (hr : 0 < r ∧ r < 1),
                             eLpNorm
                               (fun θ : ℝ =>
                                 f ⟨r * exp (I * θ), mul_cexp_I_mul_mem_unitDisc hr.1 hr.2⟩)
                               p μ)
                         r))
                     ‖c‖ₑ
           . have hmin : min p.toReal 1 = p.toReal := by
                refine min_eq_left ?_
                exact (ENNReal.toReal_le_toReal hi (by simp)).2 (le_of_not_ge hp1)
             simp [hmin] at *
             -- the rest is given by codex and I haven't review it yet
             let μ : Measure ℝ := (ENNReal.ofReal (π⁻¹ * 2⁻¹)) • volume.restrict (Set.Ico 0 (2 * π))
             change (⨆ (r : ℝ) (hr : 0 < r ∧ r < 1), eLpNorm _ p μ ^ p.toReal) < ∞ at ⊢ hf_norm
             have hqpos : 0 < p.toReal := by
               rw [ENNReal.toReal_pos_iff]
               exact ⟨pos_iff_ne_zero.mpr hp, lt_top_iff_ne_top.mpr hi⟩
             let A : ℝ≥0∞ :=
               ⨆ (r : ℝ) (hr : 0 < r ∧ r < 1),
                 eLpNorm
                   (fun θ : ℝ =>
                     f ⟨r * exp (I * θ), mul_cexp_I_mul_mem_unitDisc hr.1 hr.2⟩)
                   p μ ^ p.toReal
             let M : ℝ≥0∞ := (‖c‖ₑ * A ^ p.toReal⁻¹) ^ p.toReal
             have hA_top : A < ∞ := by simpa [A] using hf_norm
             have hM_top : M < ∞ := by
               refine ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg ?_
               refine ne_of_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top ?_)
               exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hA_top.ne
             refine lt_of_le_of_lt ?_ hM_top
             refine iSup_le ?_
             intro r
             refine iSup_le ?_
             intro hr
             have hf_le :
                 eLpNorm
                     (fun θ : ℝ =>
                       f ⟨r * exp (I * θ), mul_cexp_I_mul_mem_unitDisc hr.1 hr.2⟩)
                     p μ ≤ A ^ p.toReal⁻¹ := by
               refine (ENNReal.le_rpow_inv_iff hqpos).2 ?_
               exact (le_iSup
                 (fun hr : 0 < r ∧ r < 1 =>
                   eLpNorm
                     (fun θ : ℝ =>
                       f ⟨r * exp (I * θ), mul_cexp_I_mul_mem_unitDisc hr.1 hr.2⟩)
                     p μ ^ p.toReal)
                 hr).trans
                 (le_iSup
                   (fun r : ℝ =>
                     ⨆ (hr : 0 < r ∧ r < 1),
                       eLpNorm
                         (fun θ : ℝ =>
                           f ⟨r * exp (I * θ), mul_cexp_I_mul_mem_unitDisc hr.1 hr.2⟩)
                         p μ ^ p.toReal)
                   r)
             have hsmul_le :
                 eLpNorm
                     (fun θ : ℝ =>
                       c • f ⟨r * exp (I * θ), mul_cexp_I_mul_mem_unitDisc hr.1 hr.2⟩)
                     p μ ≤ ‖c‖ₑ * A ^ p.toReal⁻¹ := by
               calc
                 eLpNorm
                     (fun θ : ℝ =>
                       c • f ⟨r * exp (I * θ), mul_cexp_I_mul_mem_unitDisc hr.1 hr.2⟩)
                     p μ
                     = ‖c‖ₑ *
                       eLpNorm
                         (fun θ : ℝ =>
                           f ⟨r * exp (I * θ), mul_cexp_I_mul_mem_unitDisc hr.1 hr.2⟩)
                         p μ := by
                   simpa [Pi.smul_apply] using
                     eLpNorm_const_smul c
                       (fun θ : ℝ =>
                         f ⟨r * exp (I * θ), mul_cexp_I_mul_mem_unitDisc hr.1 hr.2⟩)
                       p μ
                 _ ≤ ‖c‖ₑ * A ^ p.toReal⁻¹ := by
                   exact mul_le_mul_right hf_le ‖c‖ₑ
             exact ENNReal.rpow_le_rpow hsmul_le ENNReal.toReal_nonneg






namespace HpDisc


instance instNorm (p : ℝ≥0∞) : Norm (HpDisc (E := E) p) where
  norm f := (hardyNorm (E := E) f.1 p).toReal

instance instDist (p : ℝ≥0∞)  : Dist (HpDisc (E := E) p) where
  dist f g := ‖- f + g‖

instance instEDist (p : ℝ≥0∞)  : EDist (HpDisc (E := E) p) where
  edist f g := hardyNorm (E := E) (f.1 - g.1) p


@[simp] lemma norm_def (p : ℝ≥0∞) (f : HpDisc (E := E) p)  :
    ‖f‖ = (hardyNorm (E := E) f.1 p).toReal := rfl

@[simp] lemma norm_zero (p : ℝ≥0∞)  :
    ‖(0 : HpDisc (E := E) p)‖ = 0 := by
  simp [hardyNorm]
  by_cases hp : p = 0
  . simp [hp]
  . simp [hp]; by_cases hi : p = ∞
    . simp [hi]
    . simp [hi]
      rw [ENNReal.zero_rpow_of_pos ?_]
      . simp
      . apply lt_min
        . rw [ENNReal.toReal_pos_iff]
          constructor
          . rw [pos_iff_ne_zero]; simpa
          . rw [lt_top_iff_ne_top]; simpa
        . exact Real.zero_lt_one


@[simp] lemma norm_neg (p : ℝ≥0∞) (f : HpDisc (E := E) p) :
    ‖-f‖ = ‖f‖ := by
  simp [hardyNorm]
  by_cases hp : p = 0
  . simp [hp]
  . simp [hp]; by_cases hi : p = ∞
    . simp [hi]
    . simp [hi]
      have eLpNorm_radial_neg
          (p : ℝ≥0∞) (μ : Measure ℝ) (f : unitDisc → E) (r : ℝ) (hr : 0 < r ∧ r < 1) :
          eLpNorm (fun θ : ℝ => -f ⟨r * exp (I * θ), mul_cexp_I_mul_mem_unitDisc hr.1 hr.2⟩) p μ =
            eLpNorm (fun θ : ℝ => f ⟨r * exp (I * θ), mul_cexp_I_mul_mem_unitDisc hr.1 hr.2⟩) p μ := by
        simpa only [Pi.neg_apply] using
          (MeasureTheory.eLpNorm_neg
            (fun θ : ℝ => f ⟨r * exp (I * θ), mul_cexp_I_mul_mem_unitDisc hr.1 hr.2⟩) p μ)
      congr; ext r; congr; ext x; congr 1; exact eLpNorm_radial_neg p
        ((ENNReal.ofReal (π⁻¹ * 2⁻¹)) • volume.restrict (Set.Ico 0 (2 * π))) f.1 r x

lemma norm_add_le (p : ℝ≥0∞)
    (f g : HpDisc (E := E) p) :
    ‖f + g‖ ≤ ‖f‖ + ‖g‖ := by
   simp [hardyNorm]
   by_cases hp : p = 0
   . simp [hp]
   . simp [hp]; by_cases hi : p = ∞
     . simp [hi]
       -- fill in using codex
       have hf_fin : (⨆ z : unitDisc, ‖f.1 z‖ₑ) < ∞ := by
         rcases f.2 with ⟨_, hf_norm⟩
         simpa [hardyNorm, hp, hi] using hf_norm
       have hg_fin : (⨆ z : unitDisc, ‖g.1 z‖ₑ) < ∞ := by
         rcases g.2 with ⟨_, hg_norm⟩
         simpa [hardyNorm, hp, hi] using hg_norm
       refine ENNReal.toReal_le_add ?_ hf_fin.ne hg_fin.ne
       calc
         (⨆ z : unitDisc, ‖f.1 z + g.1 z‖ₑ) ≤ ⨆ z : unitDisc, (‖f.1 z‖ₑ + ‖g.1 z‖ₑ) := by
           refine iSup_le ?_
           intro z
           have hz' : (‖f.1 z + g.1 z‖₊ : ℝ≥0∞) ≤ (‖f.1 z‖₊ : ℝ≥0∞) + (‖g.1 z‖₊ : ℝ≥0∞) := by
             exact_mod_cast (nnnorm_add_le (f.1 z) (g.1 z))
           have hz : ‖f.1 z + g.1 z‖ₑ ≤ ‖f.1 z‖ₑ + ‖g.1 z‖ₑ := by
             simpa using hz'
           exact hz.trans (le_iSup (fun z : unitDisc => ‖f.1 z‖ₑ + ‖g.1 z‖ₑ) z)
         _ ≤ (⨆ z : unitDisc, ‖f.1 z‖ₑ) + ⨆ z : unitDisc, ‖g.1 z‖ₑ := by
           refine iSup_le ?_
           intro z
           exact add_le_add (le_iSup (fun z : unitDisc => ‖f.1 z‖ₑ) z)
             (le_iSup (fun z : unitDisc => ‖g.1 z‖ₑ) z)
     . simp [hi]; by_cases hp1 : 1 ≤ p
       . have hmin : min p.toReal 1 = 1 := by
                refine min_eq_right ?_
                exact (ENNReal.toReal_le_toReal (by simp) hi).2 hp1
         simp [hmin] at *
         let μ : Measure ℝ := (ENNReal.ofReal (π⁻¹ * 2⁻¹)) • volume.restrict (Set.Ico 0 (2 * π))
         change (⨆ (r : ℝ) (hr : 0 < r ∧ r < 1), eLpNorm _ p μ).toReal ≤
             (⨆ (r : ℝ) (hr : 0 < r ∧ r < 1), eLpNorm _ p μ).toReal +
                  (⨆ (r : ℝ) (hr : 0 < r ∧ r < 1), eLpNorm _ p μ).toReal
         have hf_fin :
             (⨆ (r : ℝ) (hr : 0 < r ∧ r < 1),
               eLpNorm
                 (fun θ : ℝ =>
                   f.1 ⟨r * exp (I * θ), mul_cexp_I_mul_mem_unitDisc hr.1 hr.2⟩)
                 p μ) < ∞ := by
           rcases f.2 with ⟨_, hf_norm⟩
           have hmin' : min p.toReal 1 = 1 := by
             refine min_eq_right ?_
             exact (ENNReal.toReal_le_toReal (by simp) hi).2 hp1
           simpa [hardyNorm, hp, hi, hmin', μ] using hf_norm
         have hg_fin :
             (⨆ (r : ℝ) (hr : 0 < r ∧ r < 1),
               eLpNorm
                 (fun θ : ℝ =>
                   g.1 ⟨r * exp (I * θ), mul_cexp_I_mul_mem_unitDisc hr.1 hr.2⟩)
                 p μ) < ∞ := by
           rcases g.2 with ⟨_, hg_norm⟩
           have hmin' : min p.toReal 1 = 1 := by
             refine min_eq_right ?_
             exact (ENNReal.toReal_le_toReal (by simp) hi).2 hp1
           simpa [hardyNorm, hp, hi, hmin', μ] using hg_norm
         have hsup_le :
             (⨆ (r : ℝ) (hr : 0 < r ∧ r < 1),
               eLpNorm
                 (fun θ : ℝ =>
                   f.1 ⟨r * exp (I * θ), mul_cexp_I_mul_mem_unitDisc hr.1 hr.2⟩ +
                     g.1 ⟨r * exp (I * θ), mul_cexp_I_mul_mem_unitDisc hr.1 hr.2⟩)
                 p μ)
                 ≤
                 (⨆ (r : ℝ) (hr : 0 < r ∧ r < 1),
                   eLpNorm
                     (fun θ : ℝ =>
                       f.1 ⟨r * exp (I * θ), mul_cexp_I_mul_mem_unitDisc hr.1 hr.2⟩)
                     p μ) +
                   ⨆ (r : ℝ) (hr : 0 < r ∧ r < 1),
                     eLpNorm
                       (fun θ : ℝ =>
                         g.1 ⟨r * exp (I * θ), mul_cexp_I_mul_mem_unitDisc hr.1 hr.2⟩)
                       p μ := by
             refine iSup_le ?_
             intro r
             refine iSup_le ?_
             intro hr
             have hf_meas :
                 AEStronglyMeasurable
                   (fun θ : ℝ =>
                     f.1 ⟨r * exp (I * θ), mul_cexp_I_mul_mem_unitDisc hr.1 hr.2⟩) μ := by
               rcases f.2 with ⟨⟨F, hF_an, hF_ext⟩, _⟩
               have hcont : Continuous (fun θ : ℝ => F (r * exp (I * θ))) := by
                 simpa [Function.comp_def] using
                   hF_an.continuousOn.comp_continuous (by fun_prop)
                     (fun θ => mul_cexp_I_mul_mem_unitDisc hr.1 hr.2)
               have h_eq :
                   (fun θ : ℝ =>
                     f.1 ⟨r * exp (I * θ), mul_cexp_I_mul_mem_unitDisc hr.1 hr.2⟩) =
                     fun θ : ℝ => F (r * exp (I * θ)) := by
                 funext θ
                 exact (hF_ext ⟨r * exp (I * θ),
                   mul_cexp_I_mul_mem_unitDisc hr.1 hr.2⟩).symm
               simpa [h_eq] using hcont.aestronglyMeasurable
             have hg_meas :
                 AEStronglyMeasurable
                   (fun θ : ℝ =>
                     g.1 ⟨r * exp (I * θ), mul_cexp_I_mul_mem_unitDisc hr.1 hr.2⟩) μ := by
               rcases g.2 with ⟨⟨G, hG_an, hG_ext⟩, _⟩
               have hcont : Continuous (fun θ : ℝ => G (r * exp (I * θ))) := by
                 simpa [Function.comp_def] using
                   hG_an.continuousOn.comp_continuous (by fun_prop)
                     (fun θ => mul_cexp_I_mul_mem_unitDisc hr.1 hr.2)
               have h_eq :
                   (fun θ : ℝ =>
                     g.1 ⟨r * exp (I * θ), mul_cexp_I_mul_mem_unitDisc hr.1 hr.2⟩) =
                     fun θ : ℝ => G (r * exp (I * θ)) := by
                 funext θ
                 exact (hG_ext ⟨r * exp (I * θ),
                   mul_cexp_I_mul_mem_unitDisc hr.1 hr.2⟩).symm
               simpa [h_eq] using hcont.aestronglyMeasurable
             refine (eLpNorm_add_le hf_meas hg_meas hp1).trans ?_
             exact add_le_add
               ((le_iSup
                 (fun hr : 0 < r ∧ r < 1 =>
                   eLpNorm
                     (fun θ : ℝ =>
                       f.1 ⟨r * exp (I * θ), mul_cexp_I_mul_mem_unitDisc hr.1 hr.2⟩)
                     p μ)
                 hr).trans
                 (le_iSup
                   (fun r : ℝ =>
                     ⨆ (hr : 0 < r ∧ r < 1),
                       eLpNorm
                         (fun θ : ℝ =>
                           f.1 ⟨r * exp (I * θ), mul_cexp_I_mul_mem_unitDisc hr.1 hr.2⟩)
                         p μ)
                   r))
               ((le_iSup
                 (fun hr : 0 < r ∧ r < 1 =>
                   eLpNorm
                     (fun θ : ℝ =>
                       g.1 ⟨r * exp (I * θ), mul_cexp_I_mul_mem_unitDisc hr.1 hr.2⟩)
                     p μ)
                 hr).trans
                 (le_iSup
                   (fun r : ℝ =>
                     ⨆ (hr : 0 < r ∧ r < 1),
                       eLpNorm
                         (fun θ : ℝ =>
                           g.1 ⟨r * exp (I * θ), mul_cexp_I_mul_mem_unitDisc hr.1 hr.2⟩)
                         p μ)
                   r))
         exact ENNReal.toReal_le_add hsup_le hf_fin.ne hg_fin.ne
       . have hmin : min p.toReal 1 = p.toReal := by
                refine min_eq_left ?_
                exact (ENNReal.toReal_le_toReal hi (by simp)).2 (le_of_not_ge hp1)
         simp [hmin] at *; sorry



lemma eq_zero_of_norm_eq_zero (p : ℝ≥0∞)
    {f : HpDisc (E := E) p} (h : ‖f‖ = 0) [Fact (1 ≤ p)] :
    f = 0 := by
   simp [hardyNorm] at h
   have hpn : p ≠ 0 := by exact ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)
   simp [hpn] at h; by_cases hi : p = ∞
   . simp [hi] at h
    -- This part of proof I filled in using codex
     have hfin : (⨆ z : unitDisc, ‖f.1 z‖ₑ) < ∞ := by
       rcases f.2 with ⟨_, hnormlt⟩
       simpa [hardyNorm, hpn, hi] using hnormlt
     have hsup : (⨆ z : unitDisc, ‖f.1 z‖ₑ) = 0 := by
       rw [ENNReal.toReal_eq_zero_iff] at h
       exact h.resolve_right hfin.ne
     ext z
     apply norm_eq_zero.mp
     have hzle : ‖f.1 z‖ₑ ≤ 0 := by
       simpa [hsup] using (le_iSup (fun z : unitDisc => ‖f.1 z‖ₑ) z)
     have hz0 : ‖f.1 z‖ₑ = 0 := le_antisymm hzle bot_le
     simpa using hz0
   . simp [hi] at h
     have hp1 : 1 ≤ p := Fact.out
     have hmin : min p.toReal 1 = 1 := by
                refine min_eq_right ?_
                exact (ENNReal.toReal_le_toReal (by simp) hi).2 hp1
     simp [hmin] at *
     sorry


lemma dist_eq_norm (p : ℝ≥0∞) (f g : HpDisc (E := E) p)  :
    dist f g = ‖- f + g‖ := rfl

lemma dist_self (p : ℝ≥0∞) (f : HpDisc (E := E) p)  :
    dist f f = 0 := by
  rw [dist_eq_norm]; rw [neg_add_cancel f]; simp only [norm_zero]

lemma dist_comm (p : ℝ≥0∞) (f g : HpDisc (E := E) p)  :
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
