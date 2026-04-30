import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.Analysis.Analytic.Constructions



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


/-- The Hardy `p`-norm on the unit disc. -/
def hardyNorm2 {E : Type*} [NormedAddCommGroup E]
    (f : ℂ → E) (p : ℝ≥0∞) : ℝ≥0∞ :=
  if p = 0 then 0
  else if p = ∞ then ⨆ z : unitDisc, ENNReal.ofReal ‖f z.1‖
  else ⨆ (r : ℝ) (_ : 0 < r ∧ r < 1),
    eLpNorm (fun (θ : ℝ) ↦ f (r * exp (I * θ))) p
   (ENNReal.ofReal (1 / (2 * π)) • volume.restrict (Set.Ico 0 (2 * π)))
     ^ min p.toReal 1

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
       . simp [hp] at *; by_cases hi : p = ∞
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
         . simp [hi] at *; sorry
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
       . simp [hp] at *; by_cases hi : p = ∞
         . simp [hi] at *; sorry
         . simp [hi] at *; sorry






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
     . simp [hi]; sorry
     . simp [hi]; sorry



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
