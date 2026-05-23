import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Analysis.Complex.Harmonic.MeanValue
import HardySpaceFormalization.Harmonic_max_principle

/-!
# Subharmonic functions

-/

open MeasureTheory Metric Set Real Filter
open scoped ENNReal

noncomputable section

variable {E : Type*} [NormedAddCommGroup E]


-- # First, we extend `Real.log` and `Real.exp` to the following functions

def logNormBot [DecidableEq E] : E → WithBot ℝ := fun z => if z = 0 then ⊥ else (log ‖z‖ : WithBot ℝ)

def expBot : WithBot ℝ → ℝ := fun x => if hx : x = ⊥ then 0 else exp (x.unbot hx)

lemma expBot_coe (x : ℝ) : expBot (x : WithBot ℝ) = exp x := by simp [expBot]

-- This lemma will be useful later on linking the subharmonicity of `∣f|^p` and `log |f|`:
lemma exp_mul_logNorm_eq_norm_rpow {p : ℝ} (hp : 0 < p) (z : E) [DecidableEq E] :
  expBot (p * logNormBot z) = (‖z‖ ^ p : ℝ) := by
  by_cases hz : z = 0
  · have hp0 : (p : WithBot ℝ) ≠ 0 := by exact_mod_cast hp.ne'
    simp [expBot, logNormBot, hz, zero_rpow hp.ne', WithBot.mul_bot hp0]
  · have hnorm : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hlog : logNormBot z = (log ‖z‖ : WithBot ℝ) := by simp [logNormBot, hz]
    have hprod : p * (log ‖z‖ : WithBot ℝ) = ((p * log ‖z‖ : ℝ) : WithBot ℝ) := by simp
    rw [rpow_def_of_pos hnorm]
    rw [hlog, hprod, expBot_coe, mul_comm]


-- # Now we define the subharmonic functions:

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- A function is subharmonic on a set if it is upper semicontinuous there and satisfies the
mean inequality with respect to ball averages on every ball contained in the set. -/
def SubharmonicOn
   (u : E → WithBot ℝ) (s : Set E) : Prop :=
  UpperSemicontinuousOn u s ∧ ∀ (x : E) , ∀ (r : ℝ), ∀ (h : E → ℝ),
   closedBall x r ⊆ s → ContinuousOn h (closedBall x r) →
   InnerProductSpace.HarmonicOnNhd h (ball x r) →
   (∀ y ∈ sphere x r, u y ≤ h y) → ∀ y ∈ ball x r, u y ≤ h y


/-- Every harmonic function on `s: Set ℂ` is subharmonic on `s`. -/
theorem harmonicOnNhd_subharmonicOn
  (u : E → ℝ) (s : Set E) (hu : InnerProductSpace.HarmonicOnNhd u s) :
  SubharmonicOn (fun z => (u z : WithBot ℝ)) s := by sorry




variable {s : Set E} {u : E → WithBot ℝ}


lemma UpperSemicontinuousOn.expBot_mul (hu : UpperSemicontinuousOn u s) :
  UpperSemicontinuousOn (fun z => expBot (u z)) s := sorry

lemma UpperSemicontinuousOn.const_mul {p : ℝ} (hu : UpperSemicontinuousOn u s) :
  UpperSemicontinuousOn (fun z => (p : WithBot ℝ) * u z) s := sorry

theorem SubharmonicOn.const_mul {p : ℝ} (hu : SubharmonicOn u s) :
  SubharmonicOn (fun z => (p : WithBot ℝ) * u z) s := sorry

theorem SubharmonicOn.expBot_mul (hu : SubharmonicOn u s) :
  SubharmonicOn (fun z => expBot (u z)) s := sorry


variable [NormedSpace ℂ E] [NormedSpace ℂ F]

theorem logNormBot_comp_analytic_subharmonicOn_gen [DecidableEq F] {f : E → F}
  (hs : IsOpen s) (hf : AnalyticOn ℂ f s) : SubharmonicOn (logNormBot.comp f) s := sorry

theorem norm_rpow_comp_analytic_subharmonicOn_gen {f : E → F} {p : ℝ}
  (hs : IsOpen s) (hf : AnalyticOn ℂ f s) (hp : 0 < p) :
  SubharmonicOn (fun z => ((‖f z‖ ^ p : ℝ) : WithBot ℝ)) s := sorry
