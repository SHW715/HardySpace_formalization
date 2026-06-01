import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.Analysis.Complex.Harmonic.Poisson
import HardySpaceFormalization.Harmonic_max_principle
import HardySpaceFormalization.Poisson_lemma

/-!
# Subharmonic functions

-/

open MeasureTheory Metric Set Real Filter
open scoped ENNReal

noncomputable section

variable {E : Type*} [NormedAddCommGroup E]


-- # First, we extend `Real.log` and `Real.exp` to the following functions

/-- The extended logarithm of the norm, with value `⊥` at the origin. -/
def logNormBot [DecidableEq E] : E → WithBot ℝ := fun z => if z = 0 then ⊥ else (log ‖z‖ : WithBot ℝ)

/-- The exponential map on `WithBot ℝ`, extended by sending `⊥` to `0`. -/
def expBot : WithBot ℝ → ℝ := fun x => if hx : x = ⊥ then 0 else exp (x.unbot hx)

lemma expBot_coe (x : ℝ) : expBot (x : WithBot ℝ) = exp x := by simp [expBot]

/-- Exponentiating `p * log ‖z‖`, with `logNormBot 0 = ⊥` and `expBot ⊥ = 0`,
recovers `‖z‖ ^ p`. -/
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

variable {s : Set E} {u : E → WithBot ℝ}

/-- Applying `expBot` to an upper semicontinuous `WithBot ℝ`-valued function preserves upper
semicontinuity. -/
lemma UpperSemicontinuousOn.expBot_mul (hu : UpperSemicontinuousOn u s) :
  UpperSemicontinuousOn (fun z => expBot (u z)) s := by
  intro x hx a hlt
  have hexpBot_nonneg : 0 ≤ expBot (u x) := by cases u x <;> simp [expBot, exp_nonneg]
  have ha_pos : 0 < a := lt_of_le_of_lt hexpBot_nonneg hlt
  have hx_log : u x < (log a : WithBot ℝ) := by
    cases hux : u x with
    | bot => simp
    | coe b =>
      refine WithBot.coe_lt_coe.mpr ((lt_log_iff_exp_lt ha_pos).mpr ?_)
      simpa [expBot, hux] using hlt
  have hlog_expBot : ∀ w : WithBot ℝ, w < (log a : WithBot ℝ) → expBot w < a := by
    intro w hw
    cases w with
    | bot => simpa [expBot] using ha_pos
    | coe b =>
      have hb : b < log a := WithBot.coe_lt_coe.mp hw
      simpa [expBot] using (Real.lt_log_iff_exp_lt ha_pos).mp hb
  filter_upwards [hu x hx (log a : WithBot ℝ) hx_log] with y hy
  exact hlog_expBot (u y) hy


/-- Multiplication by a nonnegative real constant preserves upper semicontinuity for `WithBot ℝ`-
valued functions. -/
lemma UpperSemicontinuousOn.const_mul {p : ℝ} (hp : 0 ≤ p)
    (hu : UpperSemicontinuousOn u s) :
  UpperSemicontinuousOn (fun z => (p : WithBot ℝ) * u z) s := by
  by_cases hp0 : p = 0
  · simpa [hp0] using (upperSemicontinuousOn_const (s := s) (z := (0 : WithBot ℝ)))
  · have hp_pos : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
    intro x hx a hlt
    cases a with
    | bot => exact False.elim (not_lt_bot hlt)
    | coe c =>
      have hx_div : u x < (c / p : WithBot ℝ) := by
        cases hux : u x with
        | bot => simp
        | coe b =>
          have hb : p * b < c := by
            exact WithBot.coe_lt_coe.mp (by simpa [hux] using hlt)
          exact WithBot.coe_lt_coe.mpr ((lt_div_iff₀' hp_pos).mpr hb)
      have hmul :
          ∀ w : WithBot ℝ, w < (c / p : WithBot ℝ) →
            (p : WithBot ℝ) * w < (c : WithBot ℝ) := by
        intro w hw
        cases w with
        | bot =>
          have hp_ne : (p : WithBot ℝ) ≠ 0 := by exact_mod_cast hp0
          simp [WithBot.mul_bot hp_ne]
        | coe b =>
          have hb : b < c / p := WithBot.coe_lt_coe.mp hw
          exact WithBot.coe_lt_coe.mpr ((lt_div_iff₀' hp_pos).mp hb)
      filter_upwards [hu x hx (c / p : WithBot ℝ) hx_div] with y hy
      exact hmul (u y) hy


-- # Now we define the subharmonic functions:

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {F : Type*} [NormedAddCommGroup F]

/-- A function is subharmonic on a set if it is upper semicontinuous there and satisfies the
harmonic comparison principle on every closed ball contained in the set. -/
def SubharmonicOn
   (u : E → WithBot ℝ) (s : Set E) : Prop :=
  UpperSemicontinuousOn u s ∧ ∀ (x : E) , ∀ (r : ℝ), ∀ (h : E → ℝ),
   closedBall x r ⊆ s → ContinuousOn h (closedBall x r) →
   InnerProductSpace.HarmonicOnNhd h (ball x r) →
   (∀ y ∈ sphere x r, u y ≤ h y) → ∀ y ∈ ball x r, u y ≤ h y


/-- Every harmonic function on `s: Set ℂ` is subharmonic on `s`. -/
theorem harmonicOnNhd_subharmonicOn
  [Nontrivial E] (u : E → ℝ) (s : Set E) (hu : InnerProductSpace.HarmonicOnNhd u s) :
  SubharmonicOn (fun z => (u z : WithBot ℝ)) s := by
  constructor
  · intro x hx a hlt
    cases a with
    | bot => exact False.elim (not_lt_bot hlt)
    | coe a =>
      have hlt_real : u x < a := WithBot.coe_lt_coe.mp hlt
      filter_upwards [(hu.continuousOn x hx) (Iio_mem_nhds hlt_real)] with x' hx'
      exact WithBot.coe_lt_coe.mpr hx'
  · intro x r h hclosed hcont hharm hbd y hy
    refine WithBot.coe_le_coe.mpr ?_
    have hu_ball : InnerProductSpace.HarmonicOnNhd u (ball x r) :=
      hu.mono fun z hz => hclosed (ball_subset_closedBall hz)
    have hu_cont_closed : ContinuousOn u (closedBall x r) :=
      hu.continuousOn.mono hclosed
    have hbd_real : ∀ z ∈ sphere x r, u z ≤ h z := by
      intro z hz; exact WithBot.coe_le_coe.mp (hbd z hz)
    exact harmonic_comparison_principle_on_ball (u := u) (v := h) (x := x) (r := r)
      hu_ball hharm hu_cont_closed hcont hbd_real y hy



/-- A nonnegative constant multiple of a subharmonic function is subharmonic. -/
theorem SubharmonicOn.const_mul [Nontrivial E] {p : ℝ} (hp : 0 ≤ p) (hu : SubharmonicOn u s) :
  SubharmonicOn (fun z => (p : WithBot ℝ) * u z) s := by
  constructor
  · exact hu.1.const_mul hp
  · intro x r h hclosed hcont hharm hbd y hy
    by_cases hp0 : p = 0
    · have hzero_harm : InnerProductSpace.HarmonicOnNhd (fun _ : E => (0 : ℝ)) (ball x r) := by
        simp
      have hzero_cont : ContinuousOn (fun _ : E => (0 : ℝ)) (closedBall x r) := continuousOn_const
      have hbd_real : ∀ z ∈ sphere x r, (0 : ℝ) ≤ h z := by
        intro z hz
        exact WithBot.coe_le_coe.mp (by simpa [hp0] using hbd z hz)
      have hball : ∀ z ∈ ball x r, (0 : ℝ) ≤ h z :=
        harmonic_comparison_principle_on_ball
          (u := fun _ : E => (0 : ℝ)) (v := h) (x := x) (r := r)
          hzero_harm hharm hzero_cont hcont hbd_real
      exact by
        simpa [hp0] using WithBot.coe_le_coe.mpr (hball y hy)
    · have hp_pos : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
      let hscaled : E → ℝ := fun z => p⁻¹ * h z
      have hscaled_cont : ContinuousOn hscaled (closedBall x r) := by
        simpa [hscaled] using hcont.const_mul p⁻¹
      have hscaled_harm : InnerProductSpace.HarmonicOnNhd hscaled (ball x r) := by
        simpa [hscaled, Pi.smul_apply, smul_eq_mul] using hharm.const_smul (c := p⁻¹)
      have hbd_scaled : ∀ z ∈ sphere x r, u z ≤ (hscaled z : WithBot ℝ) := by
        intro z hz
        cases huz : u z with
        | bot => simp [hscaled]
        | coe a =>
          have hle : p * a ≤ h z := by
            exact WithBot.coe_le_coe.mp (by simpa [huz] using hbd z hz)
          have hle_scaled : a ≤ p⁻¹ * h z := by
            rw [inv_mul_eq_div]
            exact (le_div_iff₀' hp_pos).mpr hle
          exact WithBot.coe_le_coe.mpr hle_scaled
      have hy_scaled : u y ≤ (hscaled y : WithBot ℝ) :=
        hu.2 x r hscaled hclosed hscaled_cont hscaled_harm hbd_scaled y hy
      cases huy : u y with
      | bot =>
        have hp_ne : (p : WithBot ℝ) ≠ 0 := by exact_mod_cast hp0
        simp [huy, WithBot.mul_bot hp_ne]
      | coe a =>
        have hle_scaled : a ≤ p⁻¹ * h y := by
          exact WithBot.coe_le_coe.mp (by simpa [hscaled, huy] using hy_scaled)
        have hle : p * a ≤ h y := by
          rw [inv_mul_eq_div] at hle_scaled
          exact (le_div_iff₀' hp_pos).mp hle_scaled
        simpa [huy] using WithBot.coe_le_coe.mpr hle

/-- Applying `expBot` to a subharmonic `WithBot ℝ`-valued function preserves subharmonicity. -/
theorem SubharmonicOn.expBot_mul (hu : SubharmonicOn u s) :
  SubharmonicOn (fun z => expBot (u z)) s := sorry



-- # The following lemma will be useful for estimating function e.g. |f|^p
/-- A real-valued subharmonic function is bounded above by the Poisson integral of its boundary
values on a disk. -/
theorem SubharmonicOn.le_circleAverage_poissonKernel_smul
    {u : ℂ → ℝ} {s : Set ℂ} {c w : ℂ} {R : ℝ}
    (hu : SubharmonicOn (fun z => (u z : WithBot ℝ)) s)
    (hu_cont : ContinuousOn u (sphere c R))
    (hclosed : closedBall c R ⊆ s) (hw : w ∈ ball c R) :
    u w ≤ circleAverage (fun z => poissonKernel c w z * u z) c R  := by
  rcases poissonIntegral_continuousOn_closedBall_eq_boundary
    (c := c) (R := R) hu_cont with
    ⟨h, hcont, hharm, hPoisson, hboundary⟩
  have hbd : ∀ y ∈ sphere c R, (u y : WithBot ℝ) ≤ h y := by
    intro y hy; rw [hboundary y hy]
  have hle : (u w : WithBot ℝ) ≤ h w := hu.2 c R h hclosed hcont hharm hbd w hw
  have hle_real : u w ≤ h w := WithBot.coe_le_coe.mp hle
  rw [hPoisson w hw] at hle_real
  exact hle_real
-- Note actually I don't need continuity condition but the proof might be tough (using sequence
-- to approach then translate the inequality)

variable [NormedSpace ℂ E] [NormedSpace ℂ F]

/- From math perspective, for `s ⊆ ℝ^n` case, it will be more natural to consider notion of 'log |f|'
being 'pluri-subharmonic' rather than 'subharmonic', even if this theorem is still correct (as
`pluri-subharmonic` implies `subharmonic`). But I don't think whether we need such generality. -/

theorem logNormBot_comp_analytic_subharmonicOn_gen [DecidableEq F] {f : E → F}
  (hs : IsOpen s) (hf : AnalyticOn ℂ f s) : SubharmonicOn (logNormBot.comp f) s := sorry

theorem norm_rpow_comp_analytic_subharmonicOn_gen {f : E → F} {p : ℝ}
  (hs : IsOpen s) (hf : AnalyticOn ℂ f s) (hp : 0 < p) :
  SubharmonicOn (fun z => ((‖f z‖ ^ p : ℝ) : WithBot ℝ)) s := sorry

-- The following two statements might be more natural in math perspective:

theorem logNormBot_comp_analytic_subharmonicOn_banach [DecidableEq F] {f : ℂ → F} {s : Set ℂ}
  (hs : IsOpen s) (hf : AnalyticOn ℂ f s) : SubharmonicOn (logNormBot.comp f) s := sorry

theorem norm_rpow_comp_analytic_subharmonicOn_banach [DecidableEq F] {f : ℂ → F} {p : ℝ} {s : Set ℂ}
  (hs : IsOpen s) (hf : AnalyticOn ℂ f s) (hp : 0 < p) :
  SubharmonicOn (fun z => ((‖f z‖ ^ p : ℝ) : WithBot ℝ)) s := by
  simpa [Function.comp_def, exp_mul_logNorm_eq_norm_rpow hp] using
    ((logNormBot_comp_analytic_subharmonicOn_banach hs hf).const_mul hp.le).expBot_mul
