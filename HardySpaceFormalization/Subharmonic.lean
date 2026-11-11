import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import HardySpaceFormalization.Harmonic_max_principle
import HardySpaceFormalization.poissonIntegral
import HardySpaceFormalization.circleMeasure
import HardySpaceFormalization.withBotIntegral


/-!
# Subharmonic functions

-/

open MeasureTheory Metric Set Real Filter
open scoped ENNReal Topology PoissonIntegral

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

/-- If a `WithBot ℝ` value is bounded by a real number, then its `expBot` is bounded by the
ordinary exponential of that real number. -/
lemma expBot_le_exp_of_le_coe {x : WithBot ℝ} {a : ℝ} (hx : x ≤ (a : WithBot ℝ)) :
    expBot x ≤ exp a := by
  cases hx' : x with
  | bot =>
      exact exp_nonneg a
  | coe b =>
      have hb : b ≤ a := WithBot.coe_le_coe.mp (by simpa [hx'] using hx)
      simpa [expBot, hx'] using exp_le_exp.mpr hb

/-- Boundary logarithm estimate: if `expBot x ≤ a`, then one may take the logarithm and get
`x ≤ log a`. In the finite case this forces `0 < a`; in the `⊥` case the conclusion is trivial. -/
lemma le_log_of_expBot_le {x : WithBot ℝ} {a : ℝ} (hx : expBot x ≤ a) :
    x ≤ (log a : WithBot ℝ) := by
  cases hx' : x with
  | bot => simp
  | coe b =>
      have hxb : exp b ≤ a := by simpa [expBot, hx'] using hx
      exact WithBot.coe_le_coe.mpr ((le_log_iff_exp_le ((exp_pos b).trans_le hxb)).mpr hxb)

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

/-- Coercing a real-valued upper semicontinuous function to `WithBot ℝ` preserves upper
semicontinuity. -/
lemma UpperSemicontinuousOn.withBot_coe {f : E → ℝ} (hf : UpperSemicontinuousOn f s) :
    UpperSemicontinuousOn (fun z => (f z : WithBot ℝ)) s := by
  intro x hx a hlt
  cases a with
  | bot =>
      exact False.elim (not_lt_bot hlt)
  | coe a =>
      have hlt_real : f x < a := WithBot.coe_lt_coe.mp hlt
      filter_upwards [hf x hx a hlt_real] with y hy
      exact WithBot.coe_lt_coe.mpr hy


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
def SubharmonicOn (u : E → WithBot ℝ) (s : Set E) : Prop :=
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

/--The extended notion of `HarmonicAt` for `WithBot ℝ`-valued function at `x`. -/
def HarmonicAtWithBot (u : E → WithBot ℝ) (x : E) : Prop :=
  ∃ v : E → ℝ, InnerProductSpace.HarmonicAt v x ∧ u =ᶠ[𝓝 x] (v ·)

/-- The extended notion of `HarmonicOnNhd` for a `WithBot ℝ`-valued function `u` on a set `s`. -/
def HarmonicOnNhdWithBot (u : E → WithBot ℝ) (s : Set E) : Prop :=
  ∃ v : E → ℝ, InnerProductSpace.HarmonicOnNhd v s ∧ ∀ x ∈ s, u x = v x

/-!
## Equivalent definition of subharmonic functions

Garnett's definition (6.1) of subharmonicity is upper semicontinuity together with the local
sub-mean inequality on small balls. This section introduces the sub-mean property
`HasLocalSubMeanOn` and relates it to the comparison definition `SubharmonicOn` (Garnett I.6.3):

* `SubharmonicOn.of_hasLocalSubMeanOn` (any `E`): sub-mean ⇒ comparison, via the maximum
  principle `HasLocalSubMeanOn.le_of_le_on_sphere`;
* `SubharmonicOn.hasLocalSubMeanOn` (`E = ℂ`): comparison ⇒ sub-mean, via the Dirichlet problem;
* `subharmonicOn_iff_hasLocalSubMeanOn`: the two together.

Adapted from `Subharmonic_test.lean`, where the sub-mean property was the definition itself.
-/

section EquivalentDefinition

lemma WithBot.add_lt_coe_add {x y : WithBot ℝ} {a b : ℝ}
    (hx : x < a) (hy : y < b) : x + y < a + b := by
  cases x with
  | bot => simp
  | coe x =>
      cases y with
      | bot => simp
      | coe y =>
          apply WithBot.coe_lt_coe.mpr
          linarith [WithBot.coe_lt_coe.mp hx, WithBot.coe_lt_coe.mp hy]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The sum of two upper semicontinuous `WithBot ℝ`-valued functions is upper
semicontinuous. -/
lemma UpperSemicontinuousOn.withBot_add {v : E → WithBot ℝ}
    (hu : UpperSemicontinuousOn u s) (hv : UpperSemicontinuousOn v s) :
    UpperSemicontinuousOn (u + v) s := by
  intro x hx a hlt
  cases a with
  | bot => exact False.elim (not_lt_bot hlt)
  | coe c =>
      cases hux : u x with
      | bot =>
          cases hvx : v x with
          | bot =>
              filter_upwards
                [hu x hx (c : WithBot ℝ) (by simp [hux]),
                 hv x hx (0 : WithBot ℝ) (by simp [hvx])] with y hyu hyv
              exact (WithBot.add_lt_coe_add hyu hyv).trans_eq (by norm_num)
          | coe b =>
              filter_upwards
                [hu x hx (c - (b + 1) : WithBot ℝ) (by simp [hux]),
                 hv x hx ((b + 1 : ℝ) : WithBot ℝ)
                  (by simpa [hvx] using WithBot.coe_lt_coe.mpr (lt_add_one b))] with y hyu hyv
              apply (WithBot.add_lt_coe_add hyu hyv).trans_eq
              rw [← WithBot.coe_add]
              ring_nf
      | coe b =>
          cases hvx : v x with
          | bot =>
              filter_upwards
                [hu x hx ((b + 1 : ℝ) : WithBot ℝ)
                 (by simpa [hux] using WithBot.coe_lt_coe.mpr (lt_add_one b)),
                 hv x hx (c - (b + 1) : WithBot ℝ) (by simp [hvx])] with y hyu hyv
              apply (WithBot.add_lt_coe_add hyu hyv).trans_eq
              rw [← WithBot.coe_add]
              ring_nf
          | coe d =>
              have hsum : b + d < c := by
                exact WithBot.coe_lt_coe.mp (by simpa [hux, hvx] using hlt)
              let ε : ℝ := (c - (b + d)) / 2
              have hε_pos : 0 < ε := by
                dsimp [ε]; linarith
              filter_upwards
                [hu x hx (b + ε)
                  (by simpa [hux] using
                    WithBot.coe_lt_coe.mpr (lt_add_of_pos_right b hε_pos)),
                 hv x hx (d + ε)
                  (by simpa [hvx] using
                    WithBot.coe_lt_coe.mpr (lt_add_of_pos_right d hε_pos))] with y hyu hyv
              exact (WithBot.add_lt_coe_add hyu hyv).trans_eq (by
                exact congrArg ((↑) : ℝ → WithBot ℝ) (by
                  dsimp [ε]
                  ring))



/-- Ball average for `WithBot ℝ`-valued functions, using `withBotIntegral`.
For `r ≤ 0` this is just a total-definition junk value; the sub-mean property below only uses it
under the hypothesis `0 < r`. -/
def ballAverageWithBot (u : E → WithBot ℝ) (x : E) (r : ℝ) : WithBot ℝ :=
  ((volume (ball x r)).toReal)⁻¹ * (∫ᴮ y in ball x r, u y)

/-- If a finite center value is bounded by its `WithBot` ball average on a positive-radius ball,
then the auxiliary real representative is integrable on that ball. -/
lemma integrableOn_unbotD_of_le_ballAverageWithBot {u : E → WithBot ℝ} {x : E} {r : ℝ}
    (hr : 0 < r) (hux : u x ≠ ⊥) (hle : u x ≤ ballAverageWithBot u x r) :
    IntegrableOn ((WithBot.unbotD 0) ∘ u) (ball x r) volume := by
  by_contra hnot
  have hcond_false :
      ¬ ((volume.restrict (ball x r)) {y | u y = ⊥} = 0 ∧
        Integrable ((WithBot.unbotD 0) ∘ u) (volume.restrict (ball x r))) := by
    exact fun hcond => hnot hcond.2
  have hint_bot : (∫ᴮ y in ball x r, u y) = (⊥ : WithBot ℝ) := by
    simp [withBotIntegral, hcond_false]
  have hvol_pos : 0 < (volume (ball x r)).toReal := by
    exact ENNReal.toReal_pos (measure_ball_pos volume x hr).ne' measure_ball_lt_top.ne
  let c : ℝ := ((volume (ball x r)).toReal)⁻¹
  have hcoeff_pos : 0 < c := inv_pos.mpr hvol_pos
  have hcoeff_ne : (c : WithBot ℝ) ≠ 0 := by
    exact_mod_cast hcoeff_pos.ne'
  have havg_bot : ballAverageWithBot u x r = (⊥ : WithBot ℝ) := by
    change (c : WithBot ℝ) * (∫ᴮ y in ball x r, u y) = (⊥ : WithBot ℝ)
    rw [hint_bot]
    exact WithBot.mul_bot hcoeff_ne
  have hx_le_bot : u x ≤ (⊥ : WithBot ℝ) := by
    simpa [havg_bot] using hle
  exact hux (le_antisymm hx_le_bot bot_le)

/-- For a real-valued function coerced to `WithBot ℝ`, the `WithBot` ball average is the ordinary
ball average, coerced to `WithBot ℝ`. -/
lemma ballAverageWithBot_coe (u : E → ℝ) (x : E) (r : ℝ) :
    IntegrableOn u (ball x r) volume →
    ballAverageWithBot (fun y => (u y : WithBot ℝ)) x r =
      ((ballAverage (F := ℝ) u x r : ℝ) : WithBot ℝ) := by
  intro hu
  simp [ballAverageWithBot, ballAverage, withBotIntegral_coe, hu, smul_eq_mul]

/-- Positive constant multiplication commutes with `ballAverageWithBot`. -/
lemma ballAverageWithBot_const_mul_of_pos {p : ℝ} (hp : 0 < p)
    (u : E → WithBot ℝ) (x : E) (r : ℝ) :
    ballAverageWithBot (fun y => (p : WithBot ℝ) * u y) x r =
      (p : WithBot ℝ) * ballAverageWithBot u x r := by
  unfold ballAverageWithBot
  rw [withBotIntegral_const_mul_of_pos (μ := volume.restrict (ball x r)) hp]
  let q : ℝ := ((volume (ball x r)).toReal)⁻¹
  calc
    (q : WithBot ℝ) * ((p : WithBot ℝ) * ∫ᴮ (y : E) in ball x r, u y) =
        ((q : WithBot ℝ) * (p : WithBot ℝ)) *
          ∫ᴮ (y : E) in ball x r, u y := by
          rw [mul_assoc]
    _ = ((p : WithBot ℝ) * (q : WithBot ℝ)) *
          ∫ᴮ (y : E) in ball x r, u y := by
          rw [mul_comm (q : WithBot ℝ) (p : WithBot ℝ)]
    _ = (p : WithBot ℝ) *
        ((q : WithBot ℝ) * ∫ᴮ (y : E) in ball x r, u y) := by
          rw [mul_assoc]

/-- The `WithBot` ball average of the zero function is zero. -/
lemma ballAverageWithBot_zero (x : E) (r : ℝ) : ballAverageWithBot 0 x r = 0 := by
  change ballAverageWithBot (fun _ : E => (0 : WithBot ℝ)) x r = 0
  simpa [ballAverage] using (ballAverageWithBot_coe (fun _ : E => (0 : ℝ)) x r integrableOn_zero)

/-- Linearity of `ballAverageWithBot` under addition. -/
lemma ballAverageWithBot_add {u v : E → WithBot ℝ} (x : E) (r : ℝ)
    (hu_int : IntegrableOn ((WithBot.unbotD 0) ∘ u) (ball x r) volume)
    (hv_int : IntegrableOn ((WithBot.unbotD 0) ∘ v) (ball x r) volume) :
    ballAverageWithBot (u + v) x r =
      ballAverageWithBot u x r + ballAverageWithBot v x r := by
  unfold ballAverageWithBot
  change ((volume (ball x r)).toReal)⁻¹ * (∫ᴮ y in ball x r, u y + v y) =
    ((volume (ball x r)).toReal)⁻¹ * (∫ᴮ y in ball x r, u y) +
      ((volume (ball x r)).toReal)⁻¹ * (∫ᴮ y in ball x r, v y)
  rw [withBotIntegral_add (μ := volume.restrict (ball x r)) hu_int hv_int]
  rw [WithBot.coe_mul_add]

/-- `ballAverageWithBot` is monotone in the integrand (pointwise inequality → average inequality),
provided the real representative of the upper function is integrable on the ball. -/
lemma ballAverageWithBot_mono {u v : E → WithBot ℝ} {x : E} {r : ℝ}
    (h : ∀ y, u y ≤ v y)
    (hv_int : IntegrableOn (fun y => (WithBot.unbotD 0) (v y)) (ball x r)) :
    ballAverageWithBot u x r ≤ ballAverageWithBot v x r := by
  unfold ballAverageWithBot
  by_cases hc : ((volume (ball x r)).toReal)⁻¹ = 0
  · simp [hc]
  · have hc_pos : 0 < ((volume (ball x r)).toReal)⁻¹ :=
      lt_of_le_of_ne (inv_nonneg.mpr ENNReal.toReal_nonneg) (Ne.symm hc)
    exact WithBot.const_mul_le_const_mul_of_pos hc_pos
      (withBotIntegral_mono (μ := volume.restrict (ball x r))
        (Eventually.of_forall (fun y => h y)) hv_int)

/-- The local sub-mean property on `s`: each point of `s` has a radius `ρ` such that the ball of
radius `ρ` lies in `s` and the value at the centre is at most every ball average of radius
`r < ρ`. Together with upper semicontinuity this is Garnett's definition (6.1). -/
def HasLocalSubMeanOn (u : E → WithBot ℝ) (s : Set E) : Prop :=
  ∀ x ∈ s, ∃ ρ > 0, ball x ρ ⊆ s ∧ ∀ r, 0 < r ∧ r < ρ → u x ≤ ballAverageWithBot u x r

/-- Restrict the local sub-mean property to an open subset. -/
lemma HasLocalSubMeanOn.mono (hu : HasLocalSubMeanOn u s) {t : Set E}
    (hts : t ⊆ s) (ht : IsOpen t) : HasLocalSubMeanOn u t := by
  intro x hx
  rcases hu x (hts hx) with ⟨ρs, hρs_pos, _hρs_sub, hmean⟩
  rcases Metric.isOpen_iff.mp ht x hx with ⟨ρt, hρt_pos, hρt_sub⟩
  refine ⟨min ρs ρt, lt_min hρs_pos hρt_pos, ?_, ?_⟩
  · intro y hy
    exact hρt_sub (Metric.ball_subset_ball (min_le_right _ _) hy)
  · intro r hr
    exact hmean r ⟨hr.1, lt_of_lt_of_le hr.2 (min_le_left _ _)⟩

/-- The local sub-mean property is preserved by addition; the `⊥` cases are handled by
`withBotIntegral`. -/
theorem HasLocalSubMeanOn.add (hu : HasLocalSubMeanOn u s) {v : E → WithBot ℝ}
    (hv : HasLocalSubMeanOn v s) : HasLocalSubMeanOn (u + v) s := by
  intro x hx
  rcases hu x hx with ⟨ρu, hρu_pos, hρu_sub, hmean_u⟩
  rcases hv x hx with ⟨ρv, hρv_pos, hρv_sub, hmean_v⟩
  refine ⟨min ρu ρv, lt_min hρu_pos hρv_pos, ?_, ?_⟩
  · intro y hy
    exact hρu_sub (Metric.ball_subset_ball (min_le_left _ _) hy)
  · intro r hr
    by_cases hux : u x = ⊥
    · simp [Pi.add_apply, hux]
    by_cases hvx : v x = ⊥
    · simp [Pi.add_apply, hvx]
    have hr_u : 0 < r ∧ r < ρu :=
      ⟨hr.1, lt_of_lt_of_le hr.2 (min_le_left _ _)⟩
    have hr_v : 0 < r ∧ r < ρv :=
      ⟨hr.1, lt_of_lt_of_le hr.2 (min_le_right _ _)⟩
    have hle_u := hmean_u r hr_u
    have hle_v := hmean_v r hr_v
    have hu_int : IntegrableOn ((WithBot.unbotD 0) ∘ u) (ball x r) volume :=
      integrableOn_unbotD_of_le_ballAverageWithBot hr.1 hux hle_u
    have hv_int : IntegrableOn ((WithBot.unbotD 0) ∘ v) (ball x r) volume :=
      integrableOn_unbotD_of_le_ballAverageWithBot hr.1 hvx hle_v
    change u x + v x ≤ ballAverageWithBot (u + v) x r
    rw [ballAverageWithBot_add x r hu_int hv_int]
    exact add_le_add hle_u hle_v

/-- A real-valued harmonic function on an open set has the local sub-mean property (with
equality), by the mean value property. -/
theorem hasLocalSubMeanOn_of_harmonicOnNhd (u : E → ℝ) (hs : IsOpen s)
    (hu : InnerProductSpace.HarmonicOnNhd u s) :
    HasLocalSubMeanOn (fun z => (u z : WithBot ℝ)) s := by
  intro x hx
  rcases Metric.isOpen_iff.mp hs x hx with ⟨ρ, hρ_pos, hρ_sub⟩
  refine ⟨ρ / 2, half_pos hρ_pos, ?_, ?_⟩
  · intro y hy
    exact hρ_sub (Metric.ball_subset_ball (by linarith) hy)
  · intro r hr
    have hclosed_sub : closedBall x |r| ⊆ s := by
      intro y hy
      exact hρ_sub (by
        rw [Metric.mem_ball]
        exact lt_of_le_of_lt (by simpa [Metric.mem_closedBall] using hy)
          (by rw [abs_of_pos hr.1]; linarith))
    have hu_int : IntegrableOn u (ball x r) volume :=
      (hu.continuousOn.mono hclosed_sub).integrableOn_of_subset_isCompact
        (isCompact_closedBall x |r|) measurableSet_ball
        (by
          intro y hy
          rw [Metric.mem_closedBall]
          rw [Metric.mem_ball] at hy
          exact le_of_lt (by simpa [abs_of_pos hr.1] using hy))
        measure_ball_lt_top.ne
    rw [ballAverageWithBot_coe u x r hu_int]
    refine WithBot.coe_le_coe.mpr ?_
    have hmean : ballAverage u x r = u x := by
      simpa [abs_of_pos hr.1] using
        HarmonicOnNhd.ballAverage_eq
          ((hu.mono hclosed_sub) : InnerProductSpace.HarmonicOnNhd u (closedBall x |r|))
    exact le_of_eq hmean.symm

/-- Equality case of the sub-mean inequality: if `u ≤ a` on a ball and `a` is at most the ball
average of `u`, then `u = a` almost everywhere on the ball. -/
lemma ae_eq_of_le_of_le_ballAverageWithBot {u : E → WithBot ℝ} {x : E} {r a : ℝ} (hr : 0 < r)
    (hle : ∀ y ∈ ball x r, u y ≤ a) (hmean : (a : WithBot ℝ) ≤ ballAverageWithBot u x r) :
    ∀ᵐ y ∂volume.restrict (ball x r), u y = a := by
  have hV_pos : 0 < (volume (ball x r)).toReal :=
    ENNReal.toReal_pos (measure_ball_pos volume x hr).ne' measure_ball_lt_top.ne
  have : IsFiniteMeasure (volume.restrict (ball x r)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  -- The average is not `⊥`, so the `⊥` set is null and the real representative is integrable.
  have hcond : (volume.restrict (ball x r)) {y | u y = ⊥} = 0 ∧
      Integrable ((WithBot.unbotD 0) ∘ u) (volume.restrict (ball x r)) := by
    by_contra hnot
    have hint_bot : (∫ᴮ y in ball x r, u y) = (⊥ : WithBot ℝ) := by
      simp [withBotIntegral, hnot]
    have hcoeff_ne : ((((volume (ball x r)).toReal)⁻¹ : ℝ) : WithBot ℝ) ≠ 0 := by
      exact_mod_cast (inv_pos.mpr hV_pos).ne'
    have havg_bot : ballAverageWithBot u x r = (⊥ : WithBot ℝ) := by
      unfold ballAverageWithBot
      rw [hint_bot]
      exact WithBot.mul_bot hcoeff_ne
    exact WithBot.coe_ne_bot (le_bot_iff.mp (havg_bot ▸ hmean))
  have hfi : Integrable (fun y => (u y).unbotD 0) (volume.restrict (ball x r)) := hcond.2
  have havg : ballAverageWithBot u x r =
      (((volume (ball x r)).toReal⁻¹ * ∫ y in ball x r, (u y).unbotD 0 : ℝ) : WithBot ℝ) := by
    unfold ballAverageWithBot withBotIntegral
    rw [ite_eq_left_of_eq_true _ _ (eq_true hcond), ← WithBot.coe_mul]
  have hmean' : a ≤ (volume (ball x r)).toReal⁻¹ * ∫ y in ball x r, (u y).unbotD 0 :=
    WithBot.coe_le_coe.mp (havg ▸ hmean)
  have hne : ∀ᵐ y ∂volume.restrict (ball x r), u y ≠ ⊥ := by
    rw [ae_iff]
    simpa using hcond.1
  -- `a - u` is nonnegative with nonpositive integral, hence vanishes almost everywhere.
  have hnonneg : 0 ≤ᵐ[volume.restrict (ball x r)] fun y => a - (u y).unbotD 0 := by
    filter_upwards [hne, ae_restrict_mem measurableSet_ball] with y hy hyb
    obtain ⟨b, hb⟩ := WithBot.ne_bot_iff_exists.mp hy
    have h := hle y hyb
    show 0 ≤ a - (u y).unbotD 0
    rw [← hb] at h ⊢
    simpa using WithBot.coe_le_coe.mp h
  have hint : Integrable (fun y => a - (u y).unbotD 0) (volume.restrict (ball x r)) :=
    (integrable_const a).sub hfi
  have hint_le : ∫ y in ball x r, (a - (u y).unbotD 0) ≤ 0 := by
    rw [integral_sub (integrable_const a) hfi, integral_const, smul_eq_mul]
    have hV : (volume.restrict (ball x r)).real univ = (volume (ball x r)).toReal := by
      simp [Measure.real]
    rw [hV]
    have := (le_inv_mul_iff₀ hV_pos).mp hmean'
    linarith
  have heq := (integral_eq_zero_iff_of_nonneg_ae hnonneg hint).mp
    (le_antisymm hint_le (integral_nonneg_of_ae hnonneg))
  filter_upwards [heq, hne] with y hy hyne
  obtain ⟨b, hb⟩ := WithBot.ne_bot_iff_exists.mp hyne
  have hy' : a - (u y).unbotD 0 = 0 := hy
  rw [← hb] at hy' ⊢
  rw [WithBot.unbotD_coe] at hy'
  exact_mod_cast (by linarith : b = a)

/-- **Maximum principle** for the local sub-mean property on a ball: if `v` is upper
semicontinuous on the closed ball, has the local sub-mean property in the open ball, and is at
most `M` on the boundary sphere, then it is at most `M` throughout the open ball.

Upper semicontinuity is required up to the boundary: the version in `Subharmonic_test.lean`,
assuming only `ball x r ⊆ s`, is false (take `v = 1` inside the ball and `v = 0` on the
sphere). -/
lemma HasLocalSubMeanOn.le_of_le_on_sphere [Nontrivial E] {v : E → WithBot ℝ} {x : E} {r M : ℝ}
    (husc : UpperSemicontinuousOn v (closedBall x r)) (hv : HasLocalSubMeanOn v (ball x r))
    (hbd : ∀ y ∈ sphere x r, v y ≤ M) :
    ∀ y ∈ ball x r, v y ≤ M := by
  -- Garnett's maximum principle argument from the proof of Theorem I.6.3.
  intro y hy
  have hr : 0 < r := pos_of_mem_ball hy
  -- By upper semicontinuity, `v` attains its maximum on the closed ball, at `z` say.
  obtain ⟨z, hz, hmax⟩ := husc.exists_isMaxOn (nonempty_closedBall.mpr hr.le)
    (isCompact_closedBall x r)
  have hmax' : ∀ w ∈ closedBall x r, v w ≤ v z := isMaxOn_iff.mp hmax
  refine (hmax' y (ball_subset_closedBall hy)).trans ?_
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨a, ha⟩ := WithBot.ne_bot_iff_exists.mp ((WithBot.bot_lt_coe M).trans hlt).ne'
  have huscb : UpperSemicontinuousOn v (ball x r) := husc.mono ball_subset_closedBall
  have hev : ∀ w ∈ ball x r, v w < v z → ∀ᶠ w' in 𝓝 w, v w' < v z := by
    intro w hw hw_lt
    have h := huscb w hw (v z) hw_lt
    rwa [isOpen_ball.nhdsWithin_eq hw] at h
  -- The maximum is not attained on the sphere, so `z` lies in the open ball.
  have hz_ball : z ∈ ball x r := by
    rw [mem_ball]
    refine lt_of_le_of_ne (mem_closedBall.mp hz) fun hd => ?_
    exact (hbd z (mem_sphere.mpr hd)).not_gt hlt
  -- `U` is the set where the maximum is attained; it is open, relatively closed and nonempty.
  let U : Set E := {w | w ∈ ball x r ∧ v w = v z}
  have hU_open : IsOpen U := by
    refine isOpen_iff_mem_nhds.mpr fun z₀ hz₀ => ?_
    obtain ⟨ρ, hρ, hρsub, hmean⟩ := hv z₀ hz₀.1
    refine mem_of_superset (ball_mem_nhds z₀ hρ) fun w hw => ?_
    have hwb : w ∈ ball x r := hρsub hw
    refine ⟨hwb, ?_⟩
    by_contra hne
    have hw_lt : v w < v z := lt_of_le_of_ne (hmax' w (ball_subset_closedBall hwb)) hne
    -- Pick a radius `r'` with `dist w z₀ < r' < ρ`; then `v = v z` a.e. on `ball z₀ r'`.
    have hdist : dist w z₀ < ρ := mem_ball.mp hw
    set r' : ℝ := (dist w z₀ + ρ) / 2 with hr'_def
    have hr'_gt : dist w z₀ < r' := by rw [hr'_def]; linarith
    have hr'_lt : r' < ρ := by rw [hr'_def]; linarith
    have hr'_pos : 0 < r' := dist_nonneg.trans_lt hr'_gt
    have hmean' : (a : WithBot ℝ) ≤ ballAverageWithBot v z₀ r' := by
      rw [ha, ← hz₀.2]
      exact hmean r' ⟨hr'_pos, hr'_lt⟩
    have hae := ae_eq_of_le_of_le_ballAverageWithBot hr'_pos (fun y' hy' => by
      rw [ha]
      exact hmax' y' (ball_subset_closedBall (hρsub (ball_subset_ball hr'_lt.le hy')))) hmean'
    rw [ae_restrict_iff' measurableSet_ball] at hae
    -- But `v < v z` on a neighbourhood of `w`, which has positive measure.
    have hnhds : {w' | v w' < v z} ∩ ball z₀ r' ∈ 𝓝 w :=
      inter_mem (hev w hwb hw_lt) (isOpen_ball.mem_nhds (mem_ball.mpr hr'_gt))
    have hpos := Measure.measure_pos_of_mem_nhds (volume : Measure E) hnhds
    have hnull : volume ({w' | v w' < v z} ∩ ball z₀ r') = 0 :=
      measure_mono_null (t := {w' | ¬(w' ∈ ball z₀ r' → v w' = a)})
        (fun w' hw' h => hw'.1.ne ((h hw'.2).trans ha)) (ae_iff.mp hae)
    exact hpos.ne' hnull
  have hU_closed : closure U ∩ ball x r ⊆ U := by
    rintro w ⟨hwU, hwb⟩
    refine ⟨hwb, ?_⟩
    by_contra hne
    have hw_lt : v w < v z := lt_of_le_of_ne (hmax' w (ball_subset_closedBall hwb)) hne
    obtain ⟨w', hw'U, hw'_lt⟩ :=
      ((mem_closure_iff_frequently.mp hwU).and_eventually (hev w hwb hw_lt)).exists
    exact hw'_lt.ne hw'U.2
  -- The ball is connected, so `v = v z` on the whole open ball.
  have hsub : ball x r ⊆ U :=
    (convex_ball x r).isPreconnected.subset_of_closure_inter_subset hU_open
      ⟨z, hz_ball, hz_ball, rfl⟩ hU_closed
  -- A boundary point is a limit of points of the ball, contradicting upper semicontinuity.
  obtain ⟨ζ, hζ⟩ := (NormedSpace.sphere_nonempty (x := x) (r := r)).mpr hr.le
  have hζ_lt : v ζ < v z := (hbd ζ hζ).trans_lt hlt
  have hζ_ev := husc ζ (sphere_subset_closedBall hζ) (v z) hζ_lt
  obtain ⟨t, ht_open, hζt, ht⟩ := mem_nhdsWithin.mp hζ_ev
  have hζ_cl : ζ ∈ closure (ball x r) := by
    rw [closure_ball x hr.ne']
    exact sphere_subset_closedBall hζ
  obtain ⟨w, hwt, hwb⟩ := mem_closure_iff.mp hζ_cl t ht_open hζt
  exact (ht ⟨hwt, ball_subset_closedBall hwb⟩).ne (hsub hwb).2

/-- Harmonic comparison on a ball for the local sub-mean property: if `u ≤ h` on the boundary
sphere, with `h` continuous on the closed ball and harmonic inside, then `u ≤ h` inside.
Subtract `h` and apply the maximum principle. -/
theorem HasLocalSubMeanOn.le_of_le_on_sphere_of_harmonicOnNhd [Nontrivial E] {x : E} {r : ℝ}
    {h : E → ℝ} (husc : UpperSemicontinuousOn u (closedBall x r))
    (hu : HasLocalSubMeanOn u (ball x r)) (hcont : ContinuousOn h (closedBall x r))
    (hharm : InnerProductSpace.HarmonicOnNhd h (ball x r))
    (hbd : ∀ y ∈ sphere x r, u y ≤ h y) : ∀ y ∈ ball x r, u y ≤ h y := by
  intro y hy
  let v : E → WithBot ℝ := u + fun z => ((-h z : ℝ) : WithBot ℝ)
  have hv_usc : UpperSemicontinuousOn v (closedBall x r) :=
    husc.withBot_add (hcont.neg.upperSemicontinuousOn.withBot_coe)
  have hv_mean : HasLocalSubMeanOn v (ball x r) :=
    hu.add (hasLocalSubMeanOn_of_harmonicOnNhd (fun z => -h z) isOpen_ball hharm.neg)
  have hv_bd : ∀ z ∈ sphere x r, v z ≤ ((0 : ℝ) : WithBot ℝ) := fun z hz =>
    (WithBot.add_neg_coe_le_zero_iff (u z) (h z)).2 (hbd z hz)
  exact (WithBot.add_neg_coe_le_zero_iff (u y) (h y)).1
    (hv_mean.le_of_le_on_sphere hv_usc hv_bd y hy)

/-- Garnett I.6.3, sub-mean ⇒ comparison: an upper semicontinuous function with the local
sub-mean property is subharmonic. -/
theorem SubharmonicOn.of_hasLocalSubMeanOn [Nontrivial E] (husc : UpperSemicontinuousOn u s)
    (hu : HasLocalSubMeanOn u s) : SubharmonicOn u s :=
  ⟨husc, fun _x _r _h hclosed hcont hharm hbd =>
    HasLocalSubMeanOn.le_of_le_on_sphere_of_harmonicOnNhd (husc.mono hclosed)
      (hu.mono (ball_subset_closedBall.trans hclosed) isOpen_ball) hcont hharm hbd⟩

/-- Garnett I.6.3, comparison ⇒ sub-mean, on open subsets of `ℂ`. Approximate the upper
semicontinuous boundary values from above by continuous functions, solve the Dirichlet problems,
and pass to the circle mean inequality; integrating in the radius gives the ball mean
inequality. -/
theorem SubharmonicOn.hasLocalSubMeanOn {u : ℂ → WithBot ℝ} {s : Set ℂ} (hs : IsOpen s)
    (hu : SubharmonicOn u s) : HasLocalSubMeanOn u s := by
  sorry

/-- **Garnett I.6.3**: on an open subset of `ℂ`, the comparison definition of subharmonicity
agrees with Garnett's definition (6.1): upper semicontinuity and the local sub-mean property. -/
theorem subharmonicOn_iff_hasLocalSubMeanOn {u : ℂ → WithBot ℝ} {s : Set ℂ} (hs : IsOpen s) :
    SubharmonicOn u s ↔ UpperSemicontinuousOn u s ∧ HasLocalSubMeanOn u s :=
  ⟨fun hu => ⟨hu.1, hu.hasLocalSubMeanOn hs⟩, fun h => SubharmonicOn.of_hasLocalSubMeanOn h.1 h.2⟩

/-- A function that is locally harmonic at a finite point satisfies the sub-mean inequality there
(with equality) on all small balls. -/
lemma exists_le_ballAverageWithBot_of_harmonicAtWithBot {u : E → WithBot ℝ} {x : E}
    (hux : u x ≠ ⊥) (hu : HarmonicAtWithBot u x) :
    ∃ ρ > 0, ∀ r, 0 < r ∧ r < ρ → u x ≤ ballAverageWithBot u x r := by
  obtain ⟨v, hv, huv⟩ := hu
  -- A metric ball where `u = v`, and one where `v` is harmonic at every point.
  obtain ⟨N_uv, hN_uv, huv_N⟩ := huv.exists_mem
  obtain ⟨ρ_uv, hρ_uv_pos, hρ_uv_sub⟩ := Metric.mem_nhds_iff.mp hN_uv
  obtain ⟨N_v, hN_v, hv_N⟩ := hv.eventually.exists_mem
  obtain ⟨ρ_v, hρ_v_pos, hρ_v_sub⟩ := Metric.mem_nhds_iff.mp hN_v
  refine ⟨min ρ_uv ρ_v, lt_min hρ_uv_pos hρ_v_pos, ?_⟩
  intro r ⟨hr_pos, hr_lt⟩
  have hr_lt_uv : r < ρ_uv := lt_of_lt_of_le hr_lt (min_le_left _ _)
  have hr_lt_v : r < ρ_v := lt_of_lt_of_le hr_lt (min_le_right _ _)
  -- u = v on ball x r
  have hu_eq_v_ball : ∀ y ∈ ball x r, u y = (v y : WithBot ℝ) := fun y hy =>
    huv_N (hρ_uv_sub (Metric.ball_subset_ball hr_lt_uv.le hy))
  -- u x = v x
  have hux_eq : u x = (v x : WithBot ℝ) := huv_N (mem_of_mem_nhds hN_uv)
  -- v is harmonic at every point of closedBall x r
  have hv_harm : InnerProductSpace.HarmonicOnNhd v (closedBall x r) := fun y hy =>
    hv_N y (hρ_v_sub (Metric.closedBall_subset_ball hr_lt_v hy))
  -- Mean value property: ballAverage v x r = v x
  have hmean : ballAverage v x r = v x :=
    HarmonicOnNhd.ballAverage_eq
      (show InnerProductSpace.HarmonicOnNhd v (closedBall x |r|) by rwa [abs_of_pos hr_pos])
  have hv_int : IntegrableOn v (ball x r) volume :=
    hv_harm.continuousOn.integrableOn_of_subset_isCompact
      (isCompact_closedBall x r) measurableSet_ball ball_subset_closedBall
      measure_ball_lt_top.ne
  -- Real integrals agree on the ball since u = v there
  have hint_eq : ∫ y in ball x r, (u y).unbotD 0 = ∫ y in ball x r, v y := by
    apply setIntegral_congr_ae measurableSet_ball (ae_of_all _ _)
    intro y hy
    rw [hu_eq_v_ball y hy]
    simp [WithBot.unbotD]
  have hu_int : IntegrableOn ((WithBot.unbotD 0) ∘ u) (ball x r) volume := by
    refine integrableOn_unbotD_of_eq_coe_ae hv_int ?_
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    exact hu_eq_v_ball y hy
  -- withBotIntegrals agree
  have h_u_bot : volume (ball x r ∩ {y | u y = ⊥}) = 0 := by
    have hempty : ball x r ∩ {y | u y = ⊥} = ∅ := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
        not_and]
      intro hy_ball; rw [hu_eq_v_ball y hy_ball]; exact WithBot.coe_ne_bot
    simp [hempty, measure_empty]
  have hwbi_eq : withBotIntegral (volume.restrict (ball x r)) u =
      withBotIntegral (volume.restrict (ball x r)) (fun y => (v y : WithBot ℝ)) := by
    sorry
  -- ballAverageWithBots agree
  have hball_avg_eq : ballAverageWithBot u x r =
      ballAverageWithBot (fun y => (v y : WithBot ℝ)) x r := by
    simp only [ballAverageWithBot, hwbi_eq]
  -- Conclude: u x = ballAverageWithBot u x r
  suffices heq : u x = ballAverageWithBot u x r from heq.le
  calc u x
      = (v x : WithBot ℝ) := hux_eq
    _ = ((ballAverage (F := ℝ) v x r : ℝ) : WithBot ℝ) := by exact_mod_cast hmean.symm
    _ = ballAverageWithBot (fun y => (v y : WithBot ℝ)) x r :=
      (ballAverageWithBot_coe v x r hv_int).symm
    _ = ballAverageWithBot u x r := hball_avg_eq.symm

/-- An upper semicontinuous `WithBot ℝ`-valued function which is locally harmonic at every finite
point is subharmonic. -/
theorem subharmonicOn_of_upperSemicontinuousOn_of_harmonicAtWithBot [Nontrivial E]
    {u : E → WithBot ℝ} {s : Set E} (husc : UpperSemicontinuousOn u s)
    (hu : ∀ z ∈ s, u z ≠ ⊥ → HarmonicAtWithBot u z) : SubharmonicOn u s := by
  refine ⟨husc, fun c R h hclosed hcont hharm hbd => ?_⟩
  refine HasLocalSubMeanOn.le_of_le_on_sphere_of_harmonicOnNhd (husc.mono hclosed) ?_ hcont
    hharm hbd
  -- The sub-mean inequality holds at every point of the open ball, on balls inside it.
  intro y hy
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp isOpen_ball y hy
  by_cases huy : u y = ⊥
  · exact ⟨ε, hε, hεsub, fun _ _ => huy ▸ bot_le⟩
  obtain ⟨ρ, hρ, hmean⟩ := exists_le_ballAverageWithBot_of_harmonicAtWithBot huy
    (hu y (hclosed (ball_subset_closedBall hy)) huy)
  exact ⟨min ρ ε, lt_min hρ hε, (ball_subset_ball (min_le_right _ _)).trans hεsub,
    fun r hr => hmean r ⟨hr.1, hr.2.trans_le (min_le_left _ _)⟩⟩

end EquivalentDefinition



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
        have hscaled_eq : hscaled = p⁻¹ • h := by
          funext z
          simp [hscaled, smul_eq_mul]
        rw [hscaled_eq]
        exact hharm.const_smul (c := p⁻¹)
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

omit [MeasurableSpace E] [BorelSpace E] in
/-- The pointwise maximum of two subharmonic functions is subharmonic. -/
theorem SubharmonicOn.sup {v : E → WithBot ℝ} (hu : SubharmonicOn u s)
    (hv : SubharmonicOn v s) : SubharmonicOn (u ⊔ v) s := by
  refine ⟨hu.1.sup hv.1, fun x r h hclosed hcont hharm hbd y hy => sup_le ?_ ?_⟩
  · exact hu.2 x r h hclosed hcont hharm (fun z hz => le_sup_left.trans (hbd z hz)) y hy
  · exact hv.2 x r h hclosed hcont hharm (fun z hz => le_sup_right.trans (hbd z hz)) y hy

/-- Weighted Jensen inequality for the exponential on a circle.  If `P` is a nonnegative
probability density with respect to `circleAverage`, then applying `exp` after the weighted
average is bounded by the weighted average after applying `exp`. -/
lemma exp_weighted_circleAverage_le_circleAverage_weighted_exp
    {c : ℂ} {R : ℝ} {P ψ : ℂ → ℝ}
    (hR : 0 ≤ R) (hP_nonneg : ∀ z ∈ sphere c R, 0 ≤ P z)
    (hP_avg : circleAverage P c R = 1)
    (hP_cont : ContinuousOn P (sphere c R))
    (hψ_cont : ContinuousOn ψ (sphere c R)) :
    exp (circleAverage (fun z : ℂ => P z * ψ z) c R)
      ≤ circleAverage (fun z : ℂ => P z * exp (ψ z)) c R := by
  let μP : Measure ℂ := (circleMeasure c R).withDensity fun z => ENNReal.ofReal (P z)
  have hP_nonneg_ae : ∀ᵐ z ∂circleMeasure c R, 0 ≤ P z :=
    (ae_mem_sphere_circleMeasure hR).mono fun z hz => hP_nonneg z hz
  have hP_int : CircleIntegrable P c R := hP_cont.circleIntegrable hR
  have hP_meas : AEMeasurable P (circleMeasure c R) :=
    hP_int.aestronglyMeasurable_circleMeasure.aemeasurable
  have : IsProbabilityMeasure μP :=
    isProbabilityMeasure_withDensity_circleMeasure hP_nonneg_ae hP_int hP_avg
  have hPψ_int : CircleIntegrable (fun z : ℂ => P z * ψ z) c R :=
    (hP_cont.mul hψ_cont).circleIntegrable hR
  have hPexpψ_int : CircleIntegrable (fun z : ℂ => P z * exp (ψ z)) c R :=
    (hP_cont.mul (by fun_prop)).circleIntegrable hR
  have hleft : circleAverage (fun z : ℂ => P z * ψ z) c R = ∫ z, ψ z ∂μP :=
    integral_withDensity_circleMeasure_eq_circleAverage_mul hP_meas hP_nonneg_ae hPψ_int
  have hright : circleAverage (fun z : ℂ => P z * exp (ψ z)) c R = ∫ z, exp (ψ z) ∂μP :=
    integral_withDensity_circleMeasure_eq_circleAverage_mul hP_meas hP_nonneg_ae hPexpψ_int
  rw [hleft, hright]
  refine convexOn_exp.map_integral_le continuousOn_exp isClosed_univ (by simp) ?_ ?_
  . exact integrable_withDensity_circleMeasure_of_circleIntegrable hP_meas hP_nonneg_ae hPψ_int
  . exact integrable_withDensity_circleMeasure_of_circleIntegrable hP_meas hP_nonneg_ae hPexpψ_int

/-- Jensen's inequality for the Poisson logarithmic barrier. If `h` is positive on the boundary,
then the exponential of the Poisson extension of `log h` is bounded by `h` inside. -/
lemma exp_poisson_log_le_harmonic {c w : ℂ} {R : ℝ} {h : ℂ → ℝ}
    (hcont : ContinuousOn h (closedBall c R))
    (hharm : InnerProductSpace.HarmonicOnNhd h (ball c R))
    (h_pos : ∀ z ∈ sphere c R, 0 < h z) (hw : w ∈ ball c R) :
    exp (circleAverage (fun z : ℂ => poissonKernel c w z * log (h z)) c R) ≤ h w := by
  let P : ℂ → ℝ := fun z => poissonKernel c w z
  let ψ : ℂ → ℝ := fun z => log (h z)
  have hR_pos : 0 < R := lt_of_le_of_lt dist_nonneg (by simpa [Metric.mem_ball] using hw)
  have hR_nonneg : 0 ≤ R := hR_pos.le
  have hP_nonneg : ∀ z ∈ sphere c R, 0 ≤ P z := by
    -- codex without review
    intro z hz
    have hz_norm : ‖z - c‖ = R := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hz
    have hw_norm : ‖w - c‖ < R := by
      simpa [Metric.mem_ball, dist_eq_norm] using hw
    have hden_ne : (z - c) - (w - c) ≠ 0 := by
      intro hden
      have hden' : z - w = 0 := by
        simpa [sub_sub_sub_cancel_right] using hden
      have hzw : z = w := sub_eq_zero.mp hden'
      have hcontr : R < R := by
        calc
          R = ‖z - c‖ := hz_norm.symm
          _ = ‖w - c‖ := by rw [hzw]
          _ < R := hw_norm
      exact (lt_irrefl R) hcontr
    have hden_pos : 0 < ‖(z - c) - (w - c)‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hden_ne)
    have hnum_nonneg : 0 ≤ ‖z - c‖ ^ 2 - ‖w - c‖ ^ 2 := by
      nlinarith [hz_norm, hw_norm.le, norm_nonneg (w - c)]
    simpa [P, poissonKernel, sub_sub_sub_cancel_right] using
      div_nonneg hnum_nonneg hden_pos.le
  have hP_cont : ContinuousOn P (sphere c R) := continuousOn_poissonKernel_right_of_mem_ball hw
  have hψ_cont : ContinuousOn ψ (sphere c R) := by
    apply (hcont.mono sphere_subset_closedBall).log
    intro z hz; exact ne_of_gt (h_pos z hz)
  have hP_avg : circleAverage P c R = 1 := by
    simpa [P, Pi.mul_def] using InnerProductSpace.HarmonicOnNhd.circleAverage_poissonKernel_smul
      (f := fun _ : ℂ => (1 : ℝ)) (by simp) hw
  have hJensen := exp_weighted_circleAverage_le_circleAverage_weighted_exp
      hR_nonneg hP_nonneg hP_avg hP_cont hψ_cont
  have hH_contcl := InnerProductSpace.HarmonicContOnCl.mk_ball hharm hcont
  have hP_H_avg : circleAverage (fun z : ℂ => P z * h z) c R = h w := by
    have hfun : (fun z : ℂ => P z * h z) = poissonKernel c w * h := by
      funext z
      simp [P]
    rw [hfun]
    exact InnerProductSpace.HarmonicContOnCl.circleAverage_poissonKernel_smul hH_contcl hw
  have hright_eq : circleAverage (fun z : ℂ => P z * exp (ψ z)) c R = h w := by
    rw [← hP_H_avg]
    apply circleAverage_congr_sphere
    intro z hz_abs
    simp [ψ]; left
    refine Real.exp_log (h_pos z ?_)
    simpa [abs_of_nonneg hR_nonneg] using hz_abs
  rw [← hright_eq]
  exact hJensen

/-- Applying `expBot` to a subharmonic `WithBot ℝ`-valued function preserves subharmonicity. -/
theorem SubharmonicOn.expBot_comp {u : ℂ → WithBot ℝ} {s : Set ℂ} (hu : SubharmonicOn u s) :
  SubharmonicOn (fun z => expBot (u z)) s := by
  constructor
  · exact hu.1.expBot_mul.withBot_coe
  · intro c R h hclosed hcont hharm hbd w hw
    have hbd_real : ∀ z ∈ sphere c R, expBot (u z) ≤ h z :=
      fun z hz => WithBot.coe_le_coe.mp (hbd z hz)
    have h_nonneg : ∀ z ∈ sphere c R, 0 ≤ h z := by
      intro z hz
      have hexp_nonneg : 0 ≤ expBot (u z) := by
        cases u z <;> simp [expBot, exp_nonneg]
      exact hexp_nonneg.trans (hbd_real z hz)
    have hle_add_eps : ∀ ε > 0, expBot (u w) ≤ h w + ε := by
      intro ε hε
      let φ : ℂ → ℝ := fun z => log (h z + ε)
      have hφ_cont : ContinuousOn φ (sphere c R) := by
        have hcont_sphere : ContinuousOn h (sphere c R) :=
          hcont.mono sphere_subset_closedBall
        have hlog_ne : ∀ z ∈ sphere c R, h z + ε ≠ 0 := by
          intro z hz; exact ne_of_gt (by linarith [h_nonneg z hz])
        have hsum_cont : ContinuousOn (fun z : ℂ => h z + ε) (sphere c R) := by fun_prop
        exact hsum_cont.log hlog_ne
      rcases poissonIntegral_continuousOn_closedBall_eq_boundary hφ_cont
        with ⟨H, hH_cont, hH_harm, hH_poisson, hH_boundary⟩
      have hbd_log : ∀ z ∈ sphere c R, u z ≤ H z := by
        intro z hz
        have hz_log : u z ≤ log (h z + ε) := le_log_of_expBot_le (by linarith [hbd_real z hz])
        rw [hH_boundary z hz]
        exact hz_log
      have huw_log : u w ≤ H w := hu.2 c R H hclosed hH_cont hH_harm hbd_log w hw
      grw [expBot_le_exp_of_le_coe huw_log]
      rw [hH_poisson w hw,
        poissonIntegral_circleMeasure_withDensityᵥ_eq_circleAverage (dist_nonneg.trans (mem_ball.mp hw).le) hw hφ_cont]
      simp only [smul_eq_mul]
      refine exp_poisson_log_le_harmonic ?_ ?_ ?_ hw
      . fun_prop
      . have hfun : (fun z => h z + ε) = h + fun _ => ε := by
          funext z
          rfl
        rw [hfun]
        exact hharm.add (InnerProductSpace.harmonicOnNhd_const ε)
      . intro z hz; linarith [h_nonneg z hz]
    exact WithBot.coe_le_coe.mpr (le_of_forall_pos_le_add hle_add_eps)



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
  rw [hPoisson w hw, poissonIntegral_circleMeasure_withDensityᵥ_eq_circleAverage
    (dist_nonneg.trans (mem_ball.mp hw).le) hw hu_cont] at hle_real
  simpa only [smul_eq_mul] using hle_real
-- Note actually I don't need continuity condition but the proof might be tough (using sequence
-- to approach then translate the inequality)


variable [NormedSpace ℂ E] [NormedSpace ℂ F]

/-- If `f` is analytic on an open set, then `log ‖f‖`, with value `⊥` at zeros, is upper
semicontinuous there. -/
lemma logNormBot_comp_analytic_upperSemicontinuousOn_banach [DecidableEq F]
    {f : ℂ → F} {s : Set ℂ} (_hs : IsOpen s) (hf : AnalyticOn ℂ f s) :
    UpperSemicontinuousOn (logNormBot.comp f) s := by
  intro x hx a hlt
  cases a with
  | bot => exact False.elim (not_lt_bot hlt)
  | coe c =>
      have hnorm_lt : ‖f x‖ < exp c := by
        by_cases hfx : f x = 0
        · simpa [hfx] using exp_pos c
        · apply (Real.log_lt_iff_lt_exp (norm_pos_iff.mpr hfx)).mp
          apply WithBot.coe_lt_coe.mp
          simpa [Function.comp_def, logNormBot, hfx] using hlt
      filter_upwards [(hf.continuousOn x hx).norm (Iio_mem_nhds hnorm_lt)] with y hy
      by_cases hfy : f y = 0
      · simp [logNormBot, hfy]
      · simp [logNormBot, hfy]
        exact (Real.log_lt_iff_lt_exp (norm_pos_iff.mpr hfy)).mpr hy

/-- Scalar-valued analytic functions have subharmonic logarithmic modulus. -/
theorem logNormBot_comp_analytic_subharmonicOn_scalar {f : ℂ → ℂ} {s : Set ℂ}
  (hs : IsOpen s) (hf : AnalyticOn ℂ f s) : SubharmonicOn (logNormBot ∘ f) s := by
  refine subharmonicOn_of_upperSemicontinuousOn_of_harmonicAtWithBot
    (logNormBot_comp_analytic_upperSemicontinuousOn_banach hs hf) ?_
  intro z hz hfinite
  have hfz_ne : f z ≠ 0 := by
    intro hfz
    exact hfinite (by simp [logNormBot, hfz])
  have hfz_an : AnalyticAt ℂ f z := hf.analyticAt (hs.mem_nhds hz)
  let v : ℂ → ℝ := fun y => log ‖f y‖
  have hvz : InnerProductSpace.HarmonicAt v z :=
    hfz_an.harmonicAt_log_norm hfz_ne
  refine ⟨v, hvz, ?_⟩
  filter_upwards [hfz_an.continuousAt.eventually_ne hfz_ne] with y hy
  simp [logNormBot, v, hy]


theorem logNormBot_comp_analytic_subharmonicOn_banach [DecidableEq F] {f : ℂ → F} {s : Set ℂ}
  (hs : IsOpen s) (hf : AnalyticOn ℂ f s) : SubharmonicOn (logNormBot ∘ f) s := by
  constructor
  · exact logNormBot_comp_analytic_upperSemicontinuousOn_banach hs hf
  · intro c R h hclosed hcont hharm hbd w hw
    by_cases hfw : f w = 0
    · simp [logNormBot, hfw]
    · obtain ⟨ℓ, hℓ_norm, hℓw⟩ := exists_dual_vector'' ℂ (f w)
      let g : ℂ → ℂ := ℓ ∘ f
      have hg_analytic : AnalyticOn ℂ g s := ℓ.comp_analyticOn hf
      have hg_sub : SubharmonicOn (logNormBot.comp g) s :=
        logNormBot_comp_analytic_subharmonicOn_scalar hs hg_analytic
      have hbd_g : ∀ z ∈ sphere c R, (logNormBot.comp g) z ≤ h z := by
        intro z hz
        have hlog_le : logNormBot (ℓ (f z)) ≤ logNormBot (f z) := by
          by_cases hℓz : ℓ (f z) = 0
          · simp [logNormBot, hℓz]
          · have hfz : f z ≠ 0 := by intro hfz; apply hℓz; simp [hfz]
            have hnorm_le : ‖ℓ (f z)‖ ≤ ‖f z‖ := by
              grw [ℓ.le_opNorm (f z), hℓ_norm]; simp
            simp [logNormBot, hℓz, hfz]
            exact Real.log_le_log (norm_pos_iff.mpr hℓz) hnorm_le
        exact hlog_le.trans (hbd z hz)
      have hg_eq : (logNormBot.comp g) w = (logNormBot.comp f) w := by
        have hℓfw_ne : ℓ (f w) ≠ 0 := by
          rw [hℓw]
          exact Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hfw)
        simp [Function.comp_def, g, logNormBot, hfw, hℓw]
      rw [← hg_eq]
      exact hg_sub.2 c R h hclosed hcont hharm hbd_g w hw

theorem norm_rpow_comp_analytic_subharmonicOn_banach [DecidableEq F] {f : ℂ → F} {p : ℝ} {s : Set ℂ}
  (hs : IsOpen s) (hf : AnalyticOn ℂ f s) (hp : 0 < p) :
  SubharmonicOn (fun z => ((‖f z‖ ^ p : ℝ) : WithBot ℝ)) s := by
  simpa [Function.comp_def, exp_mul_logNorm_eq_norm_rpow hp] using
    ((logNormBot_comp_analytic_subharmonicOn_banach hs hf).const_mul hp.le).expBot_comp

/-- For analytic `f`, the function `log⁺ ‖f‖ = max (log ‖f‖) 0` is subharmonic. -/
theorem posLog_norm_comp_analytic_subharmonicOn_banach {f : ℂ → F} {s : Set ℂ} [DecidableEq F]
    (hs : IsOpen s) (hf : AnalyticOn ℂ f s) :
    SubharmonicOn (fun z => (log⁺ ‖f z‖ : WithBot ℝ)) s := by
  have h0 : SubharmonicOn (fun _ : ℂ => ((0 : ℝ) : WithBot ℝ)) s :=
    harmonicOnNhd_subharmonicOn _ s (InnerProductSpace.harmonicOnNhd_const 0)
  convert (logNormBot_comp_analytic_subharmonicOn_banach hs hf).sup h0 using 1
  funext z
  by_cases hfz : f z = 0
  · simp [logNormBot, hfz]
  · simp [logNormBot, hfz, posLog_apply, max_comm]

/- From math perspective, for `s ⊆ ℝ^n` case, it will be more natural to consider notion of 'log |f|'
being 'pluri-subharmonic' rather than 'subharmonic', even if this theorem is still correct (as
`pluri-subharmonic` implies `subharmonic`). But I don't think whether we need such generality. -/

theorem logNormBot_comp_analytic_subharmonicOn_gen [DecidableEq F] {f : E → F}
  (hs : IsOpen s) (hf : AnalyticOn ℂ f s) : SubharmonicOn (logNormBot.comp f) s := sorry

theorem norm_rpow_comp_analytic_subharmonicOn_gen {f : E → F} {p : ℝ}
  (hs : IsOpen s) (hf : AnalyticOn ℂ f s) (hp : 0 < p) :
  SubharmonicOn (fun z => ((‖f z‖ ^ p : ℝ) : WithBot ℝ)) s := sorry
