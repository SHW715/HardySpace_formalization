import Mathlib.Analysis.Convex.Integral
import HardySpaceFormalization.Harmonic_max_principle
import HardySpaceFormalization.Poisson_lemma


/-!
# Subharmonic functions, mean-value test version

This file experiments with a direct mean-value definition of subharmonicity for
`WithBot ℝ`-valued functions.  It is intentionally kept separate from
`Subharmonic.lean`.

-/

open MeasureTheory Metric Set Real Filter
open scoped ENNReal Topology

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

/-- Auxiliary real-valued representative used to integrate `WithBot ℝ`-valued functions:
`⊥` is sent to `0`, while finite values are unchanged. -/
def WithBotToReal : WithBot ℝ → ℝ
  | ⊥ => 0
  | (x : ℝ) => x

/-- The integral of a `WithBot ℝ`-valued function over a set. If the `⊥` set has positive
measure, the integral is defined to be `⊥`; otherwise we integrate the real-valued representative
obtained by sending `⊥` to `0`. -/
def withBotIntegral (u : E → WithBot ℝ) (A : Set E) (μ : Measure E := volume) : WithBot ℝ :=
  if μ (A ∩ {x | u x = ⊥}) = 0 then
    ((∫ x in A, WithBotToReal (u x) ∂μ : ℝ) : WithBot ℝ)
  else ⊥

open Classical in
def withBotIntegral' (u : E → WithBot ℝ) (A : Set E) (μ : Measure E := volume) : WithBot ℝ :=
  if μ (A ∩ {x | u x = ⊥}) = 0 ∧ IntegrableOn (WithBotToReal ∘ u) A μ then
      ((∫ x in A, WithBotToReal (u x) ∂μ : ℝ) : WithBot ℝ)
  else ⊥


notation3 "∫ᴮ "(...)", "r:60:(scoped f => f)" ∂"μ:70 =>
  withBotIntegral r Set.univ μ
notation3 "∫ᴮ "(...)", "r:60:(scoped f => withBotIntegral f Set.univ volume) => r
notation3 "∫ᴮ "(...)" in "s", "r:60:(scoped f => f)" ∂"μ:70 =>
  withBotIntegral r s μ
notation3 "∫ᴮ "(...)" in "s", "r:60:(scoped f => withBotIntegral f s volume) => r

/-- Ball average for `WithBot ℝ`-valued functions, using `withBotIntegral`.
For `r ≤ 0` this is just a total-definition junk value; the sub-mean property below only uses it
under the hypothesis `0 < r`. -/
def ballAverageWithBot (u : E → WithBot ℝ) (x : E) (r : ℝ) : WithBot ℝ :=
  ((volume (ball x r)).toReal)⁻¹ * (∫ᴮ y in ball x r, u y)

/-- For a real-valued function coerced to `WithBot ℝ`, the `WithBot` integral is just the ordinary
Bochner integral, coerced to `WithBot ℝ`. -/
lemma withBotIntegral_coe (u : E → ℝ) (A : Set E) (μ : Measure E := volume) :
    ∫ᴮ x in A, (u x : WithBot ℝ) ∂μ = ((∫ x in A, u x ∂μ : ℝ) : WithBot ℝ) := by
  unfold withBotIntegral
  simp [WithBotToReal]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- If a `WithBot ℝ`-valued function agrees almost everywhere with a real-valued representative,
then the auxiliary real representative obtained by `WithBotToReal` is integrable wherever the
real representative is integrable. -/
lemma integrableOn_WithBotToReal_of_eq_coe_ae
    {u : E → WithBot ℝ} {v : E → ℝ} {A : Set E} {μ : Measure E}
    (hv : IntegrableOn v A μ)(huv : ∀ᵐ x ∂μ.restrict A, u x = v x) :
    IntegrableOn (WithBotToReal ∘ u) A μ := by
  refine hv.congr_fun_ae ?_
  filter_upwards [huv] with x hx
  simp [hx, WithBotToReal]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- If `f` is continuous and nonzero on a compact set `K`, then
`WithBotToReal ∘ logNormBot ∘ f` is integrable on any finite-measure measurable subset of `K`. -/
lemma integrableOn_WithBotToReal_logNormBot_comp_of_continuousOn_of_ne_on [DecidableEq F]
    {f : E → F} {A K : Set E} {μ : Measure E}
    (hf_cont : ContinuousOn f K) (hK : IsCompact K)
    (hA_meas : MeasurableSet A) (hA_sub : A ⊆ K) (hA_ne_top : μ A ≠ ∞)
    (hne : ∀ x ∈ K, f x ≠ 0) :
    IntegrableOn (WithBotToReal ∘ logNormBot ∘ f) A μ := by
  have hlog_cont : ContinuousOn (fun x => log ‖f x‖) K :=
    hf_cont.norm.log (fun x hx => norm_ne_zero_iff.mpr (hne x hx))
  have hlog_int : IntegrableOn (fun x => log ‖f x‖) A μ :=
    hlog_cont.integrableOn_of_subset_isCompact hK hA_meas hA_sub hA_ne_top
  refine integrableOn_WithBotToReal_of_eq_coe_ae hlog_int ?_
  filter_upwards [ae_restrict_mem hA_meas] with x hx
  simp [logNormBot, hne x (hA_sub hx)]

/-- For a real-valued function coerced to `WithBot ℝ`, the `WithBot` ball average is the ordinary
ball average, coerced to `WithBot ℝ`. -/
lemma ballAverageWithBot_coe (u : E → ℝ) (x : E) (r : ℝ) :
    ballAverageWithBot (fun y => (u y : WithBot ℝ)) x r =
      ((ballAverage (F := ℝ) u x r : ℝ) : WithBot ℝ) := by
  simp [ballAverageWithBot, ballAverage, withBotIntegral_coe, smul_eq_mul]

/-- A positive constant can be pulled through the auxiliary real representative of a
`WithBot ℝ` value. -/
lemma WithBotToReal_const_mul_of_pos {p : ℝ} (hp : 0 < p) (x : WithBot ℝ) :
    WithBotToReal ((p : WithBot ℝ) * x) = p * WithBotToReal x := by
  cases x with
  | bot =>
      have hp_ne : (p : WithBot ℝ) ≠ 0 := by exact_mod_cast hp.ne'
      simp [WithBotToReal, WithBot.mul_bot hp_ne]
  | coe a =>
      change WithBotToReal ((p * a : ℝ) : WithBot ℝ) = p * a
      simp [WithBotToReal]

/-- For a positive constant, the `⊥` set of `p * u` is the `⊥` set of `u`. -/
lemma const_mul_eq_bot_iff_of_pos {p : ℝ} (hp : 0 < p) (x : WithBot ℝ) :
    (p : WithBot ℝ) * x = ⊥ ↔ x = ⊥ := by
  cases x with
  | bot =>
      have hp_ne : (p : WithBot ℝ) ≠ 0 := by exact_mod_cast hp.ne'
      simp [WithBot.mul_bot hp_ne]
  | coe a =>
      rw [WithBot.mul_eq_bot_iff]
      simp

/-- Positive constant multiplication is monotone on `WithBot ℝ`. -/
lemma WithBot.const_mul_le_const_mul_of_pos {p : ℝ} (hp : 0 < p)
    {x y : WithBot ℝ} (hxy : x ≤ y) :
    (p : WithBot ℝ) * x ≤ (p : WithBot ℝ) * y := by
  cases x with
  | bot =>
      have hp_ne : (p : WithBot ℝ) ≠ 0 := by exact_mod_cast hp.ne'
      cases y <;> simp [WithBot.mul_bot hp_ne]
  | coe a =>
      cases y with
      | bot =>
          simp at hxy
      | coe b =>
          exact WithBot.coe_le_coe.mpr
            (mul_le_mul_of_nonneg_left (WithBot.coe_le_coe.mp hxy) hp.le)

/-- Positive constant multiplication commutes with the `WithBot` integral. -/
lemma withBotIntegral_const_mul_of_pos {p : ℝ} (hp : 0 < p)
    (u : E → WithBot ℝ) (A : Set E) (μ : Measure E := volume) :
    withBotIntegral (fun x => (p : WithBot ℝ) * u x) A μ =
      (p : WithBot ℝ) * withBotIntegral u A μ := by
  unfold withBotIntegral
  simp_rw [const_mul_eq_bot_iff_of_pos hp]
  by_cases hbot : μ (A ∩ {x | u x = ⊥}) = 0
  · simp [hbot, WithBotToReal_const_mul_of_pos hp, integral_const_mul]
  · simp [hbot]
    have hp_ne : (p : WithBot ℝ) ≠ 0 := by exact_mod_cast hp.ne'
    simp [WithBot.mul_bot hp_ne]

/-- Positive constant multiplication commutes with `ballAverageWithBot`. -/
lemma ballAverageWithBot_const_mul_of_pos {p : ℝ} (hp : 0 < p)
    (u : E → WithBot ℝ) (x : E) (r : ℝ) :
    ballAverageWithBot (fun y => (p : WithBot ℝ) * u y) x r =
      (p : WithBot ℝ) * ballAverageWithBot u x r := by
  unfold ballAverageWithBot
  rw [withBotIntegral_const_mul_of_pos hp]
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
lemma ballAverageWithBot_zero (x : E) (r : ℝ) :
    ballAverageWithBot 0 x r = 0 := by
  simpa [ballAverage] using ballAverageWithBot_coe 0 x r

/-- `withBotIntegral` is monotone: a pointwise `≤` implies the `WithBot`-integrals compare.
The key cases are:
· if `{u = ⊥}` has positive measure, `withBotIntegral u = ⊥ ≤ anything`;
· otherwise both are real and the comparison is the standard integral monotonicity
  (which requires integrability of the real representatives). -/
lemma withBotIntegral_mono {u v : E → WithBot ℝ} {A : Set E} {μ : Measure E}
    (hA : NullMeasurableSet A μ)
    (h : ∀ x ∈ A, u x ≤ v x)
    (hu_int : IntegrableOn (fun x => WithBotToReal (u x)) A μ)
    (hv_int : IntegrableOn (fun x => WithBotToReal (v x)) A μ) :
    withBotIntegral u A μ ≤ withBotIntegral v A μ := by
  unfold withBotIntegral
  have hsubset : A ∩ {x | v x = ⊥} ⊆ A ∩ {x | u x = ⊥} := fun x ⟨hxA, hvx⟩ =>
    ⟨hxA, le_antisymm (hvx ▸ h x hxA) bot_le⟩
  by_cases hu_bot : μ (A ∩ {x | u x = ⊥}) = 0
  · have hv_bot : μ (A ∩ {x | v x = ⊥}) = 0 := measure_mono_null hsubset hu_bot
    simp only [hu_bot, hv_bot, ↓reduceIte]
    apply WithBot.coe_le_coe.mpr
    apply setIntegral_mono_ae_restrict hu_int hv_int
    have hu_ne_bot : ∀ᵐ x ∂μ.restrict A, u x ≠ ⊥ := by
      rw [ae_iff]
      rw [Measure.restrict_apply₀' hA]
      simpa [inter_comm]
    filter_upwards [ae_restrict_mem₀ hA, hu_ne_bot] with x hxA hux_ne
    have hvx_ne : v x ≠ ⊥ := fun hvx => hux_ne (le_antisymm (hvx ▸ h x hxA) bot_le)
    cases hux : u x with
    | bot => exact False.elim (hux_ne hux)
    | coe a =>
      cases hvx : v x with
      | bot => exact False.elim (hvx_ne hvx)
      | coe b =>
        exact WithBot.coe_le_coe.mp (by simpa [hux, hvx] using h x hxA)
  · simp [hu_bot]

/-- `ballAverageWithBot` is monotone in the integrand (pointwise inequality → average inequality),
provided the real representatives of both functions are integrable on the ball. -/
lemma ballAverageWithBot_mono {u v : E → WithBot ℝ} {x : E} {r : ℝ}
    (h : ∀ y, u y ≤ v y)
    (hu_int : IntegrableOn (fun y => WithBotToReal (u y)) (ball x r))
    (hv_int : IntegrableOn (fun y => WithBotToReal (v y)) (ball x r)) :
    ballAverageWithBot u x r ≤ ballAverageWithBot v x r := by
  unfold ballAverageWithBot
  by_cases hc : ((volume (ball x r)).toReal)⁻¹ = (0 : ℝ)
  · simp [hc]
  · have hc_pos : 0 < ((volume (ball x r)).toReal)⁻¹ :=
      lt_of_le_of_ne (inv_nonneg.mpr ENNReal.toReal_nonneg) (Ne.symm hc)
    exact WithBot.const_mul_le_const_mul_of_pos hc_pos
      (withBotIntegral_mono isOpen_ball.nullMeasurableSet (fun y hy => h y) hu_int hv_int)

/-- A function is subharmonic on a set if it is upper semicontinuous there and satisfies the
local sub-mean inequality on sufficiently small balls. -/
def SubharmonicOn (u : E → WithBot ℝ) (s : Set E) : Prop :=
  UpperSemicontinuousOn u s ∧
    ∀ x ∈ s, ∃ ρ > 0, ball x ρ ⊆ s ∧
      ∀ r, 0 < r ∧ r < ρ → u x ≤ ballAverageWithBot u x r

/-- The local sub-mean definition implies the harmonic comparison principle on balls:
if a harmonic function dominates a subharmonic function on the boundary, then it dominates it
inside. -/
theorem SubharmonicOn.harmonicComparison [Nontrivial E] (hu : SubharmonicOn u s)
    (hs : IsOpen s) :
    ∀ (x : E) (r : ℝ) (h : E → ℝ),
      closedBall x r ⊆ s → ContinuousOn h (closedBall x r) →
      InnerProductSpace.HarmonicOnNhd h (ball x r) →
      (∀ y ∈ sphere x r, u y ≤ h y) → ∀ y ∈ ball x r, u y ≤ h y := by
  sorry

/-- Every real-valued harmonic function on an open set is subharmonic for the local
sub-mean definition. -/
theorem harmonicOnNhd_subharmonicOn
  [Nontrivial E] (u : E → ℝ) (s : Set E) (hs : IsOpen s)
  (hu : InnerProductSpace.HarmonicOnNhd u s) :
  SubharmonicOn (fun z => (u z : WithBot ℝ)) s := by
  constructor
  · exact (hu.continuousOn.upperSemicontinuousOn).withBot_coe
  · intro x hx
    rcases Metric.isOpen_iff.mp hs x hx with ⟨ρ, hρ_pos, hρ_sub⟩
    refine ⟨ρ, hρ_pos, hρ_sub, ?_⟩
    intro r hr
    rw [ballAverageWithBot_coe]
    refine WithBot.coe_le_coe.mpr ?_
    have hclosed_sub : closedBall x |r| ⊆ s := by
      intro y hy
      exact hρ_sub (by
        rw [Metric.mem_ball]
        exact lt_of_le_of_lt (by simpa [Metric.mem_closedBall] using hy)
          (by simpa [abs_of_pos hr.1] using hr.2))
    have hmean : ballAverage u x r = u x := by
      simpa [abs_of_pos hr.1] using
        HarmonicOnNhd.ballAverage_eq ((hu.mono hclosed_sub) : InnerProductSpace.HarmonicOnNhd u (closedBall x |r|))
    exact le_of_eq hmean.symm



/--The extended notion of `HarmonicAt` for `WithBot ℝ`-valued function at `x`. -/
def HarmonicAtWithBot (u : E → WithBot ℝ) (x : E) : Prop :=
  ∃ v : E → ℝ, InnerProductSpace.HarmonicAt v x ∧ u =ᶠ[𝓝 x] (v ·)



/-- An upper semicontinuous function which is locally harmonic at every finite
point is subharmonic. -/
theorem subharmonicOn_of_upperSemicontinuousOn_of_harmonicAtWithBot [Nontrivial E]
    {u : E → WithBot ℝ} {s : Set E} (hs : IsOpen s) (husc : UpperSemicontinuousOn u s)
    (hu : ∀ z ∈ s, u z ≠ ⊥ → HarmonicAtWithBot u z) : SubharmonicOn u s := by
  constructor
  · exact husc
  · intro x hx
    rcases Metric.isOpen_iff.mp hs x hx with ⟨ρ₀, hρ₀_pos, hρ₀_sub⟩
    by_cases hux : u x = ⊥
    · -- u x = ⊥, so ⊥ ≤ anything
      exact ⟨ρ₀, hρ₀_pos, hρ₀_sub, fun r _ => hux ▸ bot_le⟩
    · -- u x is finite; extract local harmonic representative
      obtain ⟨v, hv, huv⟩ := hu x hx hux
      -- Get metric ball where u = v
      obtain ⟨N_uv, hN_uv, huv_N⟩ := huv.exists_mem
      obtain ⟨ρ_uv, hρ_uv_pos, hρ_uv_sub⟩ := Metric.mem_nhds_iff.mp hN_uv
      -- Get metric ball where v is harmonic at every point
      obtain ⟨N_v, hN_v, hv_N⟩ := hv.eventually.exists_mem
      obtain ⟨ρ_v, hρ_v_pos, hρ_v_sub⟩ := Metric.mem_nhds_iff.mp hN_v
      -- Use ρ = minimum of all three radii
      refine ⟨min (min ρ₀ ρ_uv) ρ_v, lt_min (lt_min hρ₀_pos hρ_uv_pos) hρ_v_pos, ?_, ?_⟩
      · -- ball x ρ ⊆ s
        intro y hy
        exact hρ₀_sub (Metric.ball_subset_ball (le_trans (min_le_left _ _) (min_le_left _ _)) hy)
      · intro r ⟨hr_pos, hr_lt⟩
        have hr_lt_uv : r < ρ_uv :=
          lt_of_lt_of_le hr_lt (le_trans (min_le_left _ _) (min_le_right _ _))
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
        -- Real integrals agree on the ball since u = v there
        have hint_eq : ∫ y in ball x r, WithBotToReal (u y) = ∫ y in ball x r, v y := by
          apply setIntegral_congr_ae measurableSet_ball (ae_of_all _ _)
          intro y hy
          rw [hu_eq_v_ball y hy]
          simp [WithBotToReal]
        -- withBotIntegrals agree
        have hwbi_eq : withBotIntegral u (ball x r) =
            withBotIntegral (fun y => (v y : WithBot ℝ)) (ball x r) := by
          have h_u_bot : volume (ball x r ∩ {y | u y = ⊥}) = 0 := by
            have hempty : ball x r ∩ {y | u y = ⊥} = ∅ := by
              ext y
              simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
                not_and]
              intro hy_ball; rw [hu_eq_v_ball y hy_ball]; exact WithBot.coe_ne_bot
            simp [hempty, measure_empty]
          rw [withBotIntegral_coe]
          unfold withBotIntegral
          rw [if_pos h_u_bot, hint_eq]
        -- ballAverageWithBots agree
        have hball_avg_eq : ballAverageWithBot u x r =
            ballAverageWithBot (fun y => (v y : WithBot ℝ)) x r := by
          simp only [ballAverageWithBot, hwbi_eq]
        -- Conclude: u x = ballAverageWithBot u x r
        suffices heq : u x = ballAverageWithBot u x r from heq.le
        calc u x
            = (v x : WithBot ℝ) := hux_eq
          _ = ((ballAverage (F := ℝ) v x r : ℝ) : WithBot ℝ) := by exact_mod_cast hmean.symm
          _ = ballAverageWithBot (fun y => (v y : WithBot ℝ)) x r := (ballAverageWithBot_coe v x r).symm
          _ = ballAverageWithBot u x r := hball_avg_eq.symm


/-- A nonnegative constant multiple of a subharmonic function is subharmonic. -/
theorem SubharmonicOn.const_mul [Nontrivial E] {p : ℝ} (hp : 0 ≤ p) (hu : SubharmonicOn u s) :
  SubharmonicOn (fun z => (p : WithBot ℝ) * u z) s := by
  constructor
  · exact hu.1.const_mul hp
  · intro x hx
    rcases hu.2 x hx with ⟨ρ, hρ_pos, hρ_sub, hmean⟩
    refine ⟨ρ, hρ_pos, hρ_sub, ?_⟩
    intro r hr
    by_cases hp0 : p = 0
    · simp only [hp0, WithBot.coe_zero, zero_mul]
      exact le_of_eq (ballAverageWithBot_zero (E := E) x r).symm
    · have hp_pos : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
      rw [ballAverageWithBot_const_mul_of_pos hp_pos]
      exact WithBot.const_mul_le_const_mul_of_pos hp_pos (hmean r hr)

/-- `expBot` is monotone on `WithBot ℝ`. -/
lemma expBot_mono {a b : WithBot ℝ} (h : a ≤ b) : expBot a ≤ expBot b := by
  cases a with
  | bot =>
    calc expBot (⊥ : WithBot ℝ) = 0 := by simp [expBot]
      _ ≤ expBot b := by cases b <;> simp [expBot, exp_nonneg]
  | coe x =>
    cases b with
    | bot => exact absurd h (not_le.mpr (WithBot.bot_lt_coe x))
    | coe y =>
      simp only [expBot_coe]
      exact Real.exp_le_exp.mpr (WithBot.coe_le_coe.mp h)

/-- Jensen's inequality for `expBot` and `ballAverageWithBot`: the exponential of the
`WithBot`-mean is at most the mean of the exponentials.

This is the mean-value ingredient needed to prove that `expBot ∘ u` is subharmonic directly from
the local sub-mean definition. -/
lemma expBot_ballAverageWithBot_le (u : ℂ → WithBot ℝ) (x : ℂ) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (WithBotToReal ∘ u) (ball x r) →
    IntegrableOn (fun z => expBot (u z)) (ball x r) →
    (expBot (ballAverageWithBot u x r) : WithBot ℝ) ≤
      ballAverageWithBot (fun z => (expBot (u z) : WithBot ℝ)) x r := by
  intro hu_int hexp_int
  have hμ_pos : 0 < volume (ball x r) := measure_ball_pos volume x hr
  have hμ_ne_top : volume (ball x r) ≠ ∞ := measure_ball_lt_top.ne
  have hq_pos : 0 < ((volume (ball x r)).toReal)⁻¹ := by
    exact inv_pos.mpr (ENNReal.toReal_pos hμ_pos.ne' hμ_ne_top)
  have hq_nonneg : 0 ≤ ((volume (ball x r)).toReal)⁻¹ := hq_pos.le
  have hRHS :
      ballAverageWithBot (fun z => (expBot (u z) : WithBot ℝ)) x r =
        ((ballAverage (fun z => expBot (u z)) x r : ℝ) : WithBot ℝ) :=
    ballAverageWithBot_coe (fun z => expBot (u z)) x r
  have hRHS_nonneg :
      0 ≤ ballAverage (fun z => expBot (u z)) x r := by
    have hint_nonneg : 0 ≤ ∫ z in ball x r, expBot (u z) := by
      exact setIntegral_nonneg measurableSet_ball (fun z hz => by
        cases u z <;> simp [expBot, exp_nonneg])
    simp [ballAverage, smul_eq_mul]
    exact mul_nonneg (by positivity) hint_nonneg
  have hvol_toReal : (volume (ball x r)).toReal = π * r ^ 2 := by
    rw [Complex.volume_ball]
    simp [ENNReal.toReal_mul, hr.le, mul_comm, mul_left_comm, pow_two]
  have hcoef :
      π⁻¹ * (((ENNReal.ofReal r).toReal ^ 2)⁻¹) = (volume.real (ball x r))⁻¹ := by
    rw [measureReal_def, hvol_toReal]
    simp [ENNReal.toReal_ofReal, hr.le, pow_two]
    field_simp [Real.pi_ne_zero, hr.ne']
  have hballAverage_eq_average (φ : ℂ → ℝ) :
      ballAverage φ x r = ⨍ z in ball x r, φ z := by
    simp [ballAverage, average_eq, hcoef, smul_eq_mul]
  by_cases hbot : volume (ball x r ∩ {z | u z = ⊥}) = 0
  · have hLHS :
        ballAverageWithBot u x r =
          ((ballAverage (WithBotToReal ∘ u) x r : ℝ) : WithBot ℝ) := by
      unfold ballAverageWithBot withBotIntegral ballAverage
      simp [hbot, smul_eq_mul]
    have hne_bot_ae : ∀ᵐ z ∂volume.restrict (ball x r), u z ≠ ⊥ := by
      rw [ae_iff]
      simpa [Measure.restrict_apply' measurableSet_ball, inter_comm] using hbot
    have hexp_int_real :
        IntegrableOn (fun z => exp (WithBotToReal (u z))) (ball x r) := by
      refine hexp_int.congr_fun_ae ?_
      filter_upwards [hne_bot_ae] with z hz
      cases huz : u z with
      | bot => exact False.elim (hz huz)
      | coe a => simp [WithBotToReal, expBot]
    have hJensen :
        exp (ballAverage (WithBotToReal ∘ u) x r) ≤
          ballAverage (fun z => exp (WithBotToReal (u z))) x r := by
      have hJensen_avg :
          exp (⨍ z in ball x r, (WithBotToReal ∘ u) z) ≤
            ⨍ z in ball x r, exp ((WithBotToReal ∘ u) z) :=
        convexOn_exp.map_set_average_le
          (μ := volume) (t := ball x r) (f := WithBotToReal ∘ u) (s := univ)
          continuousOn_exp isClosed_univ hμ_pos.ne' hμ_ne_top (by simp) hu_int
          hexp_int_real
      simpa [hballAverage_eq_average] using hJensen_avg
    have hRHS_eq_exp :
        ballAverage (fun z => expBot (u z)) x r =
          ballAverage (fun z => exp (WithBotToReal (u z))) x r := by
      unfold ballAverage
      simp only [smul_eq_mul]
      congr 1
      exact setIntegral_congr_ae measurableSet_ball <| by
        rw [← ae_restrict_iff' measurableSet_ball]
        filter_upwards [hne_bot_ae] with z hz
        cases huz : u z with
        | bot => exact False.elim (hz huz)
        | coe a => simp [WithBotToReal, expBot]
    rw [hLHS, hRHS, hRHS_eq_exp]
    exact WithBot.coe_le_coe.mpr hJensen
  · have hLHS_bot : ballAverageWithBot u x r = ⊥ := by
      have hq_ne : ((((volume (ball x r)).toReal)⁻¹ : ℝ) : WithBot ℝ) ≠ 0 := by
        exact_mod_cast hq_pos.ne'
      unfold ballAverageWithBot withBotIntegral
      rw [if_neg hbot]
      change ((((volume (ball x r)).toReal)⁻¹ : ℝ) : WithBot ℝ) * ⊥ = ⊥
      exact WithBot.mul_bot hq_ne
    rw [hLHS_bot, hRHS]
    exact WithBot.coe_le_coe.mpr hRHS_nonneg

/-- Applying `expBot` to a subharmonic `WithBot ℝ`-valued function preserves subharmonicity. -/
theorem SubharmonicOn.expBot_comp {u : ℂ → WithBot ℝ} {s : Set ℂ} (hu : SubharmonicOn u s) :
  SubharmonicOn (fun z => expBot (u z)) s := by
  constructor
  · exact hu.1.expBot_mul.withBot_coe
  · intro x hx
    rcases hu.2 x hx with ⟨ρ, hρ_pos, hρ_sub, hmean⟩
    exact ⟨ρ, hρ_pos, hρ_sub, fun r hr =>
      have hu_int : IntegrableOn (WithBotToReal ∘ u) (ball x r) := by
        sorry
      have hexp_int : IntegrableOn (fun z => expBot (u z)) (ball x r) := by
        sorry
      calc (expBot (u x) : WithBot ℝ)
          ≤ (expBot (ballAverageWithBot u x r) : WithBot ℝ) :=
              WithBot.coe_le_coe.mpr (expBot_mono (hmean r hr))
        _ ≤ ballAverageWithBot (fun z => (expBot (u z) : WithBot ℝ)) x r :=
              expBot_ballAverageWithBot_le u x hr.1 hu_int hexp_int⟩



-- # The following lemma will be useful for estimating function e.g. |f|^p
/-- A real-valued subharmonic function is bounded above by the Poisson integral of its boundary
values on a disk. -/
theorem SubharmonicOn.le_circleAverage_poissonKernel_smul
    {u : ℂ → ℝ} {s : Set ℂ} {c w : ℂ} {R : ℝ}
    (hu : SubharmonicOn (fun z => (u z : WithBot ℝ)) s)
    (hs : IsOpen s)
    (hu_cont : ContinuousOn u (sphere c R))
    (hclosed : closedBall c R ⊆ s) (hw : w ∈ ball c R) :
    u w ≤ circleAverage (fun z => poissonKernel c w z * u z) c R  := by
  rcases poissonIntegral_continuousOn_closedBall_eq_boundary
    (c := c) (R := R) hu_cont with
    ⟨h, hcont, hharm, hPoisson, hboundary⟩
  have hbd : ∀ y ∈ sphere c R, (u y : WithBot ℝ) ≤ h y := by
    intro y hy
    rw [hboundary y hy]
  have hle : (u w : WithBot ℝ) ≤ h w :=
    hu.harmonicComparison hs c R h hclosed hcont hharm hbd w hw
  have hle_real : u w ≤ h w := WithBot.coe_le_coe.mp hle
  rw [hPoisson w hw] at hle_real
  exact hle_real
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
  refine subharmonicOn_of_upperSemicontinuousOn_of_harmonicAtWithBot hs
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
  · intro w hw
    by_cases hfw : f w = 0
    · rcases Metric.isOpen_iff.mp hs w hw with ⟨ρ, hρ_pos, hρ_sub⟩
      exact ⟨ρ, hρ_pos, hρ_sub, fun r _ => by simp [Function.comp_def, logNormBot, hfw]⟩
    · obtain ⟨ℓ, hℓ_norm, hℓw⟩ := exists_dual_vector'' ℂ (f w)
      let g : ℂ → ℂ := ℓ ∘ f
      have hg_analytic : AnalyticOn ℂ g s := ℓ.comp_analyticOn hf
      have hg_sub : SubharmonicOn (logNormBot.comp g) s :=
        logNormBot_comp_analytic_subharmonicOn_scalar hs hg_analytic
      have hg_eq : (logNormBot.comp g) w = (logNormBot.comp f) w := by
        have hℓfw_ne : ℓ (f w) ≠ 0 := by
          rw [hℓw]
          exact Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hfw)
        simp [Function.comp_def, g, logNormBot, hfw, hℓw]
      have hpointwise : ∀ z, (logNormBot.comp g) z ≤ (logNormBot.comp f) z := by
        intro z
        have hlog_le : logNormBot (ℓ (f z)) ≤ logNormBot (f z) := by
          by_cases hℓz : ℓ (f z) = 0
          · simp [logNormBot, hℓz]
          · have hfz : f z ≠ 0 := by
              intro hfz
              exact hℓz (by simp [hfz])
            have hnorm_le : ‖ℓ (f z)‖ ≤ ‖f z‖ := by
              grw [ℓ.le_opNorm (f z), hℓ_norm]
              simp
            simp [logNormBot, hℓz, hfz]
            exact Real.log_le_log (norm_pos_iff.mpr hℓz) hnorm_le
        exact hlog_le
      have hgw_ne : g w ≠ 0 := by
        rw [show g w = ℓ (f w) by rfl, hℓw]
        exact Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hfw)
      rcases hg_sub.2 w hw with ⟨ρ₀, hρ₀_pos, hρ₀_sub, hg_mean⟩
      rcases Metric.eventually_nhds_iff.mp
          ((hf.analyticAt (hs.mem_nhds hw)).continuousAt.eventually_ne hfw) with
        ⟨ρf, hρf_pos, hρf_ne⟩
      rcases Metric.eventually_nhds_iff.mp
          ((hg_analytic.analyticAt (hs.mem_nhds hw)).continuousAt.eventually_ne hgw_ne) with
        ⟨ρg, hρg_pos, hρg_ne⟩
      refine ⟨min (min ρ₀ ρf) ρg, lt_min (lt_min hρ₀_pos hρf_pos) hρg_pos, ?_, fun r hr => ?_⟩
      · intro y hy
        exact hρ₀_sub (Metric.ball_subset_ball
          (le_trans (min_le_left _ _) (min_le_left _ _)) hy)
      have hr_lt_ρ₀ : r < ρ₀ :=
        lt_of_lt_of_le hr.2 (le_trans (min_le_left _ _) (min_le_left _ _))
      have hr_lt_ρf : r < ρf :=
        lt_of_lt_of_le hr.2 (le_trans (min_le_left _ _) (min_le_right _ _))
      have hr_lt_ρg : r < ρg :=
        lt_of_lt_of_le hr.2 (min_le_right _ _)
      have hclosed_sub_s : closedBall w r ⊆ s := fun y hy =>
        hρ₀_sub (Metric.closedBall_subset_ball hr_lt_ρ₀ hy)
      have hf_ne_closed : ∀ y ∈ closedBall w r, f y ≠ 0 := by
        intro y hy
        exact hρf_ne (lt_of_le_of_lt (by simpa [dist_comm, Metric.mem_closedBall] using hy) hr_lt_ρf)
      have hg_ne_closed : ∀ y ∈ closedBall w r, g y ≠ 0 := by
        intro y hy
        exact hρg_ne (lt_of_le_of_lt (by simpa [dist_comm, Metric.mem_closedBall] using hy) hr_lt_ρg)
      have hg_int : IntegrableOn (WithBotToReal ∘ logNormBot ∘ g) (ball w r) := by
        exact integrableOn_WithBotToReal_logNormBot_comp_of_continuousOn_of_ne_on
          (f := g) (A := ball w r) (K := closedBall w r) (μ := volume)
          (hg_analytic.continuousOn.mono hclosed_sub_s) (isCompact_closedBall w r)
          measurableSet_ball ball_subset_closedBall measure_ball_lt_top.ne hg_ne_closed
      have hf_int : IntegrableOn (WithBotToReal ∘ logNormBot ∘ f) (ball w r) := by
        exact integrableOn_WithBotToReal_logNormBot_comp_of_continuousOn_of_ne_on
          (f := f) (A := ball w r) (K := closedBall w r) (μ := volume)
          (hf.continuousOn.mono hclosed_sub_s) (isCompact_closedBall w r)
          measurableSet_ball ball_subset_closedBall measure_ball_lt_top.ne hf_ne_closed
      calc
        (logNormBot ∘ f) w = (logNormBot.comp g) w := hg_eq.symm
        _ ≤ ballAverageWithBot (logNormBot.comp g) w r := hg_mean r ⟨hr.1, hr_lt_ρ₀⟩
        _ ≤ ballAverageWithBot (logNormBot.comp f) w r :=
            ballAverageWithBot_mono hpointwise hg_int hf_int

theorem norm_rpow_comp_analytic_subharmonicOn_banach [DecidableEq F] {f : ℂ → F} {p : ℝ} {s : Set ℂ}
  (hs : IsOpen s) (hf : AnalyticOn ℂ f s) (hp : 0 < p) :
  SubharmonicOn (fun z => ((‖f z‖ ^ p : ℝ) : WithBot ℝ)) s := by
  simpa [Function.comp_def, exp_mul_logNorm_eq_norm_rpow hp] using
    ((logNormBot_comp_analytic_subharmonicOn_banach hs hf).const_mul hp.le).expBot_comp


end
