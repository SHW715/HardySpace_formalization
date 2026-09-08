import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Normed.Module.HahnBanach
import HardySpaceFormalization.Harmonic_max_principle
import HardySpaceFormalization.poissonIntegral
import HardySpaceFormalization.circleMeasure


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



/-- An upper semicontinuous `WithBot ℝ`-valued function which is locally harmonic at every finite
point is subharmonic. -/
theorem subharmonicOn_of_upperSemicontinuousOn_of_harmonicAtWithBot [Nontrivial E]
    {u : E → WithBot ℝ} {s : Set E} (husc : UpperSemicontinuousOn u s)
    (hu : ∀ z ∈ s, u z ≠ ⊥ → HarmonicAtWithBot u z) : SubharmonicOn u s := by
  constructor
  · exact husc
  · intro c R h hclosed hcont hharm hbd w hw
    sorry


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
  haveI : IsProbabilityMeasure μP :=
    isProbabilityMeasure_withDensity_circleMeasure hP_nonneg_ae hP_int hP_avg
  have hPψ_int : CircleIntegrable (fun z : ℂ => P z * ψ z) c R :=
    (hP_cont.mul hψ_cont).circleIntegrable hR
  have hPexpψ_int : CircleIntegrable (fun z : ℂ => P z * exp (ψ z)) c R :=
    (hP_cont.mul (by fun_prop)).circleIntegrable hR
  have hleft : circleAverage (fun z : ℂ => P z * ψ z) c R = ∫ z, ψ z ∂μP :=
    integral_withDensity_circleMeasure_eq_circleAverage_mul hP_nonneg_ae hPψ_int
  have hright : circleAverage (fun z : ℂ => P z * exp (ψ z)) c R = ∫ z, exp (ψ z) ∂μP :=
    integral_withDensity_circleMeasure_eq_circleAverage_mul hP_nonneg_ae hPexpψ_int
  rw [hleft, hright]
  refine convexOn_exp.map_integral_le continuousOn_exp isClosed_univ (by simp) ?_ ?_
  . exact integrable_withDensity_circleMeasure_of_circleIntegrable hP_nonneg_ae hPψ_int
  . exact integrable_withDensity_circleMeasure_of_circleIntegrable hP_nonneg_ae hPexpψ_int

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

/- From math perspective, for `s ⊆ ℝ^n` case, it will be more natural to consider notion of 'log |f|'
being 'pluri-subharmonic' rather than 'subharmonic', even if this theorem is still correct (as
`pluri-subharmonic` implies `subharmonic`). But I don't think whether we need such generality. -/

theorem logNormBot_comp_analytic_subharmonicOn_gen [DecidableEq F] {f : E → F}
  (hs : IsOpen s) (hf : AnalyticOn ℂ f s) : SubharmonicOn (logNormBot.comp f) s := sorry

theorem norm_rpow_comp_analytic_subharmonicOn_gen {f : E → F} {p : ℝ}
  (hs : IsOpen s) (hf : AnalyticOn ℂ f s) (hp : 0 < p) :
  SubharmonicOn (fun z => ((‖f z‖ ^ p : ℝ) : WithBot ℝ)) s := sorry
