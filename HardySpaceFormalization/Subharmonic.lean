import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Normed.Module.HahnBanach
import HardySpaceFormalization.Harmonic_max_principle
import HardySpaceFormalization.Poisson_lemma


/-!
# Subharmonic functions

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
   ∃ t ∈ 𝓝 x, ∃ v : E → ℝ, InnerProductSpace.HarmonicOnNhd v t ∧ ∀ y ∈ t, u y = (v y : WithBot ℝ)


/-- No positive superlevel set above a harmonic comparison function can occur inside a
ball whose boundary is already controlled. -/
lemma no_positive_superlevel_of_usc_locally_harmonic_withBot
    [Nontrivial E]
    {u : E → WithBot ℝ} {s : Set E} (husc : UpperSemicontinuousOn u s)
    (hharm : ∀ z ∈ s, u z ≠ ⊥ → HarmonicAtWithBot u z)
    {c : E} {R : ℝ} {h : E → ℝ}
    (hclosed : closedBall c R ⊆ s)
    (hcont : ContinuousOn h (closedBall c R))
    (hharm_on_ball : InnerProductSpace.HarmonicOnNhd h (ball c R)):
    (∀ y ∈ sphere c R, u y ≤ h y) → ∀ ε > 0,
      {y ∈ ball c R | ((h y + ε : ℝ) : WithBot ℝ) < u y} = ∅ := by
  intro hbd ε hε
  let V : Set E := {y ∈ ball c R | ((h y + ε : ℝ) : WithBot ℝ) < u y}
  by_contra hV_ne
  have hV_nonempty : V.Nonempty := Set.nonempty_iff_ne_empty.mpr hV_ne
  have hV_subset_ball : V ⊆ ball c R := fun y hy => hy.1
  have hV_subset_closedBall : V ⊆ closedBall c R := fun y hy => ball_subset_closedBall hy.1
  have hV_subset_s : V ⊆ s := fun y hy => hclosed (hV_subset_closedBall hy)
  have hV_finite : ∀ y ∈ V, u y ≠ ⊥ := by
    intro y hy hy_bot
    have hlt : ((h y + ε : ℝ) : WithBot ℝ) < u y := hy.2
    simp [hy_bot] at hlt
  have hV_harmonicAtWithBot : ∀ y ∈ V, HarmonicAtWithBot u y := by
    intro y hy; exact hharm y (hV_subset_s hy) (hV_finite y hy)
  have hV_open : IsOpen V := by
    rw [isOpen_iff_mem_nhds]
    intro x hxV
    rcases hV_harmonicAtWithBot x hxV with ⟨t, ht_nhds, v, hv_harm, huv⟩
    have hx_ball : x ∈ ball c R := hxV.1
    have hx_t : x ∈ t := mem_of_mem_nhds ht_nhds
    have hx_eq : u x = (v x : WithBot ℝ) := huv x hx_t
    have hx_lt : h x + ε < v x := by
      exact WithBot.coe_lt_coe.mp (by simpa [hx_eq] using hxV.2)
    have ht_contAt : ContinuousAt v x :=
      (hv_harm.continuousOn x hx_t).continuousAt ht_nhds
    have hclosedBall_mem : closedBall c R ∈ 𝓝 x :=
      mem_of_superset (isOpen_ball.mem_nhds hx_ball) ball_subset_closedBall
    have hh_contAt : ContinuousAt h x :=
      (hcont x (ball_subset_closedBall hx_ball)).continuousAt hclosedBall_mem
    have hdiff_contAt : ContinuousAt (fun y => h y + ε - v y) x :=
      (hh_contAt.add continuousAt_const).sub ht_contAt
    have hdiff_lt : h x + ε - v x < 0 := by linarith
    have hlt_eventually : ∀ᶠ y in 𝓝 x, h y + ε < v y := by
      filter_upwards [hdiff_contAt (Iio_mem_nhds hdiff_lt)] with y hy
      have hy' : h y + ε - v y < 0 := by simpa using hy
      linarith
    filter_upwards [isOpen_ball.mem_nhds hx_ball, ht_nhds, hlt_eventually] with y hy_ball hy_t hy_lt
    constructor
    · exact hy_ball
    · have hy_eq : u y = (v y : WithBot ℝ) := huv y hy_t
      rw [hy_eq]
      exact WithBot.coe_lt_coe.mpr hy_lt
  have hclosureV_subset_closedBall : closure V ⊆ closedBall c R :=
    closure_minimal hV_subset_closedBall isClosed_closedBall
  have hclosureV_lower :
      ∀ z ∈ closure V, ((h z + ε / 2 : ℝ) : WithBot ℝ) ≤ u z := by
    intro z hz_closure
    have hz_closedBall : z ∈ closedBall c R := hclosureV_subset_closedBall hz_closure
    have hz_s : z ∈ s := hclosed hz_closedBall
    have hh_eventually_closedBall :
        ∀ᶠ y in 𝓝[closedBall c R] z, h z - ε / 2 < h y :=
      (hcont z hz_closedBall) (Ioi_mem_nhds (by linarith))
    have hh_eventually :
        ∀ᶠ y in 𝓝 z, y ∈ closedBall c R → h z - ε / 2 < h y := by
      simpa [eventually_nhdsWithin_iff] using hh_eventually_closedBall
    have hfreqV : ∃ᶠ y in 𝓝 z, y ∈ V :=
      mem_closure_iff_frequently.mp hz_closure
    have hfreq_lower_nhds :
        ∃ᶠ y in 𝓝 z, ((h z + ε / 2 : ℝ) : WithBot ℝ) ≤ u y ∧ y ∈ s := by
      exact (hfreqV.and_eventually hh_eventually).mono fun y hy => by
        rcases hy with ⟨hyV, hyh⟩
        have hy_closedBall : y ∈ closedBall c R := hV_subset_closedBall hyV
        have hreal : h z + ε / 2 < h y + ε := by
          have hyh' : h z - ε / 2 < h y := hyh hy_closedBall
          linarith
        have hle₁ : ((h z + ε / 2 : ℝ) : WithBot ℝ) ≤
            ((h y + ε : ℝ) : WithBot ℝ) :=
          WithBot.coe_le_coe.mpr hreal.le
        exact ⟨hle₁.trans (le_of_lt hyV.2), hV_subset_s hyV⟩
    have hfreq_lower :
        ∃ᶠ y in 𝓝[s] z, ((h z + ε / 2 : ℝ) : WithBot ℝ) ≤ u y := by
      rw [frequently_nhdsWithin_iff]
      exact hfreq_lower_nhds
    exact husc.frequently z hz_s ((h z + ε / 2 : ℝ) : WithBot ℝ) hfreq_lower
  have hclosureV_finite : ∀ z ∈ closure V, u z ≠ ⊥ := by
    intro z hz_closure hz_bot
    have hz_lower := hclosureV_lower z hz_closure
    simp [hz_bot] at hz_lower
  have hclosureV_disjoint_sphere : Disjoint (closure V) (sphere c R) := by
    rw [Set.disjoint_left]
    intro z hz_closure hz_sphere
    have hz_bd : u z ≤ (h z : WithBot ℝ) := hbd z hz_sphere
    have hreal_le : h z + ε / 2 ≤ h z :=
      WithBot.coe_le_coe.mp ((hclosureV_lower z hz_closure).trans hz_bd)
    linarith
  have hclosureV_subset_ball : closure V ⊆ ball c R := by
    intro y hy
    have hy_closed : y ∈ closedBall c R := hclosureV_subset_closedBall hy
    have hy_not_sphere : y ∉ sphere c R := by
      intro hy_sphere
      exact (Set.disjoint_left.mp hclosureV_disjoint_sphere hy) hy_sphere
    rw [mem_ball]
    rw [mem_closedBall] at hy_closed
    exact lt_of_le_of_ne hy_closed fun hy_eq =>
      hy_not_sphere (by simpa [mem_sphere, dist_eq_norm] using hy_eq)
  rcases hV_nonempty with ⟨p, hpV⟩
  let W : Set E := connectedComponentIn V p
  have hpW : p ∈ W := mem_connectedComponentIn hpV
  have hW_nonempty : W.Nonempty := ⟨p, hpW⟩
  have hW_subset_V : W ⊆ V := connectedComponentIn_subset V p
  have hW_subset_ball : W ⊆ ball c R := hW_subset_V.trans hV_subset_ball
  have hW_subset_s : W ⊆ s := hW_subset_V.trans hV_subset_s
  have hW_preconnected : IsPreconnected W := isPreconnected_connectedComponentIn
  have hW_open : IsOpen W := hV_open.connectedComponentIn
  let U : E → ℝ := fun y => if hy : u y = ⊥ then 0 else (u y).unbot hy
  have hU_eq : ∀ y ∈ W, u y = (U y : WithBot ℝ) := by
    intro y hyW
    have hyV : y ∈ V := hW_subset_V hyW
    have hy_finite : u y ≠ ⊥ := hV_finite y hyV
    simp [U, hy_finite]
  have hU_harm : InnerProductSpace.HarmonicOnNhd U W := by
    intro x hxW
    have hxV : x ∈ V := hW_subset_V hxW
    rcases hV_harmonicAtWithBot x hxV with ⟨t, ht_nhds, v, hv_harm, huv⟩
    have hx_t : x ∈ t := mem_of_mem_nhds ht_nhds
    have hUv_eventually : U =ᶠ[𝓝 x] v := by
      filter_upwards [ht_nhds] with y hy_t
      have huy : u y = (v y : WithBot ℝ) := huv y hy_t
      have hy_finite : u y ≠ ⊥ := by
        rw [huy]
        simp
      simp [U, huy]
    exact (InnerProductSpace.harmonicAt_congr_nhds hUv_eventually).mpr (hv_harm x hx_t)
  have hclosureW_subset_closureV : closure W ⊆ closure V :=
    closure_mono hW_subset_V
  have hclosureW_subset_closedBall : closure W ⊆ closedBall c R :=
    hclosureW_subset_closureV.trans hclosureV_subset_closedBall
  have hclosureW_subset_ball : closure W ⊆ ball c R :=
    hclosureW_subset_closureV.trans hclosureV_subset_ball
  have hclosureW_subset_s : closure W ⊆ s := fun z hz =>
    hclosed (hclosureW_subset_closedBall hz)
  have hU_eq_closureW : ∀ z ∈ closure W, u z = (U z : WithBot ℝ) := by
    intro z hzW
    have hzV : z ∈ closure V := hclosureW_subset_closureV hzW
    have hz_finite : u z ≠ ⊥ := hclosureV_finite z hzV
    simp [U, hz_finite]
  have hU_cont_closureW : ContinuousOn U (closure W) := by
    intro z hzW
    have hzV : z ∈ closure V := hclosureW_subset_closureV hzW
    have hz_finite : u z ≠ ⊥ := hclosureV_finite z hzV
    rcases hharm z (hclosureW_subset_s hzW) hz_finite with ⟨t, ht_nhds, v, hv_harm, huv⟩
    have hz_t : z ∈ t := mem_of_mem_nhds ht_nhds
    have hUv_eventually : U =ᶠ[𝓝 z] v := by
      filter_upwards [ht_nhds] with y hy_t
      have huy : u y = (v y : WithBot ℝ) := huv y hy_t
      have hy_finite : u y ≠ ⊥ := by
        rw [huy]
        simp
      simp [U, huy]
    have hv_contAt : ContinuousAt v z :=
      (hv_harm.continuousOn z hz_t).continuousAt ht_nhds
    exact (hv_contAt.congr_of_eventuallyEq hUv_eventually).continuousWithinAt
  have hclosureW_inter_V_subset_W : closure W ∩ V ⊆ W := by
    intro z hz
    rcases hz with ⟨hz_closureW, hzV⟩
    let C : Set E := connectedComponentIn V z
    have hzC : z ∈ C := mem_connectedComponentIn hzV
    have hC_open : IsOpen C := hV_open.connectedComponentIn
    have hfreqW : ∃ᶠ y in 𝓝 z, y ∈ W :=
      mem_closure_iff_frequently.mp hz_closureW
    have hfreqWC : ∃ᶠ y in 𝓝 z, y ∈ W ∧ y ∈ C :=
      hfreqW.and_eventually (hC_open.mem_nhds hzC)
    rcases hfreqWC.exists with ⟨y, hyW, hyC⟩
    have hW_eq_C : W = C := by
      dsimp [W, C]
      exact (connectedComponentIn_eq hyW).trans (connectedComponentIn_eq hyC).symm
    simpa [hW_eq_C] using hzC
  have hfrontierW_disjoint_V : Disjoint (frontier W) V := by
    rw [Set.disjoint_left]
    intro z hz_frontier hzV
    have hzW : z ∈ W :=
      hclosureW_inter_V_subset_W ⟨frontier_subset_closure hz_frontier, hzV⟩
    have hz_notW : z ∉ W := by
      rw [hW_open.frontier_eq] at hz_frontier
      exact hz_frontier.2
    exact hz_notW hzW
  let H : E → ℝ := fun y => h y + ε
  have hfrontier_le : ∀ z ∈ frontier W, U z ≤ H z := by
    intro z hz_frontier
    have hz_closureW : z ∈ closure W := frontier_subset_closure hz_frontier
    have hz_ball : z ∈ ball c R := hclosureW_subset_ball hz_closureW
    have hz_notV : z ∉ V := by
      intro hzV
      exact (Set.disjoint_left.mp hfrontierW_disjoint_V hz_frontier) hzV
    have hnot_lt : ¬ ((h z + ε : ℝ) : WithBot ℝ) < u z := by
      intro hlt
      exact hz_notV ⟨hz_ball, hlt⟩
    have hu_le : u z ≤ ((h z + ε : ℝ) : WithBot ℝ) := not_lt.mp hnot_lt
    have hUz_le : (U z : WithBot ℝ) ≤ ((h z + ε : ℝ) : WithBot ℝ) := by
      simpa [hU_eq_closureW z hz_closureW] using hu_le
    exact WithBot.coe_le_coe.mp (by simpa [H] using hUz_le)
  have hW_bdd : Bornology.IsBounded W := isBounded_ball.subset hW_subset_ball
  have hH_harm : InnerProductSpace.HarmonicOnNhd H W := by
    simpa [H, Pi.add_apply] using
      (hharm_on_ball.mono hW_subset_ball).add
        (InnerProductSpace.harmonicOnNhd_const (E := E) (s := W) ε)
  have hH_cont_closureW : ContinuousOn H (closure W) := by
    simpa [H, Pi.add_apply] using
      (hcont.mono hclosureW_subset_closedBall).add continuousOn_const
  have hcomp : U p ≤ H p :=
    harmonic_comparison_principle_on_domain
      (s := W) (u := U) (v := H)
      hW_open hW_preconnected hW_nonempty hW_bdd
      hU_harm hH_harm hU_cont_closureW hH_cont_closureW
      hfrontier_le p hpW
  have hp_lt : H p < U p := by
    have hp_eq : u p = (U p : WithBot ℝ) := hU_eq p hpW
    have hp_withBot : ((H p : ℝ) : WithBot ℝ) < (U p : WithBot ℝ) := by
      rw [← hp_eq]
      simpa [H] using hpV.2
    exact WithBot.coe_lt_coe.mp hp_withBot
  linarith


/-- An upper semicontinuous `WithBot ℝ`-valued function which is locally harmonic at every finite
point is subharmonic. -/
theorem subharmonicOn_of_upperSemicontinuousOn_of_harmonicAtWithBot
    [Nontrivial E]
    {u : E → WithBot ℝ} {s : Set E} (husc : UpperSemicontinuousOn u s)
    (hharm : ∀ z ∈ s, u z ≠ ⊥ → HarmonicAtWithBot u z) : SubharmonicOn u s := by
  constructor
  · exact husc
  · intro c R h hclosed hcont hharm_on_ball hbd w hw
    have hno_superlevel :
        ∀ ε > 0, {y ∈ ball c R | ((h y + ε : ℝ) : WithBot ℝ) < u y} = ∅ :=
      no_positive_superlevel_of_usc_locally_harmonic_withBot
        husc hharm hclosed hcont hharm_on_ball hbd
    by_contra hle
    have hlt : (h w : WithBot ℝ) < u w := not_le.mp hle
    cases huw : u w with
    | bot =>
        simp [huw] at hlt
    | coe a =>
        have hlt_real : h w < a := WithBot.coe_lt_coe.mp (by simpa [huw] using hlt)
        let ε : ℝ := (a - h w) / 2
        have hε : 0 < ε := by dsimp [ε]; linarith
        have hsuper : ((h w + ε : ℝ) : WithBot ℝ) < u w := by
          rw [huw]
          apply WithBot.coe_lt_coe.mpr
          dsimp [ε]; linarith
        have hw_super : w ∈ {y ∈ ball c R | ((h y + ε : ℝ) : WithBot ℝ) < u y} :=
          ⟨hw, hsuper⟩
        rw [hno_superlevel ε hε] at hw_super
        exact hw_super



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

/-- Weighted Jensen inequality for the exponential on a circle.  If `P` is a nonnegative
probability density with respect to `circleAverage`, then applying `exp` after the weighted
average is bounded by the weighted average after applying `exp`. -/
lemma exp_weighted_circleAverage_le_circleAverage_weighted_exp
    {c : ℂ} {R : ℝ} {P ψ : ℂ → ℝ}
    (hR_nonneg : 0 ≤ R)
    (hP_nonneg : ∀ z ∈ sphere c R, 0 ≤ P z)
    (hP_avg : circleAverage P c R = 1)
    (hP_cont : ContinuousOn P (sphere c R))
    (hψ_cont : ContinuousOn ψ (sphere c R)) :
    exp (circleAverage (fun z : ℂ => P z * ψ z) c R)
      ≤ circleAverage (fun z : ℂ => P z * exp (ψ z)) c R := by
  let A : ℝ := circleAverage (fun z : ℂ => P z * ψ z) c R
  have hP_int : CircleIntegrable P c R := hP_cont.circleIntegrable hR_nonneg
  have hψ_int : CircleIntegrable ψ c R := hψ_cont.circleIntegrable hR_nonneg
  have hPψ_int : CircleIntegrable (fun z : ℂ => P z * ψ z) c R :=
    (hP_cont.mul hψ_cont).circleIntegrable hR_nonneg
  have hleft_int :
      CircleIntegrable (fun z : ℂ => P z * (exp A * (ψ z - A + 1))) c R := by
    have hinner : CircleIntegrable (fun z : ℂ => ψ z - A + 1) c R := by
      simpa [sub_eq_add_neg, add_assoc] using
        (hψ_int.add (circleIntegrable_const (-A) c R)).add (circleIntegrable_const 1 c R)
    exact (hP_cont.mul
      (continuousOn_const.mul ((hψ_cont.sub continuousOn_const).add continuousOn_const))).circleIntegrable
        hR_nonneg
  have hright_int : CircleIntegrable (fun z : ℂ => P z * exp (ψ z)) c R := by
    have hexpψ_cont : ContinuousOn (fun z : ℂ => exp (ψ z)) (sphere c R) := by
      fun_prop
    exact (hP_cont.mul hexpψ_cont).circleIntegrable hR_nonneg
  have hmono :
      circleAverage (fun z : ℂ => P z * (exp A * (ψ z - A + 1))) c R ≤
        circleAverage (fun z : ℂ => P z * exp (ψ z)) c R := by
    refine circleAverage_mono hleft_int hright_int ?_
    intro z hz_abs
    have hz : z ∈ sphere c R := by simpa [abs_of_nonneg hR_nonneg] using hz_abs
    have htangent : exp A * (ψ z - A + 1) ≤ exp (ψ z) := by
      have hbase : ψ z - A + 1 ≤ exp (ψ z - A) := by
        simpa [add_comm] using Real.add_one_le_exp (ψ z - A)
      calc
        exp A * (ψ z - A + 1) ≤ exp A * exp (ψ z - A) :=
          mul_le_mul_of_nonneg_left hbase (exp_nonneg A)
        _ = exp (ψ z) := by
          rw [← exp_add]
          ring_nf
    exact mul_le_mul_of_nonneg_left htangent (hP_nonneg z hz)
  have hleft_eq :
      circleAverage (fun z : ℂ => P z * (exp A * (ψ z - A + 1))) c R = exp A := by
    have hAP_int : CircleIntegrable (fun z : ℂ => A * P z) c R := by
      simpa [smul_eq_mul] using (CircleIntegrable.const_fun_smul (a := A) hP_int)
    have hdiff_int : CircleIntegrable (fun z : ℂ => P z * ψ z - A * P z) c R :=
      hPψ_int.sub hAP_int
    have hsum_int : CircleIntegrable (fun z : ℂ => P z * ψ z - A * P z + P z) c R :=
      hdiff_int.add hP_int
    have hAP_avg : circleAverage (fun z : ℂ => A * P z) c R = A * circleAverage P c R := by
      simpa [smul_eq_mul] using
        (circleAverage_fun_smul (a := A) (f := P) (c := c) (R := R))
    calc
      circleAverage (fun z : ℂ => P z * (exp A * (ψ z - A + 1))) c R
          = exp A *
              circleAverage (fun z : ℂ => P z * ψ z - A * P z + P z) c R := by
            change circleAverage (fun z : ℂ => P z * (exp A * (ψ z - A + 1))) c R =
              (exp A) • circleAverage (fun z : ℂ => P z * ψ z - A * P z + P z) c R
            rw [← circleAverage_fun_smul
              (a := exp A) (f := fun z : ℂ => P z * ψ z - A * P z + P z)
              (c := c) (R := R)]
            apply circleAverage_congr_sphere
            intro z _hz
            simp [smul_eq_mul]
            ring
      _ = exp A * ((circleAverage (fun z : ℂ => P z * ψ z) c R -
              circleAverage (fun z : ℂ => A * P z) c R) + circleAverage P c R) := by
            rw [circleAverage_fun_add hdiff_int hP_int]
            rw [circleAverage_fun_sub hPψ_int hAP_int]
      _ = exp A * ((A - A * 1) + 1) := by
            rw [hAP_avg, hP_avg]
      _ = exp A := by ring
  calc
    exp (circleAverage (fun z : ℂ => P z * ψ z) c R)
        = exp A := by rfl
    _ = circleAverage (fun z : ℂ => P z * (exp A * (ψ z - A + 1))) c R := hleft_eq.symm
    _ ≤ circleAverage (fun z : ℂ => P z * exp (ψ z)) c R := hmono

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
    have hpo : circleAverage (fun z : ℂ => poissonKernel c w z * 1) c R = 1 :=
      InnerProductSpace.HarmonicOnNhd.circleAverage_poissonKernel_smul
        (f := fun _ : ℂ => (1 : ℝ)) (by simp) hw
    simpa [P] using hpo
  have hJensen := exp_weighted_circleAverage_le_circleAverage_weighted_exp
      hR_nonneg hP_nonneg hP_avg hP_cont hψ_cont
  have hH_contcl := InnerProductSpace.HarmonicContOnCl.mk_ball hharm hcont
  have hP_H_avg : circleAverage (fun z : ℂ => P z * h z) c R = h w := by
    simpa [P, Pi.smul_apply, smul_eq_mul] using
      InnerProductSpace.HarmonicContOnCl.circleAverage_poissonKernel_smul hH_contcl hw
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
      rw [hH_poisson w hw]
      refine exp_poisson_log_le_harmonic ?_ ?_ ?_ hw
      . fun_prop
      . simpa [Pi.add_apply] using hharm.add (InnerProductSpace.harmonicOnNhd_const ε)
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
  let t : Set ℂ := {y | InnerProductSpace.HarmonicAt v y ∧ f y ≠ 0}
  have ht_nhds : t ∈ 𝓝 z := by
    have hne_nhds : {y | f y ≠ 0} ∈ 𝓝 z :=
      hfz_an.continuousAt.eventually_ne hfz_ne
    exact Filter.inter_mem hvz.eventually hne_nhds
  refine ⟨t, ht_nhds, v, ?_, ?_⟩
  · intro y hy
    exact hy.1
  · intro y hy
    simp [logNormBot, v, hy.2]


lemma logNormBot_apply_le_of_norm_le_one [DecidableEq F] (ℓ : StrongDual ℂ F)
    (hℓ : ‖ℓ‖ ≤ 1) (z : F) : logNormBot (ℓ z) ≤ logNormBot z := by
  by_cases hℓz : ℓ z = 0
  · simp [logNormBot, hℓz]
  · have hz : z ≠ 0 := by
      intro hz
      exact hℓz (by simp [hz])
    have hnorm_le : ‖ℓ z‖ ≤ ‖z‖ := by
      calc
        ‖ℓ z‖ ≤ ‖ℓ‖ * ‖z‖ := ℓ.le_opNorm z
        _ ≤ 1 * ‖z‖ := by gcongr
        _ = ‖z‖ := one_mul _
    have hlog_le : log ‖ℓ z‖ ≤ log ‖z‖ :=
      Real.log_le_log (norm_pos_iff.mpr hℓz) hnorm_le
    simpa [logNormBot, hℓz, hz] using WithBot.coe_le_coe.mpr hlog_le

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
        exact (logNormBot_apply_le_of_norm_le_one ℓ hℓ_norm (f z)).trans (hbd z hz)
      have hle_g : (logNormBot.comp g) w ≤ h w :=
        hg_sub.2 c R h hclosed hcont hharm hbd_g w hw
      have hg_eq : (logNormBot.comp g) w = (logNormBot.comp f) w := by
        have hℓfw_ne : ℓ (f w) ≠ 0 := by
          rw [hℓw]
          exact Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hfw)
        simp [Function.comp_def, g, logNormBot, hfw, hℓw]
      change (logNormBot.comp f) w ≤ (h w : WithBot ℝ)
      rw [← hg_eq]
      exact hle_g

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
