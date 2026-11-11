import HardySpaceFormalization.HardySpaceBoundary
import HardySpaceFormalization.HarmonicMajorant

/-!
# Logarithmic integrability of boundary values (Garnett II.4.1–4.2)

For `f ∈ H^∞` not identically zero, `∫ log |f*| dθ/2π > -∞` with the convention `log 0 = -∞`,
encoded by `logNormBot` and the `WithBot ℝ` integral. Consequently the boundary function of a
nonzero `H^∞` function cannot vanish on a set of positive measure (II.4.2). Garnett's Poisson
inequality (4.2) is not needed in this project and is not formalized.

Garnett states II.4.1 for `0 < p ≤ ∞`; only `p = ∞` is treated here, which is the case used for
II.5.3. The case `p < ∞` additionally needs the integrable maximal function of II.3.1.
-/

noncomputable section

open MeasureTheory Metric Complex
open scoped ENNReal PoissonIntegral Topology

namespace HardySpace


/-- `w ↦ log M - log |w|`, valued in `ℝ≥0∞` and extended by `∞` at `w = 0`, is continuous. -/
lemma continuous_ofReal_log_sub_log_norm (M : ℝ) :
    Continuous fun w : ℂ => if w = 0 then ∞ else ENNReal.ofReal (Real.log M - Real.log ‖w‖) := by
  refine continuous_iff_continuousAt.mpr fun w₀ => ?_
  by_cases hw₀ : w₀ = 0
  · subst hw₀
    simp only [ContinuousAt, ↓reduceIte]
    refine ENNReal.tendsto_nhds_top_iff_nat.mpr fun n => ?_
    filter_upwards [ball_mem_nhds (0 : ℂ) (Real.exp_pos (Real.log M - (n + 1)))] with w hw
    by_cases hw0 : w = 0
    · simp [hw0]
    simp only [hw0, ↓reduceIte, ← ENNReal.ofReal_natCast]
    rw [mem_ball_zero_iff] at hw
    have hlog : Real.log ‖w‖ < Real.log M - (n + 1) :=
      (Real.log_lt_iff_lt_exp (norm_pos_iff.mpr hw0)).mpr hw
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
  · have hev : (fun w : ℂ => if w = 0 then ∞ else ENNReal.ofReal (Real.log M - Real.log ‖w‖)) =ᶠ[𝓝 w₀]
        fun w => ENNReal.ofReal (Real.log M - Real.log ‖w‖) :=
      Filter.eventually_of_mem (isOpen_ne.mem_nhds hw₀) fun w (hw : w ≠ 0) => by simp [hw]
    refine ContinuousAt.congr ?_ hev.symm
    exact ENNReal.continuous_ofReal.continuousAt.comp (continuousAt_const.sub
      ((Real.continuousAt_log (norm_ne_zero_iff.mpr hw₀)).comp continuous_norm.continuousAt))

/-- Radial approach to a point of the unit circle is nontangential. -/
lemma tendsto_ofReal_mul_nontangentially {ζ : ℂ} (hζ : ‖ζ‖ = 1) {ι : Type*} {l : Filter ι}
    {r : ι → ℝ} (hr : Filter.Tendsto r l (𝓝 1)) (hr₀ : ∀ i, 0 ≤ r i) (hr₁ : ∀ i, r i < 1) :
    Filter.Tendsto (fun i => (r i : ℂ) * ζ) l (nontangentially ζ) := by
  have h2 : Filter.Tendsto (fun i => (r i : ℂ) * ζ) l (𝓝[stolzSetAt ζ 2] ζ) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Filter.Eventually.of_forall fun i =>
      radial_mem_stolzSetAt hζ (by norm_num) (hr₀ i) (hr₁ i)⟩
    simpa using ((Complex.continuous_ofReal.tendsto 1).comp hr).mul_const ζ
  refine h2.mono_right ?_
  unfold nontangentially
  exact le_iSup₂ (f := fun α (_ : α ∈ Set.Ioi (1 : ℝ)) => 𝓝[stolzSetAt ζ α] ζ) 2 (by norm_num)

/-- **Garnett II.4.1 (`p = ∞`).** If `f ∈ H^∞` is not identically zero, then
`∫ log |f*| dθ/2π > -∞`, where `log 0 = -∞`. -/
theorem MemHpDisc.withBotIntegral_logNormBot_boundaryValue_ne_bot {f : ℂ → ℂ}
    (hf : MemHpDisc ∞ f) (hf_ne : ∃ z ∈ unitDisc, f z ≠ 0) :
    ∫ᴮ ζ, logNormBot (boundaryValue f ζ) ∂circleMeasure 0 1 ≠ ⊥ := by
  -- Follows Garnett's subharmonic argument, with I.6.5 at a fixed radius in place of I.6.7: since
  -- the hypothesis provides `z₀` with `f(z₀) ≠ 0`, no zero at the origin has to be removed.
  obtain ⟨han, ⟨M₀, hM₀⟩, -⟩ := memHpDisc_top_iff.mp hf
  have hfa : AnalyticOnNhd ℂ f (ball 0 1) := isOpen_ball.analyticOn_iff_analyticOnNhd.mp han
  set M : ℝ := max M₀ 1
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg (le_max_right _ _)
  have hfM : ∀ z ∈ ball (0 : ℂ) 1, ‖f z‖ ≤ M := fun z hz => (hM₀ z hz).trans (le_max_left _ _)
  obtain ⟨z₀, hz₀, hfz₀⟩ := hf_ne
  -- `h = log M - log |f| ≥ 0`, valued in `ℝ≥0∞` with `h = ∞` at the zeros of `f`.
  set H : ℂ → ℝ≥0∞ := fun w => if w = 0 then ∞ else ENNReal.ofReal (Real.log M - Real.log ‖w‖)
  have hHc : Continuous H := continuous_ofReal_log_sub_log_norm M
  -- For `r₀ ≤ r < 1`, the Poisson kernel `P_{z₀/r}` lies in `[c, 1/c]` on the unit circle.
  set r₀ : ℝ := (1 + ‖z₀‖) / 2
  have hz₀r₀ : ‖z₀‖ < r₀ := by have := mem_ball_zero_iff.mp hz₀; simp only [r₀]; linarith
  have hr₀1 : r₀ < 1 := by have := mem_ball_zero_iff.mp hz₀; simp only [r₀]; linarith
  have hr₀pos : 0 < r₀ := (norm_nonneg z₀).trans_lt hz₀r₀
  set t : ℝ := ‖z₀‖ / r₀
  have ht0 : 0 ≤ t := div_nonneg (norm_nonneg _) hr₀pos.le
  have ht1 : t < 1 := (div_lt_one hr₀pos).mpr hz₀r₀
  set c : ℝ := (1 - t) / (1 + t)
  have hc : 0 < c := div_pos (by linarith) (by linarith)
  have hP : ∀ r ∈ Set.Ico r₀ 1, ∀ θ : ℝ, c ≤ poissonKernel 0 (z₀ / r) (exp (I * θ)) ∧
      poissonKernel 0 (z₀ / r) (exp (I * θ)) ≤ 1 / c := by
    intro r hr θ
    have hrpos : 0 < r := hr₀pos.trans_le hr.1
    have hs : ‖z₀ / (r : ℂ)‖ = ‖z₀‖ / r := by
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hrpos.le]
    have hst : ‖z₀ / (r : ℂ)‖ ≤ t := by
      rw [hs]; exact div_le_div_of_nonneg_left (norm_nonneg _) hr₀pos hr.1
    have hs0 := norm_nonneg (z₀ / (r : ℂ))
    have hw : z₀ / (r : ℂ) ∈ ball (0 : ℂ) 1 := by rw [mem_ball_zero_iff]; linarith
    have hζ : exp (I * θ) ∈ sphere (0 : ℂ) 1 := by
      rw [mem_sphere_zero_iff_norm]; exact Complex.norm_exp_I_mul_ofReal θ
    have hlo := le_poissonKernel_of_mem_ball hw hζ
    have hhi := poissonKernel_le_of_mem_ball hw hζ
    simp only [sub_zero] at hlo hhi
    constructor
    · refine le_trans ?_ hlo
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith
    · refine hhi.trans ?_
      rw [one_div_div, div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith
  -- Theorem I.6.5 at a fixed radius bounds `∫ h(r·)` uniformly in `r₀ ≤ r < 1`.
  set C : ℝ := (Real.log M / c - Real.log ‖f z₀‖) / c
  have hbound : ∀ r ∈ Set.Ico r₀ 1,
      ∫⁻ θ, H (f (r * exp (I * θ))) ∂angularMeasure ≤ ENNReal.ofReal C := by
    intro r hr
    have hrpos : 0 < r := hr₀pos.trans_le hr.1
    have hzr : ¬ r ≤ ‖z₀‖ := not_le.mpr (hz₀r₀.trans_le hr.1)
    have h65 := Subharmonic.le_poissonModification
      (logNormBot_comp_analytic_subharmonicOn_scalar isOpen_ball han)
      ⟨z₀, hz₀, by simp [logNormBot, hfz₀]⟩ ⟨hrpos, hr.2⟩ z₀ hz₀
    simp only [Subharmonic.poissonModification, hzr, ↓reduceIte, Function.comp_apply] at h65
    set F : ℝ → WithBot ℝ := fun θ =>
      (poissonKernel 0 (z₀ / r) (exp (I * θ)) : WithBot ℝ) * logNormBot (f (r * exp (I * θ)))
    -- The integral is `≥ log |f(z₀)| > ⊥`, so its integrand is a.e. finite and integrable.
    unfold withBotIntegral at h65
    split_ifs at h65 with hcond
    swap
    · simp [logNormBot, hfz₀] at h65
    obtain ⟨hnull, hint⟩ := hcond
    have hint' : Integrable (fun θ => (F θ).unbotD 0) angularMeasure := hint
    have hz₀le : Real.log ‖f z₀‖ ≤ ∫ θ, (F θ).unbotD 0 ∂angularMeasure := by
      simpa [logNormBot, hfz₀] using h65
    -- Pointwise, `h(r e^{iθ}) ≤ (log M / c - P_{z₀/r} log |f(r e^{iθ})|) / c`, using
    -- `c ≤ P_{z₀/r} ≤ 1/c` and `h ≥ 0`; the right side is nonnegative.
    have hpt : ∀ᵐ θ : ℝ ∂angularMeasure, H (f (r * exp (I * θ))) ≤
        ENNReal.ofReal ((Real.log M / c - (F θ).unbotD 0) / c) ∧
          0 ≤ (Real.log M / c - (F θ).unbotD 0) / c := by
      filter_upwards [(ae_iff (p := fun θ => F θ ≠ ⊥)).mpr (by simpa using hnull)] with θ hθ
      obtain ⟨hcP, hPc⟩ := hP r hr θ
      have hPpos : 0 < poissonKernel 0 (z₀ / r) (exp (I * θ)) := hc.trans_le hcP
      have hf0 : f (r * exp (I * θ)) ≠ 0 := by
        intro h0
        exact hθ ((const_mul_eq_bot_iff_of_pos hPpos _).mpr (by simp [logNormBot, h0]))
      have hmem : (r : ℂ) * exp (I * θ) ∈ ball (0 : ℂ) 1 := by
        rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_of_nonneg hrpos.le,
          Complex.norm_exp_I_mul_ofReal, mul_one]
        exact hr.2
      have ha : Real.log ‖f (r * exp (I * θ))‖ ≤ Real.log M :=
        Real.log_le_log (norm_pos_iff.mpr hf0) (hfM _ hmem)
      have hF : (F θ).unbotD 0 =
          poissonKernel 0 (z₀ / r) (exp (I * θ)) * Real.log ‖f (r * exp (I * θ))‖ := by
        simp only [F]
        rw [unbotD_const_mul_of_pos hPpos]
        simp [logNormBot, hf0]
      have hdiv : Real.log M / c = 1 / c * Real.log M := by ring
      rw [hF]
      refine ⟨?_, ?_⟩
      · simp only [H, hf0, ↓reduceIte]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [le_div_iff₀ hc, hdiv]
        nlinarith [mul_le_mul_of_nonneg_right hcP (sub_nonneg.mpr ha),
          mul_le_mul_of_nonneg_right hPc hlogM]
      · refine div_nonneg ?_ hc.le
        rw [hdiv]
        nlinarith [mul_le_mul_of_nonneg_right hPc hlogM, mul_le_mul_of_nonneg_left ha hPpos.le]
    have hgint : Integrable (fun θ => (Real.log M / c - (F θ).unbotD 0) / c) angularMeasure :=
      ((integrable_const _).sub hint').div_const c
    calc ∫⁻ θ, H (f (r * exp (I * θ))) ∂angularMeasure
        ≤ ∫⁻ θ, ENNReal.ofReal ((Real.log M / c - (F θ).unbotD 0) / c) ∂angularMeasure :=
          lintegral_mono_ae (hpt.mono fun θ h => h.1)
      _ = ENNReal.ofReal (∫ θ, (Real.log M / c - (F θ).unbotD 0) / c ∂angularMeasure) :=
          (ofReal_integral_eq_lintegral_ofReal hgint (hpt.mono fun θ h => h.2)).symm
      _ ≤ ENNReal.ofReal C := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [integral_div, integral_sub (integrable_const _) hint', integral_const]
          simp only [probReal_univ, smul_eq_mul, one_mul]
          exact div_le_div_of_nonneg_right (by linarith) hc.le
  -- Radii `rₙ = 1 - (1 - r₀)/2ⁿ ↑ 1`, along which `f` converges radially almost everywhere.
  set rs : ℕ → ℝ := fun n => 1 - (1 - r₀) * (1 / 2) ^ n
  have hrs : ∀ n, rs n ∈ Set.Ico r₀ 1 := fun n => by
    have h1 : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have h2 : 0 < (1 / 2 : ℝ) ^ n := by positivity
    constructor <;> simp only [rs] <;> nlinarith
  have hrs_lim : Filter.Tendsto rs Filter.atTop (𝓝 1) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul (1 - r₀)
    simpa [rs] using (tendsto_const_nhds (x := (1 : ℝ))).sub this
  have hrad : ∀ᵐ θ : ℝ ∂angularMeasure, Filter.Tendsto (fun n => f (rs n * exp (I * θ)))
      Filter.atTop (𝓝 (boundaryValue f (exp (I * θ)))) := by
    have h := ae_of_ae_map (μ := angularMeasure) (measurable_circleMap 0 1).aemeasurable
      hf.ae_nontangentiallyConvergentAt
    filter_upwards [h] with θ hθ
    have hcm : circleMap 0 1 θ = exp (I * θ) := by simp [circleMap, mul_comm]
    rw [hcm] at hθ
    exact hθ.hasNontangentialLimit.comp (tendsto_ofReal_mul_nontangentially
      (Complex.norm_exp_I_mul_ofReal θ) hrs_lim (fun n => (hr₀pos.trans_le (hrs n).1).le)
      fun n => (hrs n).2)
  -- Fatou's lemma: `∫ h(f*) ≤ liminf ∫ h(f(rₙ·)) ≤ C`.
  have hlim_lint : ∫⁻ θ, H (boundaryValue f (exp (I * θ))) ∂angularMeasure ≤ ENNReal.ofReal C := by
    have hmeas : ∀ n, Measurable fun θ : ℝ => H (f (rs n * exp (I * θ))) := fun n => by
      refine hHc.measurable.comp (Continuous.measurable ?_)
      refine hfa.continuousOn.comp_continuous (by fun_prop) fun θ => ?_
      rw [mem_ball_zero_iff, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (hr₀pos.trans_le (hrs n).1).le, Complex.norm_exp_I_mul_ofReal, mul_one]
      exact (hrs n).2
    calc ∫⁻ θ, H (boundaryValue f (exp (I * θ))) ∂angularMeasure
        = ∫⁻ θ, Filter.liminf (fun n => H (f (rs n * exp (I * θ)))) Filter.atTop
            ∂angularMeasure :=
          lintegral_congr_ae (hrad.mono fun θ hθ => ((hHc.tendsto _).comp hθ).liminf_eq.symm)
      _ ≤ Filter.liminf (fun n => ∫⁻ θ, H (f (rs n * exp (I * θ))) ∂angularMeasure)
            Filter.atTop := lintegral_liminf_le hmeas
      _ ≤ ENNReal.ofReal C := Filter.liminf_le_of_frequently_le'
          (Filter.Eventually.frequently (Filter.Eventually.of_forall fun n => hbound _ (hrs n)))
  -- Back on the circle: `∫ h(f*) dσ < ∞`.
  have hσ : AEMeasurable (boundaryValue f) (circleMeasure 0 1) :=
    (hfa.memLp_boundaryValue_of_bounded hfM).aestronglyMeasurable.aemeasurable
  have hHσ : AEMeasurable (fun ζ => H (boundaryValue f ζ)) (circleMeasure 0 1) :=
    hHc.measurable.comp_aemeasurable hσ
  have hfin : ∫⁻ ζ, H (boundaryValue f ζ) ∂circleMeasure 0 1 ≠ ∞ := by
    rw [lintegral_circleMeasure_eq_lintegral_angularMeasure hHσ]
    have hcm : ∀ θ : ℝ, circleMap 0 1 θ = exp (I * θ) := fun θ => by simp [circleMap, mul_comm]
    simp only [hcm]
    exact (hlim_lint.trans_lt ENNReal.ofReal_lt_top).ne
  -- Hence `f* ≠ 0` a.e. and `log |f*| = log M - h(f*)` is integrable.
  have hne : ∀ᵐ ζ ∂circleMeasure 0 1, boundaryValue f ζ ≠ 0 := by
    filter_upwards [ae_lt_top' hHσ hfin] with ζ hζ h0
    simp [H, h0] at hζ
  have hle : ∀ᵐ ζ ∂circleMeasure 0 1, ‖boundaryValue f ζ‖ ≤ M := by
    filter_upwards [hf.ae_nontangentiallyConvergentAt, ae_nontangentially_neBot_circleMeasure]
      with ζ hζ hζne
    exact le_of_tendsto hζ.hasNontangentialLimit.norm
      ((eventually_mem_ball_nontangentially ζ).mono fun z hz => hfM z hz)
  have hlog : Integrable (fun ζ => Real.log ‖boundaryValue f ζ‖) (circleMeasure 0 1) := by
    refine ((integrable_const (Real.log M)).sub
      (integrable_toReal_of_lintegral_ne_top hHσ hfin)).congr ?_
    filter_upwards [hne, hle] with ζ h0 hM
    simp only [Pi.sub_apply, H, h0, ↓reduceIte]
    rw [ENNReal.toReal_ofReal (sub_nonneg.mpr (Real.log_le_log (norm_pos_iff.mpr h0) hM))]
    ring
  unfold withBotIntegral
  split_ifs with hcond
  · exact WithBot.coe_ne_bot
  · refine absurd ⟨?_, ?_⟩ hcond
    · refine measure_mono_null (fun ζ hζ => ?_) (ae_iff.mp hne)
      intro h0
      simp [logNormBot, h0] at hζ
    · refine hlog.congr (Filter.Eventually.of_forall fun ζ => ?_)
      by_cases h0 : boundaryValue f ζ = 0 <;> simp [logNormBot, h0]

/-- **Garnett II.4.2 (`p = ∞`).** If `f ∈ H^∞` and its boundary function vanishes on a set of
positive measure, then `f ≡ 0`. -/
theorem MemHpDisc.eq_zero_of_frequently_boundaryValue_eq_zero {f : ℂ → ℂ}
    (hf : MemHpDisc ∞ f) (hzero : ∃ᵐ ζ ∂circleMeasure 0 1, boundaryValue f ζ = 0) :
    f = 0 := by
  by_contra hne
  -- `f` vanishes off the disc, so `f ≢ 0` means `f` has a nonzero value in the disc.
  have hf_ne : ∃ z ∈ unitDisc, f z ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (funext fun z => by by_cases hz : z ∈ unitDisc; exacts [h z hz, hf.2.2 z hz])
  -- By II.4.1, `∫ log |f*| > -∞`, so the set where `log |f*| = -∞`, i.e. `f* = 0`, is null.
  have hint := hf.withBotIntegral_logNormBot_boundaryValue_ne_bot hf_ne
  have hnull : circleMeasure 0 1 {ζ | logNormBot (boundaryValue f ζ) = ⊥} = 0 := by
    by_contra h
    exact hint (by simp [withBotIntegral, h])
  refine hzero (ae_iff.mpr ?_)
  simpa [logNormBot] using hnull

/-- **Garnett II.4.2 (`p = ∞`), almost-everywhere form.** The boundary function of a nonzero
`H^∞` function is nonzero almost everywhere. -/
theorem MemHpDisc.ae_boundaryValue_ne_zero {f : ℂ → ℂ} (hf : MemHpDisc ∞ f)
    (hf_ne : ∃ z ∈ unitDisc, f z ≠ 0) :
    ∀ᵐ ζ ∂circleMeasure 0 1, boundaryValue f ζ ≠ 0 :=
  Filter.not_frequently.mp fun hfreq => by
    obtain ⟨z, -, hz⟩ := hf_ne
    exact hz (congrFun (hf.eq_zero_of_frequently_boundaryValue_eq_zero hfreq) z)

/-- **Garnett II.4.1 (`p = ∞`), real-valued form.** If `f ∈ H^∞` is not identically zero, then
`log |f*|` is integrable. Here `Real.log 0 = 0`; that `f* ≠ 0` almost everywhere is
`MemHpDisc.ae_boundaryValue_ne_zero`. -/
theorem MemHpDisc.integrable_log_norm_boundaryValue {f : ℂ → ℂ} (hf : MemHpDisc ∞ f)
    (hf_ne : ∃ z ∈ unitDisc, f z ≠ 0) :
    Integrable (fun ζ => Real.log ‖boundaryValue f ζ‖) (circleMeasure 0 1) := by
  -- `∫ᴮ logNormBot (f*) ≠ ⊥` forces the real representative `unbotD 0 ∘ logNormBot ∘ f*` to be
  -- integrable, and that representative is `log ‖f*‖`.
  have hint := hf.withBotIntegral_logNormBot_boundaryValue_ne_bot hf_ne
  have h : Integrable ((WithBot.unbotD 0) ∘ fun ζ => logNormBot (boundaryValue f ζ))
      (circleMeasure 0 1) := by
    by_contra h
    exact hint (by simp only [withBotIntegral, h, and_false, ↓reduceIte])
  refine h.congr (Filter.Eventually.of_forall fun ζ => ?_)
  by_cases hζ : boundaryValue f ζ = 0 <;> simp [logNormBot, hζ]

end HardySpace
