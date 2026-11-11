import HardySpaceFormalization.NevanlinnaClass
import HardySpaceFormalization.HarmonicMajorant
import HardySpaceFormalization.BlaschkeProduct
import HardySpaceFormalization.HardySpaceLog


/-!
# The properties of Nevanlinna functions

-/

noncomputable section

open scoped Real ENNReal NNReal PoissonIntegral Topology
open MeasureTheory Real Complex Set Metric HardySpace



namespace Nevanlinna

variable {E F : Type*} [NormedAddCommGroup E] [NormedCommRing F]

/-- **Garnett II.5.1.**  Let `f` be analytic on the unit disc with `f ≢ 0`.  Then `f` belongs to the
Nevanlinna class if and only if `log ‖f‖` has as least harmonic majorant the Poisson integral of a
finite signed measure on the boundary circle.-/
theorem memNevanlinnaDisc_iff_exists_signedMeasure_isLeastHarmonicMajorant {f : ℂ → ℂ}
    (hf : AnalyticOn ℂ f unitDisc) (hf_out : ∀ z ∉ unitDisc, f z = 0)
    (hf_ne : ∃ z ∈ unitDisc, f z ≠ 0) :
    MemNevanlinnaDisc f ↔ ∃ μ : SignedMeasure ℂ, μ.totalVariation (sphere 0 1)ᶜ = 0 ∧
      Subharmonic.IsLeastHarmonicMajorant P[0; μ] (logNormBot ∘ f) unitDisc := by
  constructor
  · intro hN
    -- A harmonic majorant `U ≥ log⁺ |f| ≥ 0` also majorizes `log |f|`.
    obtain ⟨U, hU, hUle⟩ := (memNevanlinnaDisc_iff_hasHarmonicMajorant hf hf_out).mp hN
    have hposLog : ∀ z ∈ unitDisc, log⁺ ‖f z‖ ≤ U z :=
      fun z hz => WithBot.coe_le_coe.mp (hUle z hz)
    have hU_nonneg : ∀ z ∈ unitDisc, 0 ≤ U z := fun z hz => posLog_nonneg.trans (hposLog z hz)
    have hUmaj : Subharmonic.IsHarmonicMajorant U (logNormBot ∘ f) unitDisc := by
      refine ⟨hU, fun z hz => ?_⟩
      by_cases hfz : f z = 0
      · simp [logNormBot, hfz]
      · simpa [logNormBot, hfz] using (le_max_right _ _).trans (hposLog z hz)
    -- So `log |f|` has a least harmonic majorant `u ≤ U`.
    obtain ⟨u, hu, -⟩ := Subharmonic.exists_isLeastHarmonicMajorant_tendsto_poissonModification
      (logNormBot_comp_analytic_subharmonicOn_scalar isOpen_ball hf)
      (by
        obtain ⟨z, hz, hfz⟩ := hf_ne
        exact ⟨z, hz, by simp [logNormBot, hfz]⟩)
      ⟨U, hUmaj⟩
    have huU : ∀ z ∈ unitDisc, u z ≤ U z := hu.2 U hUmaj
    -- `u = U - (U - u)` is a difference of positive harmonic functions, hence of Poisson
    -- integrals of finite positive measures.
    obtain ⟨μ₁, _, hμ₁, hUμ₁⟩ :=
      (harmonicOnNhd_nonneg_iff_exists_eq_poissonIntegral one_pos).mp ⟨hU, hU_nonneg⟩
    obtain ⟨μ₂, _, hμ₂, hUμ₂⟩ := (harmonicOnNhd_nonneg_iff_exists_eq_poissonIntegral one_pos).mp
      ⟨hU.sub hu.1.1, fun z hz => sub_nonneg.mpr (huU z hz)⟩
    refine ⟨μ₁.toSignedMeasure - μ₂.toSignedMeasure,
      totalVariation_toSignedMeasure_sub_eq_zero hμ₁ hμ₂, hu.congr isOpen_ball fun w hw => ?_⟩
    rw [poissonIntegral_toSignedMeasure_sub hμ₁ hμ₂ hw, ← hUμ₁ w hw, ← hUμ₂ w hw]
    simp
  · rintro ⟨μ, hμ, hmajor⟩
    have hparts : μ.toJordanDecomposition.posPart (sphere 0 1)ᶜ = 0 ∧
        μ.toJordanDecomposition.negPart (sphere 0 1)ᶜ = 0 :=
      SignedMeasure.totalVariation_apply_eq_zero_iff.mp hμ
    let U := P[0; μ.toJordanDecomposition.posPart.toSignedMeasure]
    have hU : InnerProductSpace.HarmonicOnNhd U unitDisc :=
      harmonicOnNhd_poissonIntegral_toSignedMeasure hparts.1
    have hU_nonneg : ∀ z ∈ unitDisc, 0 ≤ U z :=
      fun z hz => poissonIntegral_toSignedMeasure_nonneg hparts.1 hz
    have hlog : ∀ z ∈ unitDisc, Real.log ‖f z‖ ≤ U z := by
      intro z hz
      by_cases hzero : f z = 0
      · simpa [hzero] using hU_nonneg z hz
      have hle : Real.log ‖f z‖ ≤ P[0; μ] z := by
        simpa [Function.comp_def, logNormBot, hzero] using hmajor.1.2 z hz
      refine hle.trans ?_
      rw [poissonIntegral_eq_posPart_sub_negPart
        (integrable_poissonKernel_totalVariation hμ hz)]
      have hneg := poissonIntegral_toSignedMeasure_nonneg hparts.2 hz
      rw [poissonIntegral_toSignedMeasure] at hneg
      simpa [U, poissonIntegral_toSignedMeasure] using sub_le_self
        (∫ ζ, poissonKernel 0 z ζ ∂μ.toJordanDecomposition.posPart) hneg
    -- `log⁺ |f| ≤ P[μ⁺]`, so `log⁺ |f|` has a harmonic majorant and (5.1) applies.
    refine (memNevanlinnaDisc_iff_hasHarmonicMajorant hf hf_out).mpr ⟨U, hU, fun z hz => ?_⟩
    exact WithBot.coe_le_coe.mpr (max_le (hU_nonneg z hz) (hlog z hz))

/-- **Garnett II.5.2 (convergence).** The zeros of a nonzero function in the Nevanlinna class,
counted with multiplicity, satisfy the Blaschke condition; hence the Blaschke product formed from
them converges. -/
theorem MemNevanlinnaDisc.blaschkeCondition {f : ℂ → ℂ} (hf : MemNevanlinnaDisc f)
    (hf_ne : ∃ z ∈ unitDisc, f z ≠ 0) :
    BlaschkeCondition (analyticOrderAt f) := by
  obtain ⟨U, hU, hUle⟩ := (memNevanlinnaDisc_iff_hasHarmonicMajorant hf.1 hf.2.2).mp hf
  refine blaschkeCondition_of_hasHarmonicMajorant
    (isOpen_ball.analyticOn_iff_analyticOnNhd.mp hf.1) hf_ne ⟨U, hU, fun z hz => ?_⟩
  by_cases hfz : f z = 0
  · simp [logNormBot, hfz]
  · simpa [logNormBot, hfz] using (le_max_right _ _).trans (WithBot.coe_le_coe.mp (hUle z hz))

/-- Division with removable singularities filled in. If `f` and `h` are analytic on `U`, have the
same order at every point of `U`, and these orders are finite, then `f = h * g` on `U` for an
analytic `g` without zeros on `U`. -/
lemma _root_.AnalyticOnNhd.exists_eq_mul_of_analyticOrderAt_eq {f h : ℂ → ℂ} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hh : AnalyticOnNhd ℂ h U)
    (horder : ∀ z ∈ U, analyticOrderAt f z = analyticOrderAt h z)
    (hh_top : ∀ z ∈ U, analyticOrderAt h z ≠ ⊤) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g U ∧ (∀ z ∈ U, g z ≠ 0) ∧ ∀ z ∈ U, f z = h z * g z := by
  -- `g` is the normal form of the meromorphic quotient `f / h`.
  have hq : MeromorphicOn (f / h) U := hf.meromorphicOn.div hh.meromorphicOn
  set g := toMeromorphicNFOn (f / h) U
  have hnf : MeromorphicNFOn g U := meromorphicNFOn_toMeromorphicNFOn (f / h) U
  -- Equal finite orders make the quotient have order zero at every point of `U`.
  have hord : ∀ z ∈ U, meromorphicOrderAt g z = 0 := by
    intro z hz
    rw [meromorphicOrderAt_toMeromorphicNFOn hq hz,
      meromorphicOrderAt_div (hf z hz).meromorphicAt (hh z hz).meromorphicAt,
      (hf z hz).meromorphicOrderAt_eq, (hh z hz).meromorphicOrderAt_eq, horder z hz]
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (hh_top z hz)
    rw [← hn]
    simp
  have hg : AnalyticOnNhd ℂ g U :=
    fun z hz => (hnf hz).meromorphicOrderAt_nonneg_iff_analyticAt.mp (hord z hz).ge
  refine ⟨g, hg, fun z hz => (hnf hz).meromorphicOrderAt_eq_zero_iff.mp (hord z hz),
    fun z hz => ?_⟩
  -- `f = h * g` off `z` near `z`, hence at `z` by continuity.
  have hh_ne : ∀ᶠ w in 𝓝[≠] z, h w ≠ 0 :=
    (hh z hz).eventually_eq_zero_or_eventually_ne_zero.resolve_left
      fun h0 => hh_top z hz (analyticOrderAt_eq_top.mpr h0)
  have hev : f =ᶠ[𝓝[≠] z] h * g := by
    filter_upwards [hq.toMeromorphicNFOn_eq_self_on_nhdsNE hz, hh_ne] with w hw hhw
    simp [g, hw, mul_div_cancel₀ _ hhw]
  exact (((hf z hz).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    ((hh z hz).continuousAt.mul (hg z hz).continuousAt)).mp hev).eq_of_nhds

/-- **Garnett II.5.2.** Let `f ≢ 0` belong to the Nevanlinna class and let `B` be the Blaschke
product formed from the zeros of `f`, counted with multiplicity. Then `f = B * g` on the disc for
a zero-free `g` in the Nevanlinna class, and `log ‖g‖` is the least harmonic majorant of
`log ‖f‖`. Since `B ≢ 0`, `g` is `f / B` with its removable singularities filled in. -/
theorem MemNevanlinnaDisc.exists_eq_blaschkeProduct_mul {f : ℂ → ℂ} (hf : MemNevanlinnaDisc f)
    (hf_ne : ∃ z ∈ unitDisc, f z ≠ 0) :
    ∃ g : ℂ → ℂ, MemNevanlinnaDisc g ∧ (∀ z ∈ unitDisc, g z ≠ 0) ∧
      (∀ z ∈ unitDisc, f z = BlaschkeProduct (analyticOrderAt f) z * g z) ∧
      Subharmonic.IsLeastHarmonicMajorant (fun z => Real.log ‖g z‖) (logNormBot ∘ f) unitDisc := by
  classical
  have hB := hf.blaschkeCondition hf_ne
  set B := BlaschkeProduct (analyticOrderAt f)
  have hfa : AnalyticOnNhd ℂ f unitDisc := isOpen_ball.analyticOn_iff_analyticOnNhd.mp hf.1
  have hBa : AnalyticOnNhd ℂ B unitDisc := analyticOnNhd_blaschkeProduct hB
  -- `B` has the zeros of `f` with the same multiplicities (Theorem II.2.2), so `f / B` has only
  -- removable singularities; removing them gives a zero-free analytic `g₀` with `f = B g₀`.
  obtain ⟨g₀, hg₀, hg₀_ne, hfg₀⟩ := hfa.exists_eq_mul_of_analyticOrderAt_eq hBa
    (fun z hz => (analyticOrderAt_blaschkeProduct hB hz).symm)
    (fun z hz => by rw [analyticOrderAt_blaschkeProduct hB hz]; exact hB.ne_top hz)
  -- By (5.1), `log⁺ |f| ≤ U` for a harmonic `U`, and Theorem I.6.7 gives the least harmonic
  -- majorant `u ≤ U` of `log |f|`.
  obtain ⟨U, hU, hUle⟩ := (memNevanlinnaDisc_iff_hasHarmonicMajorant hf.1 hf.2.2).mp hf
  have hU_nonneg : ∀ z ∈ unitDisc, 0 ≤ U z :=
    fun z hz => posLog_nonneg.trans (WithBot.coe_le_coe.mp (hUle z hz))
  have hUmaj : Subharmonic.IsHarmonicMajorant U (logNormBot ∘ f) unitDisc := by
    refine ⟨hU, fun z hz => ?_⟩
    by_cases hfz : f z = 0
    · simp [logNormBot, hfz]
    · simpa [logNormBot, hfz] using (le_max_right _ _).trans (WithBot.coe_le_coe.mp (hUle z hz))
  obtain ⟨u, hu, -⟩ := Subharmonic.exists_isLeastHarmonicMajorant_tendsto_poissonModification
    (logNormBot_comp_analytic_subharmonicOn_scalar isOpen_ball hf.1)
    (by
      obtain ⟨z, hz, hfz⟩ := hf_ne
      exact ⟨z, hz, by simp [logNormBot, hfz]⟩)
    ⟨U, hUmaj⟩
  -- As `|B| ≤ 1`, `log |g₀|` is a harmonic majorant of `log |f|`, so `u ≤ log |g₀|`.
  have hlog_g₀ : InnerProductSpace.HarmonicOnNhd (fun z => Real.log ‖g₀ z‖) unitDisc :=
    fun z hz => (hg₀ z hz).harmonicAt_log_norm (hg₀_ne z hz)
  have hu_le : ∀ z ∈ unitDisc, u z ≤ Real.log ‖g₀ z‖ := by
    refine hu.2 _ ⟨hlog_g₀, fun z hz => ?_⟩
    by_cases hfz : f z = 0
    · simp [logNormBot, hfz]
    have hBz : B z ≠ 0 := fun h => hfz (by rw [hfg₀ z hz, h, zero_mul])
    simp only [Function.comp_apply, logNormBot, hfz, ↓reduceIte]
    rw [hfg₀ z hz, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hBz)
      (norm_ne_zero_iff.mpr (hg₀_ne z hz))]
    exact WithBot.coe_le_coe.mpr (add_le_of_nonpos_left
      (Real.log_nonpos (norm_nonneg _) (norm_blaschkeProduct_le_one hB hz)))
  -- Conversely, `u - log |g₀|` is a harmonic majorant of `log |B|`, whose least harmonic majorant
  -- is `0` by Theorem II.2.4; hence `u = log |g₀|`.
  have hB0 : Subharmonic.IsLeastHarmonicMajorant 0 (logNormBot ∘ B) unitDisc :=
    (tendsto_withBotRadialMean_logNormBot_iff_isLeastHarmonicMajorant_zero hBa
      fun z hz => norm_blaschkeProduct_le_one hB hz).mp
      (by simpa using tendsto_withBotRadialMean_logNormBot_blaschkeProduct hB (c := 1) (by simp))
  have hu_eq : ∀ z ∈ unitDisc, u z = Real.log ‖g₀ z‖ := by
    intro z hz
    refine le_antisymm (hu_le z hz) (sub_nonneg.mp
      (hB0.2 (fun w => u w - Real.log ‖g₀ w‖) ⟨hu.1.1.sub hlog_g₀, fun w hw => ?_⟩ z hz))
    by_cases hBw : B w = 0
    · simp [logNormBot, hBw]
    have hfw : f w ≠ 0 := by rw [hfg₀ w hw]; exact mul_ne_zero hBw (hg₀_ne w hw)
    have hmaj : Real.log ‖f w‖ ≤ u w := by simpa [logNormBot, hfw] using hu.1.2 w hw
    rw [hfg₀ w hw, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hBw)
      (norm_ne_zero_iff.mpr (hg₀_ne w hw))] at hmaj
    simp only [Function.comp_apply, logNormBot, hBw, ↓reduceIte]
    exact WithBot.coe_le_coe.mpr (by linarith)
  -- Extend `g₀` by zero off the disc.
  let g : ℂ → ℂ := fun z => if z ∈ unitDisc then g₀ z else 0
  have hg_eq : EqOn g g₀ unitDisc := fun z hz => by simp [g, hz]
  -- Finally `log⁺ |g| = max(u, 0) ≤ U`, so `g ∈ N` by (5.1).
  have hgN : MemNevanlinnaDisc g := by
    refine (memNevanlinnaDisc_iff_hasHarmonicMajorant (hg₀.analyticOn.congr hg_eq)
      fun z hz => by simp [g, hz]).mpr ⟨U, hU, fun z hz => ?_⟩
    show (log⁺ ‖g z‖ : WithBot ℝ) ≤ U z
    rw [hg_eq hz]
    exact WithBot.coe_le_coe.mpr (max_le (hU_nonneg z hz) (hu_eq z hz ▸ hu.2 U hUmaj z hz))
  refine ⟨g, hgN, fun z hz => by rw [hg_eq hz]; exact hg₀_ne z hz,
    fun z hz => by rw [hg_eq hz]; exact hfg₀ z hz, hu.congr isOpen_ball fun z hz => ?_⟩
  simp only [hg_eq hz, hu_eq z hz]

/-- The representation from the proof of Garnett II.5.3: a nonzero function in the Nevanlinna class
is `B h G₂ / G₁` on the disc, where `B` is its Blaschke product, `|h| = 1`, and `G₁, G₂ ∈ H^∞` are
zero-free on the disc. Garnett shows that `h` is a unimodular constant; `|h| = 1` is all that is
needed. -/
theorem MemNevanlinnaDisc.exists_eq_blaschkeProduct_mul_div {f : ℂ → ℂ}
    (hf : MemNevanlinnaDisc f) (hf_ne : ∃ z ∈ unitDisc, f z ≠ 0) :
    ∃ h G₁ G₂ : ℂ → ℂ, AnalyticOnNhd ℂ h unitDisc ∧ (∀ z ∈ unitDisc, ‖h z‖ = 1) ∧
      MemHpDisc ∞ G₁ ∧ MemHpDisc ∞ G₂ ∧ (∀ z ∈ unitDisc, G₁ z ≠ 0) ∧
      (∀ z ∈ unitDisc, G₂ z ≠ 0) ∧
      ∀ z ∈ unitDisc, f z = BlaschkeProduct (analyticOrderAt f) z * h z * G₂ z / G₁ z := by
  -- Lemma II.5.2: `f = B g` with `g ∈ N` zero-free and `log |g|` the least harmonic majorant of
  -- `log |f|`.
  obtain ⟨g, hgN, hg_ne, hfg, hu⟩ := hf.exists_eq_blaschkeProduct_mul hf_ne
  have hga : AnalyticOnNhd ℂ g unitDisc := isOpen_ball.analyticOn_iff_analyticOnNhd.mp hgN.1
  -- `log |g| = u₁ - u₂` with `u₁ = U ≥ 0` a harmonic majorant of `log⁺ |f|` from (5.1) and
  -- `u₂ = U - log |g| ≥ 0`, since `log |g| ≤ U` by leastness.
  obtain ⟨U, hU, hUle⟩ := (memNevanlinnaDisc_iff_hasHarmonicMajorant hf.1 hf.2.2).mp hf
  have hU_nonneg : ∀ z ∈ unitDisc, 0 ≤ U z :=
    fun z hz => posLog_nonneg.trans (WithBot.coe_le_coe.mp (hUle z hz))
  have hUmaj : Subharmonic.IsHarmonicMajorant U (logNormBot ∘ f) unitDisc := by
    refine ⟨hU, fun z hz => ?_⟩
    by_cases hfz : f z = 0
    · simp [logNormBot, hfz]
    · simpa [logNormBot, hfz] using (le_max_right _ _).trans (WithBot.coe_le_coe.mp (hUle z hz))
  have hgU : ∀ z ∈ unitDisc, Real.log ‖g z‖ ≤ U z := hu.2 U hUmaj
  -- Harmonic conjugates: `F₁, F₂` analytic with `Re F₁ = u₁`, `Re F₂ = u₂`.
  obtain ⟨F₁, hF₁, hF₁re⟩ := hU.exists_analyticOnNhd_ball_re_eq
  obtain ⟨F₂, hF₂, hF₂re⟩ := (hU.sub hu.1.1).exists_analyticOnNhd_ball_re_eq
  have hre₁ : ∀ z ∈ unitDisc, (F₁ z).re = U z := fun z hz => hF₁re hz
  have hre₂ : ∀ z ∈ unitDisc, (F₂ z).re = U z - Real.log ‖g z‖ := fun z hz => hF₂re hz
  -- `G₁ = e^{-F₁}`, `G₂ = e^{-F₂}` (extended by zero off the disc) and `h = g e^{F₂ - F₁}`.
  refine ⟨fun z => g z * Complex.exp (F₂ z - F₁ z),
    unitDisc.indicator fun z => Complex.exp (-F₁ z),
    unitDisc.indicator fun z => Complex.exp (-F₂ z),
    fun z hz => (hga z hz).mul ((hF₂ z hz).sub (hF₁ z hz)).cexp, fun z hz => ?_, ?_, ?_,
    fun z hz => by simp [indicator_of_mem hz], fun z hz => by simp [indicator_of_mem hz],
    fun z hz => ?_⟩
  · have hgz : 0 < ‖g z‖ := norm_pos_iff.mpr (hg_ne z hz)
    rw [norm_mul, Complex.norm_exp, Complex.sub_re, hre₁ z hz, hre₂ z hz,
      show U z - Real.log ‖g z‖ - U z = -Real.log ‖g z‖ by ring, Real.exp_neg, Real.exp_log hgz,
      mul_inv_cancel₀ hgz.ne']
  · refine memHpDisc_top_indicator_of_norm_le
      (fun z hz => ((hF₁ z hz).neg.cexp).analyticWithinAt) (M := 1) fun z hz => ?_
    rw [Complex.norm_exp, Complex.neg_re, hre₁ z hz, Real.exp_le_one_iff]
    linarith [hU_nonneg z hz]
  · refine memHpDisc_top_indicator_of_norm_le
      (fun z hz => ((hF₂ z hz).neg.cexp).analyticWithinAt) (M := 1) fun z hz => ?_
    rw [Complex.norm_exp, Complex.neg_re, hre₂ z hz, Real.exp_le_one_iff]
    linarith [hgU z hz]
  · simp only [indicator_of_mem hz, Complex.exp_sub, Complex.exp_neg]
    rw [hfg z hz]
    field_simp

/-- **Garnett II.5.3 (nontangential limits).** A function in the Nevanlinna class has a
nontangential limit at almost every point of the unit circle. Garnett's hypothesis `f ≢ 0` is not
needed here. -/
theorem MemNevanlinnaDisc.ae_nontangentiallyConvergentAt {f : ℂ → ℂ}
    (hf : MemNevanlinnaDisc f) :
    ∀ᵐ ζ ∂circleMeasure 0 1, NontangentiallyConvergentAt f ζ := by
  by_cases hf0 : ∀ z ∈ unitDisc, f z = 0
  · -- If `f ≡ 0` on the disc, it converges to `0`, since the filter only sees the disc.
    exact Filter.Eventually.of_forall fun ζ => ⟨0, tendsto_const_nhds.congr'
      ((eventually_mem_ball_nontangentially ζ).mono fun z hz => (hf0 z hz).symm)⟩
  have hf_ne : ∃ z ∈ unitDisc, f z ≠ 0 := by push Not at hf0; exact hf0
  have hB := hf.blaschkeCondition hf_ne
  obtain ⟨h, G₁, G₂, hh, hh1, hG₁, hG₂, hG₁_ne, -, heq⟩ :=
    hf.exists_eq_blaschkeProduct_mul_div hf_ne
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  -- `f = B h G₂ / G₁`: bounded analytic functions have nontangential limits almost everywhere
  -- (II.3.1, `p = ∞`), and the denominator has nonzero boundary values almost everywhere (II.4.2).
  filter_upwards [(analyticOnNhd_blaschkeProduct hB).ae_nontangentiallyConvergentAt_of_bounded
      fun z hz => norm_blaschkeProduct_le_one hB hz,
    hh.ae_nontangentiallyConvergentAt_of_bounded fun z hz => (hh1 z hz).le,
    hG₂.ae_nontangentiallyConvergentAt, hG₁.ae_nontangentiallyConvergentAt,
    hG₁.ae_boundaryValue_ne_zero ⟨0, h0, hG₁_ne 0 h0⟩] with ζ ⟨b, hb⟩ ⟨c, hc⟩ ⟨d, hd⟩ hG₁ζ hG₁ζ_ne
  exact ⟨_, (((hb.mul hc).mul hd).div hG₁ζ.hasNontangentialLimit hG₁ζ_ne).congr'
    ((eventually_mem_ball_nontangentially ζ).mono fun z hz => (heq z hz).symm)⟩

/-- From the representation `f = B h G₂ / G₁` in the proof of Garnett II.5.3: almost everywhere on
the circle, `|f*| = |G₂*| / |G₁*|` with `G₁*, G₂* ≠ 0`, for nonzero `G₁, G₂ ∈ H^∞`. -/
theorem MemNevanlinnaDisc.exists_ae_norm_boundaryValue_eq_div {f : ℂ → ℂ}
    (hf : MemNevanlinnaDisc f) (hf_ne : ∃ z ∈ unitDisc, f z ≠ 0) :
    ∃ G₁ G₂ : ℂ → ℂ, MemHpDisc ∞ G₁ ∧ MemHpDisc ∞ G₂ ∧ (∃ z ∈ unitDisc, G₁ z ≠ 0) ∧
      (∃ z ∈ unitDisc, G₂ z ≠ 0) ∧ ∀ᵐ ζ ∂circleMeasure 0 1,
        ‖boundaryValue f ζ‖ = ‖boundaryValue G₂ ζ‖ / ‖boundaryValue G₁ ζ‖ ∧
          boundaryValue G₁ ζ ≠ 0 ∧ boundaryValue G₂ ζ ≠ 0 := by
  have hB := hf.blaschkeCondition hf_ne
  obtain ⟨h, G₁, G₂, hh, hh1, hG₁, hG₂, hG₁_ne, hG₂_ne, heq⟩ :=
    hf.exists_eq_blaschkeProduct_mul_div hf_ne
  set B := BlaschkeProduct (analyticOrderAt f)
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  refine ⟨G₁, G₂, hG₁, hG₂, ⟨0, h0, hG₁_ne 0 h0⟩, ⟨0, h0, hG₂_ne 0 h0⟩, ?_⟩
  -- `f* = B* h* G₂* / G₁*`, where `|B*| = 1` (II.2.2), `|h*| = 1`, and `G₁*, G₂* ≠ 0` (II.4.2).
  filter_upwards [ae_nontangentially_neBot_circleMeasure,
    (analyticOnNhd_blaschkeProduct hB).ae_nontangentiallyConvergentAt_of_bounded
      fun z hz => norm_blaschkeProduct_le_one hB hz,
    ae_hasNontangentialLimit_blaschkeProduct hB,
    hh.ae_nontangentiallyConvergentAt_of_bounded fun z hz => (hh1 z hz).le,
    hG₂.ae_nontangentiallyConvergentAt, hG₁.ae_nontangentiallyConvergentAt,
    hG₂.ae_boundaryValue_ne_zero ⟨0, h0, hG₂_ne 0 h0⟩,
    hG₁.ae_boundaryValue_ne_zero ⟨0, h0, hG₁_ne 0 h0⟩]
    with ζ hζ hBζ hBζ1 hhζ hG₂ζ hG₁ζ hG₂ζ_ne hG₁ζ_ne
  have hmem := eventually_mem_ball_nontangentially ζ
  -- `|h| = 1` on the disc, hence `|h*| = 1`.
  have hh_norm : ‖boundaryValue h ζ‖ = 1 := tendsto_nhds_unique hhζ.hasNontangentialLimit.norm
    (tendsto_const_nhds.congr' (hmem.mono fun z hz => (hh1 z hz).symm))
  have hlim : HasNontangentialLimit f ζ
      (boundaryValue B ζ * boundaryValue h ζ * boundaryValue G₂ ζ / boundaryValue G₁ ζ) :=
    (((hBζ.hasNontangentialLimit.mul hhζ.hasNontangentialLimit).mul
      hG₂ζ.hasNontangentialLimit).div hG₁ζ.hasNontangentialLimit hG₁ζ_ne).congr'
      (hmem.mono fun z hz => (heq z hz).symm)
  refine ⟨?_, hG₁ζ_ne, hG₂ζ_ne⟩
  rw [hlim.boundaryValue_eq, norm_div, norm_mul, norm_mul, hBζ1, hh_norm, one_mul, one_mul]

/-- **Garnett II.5.3 (nonvanishing boundary values).** The boundary function of a nonzero function
in the Nevanlinna class is nonzero almost everywhere. Garnett's `log |f*| ∈ L¹` contains this, but
`Real.log 0 = 0` in Lean, so it is stated separately. -/
theorem MemNevanlinnaDisc.ae_boundaryValue_ne_zero {f : ℂ → ℂ}
    (hf : MemNevanlinnaDisc f) (hf_ne : ∃ z ∈ unitDisc, f z ≠ 0) :
    ∀ᵐ ζ ∂circleMeasure 0 1, boundaryValue f ζ ≠ 0 := by
  obtain ⟨G₁, G₂, -, -, -, -, hae⟩ := hf.exists_ae_norm_boundaryValue_eq_div hf_ne
  filter_upwards [hae] with ζ ⟨hnorm, h₁, h₂⟩
  rw [← norm_ne_zero_iff, hnorm]
  exact div_ne_zero (norm_ne_zero_iff.mpr h₂) (norm_ne_zero_iff.mpr h₁)

/-- **Garnett II, (5.2).** For a nonzero function `f` in the Nevanlinna class, `log ‖f*‖` is
integrable on the unit circle. -/
theorem MemNevanlinnaDisc.integrable_log_norm_boundaryValue {f : ℂ → ℂ}
    (hf : MemNevanlinnaDisc f) (hf_ne : ∃ z ∈ unitDisc, f z ≠ 0) :
    Integrable (fun ζ => Real.log ‖boundaryValue f ζ‖) (circleMeasure 0 1) := by
  -- `log |f*| = log |G₂*| - log |G₁*|` almost everywhere, and both terms are integrable by II.4.1.
  obtain ⟨G₁, G₂, hG₁, hG₂, hG₁_ne, hG₂_ne, hae⟩ := hf.exists_ae_norm_boundaryValue_eq_div hf_ne
  refine ((hG₂.integrable_log_norm_boundaryValue hG₂_ne).sub
    (hG₁.integrable_log_norm_boundaryValue hG₁_ne)).congr ?_
  filter_upwards [hae] with ζ ⟨hnorm, h₁, h₂⟩
  rw [Pi.sub_apply, hnorm, Real.log_div (norm_ne_zero_iff.mpr h₂) (norm_ne_zero_iff.mpr h₁)]

/-- **Garnett II, (5.3).** For a nonzero function `f` in the Nevanlinna class, the least harmonic
majorant of `log ‖f‖` is the Poisson integral of `log ‖f*‖ dθ/2π + dμ_s`, for a finite signed
measure `μ_s` on the unit circle singular to arclength. -/
theorem MemNevanlinnaDisc.exists_mutuallySingular_isLeastHarmonicMajorant {f : ℂ → ℂ}
    (hf : MemNevanlinnaDisc f) (hf_ne : ∃ z ∈ unitDisc, f z ≠ 0) :
    ∃ μs : SignedMeasure ℂ, μs.totalVariation (sphere 0 1)ᶜ = 0 ∧
      μs ⟂ᵥ (circleMeasure 0 1).toENNRealVectorMeasure ∧
      Subharmonic.IsLeastHarmonicMajorant
        P[0; (fun ζ => Real.log ‖boundaryValue f ζ‖) ∂ᵥ circleMeasure 0 1 + μs]
        (logNormBot ∘ f) unitDisc := by
  set σ := circleMeasure 0 1
  -- Theorem II.5.1: the least harmonic majorant of `log |f|` is `P[μ]`; by Lemma II.5.2 it is
  -- also `log |g|`, where `f = B g`.
  obtain ⟨μ, hμ, hμmaj⟩ :=
    (memNevanlinnaDisc_iff_exists_signedMeasure_isLeastHarmonicMajorant hf.1 hf.2.2 hf_ne).mp hf
  have hB := hf.blaschkeCondition hf_ne
  set B := BlaschkeProduct (analyticOrderAt f)
  obtain ⟨g, -, -, hfg, hu⟩ := hf.exists_eq_blaschkeProduct_mul hf_ne
  have hgμ := hu.unique hμmaj
  -- Write `dμ = k dθ/2π + dμ_s`. By Theorem I.5.3, `log |g| = P[μ]` has nontangential limit `k`
  -- almost everywhere; since `|B*| = 1`, that limit is also `log |f*|`. Hence `k = log |f*|`.
  set k := μ.rnDeriv σ
  have hk : k =ᵐ[σ] fun ζ => Real.log ‖boundaryValue f ζ‖ := by
    filter_upwards [ae_nontangentially_neBot_circleMeasure,
      isAEBoundaryValue_poissonIntegral_rnDeriv hμ, hf.ae_nontangentiallyConvergentAt, hf.ae_boundaryValue_ne_zero hf_ne,
      (analyticOnNhd_blaschkeProduct hB).ae_nontangentiallyConvergentAt_of_bounded
        fun z hz => norm_blaschkeProduct_le_one hB hz,
      ae_hasNontangentialLimit_blaschkeProduct hB] with ζ hζ hPζ hfζ hfζ_ne hBζ hBζ1
    have hB_ne : boundaryValue B ζ ≠ 0 := norm_ne_zero_iff.mp (by rw [hBζ1]; exact one_ne_zero)
    have hmem := eventually_mem_ball_nontangentially ζ
    -- `g = f / B` where `B ≠ 0`, so `g → f* / B*` and `log |g| → log |f* / B*| = log |f*|`.
    have hg : HasNontangentialLimit g ζ (boundaryValue f ζ / boundaryValue B ζ) :=
      (hfζ.hasNontangentialLimit.div hBζ.hasNontangentialLimit hB_ne).congr'
        ((hmem.and (hBζ.hasNontangentialLimit.eventually_ne hB_ne)).mono fun z ⟨hz, hBz⟩ => by
          rw [Pi.div_apply, hfg z hz]
          field_simp)
    have hlog : HasNontangentialLimit (fun z => Real.log ‖g z‖) ζ
        (Real.log ‖boundaryValue f ζ / boundaryValue B ζ‖) :=
      hg.norm.log (norm_ne_zero_iff.mpr (div_ne_zero hfζ_ne hB_ne))
    rw [norm_div, hBζ1, div_one] at hlog
    exact tendsto_nhds_unique hPζ (hlog.congr' (hmem.mono fun z hz => hgμ hz))
  -- So `μ = log |f*| dθ/2π + μ_s` with `μ_s` the singular part of `μ`.
  have hdensity : σ.withDensityᵥ k = σ.withDensityᵥ fun ζ => Real.log ‖boundaryValue f ζ‖ :=
    (Integrable.withDensityᵥ_eq_iff (SignedMeasure.integrable_rnDeriv μ σ)
      (hf.integrable_log_norm_boundaryValue hf_ne)).mpr hk
  have hdecomp : (fun ζ => Real.log ‖boundaryValue f ζ‖) ∂ᵥ σ + μ.singularPart σ = μ := by
    rw [← hdensity, add_comm]
    exact SignedMeasure.singularPart_add_withDensity_rnDeriv_eq σ μ
  -- `μ_s` lives on the circle, since `|μ_s| ≤ |μ|`.
  have hsing_le : (μ.singularPart σ).totalVariation ≤ μ.totalVariation := by
    rw [SignedMeasure.singularPart_totalVariation, SignedMeasure.totalVariation]
    exact add_le_add (Measure.singularPart_le _ _) (Measure.singularPart_le _ _)
  refine ⟨μ.singularPart σ, hsing_le.absolutelyContinuous hμ,
    SignedMeasure.mutuallySingular_singularPart μ σ, ?_⟩
  rw [hdecomp]
  exact hμmaj

end Nevanlinna

#check toMeromorphicNFOn

end
