import HardySpaceFormalization.HardySpaceDisc
import HardySpaceFormalization.poissonIntegral
import HardySpaceFormalization.NontangentialLimit
import HardySpaceFormalization.NevanlinnaClass
import HardySpaceFormalization.HardySpaceBoundary

/-!
# Outer functions on the unit disc

Garnett II.4 and II.5, printed pages 64 and 70: the outer-function formula `O_k`, the outer
predicate, and the basic properties used in the canonical factorization. `O_k` is analytic and
zero-free on the disc, and `log |O_k|` is the Poisson integral of the boundary log-data `k`.
On the circle, `O_k` has nontangential limits of modulus `e^k` almost everywhere, and an outer
function is determined by its boundary modulus up to a unimodular constant.
-/

open MeasureTheory Complex Filter Topology
open scoped PoissonIntegral


/-- The normalized **outer-function formula** with boundary log-data `k`. Its analytic
and boundary properties assume `Integrable k (circleMeasure 0 1)`. -/
noncomputable def outerFunction (k : ℂ → ℝ) (z : ℂ) : ℂ :=
  exp (∫ ζ, herglotzRieszKernel 0 z ζ * (k ζ) ∂circleMeasure 0 1)

/-- A function is an **outer function** on the unit disc if it agrees with an exponential
integral of integrable real boundary log-data up to some unimodular constant. -/
def IsOuterFunction (f : ℂ → ℂ) : Prop :=
  ∃ k : ℂ → ℝ, Integrable k (circleMeasure 0 1) ∧
    ∃ C : ℂ, ‖C‖ = 1 ∧ ∀ z ∈ unitDisc, f z = C * outerFunction k z

/-! ### The outer-function formula -/

/-- The outer-function formula never vanishes. -/
theorem outerFunction_ne_zero (k : ℂ → ℝ) (z : ℂ) : outerFunction k z ≠ 0 :=
  exp_ne_zero _

/-- The outer-function formula with integrable boundary log-data is analytic on the disc. -/
theorem analyticOn_outerFunction {k : ℂ → ℝ} (hk : Integrable k (circleMeasure 0 1)) :
    AnalyticOn ℂ (outerFunction k) unitDisc :=
  (analyticOnNhd_integral_herglotzRieszKernel_mul (c := 0) (R := 1)
    (circleMeasure_compl_sphere zero_le_one) hk.ofReal).cexp.analyticOn

/-- **Garnett II.4.** The modulus of `O_k` is the exponential of the Poisson integral of the
boundary log-data `k`, since the real part of the Herglotz--Riesz kernel is the Poisson kernel. -/
theorem norm_outerFunction {k : ℂ → ℝ} (hk : Integrable k (circleMeasure 0 1)) {z : ℂ}
    (hz : z ∈ unitDisc) :
    ‖outerFunction k z‖ = Real.exp (P[0; k ∂ᵥ circleMeasure 0 1] z) := by
  -- Claude without review
  rw [outerFunction, Complex.norm_exp,
    poissonIntegral_withDensityᵥ (circleMeasure_compl_sphere zero_le_one) hz hk,
    ← RCLike.re_eq_complex_re,
    ← integral_re (integrable_herglotzRieszKernel_mul (g := fun ζ => (k ζ : ℂ))
      (circleMeasure_compl_sphere zero_le_one) hz hk.ofReal)]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
  simp [poissonKernel_eq_re_herglotzRieszKernel]

/-- **Garnett II.4.** `log |O_k|` is the Poisson integral of the boundary log-data `k`. -/
theorem log_norm_outerFunction {k : ℂ → ℝ} (hk : Integrable k (circleMeasure 0 1)) {z : ℂ}
    (hz : z ∈ unitDisc) :
    Real.log ‖outerFunction k z‖ = P[0; k ∂ᵥ circleMeasure 0 1] z := by
  rw [norm_outerFunction hk hz, Real.log_exp]

/-- The outer-function formula with integrable boundary log-data is an outer function. -/
theorem isOuterFunction_outerFunction {k : ℂ → ℝ} (hk : Integrable k (circleMeasure 0 1)) :
    IsOuterFunction (outerFunction k) :=
  ⟨k, hk, 1, by simp, fun z _ => by simp⟩

/-! ### Outer functions -/

/-- An outer function is analytic on the unit disc. -/
theorem IsOuterFunction.analyticOn {F : ℂ → ℂ} (hF : IsOuterFunction F) :
    AnalyticOn ℂ F unitDisc := by
  obtain ⟨k, hk, C, -, hF⟩ := hF
  exact ((analyticOn_outerFunction hk).const_smul (c := C)).congr fun z hz => hF z hz

/-- An outer function has no zeros in the unit disc. -/
theorem IsOuterFunction.ne_zero {F : ℂ → ℂ} (hF : IsOuterFunction F) {z : ℂ}
    (hz : z ∈ unitDisc) : F z ≠ 0 := by
  obtain ⟨k, -, C, hC, hF⟩ := hF
  rw [hF z hz]
  exact mul_ne_zero (norm_ne_zero_iff.mp (by simp [hC])) (outerFunction_ne_zero k z)

/-- **Garnett II.4.** The logarithm of the modulus of an outer function is the Poisson integral
of integrable boundary log-data. -/
theorem IsOuterFunction.exists_log_norm_eq {F : ℂ → ℂ} (hF : IsOuterFunction F) :
    ∃ k : ℂ → ℝ, Integrable k (circleMeasure 0 1) ∧
      ∀ z ∈ unitDisc, Real.log ‖F z‖ = P[0; k ∂ᵥ circleMeasure 0 1] z := by
  obtain ⟨k, hk, C, hC, hF⟩ := hF
  refine ⟨k, hk, fun z hz => ?_⟩
  rw [hF z hz, norm_mul, hC, one_mul, log_norm_outerFunction hk hz]

/-- An outer function, extended by zero outside the disc, belongs to the Nevanlinna class:
`log⁺ |F| ≤ P[k⁺ dσ]`, a harmonic majorant, since `log |F| = P[k dσ]` and the Poisson kernel
is nonnegative on the circle. -/
theorem IsOuterFunction.memNevanlinnaDisc_indicator {F : ℂ → ℂ} (hF : IsOuterFunction F) :
    Nevanlinna.MemNevanlinnaDisc (unitDisc.indicator F) := by
  obtain ⟨k, hk, hlog⟩ := hF.exists_log_norm_eq
  have hσ : circleMeasure 0 1 (Metric.sphere 0 1)ᶜ = 0 := circleMeasure_compl_sphere zero_le_one
  have hkp : Integrable (fun ζ => max (k ζ) 0) (circleMeasure 0 1) := hk.pos_part
  refine (Nevanlinna.memNevanlinnaDisc_iff_hasHarmonicMajorant
      (hF.analyticOn.congr fun z hz => Set.indicator_of_mem hz F)
      fun z hz => Set.indicator_of_notMem hz F).mpr
    ⟨P[0; (fun ζ => max (k ζ) 0) ∂ᵥ circleMeasure 0 1],
      harmonicOnNhd_poissonIntegral_withDensityᵥ hσ hkp, fun z hz => ?_⟩
  have hae : ∀ᵐ ζ ∂circleMeasure 0 1, ζ ∈ Metric.sphere (0 : ℂ) 1 := ae_iff.2 hσ
  -- `P[k] ≤ P[k⁺]` and `0 ≤ P[k⁺]`, because the Poisson kernel is nonnegative on the circle.
  have hle : P[0; k ∂ᵥ circleMeasure 0 1] z ≤
      P[0; (fun ζ => max (k ζ) 0) ∂ᵥ circleMeasure 0 1] z := by
    rw [poissonIntegral_withDensityᵥ hσ hz hk, poissonIntegral_withDensityᵥ hσ hz hkp]
    refine integral_mono_ae (by simpa [smul_eq_mul] using integrable_poissonKernel_mul hσ hz hk)
      (by simpa [smul_eq_mul] using integrable_poissonKernel_mul hσ hz hkp) ?_
    filter_upwards [hae] with ζ hζ
    exact smul_le_smul_of_nonneg_left (le_max_left _ _) (poissonKernel_nonneg hz hζ)
  have hnonneg : 0 ≤ P[0; (fun ζ => max (k ζ) 0) ∂ᵥ circleMeasure 0 1] z := by
    rw [poissonIntegral_withDensityᵥ hσ hz hkp]
    refine integral_nonneg_of_ae ?_
    filter_upwards [hae] with ζ hζ
    exact smul_nonneg (poissonKernel_nonneg hz hζ) (le_max_right _ _)
  show ((Real.posLog ‖unitDisc.indicator F z‖ : ℝ) : WithBot ℝ) ≤
    ((P[0; (fun ζ => max (k ζ) 0) ∂ᵥ circleMeasure 0 1] z : ℝ) : WithBot ℝ)
  rw [Set.indicator_of_mem hz]
  exact WithBot.coe_le_coe.mpr (max_le hnonneg ((hlog z hz).le.trans hle))

/-! ### Boundary values -/


/-- **Garnett II.4.** The outer-function formula with integrable boundary log-data has
nontangential limits almost everywhere on the unit circle. -/
theorem ae_nontangentiallyConvergentAt_outerFunction {k : ℂ → ℝ}
    (hk : Integrable k (circleMeasure 0 1)) :
    ∀ᵐ ζ ∂circleMeasure 0 1, NontangentiallyConvergentAt (outerFunction k) ζ := by
  -- Claude without review
  -- `O_k = O_{-k⁻} / O_{-k⁺}`, a quotient of two analytic functions bounded by `1`. Bounded Fatou
  -- gives their limits, and Poisson Fatou shows the limit of the denominator does not vanish.
  have hσ : circleMeasure 0 1 (Metric.sphere 0 1)ᶜ = 0 := circleMeasure_compl_sphere zero_le_one
  have hae : ∀ᵐ ζ ∂circleMeasure 0 1, ζ ∈ Metric.sphere (0 : ℂ) 1 := ae_iff.2 hσ
  have hfatou {h : ℂ → ℝ} (hh : Integrable h (circleMeasure 0 1)) (h0 : ∀ ζ, 0 ≤ h ζ) :
      ∀ᵐ ζ ∂circleMeasure 0 1, ∃ L : ℂ, L ≠ 0 ∧
        HasNontangentialLimit (outerFunction fun ζ => -h ζ) ζ L := by
    have hhn : Integrable (fun ζ => -h ζ) (circleMeasure 0 1) := hh.neg
    have han : AnalyticOnNhd ℂ (outerFunction fun ζ => -h ζ) (Metric.ball 0 1) :=
      (analyticOnNhd_integral_herglotzRieszKernel_mul (c := 0) (R := 1) hσ hhn.ofReal).cexp
    -- `|O_{-h}| = exp P[-h] ≤ 1`, because the Poisson kernel is nonnegative on the circle.
    have hbdd : ∀ z ∈ Metric.ball (0 : ℂ) 1, ‖outerFunction (fun ζ => -h ζ) z‖ ≤ 1 := by
      intro z hz
      rw [norm_outerFunction hhn hz, Real.exp_le_one_iff, poissonIntegral_withDensityᵥ hσ hz hhn]
      refine integral_nonpos_of_ae ?_
      filter_upwards [hae] with ζ hζ
      exact smul_nonpos_of_nonneg_of_nonpos (poissonKernel_nonneg hz hζ) (neg_nonpos.2 (h0 ζ))
    filter_upwards [AnalyticOnNhd.ae_nontangentiallyConvergentAt_of_bounded han hbdd,
      isAEBoundaryValue_poissonIntegral hhn, ae_nontangentially_neBot_circleMeasure]
      with ζ ⟨L, hL⟩ hP hne
    refine ⟨L, fun hL0 => ?_, hL⟩
    have h1 : Tendsto (fun z => ‖outerFunction (fun ζ => -h ζ) z‖) (nontangentially ζ)
        (𝓝 (Real.exp (-h ζ))) := by
      refine ((Real.continuous_exp.tendsto _).comp hP).congr' ?_
      filter_upwards [eventually_mem_ball_nontangentially ζ] with z hz
      exact (norm_outerFunction hhn hz).symm
    have h2 := Filter.Tendsto.norm hL
    rw [hL0, norm_zero] at h2
    exact (Real.exp_pos _).ne' (tendsto_nhds_unique h1 h2)
  have hkp : Integrable (fun ζ => max (k ζ) 0) (circleMeasure 0 1) := hk.pos_part
  have hkn : Integrable (fun ζ => max (-k ζ) 0) (circleMeasure 0 1) := hk.neg_part
  -- The quotient formula on the disc.
  have heq : ∀ z ∈ Metric.ball (0 : ℂ) 1, outerFunction k z =
      outerFunction (fun ζ => -max (-k ζ) 0) z / outerFunction (fun ζ => -max (k ζ) 0) z := by
    intro z hz
    rw [outerFunction, outerFunction, outerFunction, ← Complex.exp_sub,
      ← integral_sub (integrable_herglotzRieszKernel_mul
          (g := fun ζ => ((-max (-k ζ) 0 : ℝ) : ℂ)) hσ hz hkn.neg.ofReal)
        (integrable_herglotzRieszKernel_mul
          (g := fun ζ => ((-max (k ζ) 0 : ℝ) : ℂ)) hσ hz hkp.neg.ofReal)]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
    have hk' : (k ζ : ℂ) = ((max (k ζ) 0 : ℝ) : ℂ) - ((max (-k ζ) 0 : ℝ) : ℂ) := by
      norm_cast
      rcases le_total (k ζ) 0 with h | h
      · rw [max_eq_right h, max_eq_left (neg_nonneg.2 h)]; ring
      · rw [max_eq_left h, max_eq_right (neg_nonpos.2 h)]; ring
    simp only [Complex.ofReal_neg]
    rw [hk']
    ring
  filter_upwards [hfatou hkp (fun _ => le_max_right _ _), hfatou hkn (fun _ => le_max_right _ _)]
    with ζ ⟨L₁, hL₁0, hL₁⟩ ⟨L₂, _, hL₂⟩
  refine ⟨L₂ / L₁, (Filter.Tendsto.div hL₂ hL₁ hL₁0).congr' ?_⟩
  filter_upwards [eventually_mem_ball_nontangentially ζ] with z hz
  exact (heq z hz).symm


/-- **Garnett II.4.** The boundary values of `O_k` have modulus `e^k` almost everywhere. -/
theorem ae_norm_boundaryValue_outerFunction {k : ℂ → ℝ}
    (hk : Integrable k (circleMeasure 0 1)) :
    ∀ᵐ ζ ∂circleMeasure 0 1, ‖boundaryValue (outerFunction k) ζ‖ = Real.exp (k ζ) := by
  -- Claude without review
  -- `|O_k| = exp P[k] → e^{k(ζ)}` by Poisson Fatou, and `|O_k| → |O_k^*(ζ)|`.
  filter_upwards [ae_nontangentiallyConvergentAt_outerFunction hk,
    isAEBoundaryValue_poissonIntegral hk, ae_nontangentially_neBot_circleMeasure]
    with ζ hO hP hne
  have h1 : Tendsto (fun z => ‖outerFunction k z‖) (nontangentially ζ)
      (𝓝 (Real.exp (k ζ))) := by
    refine ((Real.continuous_exp.tendsto _).comp hP).congr' ?_
    filter_upwards [eventually_mem_ball_nontangentially ζ] with z hz
    exact (norm_outerFunction hk hz).symm
  exact tendsto_nhds_unique (Filter.Tendsto.norm hO.hasNontangentialLimit) h1

/-- **Garnett II.4.** An outer function is determined by the modulus of its boundary values, up
to a unimodular constant. -/
theorem IsOuterFunction.exists_eq_const_mul_of_ae_norm_boundaryValue_eq {F₁ F₂ : ℂ → ℂ}
    (h₁ : IsOuterFunction F₁) (h₂ : IsOuterFunction F₂)
    (h : ∀ᵐ ζ ∂circleMeasure 0 1, ‖boundaryValue F₁ ζ‖ = ‖boundaryValue F₂ ζ‖) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ z ∈ unitDisc, F₁ z = c * F₂ z := by
  -- Claude without review
  obtain ⟨k₁, hk₁, C₁, hC₁, hF₁⟩ := h₁
  obtain ⟨k₂, hk₂, C₂, hC₂, hF₂⟩ := h₂
  -- `|F^*| = |C| |O_k^*| = e^k` almost everywhere.
  have hbv {F : ℂ → ℂ} {k : ℂ → ℝ} (hk : Integrable k (circleMeasure 0 1)) {C : ℂ}
      (hC : ‖C‖ = 1) (hF : ∀ z ∈ unitDisc, F z = C * outerFunction k z) :
      ∀ᵐ ζ ∂circleMeasure 0 1, ‖boundaryValue F ζ‖ = Real.exp (k ζ) := by
    filter_upwards [ae_nontangentiallyConvergentAt_outerFunction hk,
      ae_norm_boundaryValue_outerFunction hk, ae_nontangentially_neBot_circleMeasure]
      with ζ hO hnorm hne
    have hlim : HasNontangentialLimit F ζ (C * boundaryValue (outerFunction k) ζ) := by
      refine (tendsto_const_nhds.mul hO.hasNontangentialLimit).congr' ?_
      filter_upwards [eventually_mem_ball_nontangentially ζ] with z hz
      exact (hF z hz).symm
    rw [hlim.boundaryValue_eq, norm_mul, hC, one_mul, hnorm]
  -- Equal boundary moduli force `k₁ = k₂` a.e., hence `O_{k₁} = O_{k₂}`.
  have hk : k₁ =ᵐ[circleMeasure 0 1] k₂ := by
    filter_upwards [hbv hk₁ hC₁ hF₁, hbv hk₂ hC₂ hF₂, h] with ζ hζ₁ hζ₂ hζ
    exact Real.exp_injective (hζ₁.symm.trans (hζ.trans hζ₂))
  have hO : outerFunction k₁ = outerFunction k₂ := by
    funext z
    rw [outerFunction, outerFunction]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hk] with ζ hζ
    rw [hζ]
  have hC₂0 : C₂ ≠ 0 := norm_ne_zero_iff.1 (by rw [hC₂]; exact one_ne_zero)
  refine ⟨C₁ / C₂, by rw [norm_div, hC₁, hC₂, div_one], fun z hz => ?_⟩
  rw [hF₁ z hz, hF₂ z hz, hO]
  field_simp
