import HardySpaceFormalization.Subharmonic
import HardySpaceFormalization.HarmonicHarnack
import HardySpaceFormalization.withBotIntegral
import Mathlib.Analysis.Complex.Poisson
import Mathlib.Topology.Order.WithTop
import Mathlib.Analysis.SpecialFunctions.Integrability.Log



open scoped Real ENNReal NNReal PoissonIntegral
open MeasureTheory Real Complex Set Metric Filter Topology



variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

-- # Here's the coercion from `WithBot ℝ` to `EReal`:
noncomputable instance : Coe (WithBot ℝ) EReal := ⟨
  fun x =>
  if hx : x = ⊥ then ⊥
  else (x.unbot hx : EReal)
 ⟩


namespace Subharmonic

/-- A function `g` has a harmonic majorant on `s` if some function harmonic on `s`
dominates `g` pointwise on `s`. -/
def HasHarmonicMajorant (g : V → WithBot ℝ) (s : Set V) : Prop :=
  ∃ u : V → ℝ, InnerProductSpace.HarmonicOnNhd u s ∧ ∀ z ∈ s, g z ≤ u z

/-- `u` is a harmonic majorant of `g` on `s` if it is harmonic on `s` and dominates `g`
pointwise there. -/
def IsHarmonicMajorant (u : V → ℝ) (g : V → WithBot ℝ) (s : Set V) : Prop :=
    InnerProductSpace.HarmonicOnNhd u s ∧ ∀ z ∈ s, g z ≤ u z

/-- `u` is the least harmonic majorant of `g` on `s` with respect to pointwise order on `s`. -/
def IsLeastHarmonicMajorant (u : V → ℝ) (g : V → WithBot ℝ) (s : Set V) : Prop :=
  IsHarmonicMajorant u g s ∧ ∀ v : V → ℝ, IsHarmonicMajorant v g s  → ∀ z ∈ s, u z ≤ v z

/-- On an open set, being the least harmonic majorant only depends on the values on that set. -/
theorem IsLeastHarmonicMajorant.congr {u u' : V → ℝ} {g : V → WithBot ℝ} {s : Set V}
    (hs : IsOpen s) (hu : IsLeastHarmonicMajorant u g s) (h : EqOn u u' s) :
    IsLeastHarmonicMajorant u' g s := by
  refine ⟨⟨fun x hx => ?_, fun z hz => ?_⟩, fun v hv z hz => ?_⟩
  · exact (InnerProductSpace.harmonicAt_congr_nhds
      (Filter.eventuallyEq_of_mem (hs.mem_nhds hx) h)).1 (hu.1.1 x hx)
  · rw [← h hz]
    exact hu.1.2 z hz
  · rw [← h hz]
    exact hu.2 v hv z hz

/-- The least harmonic majorant is unique on `s`: two least harmonic majorants of `g` on `s`
agree there. -/
theorem IsLeastHarmonicMajorant.unique {u v : V → ℝ} {g : V → WithBot ℝ} {s : Set V}
    (hu : IsLeastHarmonicMajorant u g s) (hv : IsLeastHarmonicMajorant v g s) : EqOn u v s :=
  fun z hz => le_antisymm (hu.2 v hv.1 z hz) (hv.2 u hu.1 z hz)

open Classical in
/-- A choice of the least harmonic majorant of `g` on `s`, when one exists. -/
noncomputable def leastHarmonicMajorant' (g : V → WithBot ℝ) (s : Set V)
  := if h : ∃ u : V → ℝ, IsLeastHarmonicMajorant u g s then Classical.choose h else 0


/-- The normalized radial mean of a function on the circle of radius `r` centered at the origin. -/
noncomputable def withBotRadialMean (v : ℂ → WithBot ℝ) (r : ℝ) : WithBot ℝ :=
  ∫ᴮ θ, v (r * exp (I * θ)) ∂angularMeasure



/-- The **Poisson modification** `v_r` of a `WithBot ℝ`-valued function on the unit disc:
outside the circle of radius `r` (`r ≤ ‖z‖`) it agrees with `v`, while inside
(`‖z‖ < r`) it is replaced by the Poisson integral of the boundary values of `v` on the circle
of radius `r`. -/
noncomputable def poissonModification (v : ℂ → WithBot ℝ) (r : ℝ) : ℂ → WithBot ℝ :=
  fun z =>
    if r ≤ ‖z‖ then v z
    else ∫ᴮ θ, poissonKernel 0 (z / r) (exp (I * θ)) * v (r * exp (I * θ)) ∂angularMeasure

/-- At the centre of the disc the Poisson modification reduces to the radial mean:
`v_r(0) = withBotRadialMean v r`. -/
lemma poissonModification_zero_eq_withBotRadialMean (v : ℂ → WithBot ℝ) {r : ℝ} (hr : 0 < r) :
    poissonModification v r 0 = withBotRadialMean v r := by
  unfold poissonModification withBotRadialMean
  rw [ite_eq_right (by simpa using not_le.mpr hr)]
  refine congrArg _ (funext fun θ => ?_)
  rw [zero_div, poissonKernel_def]
  simp [Complex.norm_exp, mul_comm]

/-- If a `WithBot ℝ`-valued function agrees almost everywhere on the circle of radius `r` with a
circle-integrable real function `u`, its radial mean is the circle average of `u`. -/
lemma withBotRadialMean_eq_circleAverage {v : ℂ → WithBot ℝ} {u : ℂ → ℝ} {r : ℝ}
    (hvu : ∀ᵐ θ : ℝ ∂angularMeasure, v (r * exp (I * θ)) = u (r * exp (I * θ)))
    (hu : CircleIntegrable u 0 r) :
    withBotRadialMean v r = ((circleAverage u 0 r : ℝ) : WithBot ℝ) := by
  have hcm (θ : ℝ) : circleMap 0 r θ = (r : ℂ) * exp (I * θ) := by
    simp [circleMap, mul_comm]
  -- The pullback of `u` is integrable against the normalized angular measure.
  have hIco : IntegrableOn (fun θ : ℝ => u (circleMap 0 r θ)) (Ico 0 (2 * π)) volume := by
    rw [← intervalIntegrable_iff_integrableOn_Ico_of_le (by positivity)]
    exact hu
  have hint : Integrable (fun θ : ℝ => u ((r : ℂ) * exp (I * θ))) angularMeasure := by
    unfold angularMeasure
    simpa only [hcm] using hIco.smul_measure ENNReal.ofReal_ne_top
  have havg : circleAverage u 0 r = ∫ θ, u ((r : ℂ) * exp (I * θ)) ∂angularMeasure := by
    rw [circleAverage_eq_integral_circleMeasure hu,
      integral_circleMeasure_eq_integral_angularMeasure hu.aestronglyMeasurable_circleMeasure]
    simp only [hcm]
  -- The `⊥`-set is null and the real representative agrees with `u` almost everywhere.
  have hbot : angularMeasure {θ : ℝ | v (r * exp (I * θ)) = ⊥} = 0 := by
    have h : ∀ᵐ θ : ℝ ∂angularMeasure, v (r * exp (I * θ)) ≠ ⊥ :=
      hvu.mono fun θ h => by rw [h]; exact WithBot.coe_ne_bot
    simpa using ae_iff.mp h
  have hunbot : (fun θ : ℝ => (v (r * exp (I * θ))).unbotD 0) =ᵐ[angularMeasure]
      fun θ => u (r * exp (I * θ)) :=
    hvu.mono fun θ h => by simp only [h, WithBot.unbotD_coe]
  have hcond : angularMeasure {θ : ℝ | v (r * exp (I * θ)) = ⊥} = 0 ∧
      Integrable ((WithBot.unbotD 0) ∘ fun θ : ℝ => v (r * exp (I * θ))) angularMeasure :=
    ⟨hbot, hint.congr hunbot.symm⟩
  unfold withBotRadialMean withBotIntegral
  rw [ite_eq_left_of_eq_true _ _ (eq_true hcond), integral_congr_ae hunbot, havg]

/-- For an analytic function on the unit disc that is not identically zero, the `WithBot` radial
mean of `log ‖g‖` on a circle of radius `0 < r < 1` is the real circle average of `log ‖g‖`. -/
lemma withBotRadialMean_logNormBot_eq_circleAverage {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 1)) (hne : ∃ z ∈ ball (0 : ℂ) 1, g z ≠ 0)
    {r : ℝ} (hr : r ∈ Ioo 0 1) :
    withBotRadialMean (logNormBot ∘ g) r =
      ((circleAverage (fun z => Real.log ‖g z‖) 0 r : ℝ) : WithBot ℝ) := by
  obtain ⟨z₀, hz₀, hgz₀⟩ := hne
  have hr0 : r ≠ 0 := hr.1.ne'
  have hsph : sphere (0 : ℂ) |r| ⊆ ball 0 1 := by
    intro z hz
    rw [mem_sphere_zero_iff_norm, abs_of_pos hr.1] at hz
    simpa [hz] using hr.2
  -- The zeros of `g` are isolated in the disc, hence null on the circle.
  have hcod : ∀ᶠ z in codiscreteWithin (sphere (0 : ℂ) |r|), g z ≠ 0 :=
    codiscreteWithin_mono hsph ((hg.eqOn_zero_or_eventually_ne_zero_of_preconnected
      (convex_ball (0 : ℂ) 1).isPreconnected).resolve_left fun h => hgz₀ (h hz₀))
  have hθ : ∀ᵐ θ : ℝ ∂angularMeasure, g (circleMap 0 r θ) ≠ 0 := by
    have h : ∀ᵐ θ : ℝ ∂(volume.restrict (Ico 0 (2 * π))), g (circleMap 0 r θ) ≠ 0 :=
      ae_restrict_le_codiscreteWithin measurableSet_Ico
        (codiscreteWithin_mono (subset_univ _) (circleMap_preimage_codiscrete hr0 hcod))
    exact Measure.ae_smul_measure h _
  refine withBotRadialMean_eq_circleAverage ?_
    (AnalyticOnNhd.meromorphicOn (hg.mono hsph)).circleIntegrable_log_norm
  filter_upwards [hθ] with θ hθ
  have hcm : circleMap 0 r θ = (r : ℂ) * exp (I * θ) := by
    simp [circleMap, mul_comm]
  rw [hcm] at hθ
  simp [logNormBot, hθ]



/-!
### properties of the Poisson modification

For a subharmonic `v` on the unit disc with `v ≢ ⊥` and `0 < r < 1`, the Poisson modification
`v_r = poissonModification v r` is again subharmonic on the disc, is harmonic on `‖z‖ < r`,
dominates `v` pointwise, and increases with `r`.
-/

/-- Scale invariance of the Poisson kernel, relating the kernel of the circle of radius `r` to the
normalization used in `poissonModification`. -/
private lemma poissonKernel_zero_div_eq {r : ℝ} (hr : 0 < r) (z : ℂ) (θ : ℝ) :
    poissonKernel 0 (z / r) (exp (I * θ)) = poissonKernel 0 z (r * exp (I * θ)) := by
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hsub : (r : ℂ) * exp (I * θ) - z = r * (exp (I * θ) - z / r) := by field_simp
  have hnum : ‖(r : ℂ) * exp (I * θ)‖ ^ 2 - ‖z‖ ^ 2 =
      r ^ 2 * (‖exp (I * (θ : ℂ))‖ ^ 2 - ‖z / r‖ ^ 2) := by
    rw [norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg hr.le]
    field_simp
  simp only [poissonKernel_def, sub_zero]
  rw [hsub, hnum, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le, mul_pow,
    mul_div_mul_left _ _ (pow_ne_zero 2 hr.ne')]

/-- Garnett I.6.4 on circles centred at the origin: a subharmonic function `v ≢ ⊥` on the unit
disc is finite almost everywhere on each circle of radius `0 < r < 1`, and integrable there. -/
theorem ae_ne_bot_and_circleIntegrable_unbotD_of_subharmonicOn {v : ℂ → WithBot ℝ} {r : ℝ}
    (hv : SubharmonicOn v (ball 0 1)) (hv_ne : ∃ z ∈ ball (0 : ℂ) 1, v z ≠ ⊥)
    (hr : 0 < r ∧ r < 1) :
    (∀ᵐ θ : ℝ ∂angularMeasure, v (r * exp (I * θ)) ≠ ⊥) ∧
      CircleIntegrable (fun ζ => (v ζ).unbotD 0) 0 r := by
  sorry

/-- The Poisson modification of a subharmonic function is subharmonic on the
unit disc. -/
theorem subharmonicOn_poissonModification {v : ℂ → WithBot ℝ} {r : ℝ}
    (hv : SubharmonicOn v (ball 0 1)) (hv_ne : ∃ z ∈ ball (0 : ℂ) 1, v z ≠ ⊥)
    (hr : 0 < r ∧ r < 1) :
    SubharmonicOn (poissonModification v r) (ball 0 1) := by
  sorry

/-- The Poisson modification is harmonic on the open disc of radius `r`. -/
theorem harmonicOnNhdWithBot_poissonModification {v : ℂ → WithBot ℝ} {r : ℝ}
    (hv : SubharmonicOn v (ball 0 1)) (hv_ne : ∃ z ∈ ball (0 : ℂ) 1, v z ≠ ⊥)
    (hr : 0 < r ∧ r < 1) :
    HarmonicOnNhdWithBot (poissonModification v r) (ball 0 r) := by
  obtain ⟨hne, hk⟩ := ae_ne_bot_and_circleIntegrable_unbotD_of_subharmonicOn hv hv_ne hr
  set k : ℂ → ℝ := fun ζ => (v ζ).unbotD 0 with hk_def
  have hcm (θ : ℝ) : circleMap 0 r θ = (r : ℂ) * exp (I * θ) := by
    simp [circleMap, mul_comm]
  have hσ : circleMeasure 0 r (sphere (0 : ℂ) r)ᶜ = 0 := circleMeasure_compl_sphere hr.1.le
  have hkσ : Integrable k (circleMeasure 0 r) := hk.integrable_circleMeasure
  -- The Poisson integral of the `L¹` boundary data is harmonic; it remains to identify it.
  refine ⟨fun z => P[0; k ∂ᵥcircleMeasure 0 r] z,
    harmonicOnNhd_poissonIntegral_withDensityᵥ hσ hkσ, fun z hz => ?_⟩
  have hL : poissonModification v r z = ∫ᴮ θ, poissonKernel 0 (z / r) (exp (I * θ)) *
      v (r * exp (I * θ)) ∂angularMeasure :=
    ite_eq_right (not_le.2 (mem_ball_zero_iff.1 hz))
  -- The kernel is bounded on the circle, so kernel times data is integrable.
  have hPkσ : Integrable (fun ζ => poissonKernel 0 z ζ * k ζ) (circleMeasure 0 r) := by
    refine hkσ.bdd_mul (c := (r + ‖z - 0‖) / (r - ‖z - 0‖))
      (ContinuousOn.integrable_circleMeasure hr.1.le
        (continuousOn_poissonKernel_right_of_mem_ball hz)).aestronglyMeasurable ?_
    filter_upwards [ae_mem_sphere_circleMeasure (c := (0 : ℂ)) hr.1.le] with ζ hζ
    rw [Real.norm_of_nonneg (poissonKernel_nonneg hz hζ)]
    exact poissonKernel_le_of_mem_ball hz hζ
  have hPkθ : Integrable (fun θ : ℝ => poissonKernel 0 z (circleMap 0 r θ) *
      k (circleMap 0 r θ)) angularMeasure :=
    (integrable_map_measure (μ := angularMeasure) (f := circleMap 0 r)
      hPkσ.aestronglyMeasurable (continuous_circleMap 0 r).aemeasurable).1 hPkσ
  rw [hL]
  beta_reduce
  rw [poissonIntegral_withDensityᵥ hσ hz hkσ,
    integral_circleMeasure_eq_integral_angularMeasure (by simpa using hPkσ.aestronglyMeasurable)]
  refine withBotIntegral_eq_coe_of_ae_eq ?_ (by simpa using hPkθ)
  filter_upwards [hne] with θ hθ
  obtain ⟨a, ha⟩ := WithBot.ne_bot_iff_exists.1 hθ
  rw [poissonKernel_zero_div_eq hr.1, hcm, smul_eq_mul, hk_def]
  simp only [← ha, WithBot.unbotD_coe, WithBot.coe_mul]

/-- The Poisson modification dominates the original function pointwise on the
disc. -/
theorem le_poissonModification {v : ℂ → WithBot ℝ} {r : ℝ}
    (hv : SubharmonicOn v (ball 0 1)) (hv_ne : ∃ z ∈ ball (0 : ℂ) 1, v z ≠ ⊥)
    (hr : 0 < r ∧ r < 1) :
    ∀ z ∈ ball 0 1, v z ≤ poissonModification v r z := by
  sorry

/-- If `h ≤ U` on the circle of radius `r` and `U` is harmonic on the closed disc, then the Poisson
integral of `h` over that circle is at most `U` inside: `P[h] ≤ P[U] = U`. -/
private lemma withBotIntegral_poissonKernel_mul_le {h : ℂ → WithBot ℝ} {U : ℂ → ℝ} {r : ℝ}
    {z : ℂ} (hr : 0 < r) (hU : InnerProductSpace.HarmonicOnNhd U (closedBall 0 r))
    (hle : ∀ ζ ∈ sphere (0 : ℂ) r, h ζ ≤ U ζ) (hz : z ∈ ball (0 : ℂ) r) :
    ∫ᴮ θ, poissonKernel 0 (z / r) (exp (I * θ)) * h (r * exp (I * θ)) ∂angularMeasure ≤ U z := by
  have hcm (θ : ℝ) : circleMap 0 r θ = (r : ℂ) * exp (I * θ) := by
    simp [circleMap, mul_comm]
  have hmem (θ : ℝ) : (r : ℂ) * exp (I * θ) ∈ sphere (0 : ℂ) r := by
    rw [← hcm]
    exact circleMap_mem_sphere 0 hr.le θ
  -- The Poisson formula for `U` on the circle of radius `r`, in angular form.
  have hG : CircleIntegrable (fun ζ => poissonKernel 0 z ζ * U ζ) 0 r :=
    ((continuousOn_poissonKernel_right_of_mem_ball hz).mul
      (hU.continuousOn.mono sphere_subset_closedBall)).circleIntegrable hr.le
  have hIco : IntegrableOn (fun θ : ℝ => poissonKernel 0 z (circleMap 0 r θ) *
      U (circleMap 0 r θ)) (Ico 0 (2 * π)) volume := by
    rw [← intervalIntegrable_iff_integrableOn_Ico_of_le (by positivity)]
    exact hG
  have hint : Integrable (fun θ : ℝ => poissonKernel 0 (z / r) (exp (I * θ)) *
      U (r * exp (I * θ))) angularMeasure := by
    unfold angularMeasure
    simpa only [hcm, ← poissonKernel_zero_div_eq hr] using
      hIco.smul_measure ENNReal.ofReal_ne_top
  have hformula : ∫ θ, poissonKernel 0 (z / r) (exp (I * θ)) * U (r * exp (I * θ))
      ∂angularMeasure = U z := by
    have h1 : circleAverage (fun ζ => poissonKernel 0 z ζ * U ζ) 0 r = U z := by
      simpa [Pi.smul_apply', smul_eq_mul, Pi.mul_def] using
        InnerProductSpace.HarmonicOnNhd.circleAverage_poissonKernel_smul hU hz
    rw [← h1, circleAverage_eq_integral_circleMeasure hG,
      integral_circleMeasure_eq_integral_angularMeasure hG.aestronglyMeasurable_circleMeasure]
    simp only [hcm, ← poissonKernel_zero_div_eq hr]
  -- Compare the integrands pointwise, using positivity of the kernel.
  have hpos (θ : ℝ) : 0 < poissonKernel 0 (z / r) (exp (I * θ)) := by
    rw [poissonKernel_zero_div_eq hr]
    have hz' : ‖z‖ < r := mem_ball_zero_iff.1 hz
    refine lt_of_lt_of_le ?_ (le_poissonKernel_of_mem_ball hz (hmem θ))
    rw [sub_zero]
    exact div_pos (by linarith) (by linarith [norm_nonneg z])
  have hmono : ∫ᴮ θ, poissonKernel 0 (z / r) (exp (I * θ)) * h (r * exp (I * θ))
      ∂angularMeasure ≤ ∫ᴮ θ, ((poissonKernel 0 (z / r) (exp (I * θ)) *
        U (r * exp (I * θ)) : ℝ) : WithBot ℝ) ∂angularMeasure := by
    refine withBotIntegral_mono (Eventually.of_forall fun θ => ?_) (by simpa using hint)
    rw [WithBot.coe_mul]
    exact WithBot.const_mul_le_const_mul_of_pos (hpos θ) (hle _ (hmem θ))
  have hcoe := withBotIntegral_coe (fun θ : ℝ => poissonKernel 0 (z / r) (exp (I * θ)) *
    U (r * exp (I * θ))) univ angularMeasure hint.integrableOn
  rw [Measure.restrict_univ, hformula] at hcoe
  exact hmono.trans_eq hcoe

/-- The Poisson modification is increasing in the radius `r`. -/
theorem poissonModification_mono {v : ℂ → WithBot ℝ}
    (hv : SubharmonicOn v (ball 0 1)) (hv_ne : ∃ z ∈ ball (0 : ℂ) 1, v z ≠ ⊥)
    {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : r₂ < 1) (hle : r₁ ≤ r₂) :
    ∀ z ∈ ball 0 1, poissonModification v r₁ z ≤ poissonModification v r₂ z := by
  intro z hz
  rcases hle.eq_or_lt with rfl | hlt
  · exact le_rfl
  have hr₂' : 0 < r₂ ∧ r₂ < 1 := ⟨hr₁.trans hlt, hr₂⟩
  by_cases h1 : r₁ ≤ ‖z‖
  · -- Outside the smaller disc, `v_{r₁} = v ≤ v_{r₂}`.
    have hL : poissonModification v r₁ z = v z := ite_eq_left h1
    rw [hL]
    exact le_poissonModification hv hv_ne hr₂' z hz
  · -- Inside it, `v ≤ v_{r₂}` on the circle of radius `r₁` and `v_{r₂}` is harmonic there.
    obtain ⟨w, hw, hw_eq⟩ := harmonicOnNhdWithBot_poissonModification hv hv_ne hr₂'
    have hL : poissonModification v r₁ z = ∫ᴮ θ, poissonKernel 0 (z / r₁) (exp (I * θ)) *
        v (r₁ * exp (I * θ)) ∂angularMeasure := ite_eq_right h1
    have hz₁ : ‖z‖ < r₁ := not_le.1 h1
    rw [hL, hw_eq z (mem_ball_zero_iff.2 (hz₁.trans hlt))]
    refine withBotIntegral_poissonKernel_mul_le hr₁ (hw.mono (closedBall_subset_ball hlt))
      (fun ζ hζ => ?_) (mem_ball_zero_iff.2 hz₁)
    have hζ' : ‖ζ‖ = r₁ := mem_sphere_zero_iff_norm.1 hζ
    exact (le_poissonModification hv hv_ne hr₂' ζ
      (mem_ball_zero_iff.2 (by linarith))).trans_eq
      (hw_eq ζ (mem_ball_zero_iff.2 (by linarith)))

/-- Every harmonic majorant of `v` on the unit disc also dominates the Poisson modification `v_r`:
inside `‖z‖ < r`, `v ≤ U` on the circle gives `P[v] ≤ P[U] = U`. -/
theorem poissonModification_le_of_isHarmonicMajorant {v : ℂ → WithBot ℝ} {U : ℂ → ℝ} {r : ℝ}
    (hU : IsHarmonicMajorant U v (ball 0 1)) (hr : 0 < r ∧ r < 1) :
    ∀ z ∈ ball 0 1, poissonModification v r z ≤ U z := by
  intro z hz
  by_cases h1 : r ≤ ‖z‖
  · have hL : poissonModification v r z = v z := ite_eq_left h1
    rw [hL]
    exact hU.2 z hz
  · have hL : poissonModification v r z = ∫ᴮ θ, poissonKernel 0 (z / r) (exp (I * θ)) *
        v (r * exp (I * θ)) ∂angularMeasure := ite_eq_right h1
    rw [hL]
    refine withBotIntegral_poissonKernel_mul_le hr.1 (hU.1.mono (closedBall_subset_ball hr.2))
      (fun ζ hζ => hU.2 ζ (mem_ball_zero_iff.2 ?_)) (mem_ball_zero_iff.2 (not_le.1 h1))
    rw [mem_sphere_zero_iff_norm.1 hζ]
    exact hr.2

/-- The core of Garnett I.6.7: if the values `v_r(0)` are bounded above, then the Poisson
modifications `v_r` increase to a harmonic majorant `u` of `v`. By Harnack's theorem, applied on
each smaller disc to a sequence of radii increasing to `1`. -/
private theorem exists_isHarmonicMajorant_tendsto_poissonModification_of_le
    {v : ℂ → WithBot ℝ} (hv : SubharmonicOn v (ball 0 1)) (hv_ne : ∃ z ∈ ball 0 1, v z ≠ ⊥)
    {M : ℝ} (hM : ∀ r ∈ Ioo (0 : ℝ) 1, poissonModification v r 0 ≤ M) :
    ∃ u : ℂ → ℝ, IsHarmonicMajorant u v (ball 0 1) ∧ ∀ z ∈ ball 0 1,
      Tendsto (fun r => poissonModification v r z) (𝓝[<] 1) (𝓝 (u z)) := by
  -- Real representatives of the Poisson modifications.
  set F : ℝ → ℂ → ℝ := fun r z => (poissonModification v r z).unbotD 0 with hF
  have hF_eq : ∀ r ∈ Ioo (0 : ℝ) 1, ∀ z ∈ ball (0 : ℂ) r,
      poissonModification v r z = F r z := by
    intro r hr z hz
    obtain ⟨w, -, hw⟩ := harmonicOnNhdWithBot_poissonModification hv hv_ne hr
    simp [F, hw z hz]
  have hF_harm : ∀ r ∈ Ioo (0 : ℝ) 1, InnerProductSpace.HarmonicOnNhd (F r) (ball 0 r) := by
    intro r hr x hx
    obtain ⟨w, hw, hwv⟩ := harmonicOnNhdWithBot_poissonModification hv hv_ne hr
    refine (InnerProductSpace.harmonicAt_congr_nhds
      (Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hx) fun y hy => ?_)).1 (hw x hx)
    simp [F, hwv y hy]
  have hF_mono : ∀ (z : ℂ) (r₁ r₂ : ℝ), ‖z‖ < r₁ → r₁ ≤ r₂ → r₂ < 1 → F r₁ z ≤ F r₂ z := by
    intro z r₁ r₂ h₁ h₁₂ h₂
    have hr₁ : r₁ ∈ Ioo (0 : ℝ) 1 := ⟨(norm_nonneg z).trans_lt h₁, h₁₂.trans_lt h₂⟩
    have hr₂ : r₂ ∈ Ioo (0 : ℝ) 1 := ⟨hr₁.1.trans_le h₁₂, h₂⟩
    have h := poissonModification_mono hv hv_ne hr₁.1 h₂ h₁₂ z
      (mem_ball_zero_iff.2 (h₁.trans hr₁.2))
    rwa [hF_eq r₁ hr₁ z (mem_ball_zero_iff.2 h₁),
      hF_eq r₂ hr₂ z (mem_ball_zero_iff.2 (h₁.trans_le h₁₂)), WithBot.coe_le_coe] at h
  -- For `ρ < 1`, the radii `rs ρ n = 1 - (1 - ρ) / (n + 2)` increase from above `ρ` to `1`.
  set rs : ℝ → ℕ → ℝ := fun ρ n => 1 - (1 - ρ) / ((n : ℝ) + 2) with hrs
  have hrs_lt : ∀ ρ < 1, ∀ n, ρ < rs ρ n ∧ rs ρ n < 1 := by
    intro ρ hρ n
    have h0 : 0 < 1 - ρ := sub_pos.2 hρ
    have hn : (1 : ℝ) < (n : ℝ) + 2 := by linarith [n.cast_nonneg (α := ℝ)]
    have h1 : (1 - ρ) / ((n : ℝ) + 2) < 1 - ρ := div_lt_self h0 hn
    have h2 : 0 < (1 - ρ) / ((n : ℝ) + 2) := div_pos h0 (by linarith)
    constructor <;> simp only [rs] <;> linarith
  have hrs_mono : ∀ ρ < 1, Monotone (rs ρ) := by
    intro ρ hρ a b hab
    simp only [rs]
    gcongr
  have hrs_tendsto : ∀ ρ < 1, Tendsto (rs ρ) atTop (𝓝[<] 1) := by
    intro ρ hρ
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => (hrs_lt ρ hρ n).2⟩
    have h : Tendsto (fun n : ℕ => (1 - ρ) / ((n : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
    simpa [rs] using (tendsto_const_nhds (x := (1 : ℝ))).sub h
  -- Harnack's theorem on each smaller disc `ball 0 ρ`.
  have hseq_mono : ∀ ρ < 1, ∀ z : ℂ, ‖z‖ < ρ → Monotone fun n => F (rs ρ n) z :=
    fun ρ hρ z hz a b hab =>
      hF_mono z _ _ (hz.trans (hrs_lt ρ hρ a).1) (hrs_mono ρ hρ hab) (hrs_lt ρ hρ b).2
  have hA : ∀ ρ ∈ Ioo (0 : ℝ) 1, ∃ g : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd g (ball 0 ρ) ∧
      ∀ z ∈ ball (0 : ℂ) ρ, Tendsto (fun n => F (rs ρ n) z) atTop (𝓝 (g z)) := by
    intro ρ hρ
    have hrsρ : ∀ n, rs ρ n ∈ Ioo (0 : ℝ) 1 :=
      fun n => ⟨hρ.1.trans (hrs_lt ρ hρ.2 n).1, (hrs_lt ρ hρ.2 n).2⟩
    have h0 : (0 : ℂ) ∈ ball (0 : ℂ) ρ := mem_ball_self hρ.1
    obtain ⟨g, hg, hconv⟩ :=
      InnerProductSpace.exists_harmonicOnNhd_tendstoLocallyUniformlyOn_of_monotone
        (f := fun n => F (rs ρ n)) isOpen_ball (convex_ball (0 : ℂ) ρ).isPreconnected
        (fun n => (hF_harm _ (hrsρ n)).mono (ball_subset_ball (hrs_lt ρ hρ.2 n).1.le))
        (fun z hz => hseq_mono ρ hρ.2 z (mem_ball_zero_iff.1 hz)) h0
        ⟨M, by
          rintro _ ⟨n, rfl⟩
          have h := hM _ (hrsρ n)
          rwa [hF_eq _ (hrsρ n) 0 (mem_ball_self (hrsρ n).1), WithBot.coe_le_coe] at h⟩
    exact ⟨g, hg, fun z hz => hconv.tendsto_at hz⟩
  -- Pointwise, `r ↦ v_r z` converges as `r → 1⁻`, being increasing and bounded.
  have hB : ∀ z ∈ ball (0 : ℂ) 1, ∃ L, Tendsto (fun r => F r z) (𝓝[<] 1) (𝓝 L) := by
    intro z hz
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
    set ρ := (‖z‖ + 1) / 2 with hρ_def
    have hzρ : ‖z‖ < ρ := by linarith
    have hρ : ρ ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [norm_nonneg z], by linarith⟩
    obtain ⟨g, -, hg⟩ := hA ρ hρ
    have hgz := hg z (mem_ball_zero_iff.2 hzρ)
    have hmonoG : MonotoneOn (fun r => F (max r ρ) z) (Iio 1) := fun a _ b hb hab =>
      hF_mono z _ _ (hzρ.trans_le (le_max_right _ _)) (max_le_max_right ρ hab) (max_lt hb hρ.2)
    have hbdd : BddAbove ((fun r => F (max r ρ) z) '' Iio 1) := by
      refine ⟨g z, ?_⟩
      rintro _ ⟨s, hs, rfl⟩
      obtain ⟨n, hn⟩ := (((hrs_tendsto ρ hρ.2).mono_right nhdsWithin_le_nhds).eventually
        (lt_mem_nhds (max_lt hs hρ.2))).exists
      exact (hF_mono z _ _ (hzρ.trans_le (le_max_right _ _)) hn.le (hrs_lt ρ hρ.2 n).2).trans
        ((hseq_mono ρ hρ.2 z hzρ).ge_of_tendsto hgz n)
    refine ⟨_, (hmonoG.tendsto_nhdsLT hbdd).congr' ?_⟩
    filter_upwards [Ioo_mem_nhdsLT hρ.2] with r hr
    simp [max_eq_left hr.1.le]
  set u : ℂ → ℝ := fun z => limUnder (𝓝[<] 1) fun r => F r z with hu
  have hu_tendsto : ∀ z ∈ ball (0 : ℂ) 1, Tendsto (fun r => F r z) (𝓝[<] 1) (𝓝 (u z)) :=
    fun z hz => tendsto_nhds_limUnder (hB z hz)
  -- `u` agrees near each point with a Harnack limit, hence is harmonic.
  have hu_harm : InnerProductSpace.HarmonicOnNhd u (ball 0 1) := by
    intro z₀ hz₀
    have hz1 : ‖z₀‖ < 1 := mem_ball_zero_iff.1 hz₀
    set ρ := (‖z₀‖ + 1) / 2 with hρ_def
    have hρ : ρ ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [norm_nonneg z₀], by linarith⟩
    have hz₀ρ : z₀ ∈ ball (0 : ℂ) ρ := mem_ball_zero_iff.2 (by linarith)
    obtain ⟨g, hg_harm, hg⟩ := hA ρ hρ
    have heq : ∀ z ∈ ball (0 : ℂ) ρ, g z = u z := fun z hz =>
      tendsto_nhds_unique (hg z hz)
        ((hu_tendsto z (ball_subset_ball hρ.2.le hz)).comp (hrs_tendsto ρ hρ.2))
    exact (InnerProductSpace.harmonicAt_congr_nhds
      (Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hz₀ρ) heq)).1 (hg_harm z₀ hz₀ρ)
  -- `u` dominates every `v_r`, hence `v`.
  have hu_le : ∀ z ∈ ball (0 : ℂ) 1, v z ≤ u z := by
    intro z hz
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
    set ρ := (‖z‖ + 1) / 2 with hρ_def
    have hzρ : ‖z‖ < ρ := by linarith
    have hρ : ρ ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [norm_nonneg z], by linarith⟩
    have h := le_poissonModification hv hv_ne hρ z hz
    rw [hF_eq ρ hρ z (mem_ball_zero_iff.2 hzρ)] at h
    refine h.trans (WithBot.coe_le_coe.2 (ge_of_tendsto (hu_tendsto z hz) ?_))
    filter_upwards [Ioo_mem_nhdsLT hρ.2] with r hr
    exact hF_mono z ρ r hzρ hr.1.le hr.2
  refine ⟨u, ⟨hu_harm, hu_le⟩, fun z hz => ?_⟩
  refine ((WithBot.continuous_coe.tendsto _).comp (hu_tendsto z hz)).congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (mem_ball_zero_iff.1 hz)] with r hr
  exact (hF_eq r ⟨(norm_nonneg z).trans_lt hr.1, hr.2⟩ z (mem_ball_zero_iff.2 hr.1)).symm

/-- The coercion `WithBot ℝ → EReal` reflects and preserves `≤` against a real number. -/
private lemma coe_eReal_le_coe_iff {x : WithBot ℝ} {M : ℝ} :
    (x : EReal) ≤ (M : EReal) ↔ x ≤ (M : WithBot ℝ) := by
  induction x using WithBot.recBotCoe <;> simp

/- A real-valued subharmonic function on the unit disc has a harmonic majorant if and only if
its radial means are uniformly bounded above. -/
theorem hasHarmonicMajorant_iff_radialMean_bddAbove
    {v : ℂ → WithBot ℝ} (hv : SubharmonicOn v (ball 0 1)) :
    HasHarmonicMajorant v (ball 0 1) ↔
      (⨆ (r : ℝ) (_ : r ∈ Ioo 0 1), (withBotRadialMean v r : EReal)) < ∞ := by
  constructor
  · rintro ⟨U, hU⟩
    refine lt_of_le_of_lt (iSup₂_le fun r hr => ?_) (EReal.coe_lt_top (U 0))
    rw [coe_eReal_le_coe_iff, ← poissonModification_zero_eq_withBotRadialMean v hr.1]
    exact poissonModification_le_of_isHarmonicMajorant hU hr 0 (mem_ball_self one_pos)
  · intro h
    by_cases hv_ne : ∃ z ∈ ball (0 : ℂ) 1, v z ≠ ⊥
    · obtain ⟨M, hM, -⟩ := EReal.lt_iff_exists_real_btwn.1 h
      have hle : ∀ r ∈ Ioo (0 : ℝ) 1, poissonModification v r 0 ≤ M := by
        intro r hr
        rw [poissonModification_zero_eq_withBotRadialMean v hr.1, ← coe_eReal_le_coe_iff]
        exact (le_iSup₂ (f := fun (r : ℝ) (_ : r ∈ Ioo 0 1) => (withBotRadialMean v r : EReal))
          r hr).trans hM.le
      obtain ⟨u, hu, -⟩ := exists_isHarmonicMajorant_tendsto_poissonModification_of_le hv hv_ne hle
      exact ⟨u, hu⟩
    · push Not at hv_ne
      exact ⟨fun _ => 0, InnerProductSpace.harmonicOnNhd_const 0,
        fun z hz => by simp [hv_ne z hz]⟩


/-- When a subharmonic function `v ≢ ⊥` on the unit disc has a harmonic
majorant, its least harmonic majorant `u` is recovered as the pointwise radial limit of the Poisson
modifications: `u z = lim_{r → 1⁻} v_r z`. The hypothesis `v ≢ ⊥` is necessary: `⊥` has every
harmonic function as a majorant, hence no least one. -/
theorem exists_isLeastHarmonicMajorant_tendsto_poissonModification {v : ℂ → WithBot ℝ}
  (hv : SubharmonicOn v (ball 0 1)) (hv_ne : ∃ z ∈ ball 0 1, v z ≠ ⊥)
  (hmaj : HasHarmonicMajorant v (ball 0 1)) :
    ∃ u : ℂ → ℝ, IsLeastHarmonicMajorant u v (ball 0 1) ∧ ∀ z ∈ ball 0 1,
      Tendsto (fun r => poissonModification v r z) (𝓝[<] 1) (𝓝 (u z) ) := by
  obtain ⟨U, hU⟩ := hmaj
  obtain ⟨u, hu, htend⟩ := exists_isHarmonicMajorant_tendsto_poissonModification_of_le hv hv_ne
    fun r hr => poissonModification_le_of_isHarmonicMajorant hU hr 0 (mem_ball_self one_pos)
  -- Every harmonic majorant dominates each `v_r`, hence their limit `u`.
  refine ⟨u, ⟨hu, fun U' hU' z hz => WithBot.coe_le_coe.1 (le_of_tendsto (htend z hz) ?_)⟩,
    htend⟩
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 from one_pos)] with r hr
  exact poissonModification_le_of_isHarmonicMajorant hU' hr z hz






end Subharmonic
