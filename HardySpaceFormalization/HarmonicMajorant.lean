import HardySpaceFormalization.Subharmonic
import HardySpaceFormalization.withBotIntegral
import Mathlib.Analysis.Complex.Poisson
import Mathlib.Topology.Order.WithTop
import Mathlib.Analysis.SpecialFunctions.Integrability.Log



open scoped Real ENNReal NNReal
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
  sorry

/-- The Poisson modification dominates the original function pointwise on the
disc. -/
theorem le_poissonModification {v : ℂ → WithBot ℝ} {r : ℝ}
    (hv : SubharmonicOn v (ball 0 1)) (hv_ne : ∃ z ∈ ball (0 : ℂ) 1, v z ≠ ⊥)
    (hr : 0 < r ∧ r < 1) :
    ∀ z ∈ ball 0 1, v z ≤ poissonModification v r z := by
  sorry

/-- The Poisson modification is increasing in the radius `r`. -/
theorem poissonModification_mono {v : ℂ → WithBot ℝ}
    (hv : SubharmonicOn v (ball 0 1)) (hv_ne : ∃ z ∈ ball (0 : ℂ) 1, v z ≠ ⊥)
    {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : r₂ < 1) (hle : r₁ ≤ r₂) :
    ∀ z ∈ ball 0 1, poissonModification v r₁ z ≤ poissonModification v r₂ z := by
  sorry



/- A real-valued subharmonic function on the unit disc has a harmonic majorant if and only if
its radial means are uniformly bounded above. -/
theorem hasHarmonicMajorant_iff_radialMean_bddAbove
    {v : ℂ → WithBot ℝ} (hv : SubharmonicOn v (ball 0 1)) :
    HasHarmonicMajorant v (ball 0 1) ↔
      (⨆ (r : ℝ) (_ : r ∈ Ioo 0 1), (withBotRadialMean v r : EReal)) < ∞ := by
  sorry


/-- When a subharmonic function `v ≢ ⊥` on the unit disc has a harmonic
majorant, its least harmonic majorant `u` is recovered as the pointwise radial limit of the Poisson
modifications: `u z = lim_{r → 1⁻} v_r z`. The hypothesis `v ≢ ⊥` is necessary: `⊥` has every
harmonic function as a majorant, hence no least one. -/
theorem exists_isLeastHarmonicMajorant_tendsto_poissonModification {v : ℂ → WithBot ℝ}
  (hv : SubharmonicOn v (ball 0 1)) (hv_ne : ∃ z ∈ ball 0 1, v z ≠ ⊥)
  (hmaj : HasHarmonicMajorant v (ball 0 1)) :
    ∃ u : ℂ → ℝ, IsLeastHarmonicMajorant u v (ball 0 1) ∧ ∀ z ∈ ball 0 1,
      Tendsto (fun r => poissonModification v r z) (𝓝[<] 1) (𝓝 (u z) ) := by
  sorry






end Subharmonic
