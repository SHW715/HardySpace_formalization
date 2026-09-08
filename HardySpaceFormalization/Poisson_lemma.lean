import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions



-- # In this file, I will put some more lemmas complementing `Mathlib.Analysis.Complex.Poisson`.

-- remained to finish: Prove Poisson extension theorem.

noncomputable section

open Complex Metric Real Set MeasureTheory
open scoped Topology ENNReal

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : ℂ → E} {R : ℝ} {w c : ℂ} {s : Set ℂ}



/-!
### Basic properties of the Poisson kernel

Measurability, nonnegativity and the uniform bound over the boundary circle at an interior point.
-/

/-- The Poisson kernel is measurable in the boundary variable. -/
theorem measurable_poissonKernel (c w : ℂ) : Measurable (fun z : ℂ => poissonKernel c w z) := by
  unfold poissonKernel
  fun_prop

/-- The Poisson kernel is nonnegative for an interior point and a boundary point. -/
theorem poissonKernel_nonneg (hw : w ∈ ball c R) {z : ℂ} (hz : z ∈ sphere c R) :
    0 ≤ poissonKernel c w z := by
  have hz_norm : ‖z - c‖ = R := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
  have hw_norm : ‖w - c‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hw
  rw [poissonKernel_def]
  refine div_nonneg ?_ (by positivity)
  nlinarith [norm_nonneg (w - c)]

/-- Uniform bound for the Poisson kernel over the boundary circle, at an interior point. -/
theorem poissonKernel_le_of_mem_ball (hw : w ∈ ball c R) {z : ℂ} (hz : z ∈ sphere c R) :
    poissonKernel c w z ≤ (R + ‖w - c‖) / (R - ‖w - c‖) := by
  simpa [poissonKernel_eq_re_herglotzRieszKernel, Function.comp_apply, herglotzRieszKernel_def]
    using re_herglotzRieszKernel_le hz hw

/-- Uniform *lower* bound for the Poisson kernel over the boundary circle, at an interior point.
Together with `poissonKernel_le_of_mem_ball` this is the two-sided estimate
`(R - ‖w - c‖)/(R + ‖w - c‖) ≤ P ≤ (R + ‖w - c‖)/(R - ‖w - c‖)` underlying Harnack's inequality. -/
theorem le_poissonKernel_of_mem_ball (hw : w ∈ ball c R) {z : ℂ} (hz : z ∈ sphere c R) :
    (R - ‖w - c‖) / (R + ‖w - c‖) ≤ poissonKernel c w z := by
  simpa [poissonKernel_eq_re_herglotzRieszKernel, Function.comp_apply, herglotzRieszKernel_def]
    using le_re_herglotzRieszKernel hz hw

/-- Norm form of `poissonKernel_le_of_mem_ball`, for use with dominated-convergence and
boundedness lemmas. -/
theorem norm_poissonKernel_le_of_mem_ball (hw : w ∈ ball c R) {z : ℂ} (hz : z ∈ sphere c R) :
    ‖poissonKernel c w z‖ ≤ (R + ‖w - c‖) / (R - ‖w - c‖) := by
  rw [Real.norm_eq_abs, abs_of_nonneg (poissonKernel_nonneg hw hz)]
  exact poissonKernel_le_of_mem_ball hw hz



/-!
### The Herglotz-Riesz kernel

Estimates, differentiability and measurability of the Herglotz-Riesz kernel.  Everything about the
Poisson kernel below is obtained from these by taking real parts.
-/

/-- For a fixed boundary point `w`, the Herglotz-Riesz kernel is analytic as a function of the
interior point `z`. -/
theorem analyticOn_herglotzRieszKernel (hw : w ∈ sphere c R) :
    AnalyticOn ℂ (fun z : ℂ => herglotzRieszKernel c z w) (ball c R) := by
  intro z hz
  have hden : (w - c) - (z - c) ≠ 0 := by
    intro hden
    have hz_eq_w : w = z := by refine sub_left_injective (sub_eq_zero.mp hden)
    have hz_dist_lt : dist z c < R := by simpa [Metric.mem_ball] using hz
    have hw_dist : dist w c = R := by simpa [Metric.mem_sphere, dist_eq_norm] using hw
    simp_all
  apply AnalyticAt.analyticWithinAt
  unfold herglotzRieszKernel
  fun_prop (disch := assumption)

/-- Lower bound for the denominator of the Herglotz-Riesz kernel: for a boundary point `z` and an
interior point `w` at distance at most `ρ` from the centre, the denominator has norm at least
`R - ρ`. -/
theorem le_norm_sub_sub_of_mem_sphere {ρ : ℝ} {z : ℂ} (hz : z ∈ sphere c R) (hw : ‖w - c‖ ≤ ρ) :
    R - ρ ≤ ‖(z - c) - (w - c)‖ := by
  have hz_norm : ‖z - c‖ = R := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
  calc R - ρ ≤ ‖z - c‖ - ‖w - c‖ := by rw [hz_norm]; linarith
    _ ≤ ‖(z - c) - (w - c)‖ := norm_sub_norm_le _ _

/-- Uniform bound for the Herglotz-Riesz kernel over the boundary circle, for interior points at
distance at most `ρ < R` from the centre. -/
theorem norm_herglotzRieszKernel_le {ρ : ℝ} {z : ℂ} (hρ : ρ < R) (hz : z ∈ sphere c R)
    (hw : ‖w - c‖ ≤ ρ) :
    ‖herglotzRieszKernel c w z‖ ≤ (R + ρ) / (R - ρ) := by
  have hz_norm : ‖z - c‖ = R := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
  have hρ_nonneg : 0 ≤ ρ := (norm_nonneg _).trans hw
  have hpos : 0 < R - ρ := by linarith
  have hden : R - ρ ≤ ‖(z - c) - (w - c)‖ := le_norm_sub_sub_of_mem_sphere hz hw
  have hden_pos : 0 < ‖(z - c) - (w - c)‖ := hpos.trans_le hden
  have hnum : ‖(z - c) + (w - c)‖ ≤ R + ρ := by
    calc ‖(z - c) + (w - c)‖ ≤ ‖z - c‖ + ‖w - c‖ := norm_add_le _ _
      _ ≤ R + ρ := by rw [hz_norm]; linarith
  rw [herglotzRieszKernel_def, norm_div, div_le_div_iff₀ hden_pos hpos]
  have h₁ : ‖(z - c) + (w - c)‖ * (R - ρ) ≤ (R + ρ) * (R - ρ) :=
    mul_le_mul_of_nonneg_right hnum hpos.le
  have h₂ : (R + ρ) * (R - ρ) ≤ (R + ρ) * ‖(z - c) - (w - c)‖ :=
    mul_le_mul_of_nonneg_left hden (by linarith)
  linarith

/-- Bound for the derivative in the interior variable of the Herglotz-Riesz kernel. -/
theorem norm_deriv_herglotzRieszKernel_le {ρ : ℝ} {z : ℂ} (hρ : ρ < R) (hz : z ∈ sphere c R)
    (hw : ‖w - c‖ ≤ ρ) :
    ‖2 * (z - c) / ((z - c) - (w - c)) ^ 2‖ ≤ 2 * R / (R - ρ) ^ 2 := by
  have hz_norm : ‖z - c‖ = R := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
  have hρ_nonneg : 0 ≤ ρ := (norm_nonneg _).trans hw
  have hpos : 0 < R - ρ := by linarith
  have hden : R - ρ ≤ ‖(z - c) - (w - c)‖ := le_norm_sub_sub_of_mem_sphere hz hw
  have hden_pos : 0 < ‖(z - c) - (w - c)‖ := hpos.trans_le hden
  have hR_nonneg : 0 ≤ R := hz_norm ▸ norm_nonneg (z - c)
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [norm_div, norm_pow, norm_mul, h2, hz_norm,
    div_le_div_iff₀ (pow_pos hden_pos 2) (pow_pos hpos 2)]
  have hkey := mul_le_mul_of_nonneg_left (mul_self_le_mul_self hpos.le hden)
    (by linarith : (0 : ℝ) ≤ 2 * R)
  simp only [pow_two]
  linarith

/-- The Herglotz-Riesz kernel is complex differentiable in the interior variable, with the expected
derivative. -/
theorem hasDerivAt_herglotzRieszKernel {z : ℂ} (hzw : (z - c) - (w - c) ≠ 0) :
    HasDerivAt (fun x : ℂ => herglotzRieszKernel c x z)
      (2 * (z - c) / ((z - c) - (w - c)) ^ 2) w := by
  have h₁ : HasDerivAt (fun x : ℂ => (z - c) + (x - c)) 1 w := by
    simpa using ((hasDerivAt_id w).sub_const c).const_add (z - c)
  have h₂ : HasDerivAt (fun x : ℂ => (z - c) - (x - c)) (-1) w := by
    simpa using ((hasDerivAt_id w).sub_const c).const_sub (z - c)
  exact (h₁.div h₂ hzw).congr_deriv (by ring)

/-- The Herglotz-Riesz kernel is measurable in the boundary variable. -/
theorem measurable_herglotzRieszKernel (c x : ℂ) :
    Measurable (fun z : ℂ => herglotzRieszKernel c x z) := by
  unfold herglotzRieszKernel
  fun_prop

/-- For an interior point, the Herglotz-Riesz kernel is integrable against any finite measure
carried by the boundary circle. -/
theorem integrable_herglotzRieszKernel {μ : Measure ℂ} [IsFiniteMeasure μ]
    (hμ : μ (sphere c R)ᶜ = 0) (hw : w ∈ ball c R) :
    Integrable (fun z : ℂ => herglotzRieszKernel c w z) μ := by
  refine (integrable_const ((R + ‖w - c‖) / (R - ‖w - c‖))).mono'
    (measurable_herglotzRieszKernel c w).aestronglyMeasurable ?_
  filter_upwards [ae_iff.2 hμ] with z hz
  refine norm_herglotzRieszKernel_le ?_ hz le_rfl
  simpa [Metric.mem_ball, dist_eq_norm] using hw

/-- **The Herglotz-Riesz transform of a boundary measure is analytic.**  For a finite measure `μ`
carried by the circle `sphere c R`, the function
`w ↦ ∫ z, herglotzRieszKernel c w z ∂μ` is analytic on `ball c R`.

This is the point-mass case `harmonicOnNhd_poissonKernel` upgraded to a general measure; it is what
makes both the Poisson integral of a measure harmonic and the singular inner functions
`exp (-∫ (ζ + z) / (ζ - z) dσ)` analytic. -/
theorem analyticOnNhd_integral_herglotzRieszKernel {μ : Measure ℂ} [IsFiniteMeasure μ]
    (hμ : μ (sphere c R)ᶜ = 0) :
    AnalyticOnNhd ℂ (fun w : ℂ => ∫ z, herglotzRieszKernel c w z ∂μ) (ball c R) := by
  -- claude without review
  refine DifferentiableOn.analyticOnNhd ?_ isOpen_ball
  intro w₀ hw₀
  refine DifferentiableAt.differentiableWithinAt ?_
  have hw₀_norm : ‖w₀ - c‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hw₀
  set ε : ℝ := (R - ‖w₀ - c‖) / 2 with hε
  have hε_pos : 0 < ε := by simp only [hε]; linarith
  set ρ : ℝ := ‖w₀ - c‖ + ε with hρ
  have hρ_lt : ρ < R := by simp only [hρ, hε]; linarith
  -- every point of `ball w₀ ε` lies at distance at most `ρ` from the centre
  have hball : ∀ x ∈ ball w₀ ε, ‖x - c‖ ≤ ρ := by
    intro x hx
    have hx' : ‖x - w₀‖ < ε := by simpa [Metric.mem_ball, dist_eq_norm] using hx
    calc ‖x - c‖ = ‖(x - w₀) + (w₀ - c)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖x - w₀‖ + ‖w₀ - c‖ := norm_add_le _ _
      _ ≤ ρ := by simp only [hρ]; linarith
  have hae : ∀ᵐ z ∂μ, z ∈ sphere c R := ae_iff.2 hμ
  have hpos : 0 < R - ρ := by linarith
  -- the derivative of the kernel is uniformly bounded on `ball w₀ ε`
  have h_bound : ∀ᵐ z ∂μ, ∀ x ∈ ball w₀ ε,
      ‖2 * (z - c) / ((z - c) - (x - c)) ^ 2‖ ≤ 2 * R / (R - ρ) ^ 2 := by
    filter_upwards [hae] with z hz x hx
    exact norm_deriv_herglotzRieszKernel_le hρ_lt hz (hball x hx)
  -- and the kernel is differentiable there, the denominator being bounded away from zero
  have h_diff : ∀ᵐ z ∂μ, ∀ x ∈ ball w₀ ε,
      HasDerivAt (fun y : ℂ => herglotzRieszKernel c y z)
        (2 * (z - c) / ((z - c) - (x - c)) ^ 2) x := by
    filter_upwards [hae] with z hz x hx
    refine hasDerivAt_herglotzRieszKernel ?_
    exact norm_pos_iff.1 (hpos.trans_le (le_norm_sub_sub_of_mem_sphere (w := x) hz (hball x hx)))
  obtain ⟨-, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := fun x z : ℂ => herglotzRieszKernel c x z)
    (F' := fun x z : ℂ => 2 * (z - c) / ((z - c) - (x - c)) ^ 2)
    (bound := fun _ : ℂ => 2 * R / (R - ρ) ^ 2)
    (s := ball w₀ ε) (x₀ := w₀) (isOpen_ball.mem_nhds (mem_ball_self hε_pos))
    (Filter.Eventually.of_forall fun x =>
      (measurable_herglotzRieszKernel c x).aestronglyMeasurable)
    (integrable_herglotzRieszKernel hμ hw₀)
    (Measurable.aestronglyMeasurable (by fun_prop))
    h_bound (integrable_const _) h_diff
  exact hderiv.differentiableAt


/-- For a fixed boundary point `z`, the Poisson kernel is harmonic as a function of the interior
point `w`. -/
theorem harmonicOnNhd_poissonKernel (hw : w ∈ sphere c R) :
  InnerProductSpace.HarmonicOnNhd (fun z : ℂ => poissonKernel c z w) (ball c R) := by
  intro z hz
  have hker : InnerProductSpace.HarmonicAt (fun x : ℂ => (herglotzRieszKernel c x w).re) z :=
    ((analyticOn_herglotzRieszKernel hw).analyticAt (isOpen_ball.mem_nhds hz)).harmonicAt_re
  refine (InnerProductSpace.harmonicAt_congr_nhds ?_).2 hker
  exact Filter.Eventually.of_forall fun x => by
    have h := congrFun (poissonKernel_eq_re_herglotzRieszKernel (c := c) (w := x)) w
    simpa [Function.comp_apply] using h

/-- For a fixed interior point `w`, the Poisson kernel is continuous as a function of the
boundary variable. -/
theorem continuousOn_poissonKernel_right_of_mem_ball (hw : w ∈ ball c R) :
    ContinuousOn (fun z : ℂ => poissonKernel c w z) (sphere c R) := by
  -- codex after review
  unfold poissonKernel
  refine ContinuousOn.div ?_ ?_ ?_
  · fun_prop
  · fun_prop
  · intro z hz hden
    have hz_norm : ‖z - c‖ = R := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
    have hw_norm : ‖w - c‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hw
    have hzw : z = w := by
      refine sub_eq_zero.mp (norm_eq_zero.mp ?_)
      have hnorm_zero : ‖(z - c) - (w - c)‖ = 0 := sq_eq_zero_iff.mp hden
      simpa [sub_sub_sub_cancel_right] using hnorm_zero
    rw [← hzw, hz_norm] at hw_norm
    exact (lt_irrefl R) hw_norm

/-- For an interior point, the Poisson kernel is integrable against any finite measure carried by
the boundary circle. -/
theorem integrable_poissonKernel {μ : Measure ℂ} [IsFiniteMeasure μ]
    (hμ : μ (sphere c R)ᶜ = 0) (hw : w ∈ ball c R) :
    Integrable (fun z : ℂ => poissonKernel c w z) μ := by
  refine (integrable_const ((R + ‖w - c‖) / (R - ‖w - c‖))).mono'
    (measurable_poissonKernel c w).aestronglyMeasurable ?_
  filter_upwards [ae_iff.2 hμ] with z hz
  exact norm_poissonKernel_le_of_mem_ball hw hz

/-- For an interior point, the Poisson kernel times an integrable boundary density is integrable
against any finite measure carried by the boundary circle. -/
theorem integrable_poissonKernel_mul {μ : Measure ℂ} [IsFiniteMeasure μ] {k : ℂ → ℝ}
    (hμ : μ (sphere c R)ᶜ = 0) (hw : w ∈ ball c R) (hk : Integrable k μ) :
    Integrable (fun z : ℂ => poissonKernel c w z * k z) μ := by
  have hbdd : ∀ᵐ z ∂μ, ‖poissonKernel c w z‖ ≤ (R + ‖w - c‖) / (R - ‖w - c‖) := by
    filter_upwards [ae_iff.2 hμ] with z hz
    exact norm_poissonKernel_le_of_mem_ball hw hz
  exact hk.bdd_mul (measurable_poissonKernel c w).aestronglyMeasurable hbdd


end
