import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Poisson
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.Prod
import HardySpaceFormalization.Harmonic_max_principle
import Mathlib.MeasureTheory.VectorMeasure.Integral



-- # In this file, I will put some more lemmas complementing `Mathlib.Analysis.Complex.Poisson`.

-- remained to finish: Prove Poisson extension theorem.

noncomputable section

open Complex Metric Real Set MeasureTheory
open scoped Topology

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f : ℂ → E} {R : ℝ} {w c : ℂ} {s : Set ℂ}



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


/-- Joint continuity on `s ×ˢ uIcc a b` implies continuity of the compact-parameter interval
integral in the base variable. -/
theorem ContinuousOn.intervalIntegral_uIcc
    {a b : ℝ} {Φ : ℂ → ℝ → E} {s : Set ℂ}
    (hcont : ContinuousOn (fun p : ℂ × ℝ => Φ p.1 p.2) (s ×ˢ uIcc a b)) :
    ContinuousOn (fun w : ℂ => ∫ θ in a..b, Φ w θ) s := by
  -- codex without review
  rw [continuousOn_iff_continuous_restrict]
  by_cases hab : a ≤ b
  · let Ψ : s → ℝ → E := fun w θ =>
      Φ w ((Set.projIcc a b hab θ : Set.Icc a b) : ℝ)
    have hΨcont : Continuous (Function.uncurry Ψ) := by
      dsimp [Ψ, Function.uncurry]
      have hmap : Continuous fun p : s × ℝ =>
          ((p.1 : ℂ), ((Set.projIcc a b hab p.2 : Set.Icc a b) : ℝ)) :=
        (continuous_subtype_val.comp continuous_fst).prodMk
          (continuous_subtype_val.comp (continuous_projIcc.comp continuous_snd))
      exact hcont.comp_continuous
        hmap
        (fun (p : s × ℝ) => by
          exact ⟨p.1.2, by
            simp [Set.uIcc_of_le hab, (Set.projIcc a b hab p.2).2]⟩)
    have hΨint_cont : Continuous fun w : s => ∫ θ in a..b, Ψ w θ :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hΨcont a b
    refine hΨint_cont.congr fun w => ?_
    exact intervalIntegral.integral_congr fun θ hθ => by
      have hθIcc : θ ∈ Set.Icc a b := by
        simpa [Set.uIcc_of_le hab] using hθ
      simp [Ψ, Set.projIcc_of_mem hab hθIcc]
  · have hba : b ≤ a := le_of_not_ge hab
    let Ψ : s → ℝ → E := fun w θ =>
      Φ w ((Set.projIcc b a hba θ : Set.Icc b a) : ℝ)
    have hΨcont : Continuous (Function.uncurry Ψ) := by
      dsimp [Ψ, Function.uncurry]
      have hmap : Continuous fun p : s × ℝ =>
          ((p.1 : ℂ), ((Set.projIcc b a hba p.2 : Set.Icc b a) : ℝ)) :=
        (continuous_subtype_val.comp continuous_fst).prodMk
          (continuous_subtype_val.comp (continuous_projIcc.comp continuous_snd))
      exact hcont.comp_continuous
        hmap
        (fun (p : s × ℝ) => by
          exact ⟨p.1.2, by
            simp [Set.uIcc_of_ge hba, (Set.projIcc b a hba p.2).2]⟩)
    have hΨint_cont : Continuous fun w : s => ∫ θ in a..b, Ψ w θ :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hΨcont a b
    refine hΨint_cont.congr fun w => ?_
    exact intervalIntegral.integral_congr fun θ hθ => by
      have hθIcc : θ ∈ Set.Icc b a := by
        simpa [Set.uIcc_of_ge hba] using hθ
      simp [Ψ, Set.projIcc_of_mem hba hθIcc]

/-- Ball averages commute with compact-parameter interval integrals for jointly continuous
integrands. -/
theorem ballAverage_intervalIntegral_comm
    {a b r : ℝ} {x : ℂ} {Φ : ℂ → ℝ → E}
    (hcont : ContinuousOn (fun p : ℂ × ℝ => Φ p.1 p.2)
      (closedBall x |r| ×ˢ uIcc a b)) :
    ballAverage (fun w : ℂ => ∫ θ in a..b, Φ w θ) x r =
      ∫ θ in a..b, ballAverage (fun w : ℂ => Φ w θ) x r := by
  -- codex without review
  have hcont_swap : ContinuousOn (fun p : ℝ × ℂ => Φ p.2 p.1)
      (uIcc a b ×ˢ closedBall x |r|) := by
    exact hcont.comp (f := fun p : ℝ × ℂ => (p.2, p.1))
     (continuous_snd.prodMk continuous_fst).continuousOn (fun p hp => ⟨hp.2, hp.1⟩)
  have hcompact_int : IntegrableOn (fun p : ℝ × ℂ => Φ p.2 p.1)
      (uIcc a b ×ˢ closedBall x |r|) (volume.prod volume) := by
    exact hcont_swap.integrableOn_compact (isCompact_uIcc.prod (isCompact_closedBall x |r|))
  have hsmall_int : IntegrableOn (fun p : ℝ × ℂ => Φ p.2 p.1)
      (uIoc a b ×ˢ ball x r) (volume.prod volume) := by
    refine hcompact_int.mono_set (Set.prod_mono Set.uIoc_subset_uIcc ?_)
    intro y hy
    rw [Metric.mem_closedBall]
    exact (le_of_lt (by simpa [Metric.mem_ball] using hy)).trans (le_abs_self r)
  have hint : Integrable (Function.uncurry (fun θ w => Φ w θ))
      ((volume.restrict (Set.uIoc a b)).prod (volume.restrict (ball x r))) := by
    rw [Measure.prod_restrict]
    exact hsmall_int
  unfold ballAverage
  conv_rhs => rw [intervalIntegral.integral_smul]
  have hfub := MeasureTheory.intervalIntegral_integral_swap
    (μ := volume.restrict (ball x r)) (f := fun θ w => Φ w θ) hint
  rw [hfub]

/-- Interval-integrating a jointly continuous compact-parameter family of harmonic functions
preserves harmonicity. -/
theorem harmonicOnNhd_intervalIntegral_of_harmonicOnNhd
    {a b : ℝ} {Φ : ℂ → ℝ → E} {s : Set ℂ} (hs : IsOpen s)
    (hcont : ContinuousOn (fun p : ℂ × ℝ => Φ p.1 p.2) (s ×ˢ uIcc a b))
    (hΦ : ∀ θ ∈ uIcc a b,
      InnerProductSpace.HarmonicOnNhd (fun w : ℂ => Φ w θ) s) :
    InnerProductSpace.HarmonicOnNhd (fun w : ℂ => ∫ θ in a..b, Φ w θ) s := by
  -- codex without review
  have hcont_int : ContinuousOn (fun w : ℂ => ∫ θ in a..b, Φ w θ) s :=
    hcont.intervalIntegral_uIcc
  refine HarmonicOnNhd_of_ballAverage_eq (E := ℂ) (F := E) hs hcont_int ?_
  intro x hx
  rcases Metric.isOpen_iff.mp hs x hx with ⟨ε, hε_pos, hε_sub⟩
  refine ⟨ε, hε_pos, ?_⟩
  intro r hr
  have hclosed_sub : closedBall x |r| ⊆ s := by
    intro y hy
    refine hε_sub ?_
    rw [Metric.mem_ball]
    refine lt_of_le_of_lt ?_ hr.2
    simp [Metric.mem_closedBall] at hy
    simpa [abs_of_pos hr.1] using hy
  have hslice_mean : ∀ θ ∈ uIcc a b, ballAverage (fun w : ℂ => Φ w θ) x r = Φ x θ := by
    intro θ hθ
    simpa [abs_of_pos hr.1] using HarmonicOnNhd.ballAverage_eq ((hΦ θ hθ).mono hclosed_sub)
  have hswap : ballAverage (fun w : ℂ => ∫ θ in a..b, Φ w θ) x r =
        ∫ θ in a..b, ballAverage (fun w : ℂ => Φ w θ) x r :=
      ballAverage_intervalIntegral_comm (hcont.mono (fun p hp => ⟨hclosed_sub hp.1, hp.2⟩))
  have hcollapse :
      (∫ θ in a..b, ballAverage (fun w : ℂ => Φ w θ) x r) = ∫ θ in a..b, Φ x θ := by
    exact intervalIntegral.integral_congr fun θ hθ => hslice_mean θ hθ
  exact hswap.trans hcollapse

/-- The circle average of a jointly continuous parameterized family of harmonic functions is
harmonic. -/
theorem harmonicOnNhd_circleAverage_of_harmonicOnNhd
    {Φ : ℂ → ℂ → E} {s : Set ℂ} (hR : 0 ≤ R) (hs : IsOpen s)
    (hcont : ContinuousOn (fun p : ℂ × ℂ => Φ p.1 p.2) (s ×ˢ sphere c R))
    (hΦ : ∀ z ∈ sphere c R, InnerProductSpace.HarmonicOnNhd (fun w : ℂ => Φ w z) s) :
    InnerProductSpace.HarmonicOnNhd (fun w : ℂ => circleAverage (fun z : ℂ => Φ w z) c R) s := by
  -- codex without review
  have hcont' : ContinuousOn
      (fun p : ℂ × ℝ => Φ p.1 (circleMap c R p.2))
      (s ×ˢ Set.uIcc 0 (2 * π)) := by
    refine hcont.comp
      (by fun_prop :
        ContinuousOn (fun p : ℂ × ℝ => (p.1, circleMap c R p.2))
          (s ×ˢ Set.uIcc 0 (2 * π))) ?_
    intro p hp
    exact ⟨hp.1, circleMap_mem_sphere c hR p.2⟩
  change InnerProductSpace.HarmonicOnNhd
    (fun w : ℂ => (2 * π)⁻¹ • ∫ θ in 0..2 * π, Φ w (circleMap c R θ)) s
  exact (harmonicOnNhd_intervalIntegral_of_harmonicOnNhd
    (Φ := fun w θ => Φ w (circleMap c R θ))
    (a := 0) (b := 2 * π) (s := s) hs hcont'
    (fun θ _hθ => hΦ (circleMap c R θ) (circleMap_mem_sphere c hR θ))).const_smul

/-- The Poisson integral of continuous boundary data on a circle is harmonic in the open disk. -/
theorem harmonicOnNhd_poissonIntegral (hf : ContinuousOn f (sphere c R)) :
    InnerProductSpace.HarmonicOnNhd
      (fun w : ℂ => circleAverage (fun z : ℂ => poissonKernel c w z • f z) c R)
      (ball c R) := by
  -- Claude without review
  by_cases hR : 0 ≤ R
  · have hcont : ContinuousOn (fun p : ℂ × ℂ => poissonKernel c p.1 p.2 • f p.2)
      ((ball c R) ×ˢ sphere c R) := by
      unfold poissonKernel
      refine ContinuousOn.smul ?_ ?_
      · refine ContinuousOn.div ?_ ?_ ?_
        · fun_prop
        · fun_prop
        · intro p hp hden
          rcases hp with ⟨hp_ball, hp_sphere⟩
          simp [sub_eq_zero] at hden
          simp at hp_ball
          simp [← dist_eq_norm] at hp_sphere
          rw [hden] at hp_sphere
          linarith
      · exact hf.comp continuous_snd.continuousOn (fun p hp => hp.2)
    refine harmonicOnNhd_circleAverage_of_harmonicOnNhd (E := E) (R := R) (c := c)
      (s := ball c R) hR (isOpen_ball) hcont ?_
    intro z hz
    convert
      (harmonicOnNhd_poissonKernel (c := c) (R := R) (w := z) hz).comp_CLM
        (ContinuousLinearMap.toSpanSingleton ℝ (f z) : ℝ →L[ℝ] E) using 1
    ext w
    simp [Function.comp_apply]
  · intro w hw
    simp at hR
    have hw_dist_lt : dist w c < R := by simpa [Metric.mem_ball] using hw
    exact False.elim ((not_lt_of_ge dist_nonneg) (hw_dist_lt.trans hR))

/-- The Poisson integral of continuous real-valued boundary data has a continuous extension to the
closed disk whose boundary values are the original boundary data. -/
theorem poissonIntegral_continuousOn_closedBall_eq_boundary
    {u : ℂ → ℝ} (hu_cont : ContinuousOn u (sphere c R)) :
    ∃ h : ℂ → ℝ, ContinuousOn h (closedBall c R) ∧ InnerProductSpace.HarmonicOnNhd h (ball c R)
    ∧ (∀ w ∈ ball c R, h w = circleAverage (fun z : ℂ => poissonKernel c w z * u z) c R)
    ∧ (∀ y ∈ sphere c R, h y = u y) := by
  sorry

/-- If a function is represented inside the disk by its Poisson integral over the boundary circle,
then it is harmonic on the open disk. -/
theorem harmonicOnNhd_of_circleAverage_poissonKernel
    (hf_cont : ContinuousOn f (sphere c R))
    (hrepr : ∀ w ∈ ball c R, circleAverage (fun z : ℂ => poissonKernel c w z • f z) c R = f w) :
    InnerProductSpace.HarmonicOnNhd f (ball c R) := by
  let P : ℂ → E := fun w => circleAverage (fun z : ℂ => poissonKernel c w z • f z) c R
  have hP : InnerProductSpace.HarmonicOnNhd P (ball c R) := harmonicOnNhd_poissonIntegral hf_cont
  intro w hw
  refine (InnerProductSpace.harmonicAt_congr_nhds ?_).1 (hP w hw)
  filter_upwards [isOpen_ball.mem_nhds hw] with y hy
  exact hrepr y hy


-- The rest is given in the help of Claude

/-!
### Positive harmonic functions are Poisson integrals of measures

This is the disc form of Garnett, *Bounded Analytic Functions*, Theorem I.3.5(c).
-/

/-- The Poisson integral of a measure `μ` at the point `w`, for the Poisson kernel centred at `c`.-/
noncomputable def poissonIntegral (c : ℂ) (μ : Measure ℂ) (w : ℂ) : ℝ :=
  ∫ z, poissonKernel c w z ∂μ

/-- The Poisson integral of a *signed* measure `μ` at the point `w`, for the Poisson kernel centred
at `c`, defined through the Jordan decomposition `μ = μ⁺ - μ⁻`. -/
noncomputable def poissonIntegralSigned (c : ℂ) (μ : SignedMeasure ℂ) (w : ℂ) : ℝ :=
  poissonIntegral c μ.toJordanDecomposition.posPart w -
    poissonIntegral c μ.toJordanDecomposition.negPart w

/-- *Test version* of `poissonIntegralSigned`. -/
noncomputable def poissonIntegralSigned' (c : ℂ) (μ : SignedMeasure ℂ) (w : ℂ) : ℝ :=
  ∫ᵛ z, poissonKernel c w z ∂<•μ

-- # At the moment I don't know choose which one as our definition.

/-- For an interior point, the Poisson kernel is integrable against the total variation of a signed
measure carried by the boundary circle. -/
theorem integrable_poissonKernel_totalVariation {μ : SignedMeasure ℂ}
    (hμ : μ.totalVariation (sphere c R)ᶜ = 0) (hw : w ∈ ball c R) :
    μ.Integrable (fun z : ℂ => poissonKernel c w z) := by
  -- Claude without review
  haveI : IsFiniteMeasure μ.totalVariation := by
    rw [SignedMeasure.totalVariation]; infer_instance
  have hint : Integrable (fun z : ℂ => poissonKernel c w z) μ.totalVariation := by
    have h := (integrable_herglotzRieszKernel (μ := μ.totalVariation) hμ hw).re
    simpa [poissonKernel_eq_re_herglotzRieszKernel, RCLike.re_eq_complex_re] using h
  refine hint.mono_measure (VectorMeasure.variation_le_of_forall_enorm_le ?_)
  intro E hE
  set a := μ.toJordanDecomposition.posPart E with ha
  set b := μ.toJordanDecomposition.negPart E with hb
  have ha_ne : a ≠ ⊤ := measure_ne_top _ _
  have hb_ne : b ≠ ⊤ := measure_ne_top _ _
  have hEeq : μ E = a.toReal - b.toReal := by
    conv_lhs => rw [← μ.toSignedMeasure_toJordanDecomposition]
    simp [JordanDecomposition.toSignedMeasure, Measure.toSignedMeasure_apply_measurable hE,
      measureReal_def, ha, hb]
  have habs : |a.toReal - b.toReal| ≤ a.toReal + b.toReal := by
    rw [abs_le]
    constructor <;> linarith [ENNReal.toReal_nonneg (a := a), ENNReal.toReal_nonneg (a := b)]
  rw [SignedMeasure.totalVariation, Measure.add_apply, ← ha, ← hb, Real.enorm_eq_ofReal_abs, hEeq]
  grw [ENNReal.ofReal_le_ofReal habs]
  rw [ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal ha_ne, ENNReal.ofReal_toReal hb_ne]

/-- Both parts of the Jordan decomposition of a signed measure are bounded by its variation. -/
theorem toJordanDecomposition_le_variation {α : Type*} [MeasurableSpace α] (μ : SignedMeasure α) :
    μ.toJordanDecomposition.posPart ≤ μ.variation ∧
      μ.toJordanDecomposition.negPart ≤ μ.variation := by
  -- Claude without review
  obtain ⟨i, hi₁, hi₂, hi₃, hpos, hneg⟩ := μ.toJordanDecomposition_spec
  constructor <;> refine Measure.le_intro fun E hE _ => ?_
  · calc μ.toJordanDecomposition.posPart E
        ≤ ‖μ (i ∩ E)‖ₑ := by
          rw [hpos, SignedMeasure.toMeasureOfZeroLE_apply _ hi₂ hi₁ hE, Real.enorm_eq_ofReal_abs,
            ← ENNReal.ofReal_eq_coe_nnreal]
          exact ENNReal.ofReal_le_ofReal (le_abs_self _)
      _ ≤ μ.variation (i ∩ E) := VectorMeasure.enorm_measure_le_variation _ _
      _ ≤ μ.variation E := measure_mono Set.inter_subset_right
  · calc μ.toJordanDecomposition.negPart E
        ≤ ‖μ (iᶜ ∩ E)‖ₑ := by
          rw [hneg, SignedMeasure.toMeasureOfLEZero_apply _ hi₃ hi₁.compl hE,
            Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_eq_coe_nnreal]
          exact ENNReal.ofReal_le_ofReal (neg_le_abs _)
      _ ≤ μ.variation (iᶜ ∩ E) := VectorMeasure.enorm_measure_le_variation _ _
      _ ≤ μ.variation E := measure_mono Set.inter_subset_right

/-- The two definitions of the Poisson integral of a signed boundary measure agree whenever the
Poisson kernel is integrable against the total variation of `μ`. -/
theorem poissonIntegralSigned_eq_poissonIntegralSigned' {μ : SignedMeasure ℂ}
    (hint : μ.Integrable (fun z : ℂ => poissonKernel c w z)) :
    poissonIntegralSigned c μ w = poissonIntegralSigned' c μ w := by
  -- Claude without review
  obtain ⟨hpos_le, hneg_le⟩ := toJordanDecomposition_le_variation μ
  have hpos : Integrable (fun z : ℂ => poissonKernel c w z) μ.toJordanDecomposition.posPart :=
    hint.mono_measure hpos_le
  have hneg : Integrable (fun z : ℂ => poissonKernel c w z) μ.toJordanDecomposition.negPart :=
    hint.mono_measure hneg_le
  have hpos' : (μ.toJordanDecomposition.posPart.toSignedMeasure).Integrable
      (fun z : ℂ => poissonKernel c w z) := by
    show Integrable (fun z : ℂ => poissonKernel c w z)
      (μ.toJordanDecomposition.posPart.toSignedMeasure).variation
    rwa [Measure.variation_toSignedMeasure]
  have hneg' : (μ.toJordanDecomposition.negPart.toSignedMeasure).Integrable
      (fun z : ℂ => poissonKernel c w z) := by
    show Integrable (fun z : ℂ => poissonKernel c w z)
      (μ.toJordanDecomposition.negPart.toSignedMeasure).variation
    rwa [Measure.variation_toSignedMeasure]
  have key : (∫ᵛ z, poissonKernel c w z ∂<•μ)
      = (∫ z, poissonKernel c w z ∂μ.toJordanDecomposition.posPart)
        - ∫ z, poissonKernel c w z ∂μ.toJordanDecomposition.negPart := by
    conv_lhs => rw [← μ.toSignedMeasure_toJordanDecomposition]
    rw [show μ.toJordanDecomposition.toSignedMeasure
        = μ.toJordanDecomposition.posPart.toSignedMeasure
          - μ.toJordanDecomposition.negPart.toSignedMeasure from rfl,
      VectorMeasure.integral_sub_vectorMeasure hpos' hneg',
      VectorMeasure.integral_toSignedMeasure, VectorMeasure.integral_toSignedMeasure]
  rw [poissonIntegralSigned, poissonIntegralSigned', poissonIntegral, poissonIntegral, key]

/-- The Poisson kernel is nonnegative for an interior point and a boundary point. -/
theorem poissonKernel_nonneg (hw : w ∈ ball c R) {z : ℂ} (hz : z ∈ sphere c R) :
    0 ≤ poissonKernel c w z := by
  have hz_norm : ‖z - c‖ = R := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
  have hw_norm : ‖w - c‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hw
  rw [poissonKernel_def]
  refine div_nonneg ?_ (by positivity)
  nlinarith [norm_nonneg (w - c)]

/-- The Poisson integral of a finite measure carried by the boundary circle is nonnegative on the
open disc. -/
theorem poissonIntegral_nonneg {μ : Measure ℂ} [IsFiniteMeasure μ]
    (hμ : μ (sphere c R)ᶜ = 0) (hw : w ∈ ball c R) :
    0 ≤ poissonIntegral c μ w := by
  refine integral_nonneg_of_ae ?_
  filter_upwards [ae_iff.2 hμ] with z hz using poissonKernel_nonneg hw hz

/-- The Poisson integral of a finite measure carried by the boundary circle is harmonic on the open
disc.  This is the easy direction of Garnett I.3.5(c), disc form. -/
theorem harmonicOnNhd_poissonIntegral_measure {μ : Measure ℂ} [IsFiniteMeasure μ]
    (hμ : μ (sphere c R)ᶜ = 0) :
    InnerProductSpace.HarmonicOnNhd (poissonIntegral c μ) (ball c R) := by
  intro w hw
  have hharm := (analyticOnNhd_integral_herglotzRieszKernel hμ w hw).harmonicAt_re
  refine (InnerProductSpace.harmonicAt_congr_nhds ?_).2 hharm
  filter_upwards [isOpen_ball.mem_nhds hw] with x hx
  show poissonIntegral c μ x = (∫ z, herglotzRieszKernel c x z ∂μ).re
  rw [poissonIntegral, ← RCLike.re_eq_complex_re,
    ← integral_re (integrable_herglotzRieszKernel hμ hx)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simpa [RCLike.re_eq_complex_re] using
    congrFun (poissonKernel_eq_re_herglotzRieszKernel (c := c) (w := x)) z


/-- **Garnett I.3.5(c), disc form**: the nonnegative harmonic functions
on `ball c R` are exactly the Poisson integrals of finite nonnegative measures carried by
`sphere c R`. -/
theorem harmonicOnNhd_nonneg_iff_exists_eq_poissonIntegral (hR : 0 < R) {u : ℂ → ℝ} :
    (InnerProductSpace.HarmonicOnNhd u (ball c R) ∧ ∀ w ∈ ball c R, 0 ≤ u w) ↔
      ∃ μ : Measure ℂ, IsFiniteMeasure μ ∧ μ (sphere c R)ᶜ = 0 ∧
        ∀ w ∈ ball c R, u w = poissonIntegral c μ w := by
  sorry
















end
