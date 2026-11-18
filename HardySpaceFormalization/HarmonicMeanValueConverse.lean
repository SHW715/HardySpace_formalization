import HardySpaceFormalization.Harmonic_max_principle_complex
import HardySpaceFormalization.poissonIntegral

/-!
# Harmonicity from the mean value property on `ℂ`

The converse of `HarmonicOnNhd.exists_ballAverage_eq_complex`: a continuous function with the
local ball mean value property is harmonic. It is the `ℂ` counterpart of the general
`HarmonicOnNhd_of_ballAverage_eq` in `Harmonic_max_principle.lean`.

For real-valued functions this is `HarmonicOnNhd_of_ballAverage_eq_complex_real`: on a small disc,
compare the function with the Dirichlet solution of its boundary values
(`poissonIntegral_continuousOn_closedBall_eq_boundary`) by the maximum principle for functions with
the mean value property (`maximum_principle_on_ball_of_ballAverage_eq_complex`), so it equals a
Poisson integral (`eq_poissonIntegral_of_ballAverage_eq_complex`). The general `F` case is still
open: the plan is to reduce to the real case through continuous linear functionals, which needs the
`F`-valued Poisson integral to be `C²` inside the disc.

This file imports `poissonIntegral.lean`, so it sits downstream of it; it is kept apart from
`Harmonic_max_principle_complex.lean` so that `poissonIntegral.lean` can still import the latter.
-/

open MeasureTheory Metric Set Real Filter
open scoped ENNReal Topology PoissonIntegral

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ### Functions with the local ball mean value property -/

/-- Ball averages of a difference of integrable functions. -/
lemma ballAverage_sub_complex {u v : ℂ → F} {x : ℂ} {r : ℝ}
    (hu : IntegrableOn u (ball x r)) (hv : IntegrableOn v (ball x r)) :
    ballAverage (u - v) x r = ballAverage u x r - ballAverage v x r := by
  simp only [ballAverage, Pi.sub_apply, integral_sub hu hv, smul_sub]

/-- The local ball mean value property on an open set passes to differences of continuous
functions. -/
lemma exists_ballAverage_eq_sub_complex {u v : ℂ → F} {s : Set ℂ} (hs : IsOpen s)
    (hu_cont : ContinuousOn u s) (hv_cont : ContinuousOn v s)
    (hu : ∀ x ∈ s, ∃ ε > 0, ∀ r (_ : 0 < r ∧ r < ε), ballAverage u x r = u x)
    (hv : ∀ x ∈ s, ∃ ε > 0, ∀ r (_ : 0 < r ∧ r < ε), ballAverage v x r = v x) :
    ∀ x ∈ s, ∃ ε > 0, ∀ r (_ : 0 < r ∧ r < ε), ballAverage (u - v) x r = (u - v) x := by
  intro x hx
  obtain ⟨ε₁, hε₁, h₁⟩ := hu x hx
  obtain ⟨ε₂, hε₂, h₂⟩ := hv x hx
  obtain ⟨ε₃, hε₃, h₃⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hs.mem_nhds hx)
  refine ⟨min (min ε₁ ε₂) ε₃, lt_min (lt_min hε₁ hε₂) hε₃, fun r hr => ?_⟩
  have hr₁ : r < ε₁ := hr.2.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hr₂ : r < ε₂ := hr.2.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hsub : closedBall x r ⊆ s :=
    (closedBall_subset_closedBall (hr.2.le.trans (min_le_right _ _))).trans h₃
  -- Integrability on the ball comes from continuity on the compact closed ball.
  have hint {f : ℂ → F} (hf : ContinuousOn f s) : IntegrableOn f (ball x r) :=
    ((hf.mono hsub).integrableOn_compact (isCompact_closedBall x r)).mono_set
      ball_subset_closedBall
  rw [ballAverage_sub_complex (hint hu_cont) (hint hv_cont), h₁ r ⟨hr.1, hr₁⟩,
    h₂ r ⟨hr.1, hr₂⟩, Pi.sub_apply]

/-- Maximum principle on a disc for continuous real functions with the local ball mean value
property: if such a function is bounded above by `M` on the circle, then it is bounded above by
`M` inside the disc. -/
theorem maximum_principle_on_ball_of_ballAverage_eq_complex
    {u : ℂ → ℝ} {x : ℂ} {r M : ℝ}
    (hu_mean : ∀ y ∈ ball x r, ∃ ε > 0, ∀ ρ (_ : 0 < ρ ∧ ρ < ε), ballAverage u y ρ = u y)
    (huc : ContinuousOn u (closedBall x r)) :
    (∀ y ∈ sphere x r, u y ≤ M) → ∀ y ∈ ball x r, u y ≤ M := by
  intro hbd y hy
  have hr : 0 < r := pos_of_mem_ball hy
  -- `u` attains its maximum over the compact closed disc at some `a`.
  obtain ⟨a, ha, hmax⟩ := (isCompact_closedBall x r).exists_isMaxOn
    ⟨x, mem_closedBall_self hr.le⟩ huc
  rcases (mem_closedBall.1 ha).lt_or_eq with ha_ball | ha_sphere
  · -- Interior maximum: `u` is constant on the open disc, hence on the closed disc.
    obtain ⟨C, hC⟩ := maximum_minimum_principle_of_ballAverage_eq_complex isOpen_ball
      (convex_ball x r).isPreconnected (huc.mono ball_subset_closedBall) hu_mean
      (Or.inl ⟨a, mem_ball.2 ha_ball, fun z hz => hmax (ball_subset_closedBall hz)⟩)
    have hC_closed : ∀ z ∈ closedBall x r, u z = C := by
      rw [← closure_ball x hr.ne'] at huc ⊢
      exact eqOn_closure_of_eqOn_of_continuousOn huc hC
    obtain ⟨z, hz⟩ := (NormedSpace.sphere_nonempty (x := x)).2 hr.le
    calc u y = C := hC y hy
      _ = u z := (hC_closed z (sphere_subset_closedBall hz)).symm
      _ ≤ M := hbd z hz
  · exact (hmax (ball_subset_closedBall hy)).trans (hbd a (mem_sphere.2 ha_sphere))

/-! ### The real-valued converse -/

/-- **Real core of the converse.** A real function that is continuous on a closed disc and has the
local ball mean value property in the open disc equals there the Poisson integral of its boundary
values: compare it with the Dirichlet solution by the maximum principle. -/
theorem eq_poissonIntegral_of_ballAverage_eq_complex {u : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hcont : ContinuousOn u (closedBall c R))
    (hmean : ∀ x ∈ ball c R, ∃ ε > 0, ∀ r (_ : 0 < r ∧ r < ε), ballAverage u x r = u x)
    {w : ℂ} (hw : w ∈ ball c R) :
    u w = P[c; u ∂ᵥcircleMeasure c R] w := by
  obtain ⟨h, hh_cont, hh_harm, hh_P, hh_bd⟩ :=
    poissonIntegral_continuousOn_closedBall_eq_boundary (c := c) (R := R)
      (hcont.mono sphere_subset_closedBall)
  -- `u - h` and `h - u` have the mean value property in the disc and vanish on the circle.
  have hh_mean := HarmonicOnNhd.exists_ballAverage_eq_complex isOpen_ball hh_harm
  have hu_ball := hcont.mono ball_subset_closedBall
  have hh_ball := hh_cont.mono ball_subset_closedBall
  have h₁ : ∀ y ∈ ball c R, (u - h) y ≤ 0 :=
    maximum_principle_on_ball_of_ballAverage_eq_complex
      (exists_ballAverage_eq_sub_complex isOpen_ball hu_ball hh_ball hmean hh_mean)
      (hcont.sub hh_cont) fun y hy => by simp [hh_bd y hy]
  have h₂ : ∀ y ∈ ball c R, (h - u) y ≤ 0 :=
    maximum_principle_on_ball_of_ballAverage_eq_complex
      (exists_ballAverage_eq_sub_complex isOpen_ball hh_ball hu_ball hh_mean hmean)
      (hh_cont.sub hcont) fun y hy => by simp [hh_bd y hy]
  have h₁w := h₁ w hw
  have h₂w := h₂ w hw
  simp only [Pi.sub_apply] at h₁w h₂w
  rw [← hh_P w hw]
  linarith

/-- The converse of the mean value property for real-valued functions on `ℂ`. -/
theorem HarmonicOnNhd_of_ballAverage_eq_complex_real {u : ℂ → ℝ} {s : Set ℂ}
    (hs : IsOpen s) (hcont : ContinuousOn u s)
    (hmean : ∀ x ∈ s, ∃ ε > 0, ∀ r (_ : 0 < r ∧ r < ε), ballAverage u x r = u x) :
    InnerProductSpace.HarmonicOnNhd u s := by
  intro x hx
  obtain ⟨R, hR, hRs⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hs.mem_nhds hx)
  -- On a small disc around `x`, `u` is the Poisson integral of its boundary values.
  have hball : ∀ w ∈ ball x R, u w = P[x; u ∂ᵥcircleMeasure x R] w := fun w hw =>
    eq_poissonIntegral_of_ballAverage_eq_complex (hcont.mono hRs)
      (fun y hy => hmean y (hRs (ball_subset_closedBall hy))) hw
  exact (InnerProductSpace.harmonicAt_congr_nhds
    (Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds (mem_ball_self hR)) hball)).2
    (harmonicOnNhd_poissonIntegral_withDensityᵥ (circleMeasure_compl_sphere hR.le)
      ((hcont.mono (sphere_subset_closedBall.trans hRs)).integrable_circleMeasure hR.le) x
      (mem_ball_self hR))

/-! ### The general converse -/

/-- A local mean-value property for ball averages implies harmonicity on `ℂ`. -/
theorem HarmonicOnNhd_of_ballAverage_eq_complex {u : ℂ → F} {s : Set ℂ}
    (hs : IsOpen s) (hcont : ContinuousOn u s)
    (hmean : ∀ x ∈ s, ∃ ε > 0, ∀ r (_ : 0 < r ∧ r < ε), ballAverage u x r = u x) :
    InnerProductSpace.HarmonicOnNhd u s := by
  sorry
