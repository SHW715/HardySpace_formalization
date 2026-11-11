import HardySpaceFormalization.Subharmonic

/-!
# The circle mean inequality for subharmonic functions

For a subharmonic function `u` (comparison definition `SubharmonicOn`) and a closed disc
`closedBall c R` inside its domain, Garnett's proof of Theorem I.6.3 (converse direction) shows

`u c ≤ (1 / 2π) ∫ u (c + R e^{iθ}) dθ`.

The argument: approximate the upper semicontinuous boundary values from above by a decreasing
sequence of continuous functions `g n`, solve the Dirichlet problem for each `g n`, compare, and
pass to the limit by monotone convergence.

* `SubharmonicOn.le_circleAverage_of_le_on_sphere`: the step for one continuous majorant;
* `UpperSemicontinuousOn.exists_antitone_continuous_seq`: the approximation from above;
* `circleAverageWithBot`: the circle average of a `WithBot ℝ`-valued function;
* `SubharmonicOn.le_circleAverageWithBot`: the circle mean inequality.
-/

open MeasureTheory Metric Set Real Filter
open scoped Topology PoissonIntegral

noncomputable section

/-- Circle mean inequality against a continuous majorant: if `u` is subharmonic and `u ≤ g` on
the circle with `g` continuous there, then `u c` is at most the circle average of `g`. -/
theorem SubharmonicOn.le_circleAverage_of_le_on_sphere {u : ℂ → WithBot ℝ} {s : Set ℂ} {c : ℂ}
    {R : ℝ} {g : ℂ → ℝ} (hu : SubharmonicOn u s) (hR : 0 < R) (hclosed : closedBall c R ⊆ s)
    (hg : ContinuousOn g (sphere c R)) (hle : ∀ ζ ∈ sphere c R, u ζ ≤ g ζ) :
    u c ≤ (circleAverage g c R : ℝ) := by
  obtain ⟨h, hcont, hharm, hPoisson, hboundary⟩ :=
    poissonIntegral_continuousOn_closedBall_eq_boundary (c := c) (R := R) hg
  have hc : c ∈ ball c R := mem_ball_self hR
  have hbd : ∀ ζ ∈ sphere c R, u ζ ≤ h ζ := fun ζ hζ => by
    rw [hboundary ζ hζ]
    exact hle ζ hζ
  refine (hu.2 c R h hclosed hcont hharm hbd c hc).trans_eq ?_
  rw [hPoisson c hc, poissonIntegral_circleMeasure_withDensityᵥ_eq_circleAverage hR.le hc hg]
  congr 1
  refine circleAverage_congr_sphere fun ζ hζ => ?_
  rw [abs_of_pos hR, mem_sphere, Complex.dist_eq] at hζ
  simp [poissonKernel_def, hζ, hR.ne']

/-- An upper semicontinuous `WithBot ℝ`-valued function on a compact subset of a metric space is
the pointwise limit of a decreasing sequence of continuous real-valued functions. -/
theorem UpperSemicontinuousOn.exists_antitone_continuous_seq {X : Type*} [PseudoMetricSpace X]
    {K : Set X} (hK : IsCompact K) {u : X → WithBot ℝ} (hu : UpperSemicontinuousOn u K) :
    ∃ g : ℕ → X → ℝ, (∀ n, Continuous (g n)) ∧ Antitone g ∧ (∀ n, ∀ x ∈ K, u x ≤ g n x) ∧
      ∀ x ∈ K, ∀ a : ℝ, u x < a → ∃ n, g n x < a := by
  sorry

/-- Circle average of a `WithBot ℝ`-valued function, using `withBotIntegral` against the
normalized circle measure. It is `⊥` when the function is `⊥` on a set of positive measure or
its real representative is not integrable. -/
def circleAverageWithBot (u : ℂ → WithBot ℝ) (c : ℂ) (R : ℝ) : WithBot ℝ :=
  ∫ᴮ ζ, u ζ ∂circleMeasure c R

/-- For a circle integrable real-valued function, `circleAverageWithBot` is the ordinary circle
average. -/
lemma circleAverageWithBot_coe {f : ℂ → ℝ} {c : ℂ} {R : ℝ} (hf : CircleIntegrable f c R) :
    circleAverageWithBot (fun ζ => (f ζ : WithBot ℝ)) c R = (circleAverage f c R : ℝ) := by
  unfold circleAverageWithBot
  rw [withBotIntegral_eq_coe_of_ae_eq (f := f) (ae_of_all _ fun _ => rfl)
    hf.integrable_circleMeasure, circleAverage_eq_integral_circleMeasure hf]

/-- **Circle mean inequality** (Garnett, proof of Theorem I.6.3): a subharmonic function is at
most its average over any circle bounding a closed disc inside its domain. -/
theorem SubharmonicOn.le_circleAverageWithBot {u : ℂ → WithBot ℝ} {s : Set ℂ} {c : ℂ} {R : ℝ}
    (hu : SubharmonicOn u s) (hR : 0 < R) (hclosed : closedBall c R ⊆ s) :
    u c ≤ circleAverageWithBot u c R := by
  sorry
