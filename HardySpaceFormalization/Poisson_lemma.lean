import Mathlib.Analysis.Complex.Poisson
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.Prod
import HardySpaceFormalization.Harmonic_max_principle



-- # In this file, I will put some more lemmas complementing `Mathlib.Analysis.Complex.Poisson`.

-- remained to finish: Prove Poisson extension theorem.

noncomputable section

open Complex Metric Real Set MeasureTheory
open scoped Topology

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f : ℂ → E} {R : ℝ} {w c : ℂ} {s : Set ℂ}

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
    simpa [Function.uncurry, IntegrableOn, Measure.prod_restrict] using hsmall_int
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
    simpa [Function.comp_apply] using
      (harmonicOnNhd_poissonKernel (c := c) (R := R) (w := z) hz).comp_CLM
        (ContinuousLinearMap.toSpanSingleton ℝ (f z) : ℝ →L[ℝ] E)
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
end
