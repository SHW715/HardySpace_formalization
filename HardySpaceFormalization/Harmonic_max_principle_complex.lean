import HardySpaceFormalization.Harmonic_max_principle
import Mathlib.Analysis.Complex.Harmonic.MeanValue

/-!
# Mean value property for ball averages on `ℂ`

The complex case of the ball-average mean value property and its converse, split off from
`Harmonic_max_principle.lean`.
-/

open MeasureTheory Metric Set Real Filter
open scoped ENNReal Topology

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ### The complex case

On `ℂ` the mean value property for balls follows from mathlib's circle version
`InnerProductSpace.HarmonicOnNhd.circleAverage_eq` by integrating in polar coordinates. -/

/-- In polar coordinates, the ball average on `ℂ` is a weighted radial integral of circle
averages: `ballAverage f c R = (2 / R ^ 2) • ∫ r in 0..R, r • circleAverage f c r`. -/
theorem ballAverage_eq_intervalIntegral_circleAverage [CompleteSpace F] {f : ℂ → F} {c : ℂ}
    {R : ℝ} (hR : 0 < R) (hf : ContinuousOn f (closedBall c R)) :
    ballAverage f c R = (2 / R ^ 2) • ∫ r in (0 : ℝ)..R, r • circleAverage f c r := by
  -- The integrand in polar coordinates.
  set G : ℝ × ℝ → F := fun p => p.1 • f (circleMap c p.1 p.2) with hG
  have hsymm : ∀ p : ℝ × ℝ, c + Complex.polarCoord.symm p = circleMap c p.1 p.2 := by
    intro p
    simp [circleMap, Complex.exp_mul_I]
  -- Translate to the origin and change to polar coordinates.
  have hpolar : ∫ y in ball c R, f y = ∫ p in Ioo 0 R ×ˢ Ioo (-π) π, G p := by
    have h1 : ∫ y in ball c R, f y = ∫ z, (ball c R).indicator f (c + z) := by
      rw [integral_add_left_eq_self (fun y => (ball c R).indicator f y) c,
        integral_indicator measurableSet_ball]
    rw [h1, ← Complex.integral_comp_polarCoord_symm
      (fun z => (ball c R).indicator f (c + z)), polarCoord_target]
    have hset : Ioo 0 R ×ˢ Ioo (-π) π = (Ioi (0 : ℝ) ×ˢ Ioo (-π) π) ∩ (Iio R ×ˢ univ) := by
      ext p
      simp only [mem_prod, mem_Ioo, mem_inter_iff, mem_Ioi, mem_Iio, mem_univ]
      tauto
    rw [hset, ← setIntegral_indicator (measurableSet_Iio.prod MeasurableSet.univ)]
    refine setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) fun p hp => ?_
    have hp0 : 0 < p.1 := hp.1
    have hiff : c + Complex.polarCoord.symm p ∈ ball c R ↔ p.1 < R := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_polarCoord_symm,
        abs_of_pos hp0]
    by_cases hpR : p.1 < R
    · have hmem : p ∈ Iio R ×ˢ (univ : Set ℝ) := ⟨hpR, mem_univ _⟩
      rw [indicator_of_mem (hiff.2 hpR), indicator_of_mem hmem, hsymm]
    · have hmem : p ∉ Iio R ×ˢ (univ : Set ℝ) := fun h => hpR h.1
      simp only [indicator_of_notMem (mt hiff.1 hpR), indicator_of_notMem hmem, smul_zero]
  -- Fubini on the rectangle; integrability comes from continuity on the compact closure.
  have hGcont : ContinuousOn G (Icc 0 R ×ˢ Icc (-π) π) := by
    refine continuousOn_fst.smul (hf.comp (by unfold circleMap; fun_prop) fun p hp => ?_)
    rw [← hsymm, mem_closedBall, dist_eq_norm, add_sub_cancel_left,
      Complex.norm_polarCoord_symm, abs_of_nonneg hp.1.1]
    exact hp.1.2
  have hGint : IntegrableOn G (Ioo 0 R ×ˢ Ioo (-π) π) :=
    (hGcont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  have hfub : ∫ p in Ioo 0 R ×ˢ Ioo (-π) π, G p =
      ∫ r in Ioo 0 R, ∫ θ in Ioo (-π) π, G (r, θ) := by
    rw [Measure.volume_eq_prod] at hGint ⊢
    exact setIntegral_prod _ hGint
  -- The angular integral is `2π` times the circle average.
  have hinner : ∀ r : ℝ, ∫ θ in Ioo (-π) π, G (r, θ) = (2 * π) • (r • circleAverage f c r) := by
    intro r
    have hc : circleAverage f c r = (2 * π)⁻¹ • ∫ θ in (-π)..π, f (circleMap c r θ) := by
      rw [circleAverage_eq_integral_add (-π),
        intervalIntegral.integral_comp_add_right (fun θ => f (circleMap c r θ))]
      congr 2 <;> ring
    simp only [hG]
    rw [integral_smul, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by linarith [pi_pos]), hc, smul_comm r (2 * π)⁻¹,
      smul_smul, mul_inv_cancel₀ (by positivity), one_smul]
  unfold ballAverage
  simp_rw [hpolar, hfub, hinner]
  rw [integral_smul, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hR.le,
    Complex.volume_ball, smul_smul]
  congr 1
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hR.le,
    ENNReal.coe_toReal, NNReal.coe_real_pi]
  field_simp

/-- Mean value property for ball averages on `ℂ`. -/
theorem HarmonicOnNhd.ballAverage_eq_complex [CompleteSpace F] {f : ℂ → F} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : InnerProductSpace.HarmonicOnNhd f (closedBall c R)) :
    ballAverage f c R = f c := by
  rw [ballAverage_eq_intervalIntegral_circleAverage hR hf.continuousOn]
  -- Every circle average of radius `r ∈ [0, R]` equals `f c`.
  have h : ∀ r ∈ Set.uIcc 0 R, r • circleAverage f c r = r • f c := by
    intro r hr
    rw [Set.uIcc_of_le hR.le] at hr
    rw [InnerProductSpace.HarmonicOnNhd.circleAverage_eq
      (hf.mono (closedBall_subset_closedBall (by rw [abs_of_nonneg hr.1]; exact hr.2)))]
  rw [intervalIntegral.integral_congr h, intervalIntegral.integral_smul_const, integral_id,
    smul_smul]
  have hc : 2 / R ^ 2 * ((R ^ 2 - 0 ^ 2) / 2) = 1 := by
    field_simp
    ring
  rw [hc, one_smul]

/-- A local mean-value property for ball averages implies harmonicity on `ℂ`. -/
theorem HarmonicOnNhd_of_ballAverage_eq_complex {u : ℂ → F} {s : Set ℂ}
    (hs : IsOpen s) (hcont : ContinuousOn u s)
    (hmean : ∀ x ∈ s, ∃ ε > 0, ∀ r (_ : 0 < r ∧ r < ε), ballAverage u x r = u x) :
    InnerProductSpace.HarmonicOnNhd u s := by
  sorry
