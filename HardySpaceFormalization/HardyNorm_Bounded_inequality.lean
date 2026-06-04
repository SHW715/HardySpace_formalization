import HardySpaceFormalization.HardySpaceDisc
import HardySpaceFormalization.Subharmonic

noncomputable section

open scoped Real ENNReal NNReal
open MeasureTheory Real Complex Set Metric


variable {E : Type*} [NormedAddCommGroup E]

namespace HardySpace


/- First we need an inequality for integration with kernel, which later will be useful on estimating
Poisson integral. -/

/-- If a kernel is bounded above by `K` on a circle and `g` is nonnegative there, then
the circle average of `kernel * g` is bounded by `K` times the circle average of `g`. -/
lemma circleAverage_kernel_mul_le_const_mul_circleAverage
    {R : ℝ≥0} {K : ℝ} {kernel g : ℂ → ℝ}
    (hg : CircleIntegrable g 0 R)
    (hkg : CircleIntegrable (fun ξ : ℂ => kernel ξ * g ξ) 0 R)
    (hg_nonneg : ∀ ξ ∈ sphere (0 : ℂ) R, 0 ≤ g ξ)
    (hK : ∀ ξ ∈ sphere (0 : ℂ) R, kernel ξ ≤ K) :
    circleAverage (fun ξ : ℂ => kernel ξ * g ξ) 0 R ≤
      K * circleAverage g 0 R := by
  rw [← smul_eq_mul, ← circleAverage_fun_smul (a := K)
     (f := g) (c := 0) (R := R)]
  refine circleAverage_mono hkg ?_ ?_
  . simpa [smul_eq_mul] using (CircleIntegrable.const_fun_smul (a := K) hg)
  . intro z hz
    have hzR : z ∈ sphere (0 : ℂ) R := by simp_all
    exact mul_le_mul_of_nonneg_right (hK z hzR) (hg_nonneg z hzR)

-- Now we give an upper bound for Poisson kernel:

/-- If the pole is in the closed ball of radius `r` and the boundary point lies on the
circle of radius `R`, with `r < R`, then the Poisson kernel is bounded by
`(R + r) / (R - r)`. -/
lemma poissonKernel_le_of_norm_le {R r : ℝ} {w ξ : ℂ}
  (hξ : ξ ∈ sphere 0 R) (hw : w ∈ closedBall 0 r)(hrR : r < R) :
   poissonKernel 0 w ξ ≤ (R + r) / (R - r) := by
  have hw_norm_le : ‖w‖ ≤ r := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hw
  have hw_mem_ball_R : w ∈ ball (0 : ℂ) R := by
    rw [Metric.mem_ball, dist_zero_right]
    exact hw_norm_le.trans_lt hrR
  have h_kernel :
      poissonKernel 0 w ξ ≤ (R + ‖w‖) / (R - ‖w‖) := by
    simpa [poissonKernel_eq_re_herglotzRieszKernel, Function.comp_apply,
      herglotzRieszKernel_def] using
      (re_herglotzRieszKernel_le (c := 0) (z := ξ) (w := w) (R := R) hξ hw_mem_ball_R)
  have h_mono : (R + ‖w‖) / (R - ‖w‖) ≤ (R + r) / (R - r) := by
    rw [div_le_div_iff₀] <;> nlinarith [norm_nonneg w, hw_norm_le, hrR]
  exact h_kernel.trans h_mono


/-- For finite `p ≥ 1`, the circle average of the `p.toReal`-power of the boundary norm on
the circle of radius `R` is the corresponding radial `eLpNormFixed` slice, converted to `ℝ` and
raised to `p.toReal`. -/
lemma circleAverage_norm_rpow_eq_eLpNormFixed_toReal_rpow
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_ne_top : p ≠ ∞) {R : ℝ}
    (hR : 0 < R ∧ R < 1) {f : ℂ → E} (hf_cont : ContinuousOn f unitDisc) :
    circleAverage (fun z : ℂ => ‖f z‖ ^ p.toReal) 0 R =
      (eLpNormFixed (fun θ : ℝ => f (R * exp (I * θ))) p
        (ENNReal.ofReal (1 / (2 * π)) • volume.restrict (Ico 0 (2 * π)))).toReal ^
          p.toReal := by
  -- codex without review
  let μ : Measure ℝ := ENNReal.ofReal (1 / (2 * π)) • volume.restrict (Ico 0 (2 * π))
  have hp_ne_zero : p ≠ 0 := ne_of_gt (zero_lt_one.trans_le hp)
  have hp_not_small : p ∉ Ioo (0 : ℝ≥0∞) 1 := by
    intro hp_small
    exact (not_lt_of_ge hp) hp_small.2
  have hrad_meas :
      AEStronglyMeasurable (fun θ : ℝ => f (R * exp (I * θ))) μ :=
    (radial_cont hf_cont hR).aestronglyMeasurable
  have hq_pos : 0 < p.toReal := ENNReal.toReal_pos hp_ne_zero hp_ne_top
  have h_int_nonneg :
      0 ≤ ∫ θ, ‖f (R * exp (I * θ))‖ ^ p.toReal ∂μ := by
    exact integral_nonneg fun θ => Real.rpow_nonneg (norm_nonneg _) _
  rw [eLpNormFixed, if_neg hp_not_small, MeasureTheory.toReal_eLpNorm hrad_meas,
    MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal hp_ne_zero hp_ne_top hrad_meas]
  have hpow :
      ((∫ θ, ‖f (R * exp (I * θ))‖ ^ p.toReal ∂μ) ^ p.toReal⁻¹) ^ p.toReal =
        ∫ θ, ‖f (R * exp (I * θ))‖ ^ p.toReal ∂μ := by
    rw [← Real.rpow_mul h_int_nonneg]
    have hmul : p.toReal⁻¹ * p.toReal = 1 := inv_mul_cancel₀ hq_pos.ne'
    rw [hmul, Real.rpow_one]
  rw [hpow]
  rw [circleAverage_def]
  simp only [circleMap_zero]
  rw [MeasureTheory.integral_smul_measure]
  rw [MeasureTheory.integral_Ico_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le (show 0 ≤ 2 * π by positivity)]
  have hcoeff : (ENNReal.ofReal (1 / (2 * π))).toReal = 1 / (2 * π) :=
    ENNReal.toReal_ofReal (by positivity)
  rw [hcoeff]
  ring_nf
  congr 1
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp [mul_comm]

/-- If `f` is continuous on the unit disc, then `‖f‖ ^ q` is continuous on every circle
of radius `R < 1`. -/
lemma continuousOn_norm_rpow_of_continuousOn_unitDisc {q R : ℝ}
    (hq_nonneg : 0 ≤ q) (hR_lt : R < 1)
    {f : ℂ → E} (hf_cont : ContinuousOn f unitDisc) :
    ContinuousOn (fun ξ : ℂ => ‖f ξ‖ ^ q) (sphere (0 : ℂ) R) := by
  have hsphere_subset : sphere (0 : ℂ) R ⊆ unitDisc := by
    intro ξ hξ
    rw [unitDisc, Metric.mem_ball, dist_zero_right]
    have hnorm : ‖ξ‖ = R := by
      simpa [Metric.mem_sphere, dist_zero_right] using hξ
    exact hnorm.trans_lt hR_lt
  exact (hf_cont.mono hsphere_subset).norm.rpow_const
    (fun _ _ => Or.inr hq_nonneg)

omit [NormedAddCommGroup E] in
/-- If `z` lies in the closed ball of radius `r` and `r < R`, then the Poisson kernel
`ξ ↦ poissonKernel 0 z ξ` is continuous on the circle of radius `R`. -/
lemma continuousOn_poissonKernel_of_mem_closedBall {r R : ℝ} {z : ℂ}
    (hz : z ∈ closedBall (0 : ℂ) r) (hrR : r < R) :
    ContinuousOn (fun ξ : ℂ => poissonKernel 0 z ξ) (sphere (0 : ℂ) R) := by
  simp only [poissonKernel_def, sub_zero]
  refine ContinuousOn.div ?_ ?_ ?_
  · fun_prop
  · fun_prop
  · intro ξ hξ hden
    have hξ_eq_z : ξ = z := by
      exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hden))
    have hz_norm_le : ‖z‖ ≤ r := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hz
    have hξ_norm_eq : ‖ξ‖ = R := by
      simpa [Metric.mem_sphere, dist_zero_right] using hξ
    have hR_le_r : R ≤ r := by
      calc
        R = ‖ξ‖ := hξ_norm_eq.symm
        _ = ‖z‖ := by rw [hξ_eq_z]
        _ ≤ r := hz_norm_le
    exact (not_lt_of_ge hR_le_r) hrR


variable [NormedSpace ℂ E]

omit [NormedSpace ℂ E] in
/-- The circle average of the `p.toReal`-power of the boundary norm on a circle of radius
`R < 1` is bounded by the `p.toReal`-power of the Hardy norm. -/
lemma ofReal_circleAverage_norm_rpow_le_hardyNorm_rpow
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_ne_top : p ≠ ∞) {R : ℝ}
    (hR : 0 < R ∧ R < 1) {f : ℂ → E} (hf_cont : ContinuousOn f unitDisc) :
    ENNReal.ofReal (circleAverage (fun z : ℂ => ‖f z‖ ^ p.toReal) 0 R) ≤
      (hardyNorm f p) ^ p.toReal := by
  -- codex without review
  rw [circleAverage_norm_rpow_eq_eLpNormFixed_toReal_rpow
      (E := E) hp hp_ne_top hR hf_cont]
  let μ : Measure ℝ := ENNReal.ofReal (1 / (2 * π)) • volume.restrict (Ico 0 (2 * π))
  have hrad_le : eLpNormFixed (fun θ : ℝ => f (R * exp (I * θ))) p μ ≤ hardyNorm f p :=
     hardyNorm_radial_le f p hR
  have hpow_le : (eLpNormFixed (fun θ : ℝ => f (R * exp (I * θ))) p μ ) ^ p.toReal ≤
    (hardyNorm f p) ^ p.toReal := ENNReal.rpow_le_rpow hrad_le ENNReal.toReal_nonneg
  rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg]
  refine (ENNReal.rpow_le_rpow ?_ ENNReal.toReal_nonneg).trans hpow_le
  exact ENNReal.ofReal_toReal_le


variable [DecidableEq E]

/-- On each closed subdisc, point evaluations are bounded by the Hardy norm. -/
lemma norm_eval_le_const_mul_hardyNorm_of_mem_closedBall {p : ℝ≥0∞} {r : ℝ} (hp : 1 ≤ p) (hr : r < 1) :
  ∃ C : ℝ≥0, ∀ f : ℂ → E, ∀ z : ℂ, AnalyticOn ℂ f unitDisc →
    z ∈ closedBall (0 : ℂ) r → ‖f z‖ₑ ≤ C * hardyNorm f p := by
  by_cases hr_neg : r < 0
  · use 0
    intro f z hf_an hz
    have hdist_le : dist z (0 : ℂ) ≤ r := by
      simpa [Metric.mem_closedBall, dist_comm] using hz
    exact False.elim ((not_lt_of_ge dist_nonneg) (hdist_le.trans_lt hr_neg))
  have hr_nonneg : 0 ≤ r := le_of_not_gt hr_neg
  by_cases hp_top : p = ∞
  · subst p
    use 1
    intro f z hf_an hz
    have hz_unit : z ∈ unitDisc := by
      rw [unitDisc, Metric.mem_ball, dist_zero_right]
      have hz_norm_le : ‖z‖ ≤ r := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hz
      exact hz_norm_le.trans_lt hr
    simp [hardyNorm_top_eq_Sup_norm hf_an.continuousOn]
    exact le_iSup (fun w : unitDisc => ‖f w.1‖ₑ) ⟨z, hz_unit⟩
  let R : ℝ := (r + 1) / 2
  have hR_pos : 0 < R := by dsimp [R]; linarith
  have hR_lt_one : R < 1 := by dsimp [R]; linarith
  have hrR : r < R := by dsimp [R]; linarith
  have hR : 0 < R ∧ R < 1 := ⟨hR_pos, hR_lt_one⟩
  let K : ℝ := (R + r) / (R - r)
  have hK_nonneg : 0 ≤ K := div_nonneg (add_nonneg hR_pos.le hr_nonneg) (sub_nonneg.mpr hrR.le)
  let q : ℝ := p.toReal
  have hq_pos : 0 < q := ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans_le hp)) hp_top
  let C : ℝ≥0 := ⟨K ^ q⁻¹, Real.rpow_nonneg hK_nonneg _⟩
  use C
  intro f z hf_an hz
  have hz_closed_R : z ∈ closedBall (0 : ℂ) R := by
    rw [Metric.mem_closedBall, dist_zero_right] at hz ⊢
    exact hz.trans hrR.le
  have hz_ball_R : z ∈ ball (0 : ℂ) R := by
    rw [Metric.mem_ball, dist_zero_right]
    have hz_norm : ‖z‖ ≤ r := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hz
    exact hz_norm.trans_lt hrR
  have hkernel_bound : ∀ ξ ∈ sphere (0 : ℂ) R, poissonKernel 0 z ξ ≤ K := by
    intro ξ hξ
    exact poissonKernel_le_of_norm_le (R := R) (r := r) (w := z) (ξ := ξ) hξ hz hrR
  have hsubharmonic : SubharmonicOn (fun w : ℂ => ((‖f w‖ ^ q : ℝ) : WithBot ℝ)) unitDisc :=
   norm_rpow_comp_analytic_subharmonicOn_banach (s := unitDisc) Metric.isOpen_ball hf_an hq_pos
  have hpoisson : ‖f z‖ ^ q ≤ circleAverage (fun ξ : ℂ => poissonKernel 0 z ξ * ‖f ξ‖ ^ q) 0 R := by
    refine SubharmonicOn.le_circleAverage_poissonKernel_smul
      (u := fun w : ℂ => ‖f w‖ ^ q) hsubharmonic
      (continuousOn_norm_rpow_of_continuousOn_unitDisc hq_pos.le hR_lt_one hf_an.continuousOn)
      ?_ hz_ball_R
    intro w hw
    have hw_norm : ‖w‖ ≤ R := by simpa [Metric.mem_closedBall, dist_zero_right] using hw
    simpa [unitDisc, Metric.mem_ball, dist_zero_right] using hw_norm.trans_lt hR_lt_one
  have hbase : CircleIntegrable (fun ξ : ℂ => ‖f ξ‖ ^ q) 0 R :=
    (continuousOn_norm_rpow_of_continuousOn_unitDisc hq_pos.le hR_lt_one
      hf_an.continuousOn).circleIntegrable hR_pos.le
  have hweighted : CircleIntegrable (fun ξ : ℂ => poissonKernel 0 z ξ * ‖f ξ‖ ^ q) 0 R := by
    have hnormpow_cont : ContinuousOn (fun ξ : ℂ => ‖f ξ‖ ^ q) (sphere (0 : ℂ) R) :=
      continuousOn_norm_rpow_of_continuousOn_unitDisc hq_pos.le hR_lt_one hf_an.continuousOn
    have hkernel_cont : ContinuousOn (fun ξ : ℂ => poissonKernel 0 z ξ) (sphere (0 : ℂ) R) :=
      continuousOn_poissonKernel_of_mem_closedBall hz hrR
    exact (hkernel_cont.mul hnormpow_cont).circleIntegrable hR_pos.le
  have hkernel_average : circleAverage (fun ξ : ℂ => poissonKernel 0 z ξ * ‖f ξ‖ ^ q) 0 R ≤
        K * circleAverage (fun ξ : ℂ => ‖f ξ‖ ^ q) 0 R := by
    exact circleAverage_kernel_mul_le_const_mul_circleAverage
      (R := ⟨R, hR_pos.le⟩) (K := K)
      (kernel := fun ξ : ℂ => poissonKernel 0 z ξ)
      (g := fun ξ : ℂ => ‖f ξ‖ ^ q)
      hbase hweighted
      (fun ξ hξ => Real.rpow_nonneg (norm_nonneg _) _)
      (by simpa using hkernel_bound)
  have hcircle_hardy : ENNReal.ofReal (circleAverage (fun ξ : ℂ => ‖f ξ‖ ^ q) 0 R) ≤
        (hardyNorm f p) ^ q := by
    simpa [q] using ofReal_circleAverage_norm_rpow_le_hardyNorm_rpow
      (E := E) hp hp_top hR hf_an.continuousOn
  have h_eval_rpow :
      ENNReal.ofReal (‖f z‖ ^ q) ≤ ENNReal.ofReal K * (hardyNorm f p) ^ q := by
    have hreal :
        ‖f z‖ ^ q ≤ K * circleAverage (fun ξ : ℂ => ‖f ξ‖ ^ q) 0 R :=
      hpoisson.trans hkernel_average
    calc
      ENNReal.ofReal (‖f z‖ ^ q)
          ≤ ENNReal.ofReal (K * circleAverage (fun ξ : ℂ => ‖f ξ‖ ^ q) 0 R) :=
        ENNReal.ofReal_le_ofReal hreal
      _ ≤ ENNReal.ofReal K *
          ENNReal.ofReal (circleAverage (fun ξ : ℂ => ‖f ξ‖ ^ q) 0 R) := by
        rw [ENNReal.ofReal_mul hK_nonneg]
      _ ≤ ENNReal.ofReal K * (hardyNorm f p) ^ q := by
        simpa [mul_comm] using
          (mul_le_mul_right hcircle_hardy (ENNReal.ofReal K))
  have h_eval :
      ‖f z‖ₑ ≤ ENNReal.ofReal (K ^ q⁻¹) * hardyNorm f p := by
    have h_eval_q : ‖f z‖ₑ ^ q ≤ ENNReal.ofReal K * (hardyNorm f p) ^ q := by
      rw [← ofReal_norm_eq_enorm,
        ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq_pos.le]
      simpa [q] using h_eval_rpow
    refine (ENNReal.rpow_le_rpow_iff hq_pos).mp ?_
    calc
      ‖f z‖ₑ ^ q
          ≤ ENNReal.ofReal K * (hardyNorm f p) ^ q := h_eval_q
      _ ≤ (ENNReal.ofReal (K ^ q⁻¹) * hardyNorm f p) ^ q := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hq_pos.le]
        rw [← ENNReal.ofReal_rpow_of_nonneg hK_nonneg (inv_nonneg.mpr hq_pos.le)]
        rw [ENNReal.rpow_inv_rpow hq_pos.ne']
  have hC_coe : (C : ℝ≥0∞) = ENNReal.ofReal (K ^ q⁻¹) := by
    rw [ENNReal.coe_nnreal_eq]
    simp [C]
  simpa [hC_coe] using h_eval

/-- Point evaluations inside the disc are bounded by the Hardy norm. -/
lemma norm_eval_le_const_mul_hardyNorm {p : ℝ≥0∞} {z : ℂ} (hp : 1 ≤ p) (hz : z ∈ unitDisc) :
  ∃ C : ℝ≥0, ∀ f : ℂ → E, AnalyticOn ℂ f unitDisc → ‖f z‖ₑ ≤ C * hardyNorm f p := by
  have hz_norm : ‖z‖ < 1 := by simpa [unitDisc, Metric.mem_ball, dist_zero_right] using hz
  let r : ℝ := (‖z‖ + 1) / 2
  have hr_lt : r < 1 := by dsimp [r]; linarith
  have hz_closed : z ∈ Metric.closedBall (0 : ℂ) r := by
    rw [Metric.mem_closedBall, dist_zero_right]; dsimp [r]; linarith
  rcases norm_eval_le_const_mul_hardyNorm_of_mem_closedBall (E := E) (p := p) hp hr_lt with
    ⟨C, hC⟩
  exact ⟨C, fun f hf_an => hC f z hf_an hz_closed⟩

end HardySpace
