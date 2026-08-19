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
    {c : ℂ} {R K : ℝ} {kernel g : ℂ → ℝ}
    (hR : 0 ≤ R) (hg : CircleIntegrable g c R)
    (hkg : CircleIntegrable (fun ξ : ℂ => kernel ξ * g ξ) c R)
    (hg_nonneg : ∀ ξ ∈ sphere c R, 0 ≤ g ξ)
    (hK : ∀ ξ ∈ sphere c R, kernel ξ ≤ K) :
    circleAverage (fun ξ : ℂ => kernel ξ * g ξ) c R ≤
      K * circleAverage g c R := by
  rw [← smul_eq_mul, ← circleAverage_fun_smul (a := K)
     (f := g) (c := c) (R := R)]
  refine circleAverage_mono hkg ?_ ?_
  . simpa [smul_eq_mul] using (CircleIntegrable.const_fun_smul (a := K) hg)
  . intro z hz
    have hzR : z ∈ sphere c R := by simpa [abs_of_nonneg hR] using hz
    exact mul_le_mul_of_nonneg_right (hK z hzR) (hg_nonneg z hzR)

-- Now we give an upper bound for Poisson kernel:

/-- If the pole is in the closed ball of radius `r` and the boundary point lies on the
circle of radius `R`, with `r < R`, then the Poisson kernel is bounded by
`(R + r) / (R - r)`. -/
lemma poissonKernel_le_of_norm_le {R r : ℝ} {w ξ : ℂ}
  (hξ : ξ ∈ sphere 0 R) (hw : w ∈ closedBall 0 r)(hrR : r < R) :
   poissonKernel 0 w ξ ≤ (R + r) / (R - r) := by
  have hw_norm_le : ‖w‖ ≤ r := by simpa [Metric.mem_closedBall, dist_zero_right] using hw
  have hw_mem_ball_R : w ∈ ball 0 R := by
    rw [Metric.mem_ball, dist_zero_right]
    exact hw_norm_le.trans_lt hrR
  grw [poissonKernel_le_of_mem_ball hw_mem_ball_R hξ]; simp
  rw [div_le_div_iff₀] <;> nlinarith [norm_nonneg w, hw_norm_le, hrR]


/-- For finite positive `p`, the circle average of the `p.toReal`-power of the boundary norm on
the circle of radius `R` is the corresponding radial `eLpNormFixed` slice, converted to `ℝ` and
raised to `max p.toReal 1`. -/
lemma circleAverage_norm_rpow_eq_eLpNormFixed_toReal_rpow
    {p : ℝ≥0∞} (hp : 0 < p) (hp_ne_top : p ≠ ∞) {R : ℝ}
    (hR : 0 < R ∧ R < 1) {f : ℂ → E} (hf_cont : ContinuousOn f unitDisc) :
    circleAverage (fun z : ℂ => ‖f z‖ ^ p.toReal) 0 R =
      (eLpNormFixed (fun θ : ℝ => f (R * exp (I * θ))) p angularMeasure).toReal ^
        max p.toReal 1 := by
  unfold angularMeasure
  let μ : Measure ℝ := ENNReal.ofReal (1 / (2 * π)) • volume.restrict (Ico 0 (2 * π))
  have hp_ne_zero : p ≠ 0 := ne_of_gt hp
  have hrad_meas : AEStronglyMeasurable (fun θ : ℝ => f (R * exp (I * θ))) μ :=
    (radial_cont hf_cont hR).aestronglyMeasurable
  have hq_pos : 0 < p.toReal := ENNReal.toReal_pos hp_ne_zero hp_ne_top
  have h_int_nonneg : 0 ≤ ∫ θ, ‖f (R * exp (I * θ))‖ ^ p.toReal ∂μ :=
    integral_nonneg fun θ => Real.rpow_nonneg (norm_nonneg _) _
  rw [ENNReal.toReal_rpow, eLpNormFixed_rpow_max_one hp hp_ne_top,
    ← ENNReal.toReal_rpow, MeasureTheory.toReal_eLpNorm hrad_meas,
    MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal hp_ne_zero hp_ne_top hrad_meas]
  rw [← Real.rpow_mul h_int_nonneg, inv_mul_cancel₀ hq_pos.ne', Real.rpow_one, circleAverage_def]
  simp only [circleMap_zero]
  rw [MeasureTheory.integral_smul_measure, MeasureTheory.integral_Ico_eq_integral_Ioc,
   ← intervalIntegral.integral_of_le (by positivity), ENNReal.toReal_ofReal (by positivity)]
  rw [intervalIntegral.integral_congr (E := ℝ)
    (f := fun θ ↦ ‖f (R * exp (θ * I))‖ ^ p.toReal)
    (g := fun θ ↦ ‖f (R * exp (I * θ))‖ ^ p.toReal)
    (fun θ _ ↦ by simp [mul_comm])]
  ring

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

variable [NormedSpace ℂ E]

omit [NormedSpace ℂ E] in
/-- For finite positive `p`, the circle average of the `p.toReal`-power of the boundary norm on a
circle of radius `R < 1` is bounded by the `max p.toReal 1`-power of the Hardy norm. -/
lemma ofReal_circleAverage_norm_rpow_le_hardyNorm_rpow
    {p : ℝ≥0∞} (hp : 0 < p) (hp_ne_top : p ≠ ∞) {R : ℝ}
    (hR : 0 < R ∧ R < 1) {f : ℂ → E} (hf_cont : ContinuousOn f unitDisc) :
    ENNReal.ofReal (circleAverage (fun z : ℂ => ‖f z‖ ^ p.toReal) 0 R) ≤
      (hardyNorm f p) ^ max p.toReal 1 := by
  rw [circleAverage_norm_rpow_eq_eLpNormFixed_toReal_rpow hp hp_ne_top hR hf_cont]
  let μ : Measure ℝ := ENNReal.ofReal (1 / (2 * π)) • volume.restrict (Ico 0 (2 * π))
  have hrad_le := hardyNorm_radial_le f p hR
  have hmax_nonneg : 0 ≤ max p.toReal 1 := ENNReal.toReal_nonneg.trans (le_max_left _ _)
  have hpow_le := ENNReal.rpow_le_rpow hrad_le hmax_nonneg
  rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hmax_nonneg]
  refine (ENNReal.rpow_le_rpow ?_ hmax_nonneg).trans hpow_le
  exact ENNReal.ofReal_toReal_le


variable [DecidableEq E]

/-- On each closed subdisc, the fixed point-evaluation gauge is bounded by the Hardy gauge. -/
lemma enorm_rpow_min_le_const_mul_hardyNorm_of_mem_closedBall
    {p : ℝ≥0∞} {r : ℝ} (hp : 0 < p) (hr : r < 1) :
  ∃ C : ℝ≥0, ∀ f : ℂ → E, ∀ z : ℂ, AnalyticOn ℂ f unitDisc →
    z ∈ closedBall (0 : ℂ) r →
      ‖f z‖ₑ ^ (min p 1).toReal ≤ C * hardyNorm f p := by
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
  have hq_pos : 0 < q := ENNReal.toReal_pos (ne_of_gt hp) hp_top
  let C : ℝ≥0 := if p < 1 then ⟨K, hK_nonneg⟩ else
    ⟨K ^ q⁻¹, Real.rpow_nonneg hK_nonneg _⟩
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
      continuousOn_poissonKernel_right_of_mem_ball (c := 0) (R := R) (w := z) hz_ball_R
    exact (hkernel_cont.mul hnormpow_cont).circleIntegrable hR_pos.le
  have hkernel_average : circleAverage (fun ξ : ℂ => poissonKernel 0 z ξ * ‖f ξ‖ ^ q) 0 R ≤
        K * circleAverage (fun ξ : ℂ => ‖f ξ‖ ^ q) 0 R := by
    exact circleAverage_kernel_mul_le_const_mul_circleAverage
      (R := R) (K := K)
      (kernel := fun ξ : ℂ => poissonKernel 0 z ξ)
      (g := fun ξ : ℂ => ‖f ξ‖ ^ q)
      hR_pos.le hbase hweighted
      (fun ξ hξ => Real.rpow_nonneg (norm_nonneg _) _)
      (by simpa using hkernel_bound)
  have hcircle_hardy : ENNReal.ofReal (circleAverage (fun ξ : ℂ => ‖f ξ‖ ^ q) 0 R) ≤
        (hardyNorm f p) ^ max q 1 := by
    simpa [q] using ofReal_circleAverage_norm_rpow_le_hardyNorm_rpow
      hp hp_top hR hf_an.continuousOn
  have h_eval_rpow :
      ENNReal.ofReal (‖f z‖ ^ q) ≤ ENNReal.ofReal K * (hardyNorm f p) ^ max q 1 := by
    grw [ENNReal.ofReal_le_ofReal (hpoisson.trans hkernel_average), ENNReal.ofReal_mul hK_nonneg]
    simpa [mul_comm] using (mul_le_mul_right hcircle_hardy (ENNReal.ofReal K))
  by_cases hp_lt_one : p < 1
  · have hq_le_one : q ≤ 1 := by
      dsimp [q]
      rw [← ENNReal.toReal_one]
      exact ENNReal.toReal_mono ENNReal.one_ne_top hp_lt_one.le
    have h_eval_q : ‖f z‖ₑ ^ q ≤ ENNReal.ofReal K * hardyNorm f p := by
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq_pos.le]
      simpa [max_eq_right hq_le_one] using h_eval_rpow
    rw [min_eq_left hp_lt_one.le]
    change ‖f z‖ₑ ^ q ≤ (C : ℝ≥0∞) * hardyNorm f p
    rw [show C = ⟨K, hK_nonneg⟩ by simp [C, hp_lt_one], ENNReal.coe_nnreal_eq]
    exact h_eval_q
  · have hp_one_le : 1 ≤ p := le_of_not_gt hp_lt_one
    have hq_one_le : 1 ≤ q := by
      dsimp [q]
      rw [← ENNReal.toReal_one]
      exact (ENNReal.toReal_le_toReal ENNReal.one_ne_top hp_top).2 hp_one_le
    have h_eval_q : ‖f z‖ₑ ^ q ≤ ENNReal.ofReal K * (hardyNorm f p) ^ q := by
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq_pos.le]
      simpa [max_eq_left hq_one_le] using h_eval_rpow
    have h_eval : ‖f z‖ₑ ≤ ENNReal.ofReal (K ^ q⁻¹) * hardyNorm f p := by
      refine (ENNReal.rpow_le_rpow_iff hq_pos).mp ?_
      grw [h_eval_q]
      rw [ENNReal.mul_rpow_of_nonneg _ _ hq_pos.le,
      ← ENNReal.ofReal_rpow_of_nonneg hK_nonneg (inv_nonneg.mpr hq_pos.le),
      ENNReal.rpow_inv_rpow hq_pos.ne']
    rw [min_eq_right hp_one_le, ENNReal.toReal_one, ENNReal.rpow_one]
    rw [show C = ⟨K ^ q⁻¹, Real.rpow_nonneg hK_nonneg _⟩ by simp [C, hp_lt_one],
      ENNReal.coe_nnreal_eq]
    exact h_eval

/-- On each closed subdisc, point evaluations are bounded by the Hardy norm for `p ≥ 1`. -/
lemma norm_eval_le_const_mul_hardyNorm_of_mem_closedBall
    {p : ℝ≥0∞} {r : ℝ} (hp : 1 ≤ p) (hr : r < 1) :
    ∃ C : ℝ≥0, ∀ f : ℂ → E, ∀ z : ℂ, AnalyticOn ℂ f unitDisc →
      z ∈ closedBall (0 : ℂ) r → ‖f z‖ₑ ≤ C * hardyNorm f p := by
  rcases enorm_rpow_min_le_const_mul_hardyNorm_of_mem_closedBall
    (E := E) (p := p) (zero_lt_one.trans_le hp) hr with ⟨C, hC⟩
  refine ⟨C, fun f z hf hz ↦ ?_⟩
  simpa [min_eq_right hp] using hC f z hf hz

/-- At each point of the unit disc, the fixed point-evaluation gauge is bounded by the Hardy
gauge for every positive exponent. -/
lemma enorm_rpow_min_le_const_mul_hardyNorm
    {p : ℝ≥0∞} {z : ℂ} (hp : 0 < p) (hz : z ∈ unitDisc) :
    ∃ C : ℝ≥0, ∀ f : ℂ → E, AnalyticOn ℂ f unitDisc →
      ‖f z‖ₑ ^ (min p 1).toReal ≤ C * hardyNorm f p := by
  have hz_norm : ‖z‖ < 1 := by simpa [unitDisc, Metric.mem_ball, dist_zero_right] using hz
  let r : ℝ := (‖z‖ + 1) / 2
  have hr_lt : r < 1 := by dsimp [r]; linarith
  have hz_closed : z ∈ Metric.closedBall (0 : ℂ) r := by
    rw [Metric.mem_closedBall, dist_zero_right]; dsimp [r]; linarith
  rcases enorm_rpow_min_le_const_mul_hardyNorm_of_mem_closedBall
    (E := E) (p := p) hp hr_lt with ⟨C, hC⟩
  exact ⟨C, fun f hf_an ↦ hC f z hf_an hz_closed⟩

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
