import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

open MeasureTheory
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [NormedSpace 𝕜 G]
    [NormedSpace ℝ G] [SMulCommClass ℝ 𝕜 G] [CompleteSpace G]

/-! # Lp duality

We'd like to show: `(L^q)^* ≅ L^p` for `1/p + 1/q = 1`, where `1 ≤ q < ∞`.
-/

/-- Hölder's inequality for the integral pairing: for Hölder conjugate `p, q`, the bilinear map
`(f, g) ↦ ∫ B (f x) (g x) ∂μ` on `Lp E p μ × Lp F q μ` has norm at most `‖B‖`. -/
theorem ContinuousLinearMap.norm_lpPairing_le
    (B : E →L[𝕜] F →L[𝕜] G) : ‖B.lpPairing μ p q‖ ≤ ‖B‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg B) fun f => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun g => ?_
  have h : B.lpPairing μ p q f g = L1.integral (B.holderL μ p q 1 f g) := by
    simp [ContinuousLinearMap.lpPairing, L1.integral_eq' 𝕜]
  rw [h]
  exact (L1.norm_integral_le _).trans (B.norm_holder_apply_apply_le (r := 1) f g)

/-- For `U ∈ Lp ℝ p μ`, the functional `f ↦ ∫ U f ∂μ` on `Lp ℝ q μ` has norm at most `‖U‖`. -/
theorem MeasureTheory.Lp.norm_lpPairing_mul_apply_le (U : Lp ℝ p μ) :
    ‖(ContinuousLinearMap.mul ℝ ℝ).lpPairing μ p q U‖ ≤ ‖U‖ :=
  ((ContinuousLinearMap.mul ℝ ℝ).lpPairing μ p q).le_of_opNorm_le
    ((ContinuousLinearMap.norm_lpPairing_le _).trans (ContinuousLinearMap.opNorm_mul_le ℝ ℝ)) U
    |>.trans_eq (one_mul _)

/-- Uniqueness of the representing function: for σ-finite `μ` and `1 ≤ p`, if
`∫ U f ∂μ = ∫ V f ∂μ` for all `f ∈ Lp ℝ q μ`, then `U = V` in `Lp ℝ p μ`. -/
theorem MeasureTheory.Lp.eq_of_forall_integral_mul_eq
  {p q : ℝ≥0∞} [Fact (1 ≤ p)] [SigmaFinite μ] {U V : Lp ℝ p μ}
  (h : ∀ f : Lp ℝ q μ, ∫ x, U x * f x ∂μ = ∫ x, V x * f x ∂μ) : U = V := by
  apply Lp.ext
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
    (fun s _ hs => integrableOn_Lp_of_measure_ne_top U (Fact.out : 1 ≤ p) hs.ne)
    (fun s _ hs => integrableOn_Lp_of_measure_ne_top V (Fact.out : 1 ≤ p) hs.ne) ?_
  intro s hs hμs
  have h_integral (W : Lp ℝ p μ) :
      ∫ x, W x * indicatorConstLp q hs hμs.ne (1 : ℝ) x ∂μ = ∫ x in s, W x ∂μ := by
    rw [← integral_indicator hs]
    apply integral_congr_ae
    filter_upwards [indicatorConstLp_coeFn (p := q) (hs := hs) (hμs := hμs.ne)
      (c := (1 : ℝ))] with x hx
    rw [hx, ← Set.indicator_mul_right]
    simp
  simpa only [h_integral] using h (indicatorConstLp q hs hμs.ne (1 : ℝ))

/-- The real Lp integral pairing is injective for sigma-finite measures. -/
theorem MeasureTheory.Lp.lpPairing_mul_injective [SigmaFinite μ] :
    Function.Injective ((ContinuousLinearMap.mul ℝ ℝ).lpPairing μ p q) := by
  intro U V h
  apply MeasureTheory.Lp.eq_of_forall_integral_mul_eq (q := q)
  intro f
  simpa [ContinuousLinearMap.lpPairing_eq_integral] using DFunLike.congr_fun h f

/-- The case of `MeasureTheory.Lp.exists_eq_integral_mul` for a finite measure; the first step of
its proof. -/
theorem MeasureTheory.Lp.exists_eq_integral_mul_of_isFiniteMeasure [IsFiniteMeasure μ]
    (hq : q ≠ ∞) (Λ : Lp ℝ q μ →L[ℝ] ℝ) :
    ∃ U : Lp ℝ p μ, ‖U‖ = ‖Λ‖ ∧ Λ = (ContinuousLinearMap.mul ℝ ℝ).lpPairing μ p q U := by
  sorry

/-- Riesz representation of `(L^q)*` (Rudin, *Real and Complex Analysis*, Thm. 6.16, real case,
with `p` and `q` interchanged): for σ-finite `μ`, `1 ≤ q < ∞` and `p` conjugate to `q`, every
bounded linear functional `Λ` on `Lp ℝ q μ` is `f ↦ ∫ U f ∂μ` for some `U ∈ Lp ℝ p μ` with
`‖U‖ = ‖Λ‖`. -/
theorem MeasureTheory.Lp.exists_eq_integral_mul [SigmaFinite μ]
    (hq : q ≠ ∞) (Λ : Lp ℝ q μ →L[ℝ] ℝ) :
    ∃ U : Lp ℝ p μ, ‖U‖ = ‖Λ‖ ∧ Λ = (ContinuousLinearMap.mul ℝ ℝ).lpPairing μ p q U := by
  sorry
