import Mathlib.MeasureTheory.Function.LpSpace.Basic

open ENNReal MeasureTheory



namespace ContinuousLinearMap

variable {α E F 𝕜 𝕜' : Type*} {m : MeasurableSpace α} {μ : Measure α} {p : ℝ≥0∞}
  [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace 𝕜 E] [NormedSpace 𝕜' F]
  {σ : 𝕜 →+* 𝕜'} [RingHomIsometric σ]

-- Proof given by Claude
lemma norm_compLp_of_isometry {L : E →SL[σ] F} (hL : Isometry L) (f : Lp E p μ) :
    ‖L.compLp f‖ = ‖f‖ := by
  refine le_antisymm (Lp.norm_le_norm_of_ae_le ?_) (Lp.norm_le_norm_of_ae_le ?_) <;>
  filter_upwards [L.coeFn_compLp f] with x hx <;> rw [hx, ((AddMonoidHomClass.isometry_iff_norm L).1 hL)]


-- Proof given by Claude
theorem isometry_compLpL [Fact (1 ≤ p)] {L : E →SL[σ] F} (hL : Isometry L):
  Isometry (L.compLpL p μ) := AddMonoidHomClass.isometry_of_norm _ (norm_compLp_of_isometry hL)


-- # The rest are my experiments:
lemma norm_compLp_of_isometry' {L : E →SL[σ] F} (hL : Isometry L) (f : Lp E p μ) :
  ‖L.compLp f‖ = ‖f‖ := by
  have hle : ‖L.compLp f‖ ≤ ‖f‖ := by
   apply Lp.norm_le_norm_of_ae_le
   filter_upwards [L.coeFn_compLp f] with x hx
   rw [hx]; exact ((AddMonoidHomClass.isometry_iff_norm L).1 hL (f x)).le
  have hge : ‖f‖ ≤ ‖L.compLp f‖ := by
   apply Lp.norm_le_norm_of_ae_le
   filter_upwards [L.coeFn_compLp f] with x hx
   rw [hx]; exact ((AddMonoidHomClass.isometry_iff_norm L).1 hL (f x)).ge
  exact le_antisymm hle hge

theorem isometry_compLpL' [Fact (1 ≤ p)] {L : E →SL[σ] F} (hL : Isometry L):
  Isometry (L.compLpL p μ) := by
  intro f g
  simp_rw [edist_dist, dist_eq_norm, ← map_sub]
  congr; exact norm_compLp_of_isometry' hL (f - g)






end ContinuousLinearMap
