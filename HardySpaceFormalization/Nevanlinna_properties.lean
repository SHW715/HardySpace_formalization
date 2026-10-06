import HardySpaceFormalization.NevanlinnaClass
import HardySpaceFormalization.HarmonicMajorant


/-!
# The properties of Nevanlinna functions

-/

noncomputable section

open scoped Real ENNReal NNReal PoissonIntegral
open MeasureTheory Real Complex Set Metric HardySpace



namespace Nevanlinna

variable {E F : Type*} [NormedAddCommGroup E] [NormedCommRing F]

/-- **Garnett II.5.1.**  Let `f` be analytic on the unit disc with `f ≢ 0`.  Then `f` belongs to the
Nevanlinna class if and only if `log ‖f‖` has as least harmonic majorant the Poisson integral of a
finite signed measure on the boundary circle.-/
theorem memNevanlinnaDisc_iff_exists_signedMeasure_isLeastHarmonicMajorant {f : ℂ → ℂ}
    (hf : AnalyticOn ℂ f unitDisc) (hf_out : ∀ z ∉ unitDisc, f z = 0)
    (hf_ne : ∃ z ∈ unitDisc, f z ≠ 0) :
    MemNevanlinnaDisc f ↔ ∃ μ : SignedMeasure ℂ, μ.totalVariation (sphere 0 1)ᶜ = 0 ∧
      Subharmonic.IsLeastHarmonicMajorant P[0; μ] (logNormBot ∘ f) unitDisc := by
  constructor
  · intro hN
    -- A harmonic majorant `U ≥ log⁺ |f| ≥ 0` also majorizes `log |f|`.
    obtain ⟨U, hU, hUle⟩ := (memNevanlinnaDisc_iff_hasHarmonicMajorant hf hf_out).mp hN
    have hposLog : ∀ z ∈ unitDisc, log⁺ ‖f z‖ ≤ U z :=
      fun z hz => WithBot.coe_le_coe.mp (hUle z hz)
    have hU_nonneg : ∀ z ∈ unitDisc, 0 ≤ U z := fun z hz => posLog_nonneg.trans (hposLog z hz)
    have hUmaj : Subharmonic.IsHarmonicMajorant U (logNormBot ∘ f) unitDisc := by
      refine ⟨hU, fun z hz => ?_⟩
      by_cases hfz : f z = 0
      · simp [logNormBot, hfz]
      · simpa [logNormBot, hfz] using (le_max_right _ _).trans (hposLog z hz)
    -- So `log |f|` has a least harmonic majorant `u ≤ U`.
    obtain ⟨u, hu, -⟩ := Subharmonic.exists_isLeastHarmonicMajorant_tendsto_poissonModification
      (logNormBot_comp_analytic_subharmonicOn_scalar isOpen_ball hf)
      (by
        obtain ⟨z, hz, hfz⟩ := hf_ne
        exact ⟨z, hz, by simp [logNormBot, hfz]⟩)
      ⟨U, hUmaj⟩
    have huU : ∀ z ∈ unitDisc, u z ≤ U z := hu.2 U hUmaj
    -- `u = U - (U - u)` is a difference of positive harmonic functions, hence of Poisson
    -- integrals of finite positive measures.
    obtain ⟨μ₁, _, hμ₁, hUμ₁⟩ :=
      (harmonicOnNhd_nonneg_iff_exists_eq_poissonIntegral one_pos).mp ⟨hU, hU_nonneg⟩
    obtain ⟨μ₂, _, hμ₂, hUμ₂⟩ := (harmonicOnNhd_nonneg_iff_exists_eq_poissonIntegral one_pos).mp
      ⟨hU.sub hu.1.1, fun z hz => sub_nonneg.mpr (huU z hz)⟩
    refine ⟨μ₁.toSignedMeasure - μ₂.toSignedMeasure,
      totalVariation_toSignedMeasure_sub_eq_zero hμ₁ hμ₂, hu.congr isOpen_ball fun w hw => ?_⟩
    rw [poissonIntegral_toSignedMeasure_sub hμ₁ hμ₂ hw, ← hUμ₁ w hw, ← hUμ₂ w hw]
    simp
  · rintro ⟨μ, hμ, hmajor⟩
    have hparts : μ.toJordanDecomposition.posPart (sphere 0 1)ᶜ = 0 ∧
        μ.toJordanDecomposition.negPart (sphere 0 1)ᶜ = 0 := by
      simpa [SignedMeasure.totalVariation, Measure.add_apply] using hμ
    let U := P[0; μ.toJordanDecomposition.posPart.toSignedMeasure]
    have hU : InnerProductSpace.HarmonicOnNhd U unitDisc :=
      harmonicOnNhd_poissonIntegral_toSignedMeasure hparts.1
    have hU_nonneg : ∀ z ∈ unitDisc, 0 ≤ U z :=
      fun z hz => poissonIntegral_toSignedMeasure_nonneg hparts.1 hz
    have hlog : ∀ z ∈ unitDisc, Real.log ‖f z‖ ≤ U z := by
      intro z hz
      by_cases hzero : f z = 0
      · simpa [hzero] using hU_nonneg z hz
      have hle : Real.log ‖f z‖ ≤ P[0; μ] z := by
        simpa [Function.comp_def, logNormBot, hzero] using hmajor.1.2 z hz
      refine hle.trans ?_
      rw [poissonIntegral_eq_posPart_sub_negPart
        (integrable_poissonKernel_totalVariation hμ hz)]
      have hneg := poissonIntegral_toSignedMeasure_nonneg hparts.2 hz
      rw [poissonIntegral_toSignedMeasure] at hneg
      simpa [U, poissonIntegral_toSignedMeasure] using sub_le_self
        (∫ ζ, poissonKernel 0 z ζ ∂μ.toJordanDecomposition.posPart) hneg
    -- `log⁺ |f| ≤ P[μ⁺]`, so `log⁺ |f|` has a harmonic majorant and (5.1) applies.
    refine (memNevanlinnaDisc_iff_hasHarmonicMajorant hf hf_out).mpr ⟨U, hU, fun z hz => ?_⟩
    exact WithBot.coe_le_coe.mpr (max_le (hU_nonneg z hz) (hlog z hz))

end Nevanlinna

end
