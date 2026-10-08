import HardySpaceFormalization.NevanlinnaClass
import HardySpaceFormalization.HarmonicMajorant
import HardySpaceFormalization.BlaschkeProduct


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
        μ.toJordanDecomposition.negPart (sphere 0 1)ᶜ = 0 :=
      SignedMeasure.totalVariation_apply_eq_zero_iff.mp hμ
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

/-- **Garnett II.5.2 (convergence).** The zeros of a nonzero function in the Nevanlinna class,
counted with multiplicity, satisfy the Blaschke condition; hence the Blaschke product formed from
them converges. -/
theorem MemNevanlinnaDisc.blaschkeCondition {f : ℂ → ℂ} (hf : MemNevanlinnaDisc f)
    (hf_ne : ∃ z ∈ unitDisc, f z ≠ 0) :
    BlaschkeCondition (analyticOrderAt f) := by
  sorry

/-- **Garnett II.5.2.** Let `f ≢ 0` belong to the Nevanlinna class and let `B` be the Blaschke
product formed from the zeros of `f`, counted with multiplicity. Then `f = B * g` on the disc for
a zero-free `g` in the Nevanlinna class, and `log ‖g‖` is the least harmonic majorant of
`log ‖f‖`. Since `B ≢ 0`, `g` is `f / B` with its removable singularities filled in. -/
theorem MemNevanlinnaDisc.exists_eq_blaschkeProduct_mul {f : ℂ → ℂ} (hf : MemNevanlinnaDisc f)
    (hf_ne : ∃ z ∈ unitDisc, f z ≠ 0) :
    ∃ g : ℂ → ℂ, MemNevanlinnaDisc g ∧ (∀ z ∈ unitDisc, g z ≠ 0) ∧
      (∀ z ∈ unitDisc, f z = BlaschkeProduct (analyticOrderAt f) z * g z) ∧
      Subharmonic.IsLeastHarmonicMajorant (fun z => Real.log ‖g z‖) (logNormBot ∘ f) unitDisc := by
  sorry

/-- **Garnett II.5.3 (nontangential limits).** A function in the Nevanlinna class has a
nontangential limit at almost every point of the unit circle. Garnett's hypothesis `f ≢ 0` is not
needed here. -/
theorem MemNevanlinnaDisc.ae_nontangentiallyConvergentAt {f : ℂ → ℂ}
    (hf : MemNevanlinnaDisc f) :
    ∀ᵐ ζ ∂circleMeasure 0 1, NontangentiallyConvergentAt f ζ := by
  sorry

/-- **Garnett II.5.3 (nonvanishing boundary values).** The boundary function of a nonzero function
in the Nevanlinna class is nonzero almost everywhere. Garnett's `log |f*| ∈ L¹` contains this, but
`Real.log 0 = 0` in Lean, so it is stated separately. -/
theorem MemNevanlinnaDisc.ae_boundaryValue_ne_zero {f : ℂ → ℂ}
    (hf : MemNevanlinnaDisc f) (hf_ne : ∃ z ∈ unitDisc, f z ≠ 0) :
    ∀ᵐ ζ ∂circleMeasure 0 1, boundaryValue f ζ ≠ 0 := by
  sorry

/-- **Garnett II, (5.2).** For a nonzero function `f` in the Nevanlinna class, `log ‖f*‖` is
integrable on the unit circle. -/
theorem MemNevanlinnaDisc.integrable_log_norm_boundaryValue {f : ℂ → ℂ}
    (hf : MemNevanlinnaDisc f) (hf_ne : ∃ z ∈ unitDisc, f z ≠ 0) :
    Integrable (fun ζ => Real.log ‖boundaryValue f ζ‖) (circleMeasure 0 1) := by
  sorry

/-- **Garnett II, (5.3).** For a nonzero function `f` in the Nevanlinna class, the least harmonic
majorant of `log ‖f‖` is the Poisson integral of `log ‖f*‖ dθ/2π + dμ_s`, for a finite signed
measure `μ_s` on the unit circle singular to arclength. -/
theorem MemNevanlinnaDisc.exists_mutuallySingular_isLeastHarmonicMajorant {f : ℂ → ℂ}
    (hf : MemNevanlinnaDisc f) (hf_ne : ∃ z ∈ unitDisc, f z ≠ 0) :
    ∃ μs : SignedMeasure ℂ, μs.totalVariation (sphere 0 1)ᶜ = 0 ∧
      μs ⟂ᵥ (circleMeasure 0 1).toENNRealVectorMeasure ∧
      Subharmonic.IsLeastHarmonicMajorant
        P[0; (fun ζ => Real.log ‖boundaryValue f ζ‖) ∂ᵥ circleMeasure 0 1 + μs]
        (logNormBot ∘ f) unitDisc := by
  sorry

end Nevanlinna

#check toMeromorphicNFOn

end
