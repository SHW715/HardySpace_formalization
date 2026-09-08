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
  sorry

end Nevanlinna

end
