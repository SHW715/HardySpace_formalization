import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.Topology.TietzeExtension

/-!
# Weak convergence of finite measures carried by a compact set

`FiniteMeasure.tendsto_iff_forall_integral_tendsto` tests weak convergence against bounded
continuous functions on the whole space. When all the measures are carried by a compact set `K`,
it suffices that the test function be continuous on `K`: by the Tietze extension theorem it agrees
on `K` with a bounded continuous function. Typical use: the Poisson kernel `poissonKernel c w`
is continuous on the circle `sphere c R` but unbounded on `ℂ`.
-/

open Filter Set
open scoped Topology BoundedContinuousFunction

namespace MeasureTheory.FiniteMeasure

variable {Ω ι : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] [T4Space Ω]
  [OpensMeasurableSpace Ω]

/-- Weak convergence of finite measures carried by a compact set `K` can be tested against any
function that is continuous on `K`. -/
theorem tendsto_integral_of_continuousOn {K : Set Ω} (hK : IsCompact K) {g : Ω → ℝ}
    (hg : ContinuousOn g K) {l : Filter ι} {μs : ι → FiniteMeasure Ω} {μ : FiniteMeasure Ω}
    (hμs : Tendsto μs l (𝓝 μ)) (hμs_K : ∀ᶠ i in l, μs i Kᶜ = 0) (hμ_K : μ Kᶜ = 0) :
    Tendsto (fun i => ∫ x, g x ∂(μs i : Measure Ω)) l (𝓝 (∫ x, g x ∂(μ : Measure Ω))) := by
  -- Extend `g|_K` to a bounded continuous `G` on the whole space (Tietze).
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let f : K →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ⟨K.domRestrict g, hg.domRestrict⟩
  obtain ⟨G, -, hG⟩ := BoundedContinuousFunction.exists_norm_eq_domRestrict_eq_of_closed f
    hK.isClosed
  have hGK (x : Ω) (hx : x ∈ K) : G x = g x := DFunLike.congr_fun hG ⟨x, hx⟩
  -- For measures carried by `K`, integrating `g` is integrating `G`.
  have key (ν : FiniteMeasure Ω) (hν : ν Kᶜ = 0) :
      ∫ x, g x ∂(ν : Measure Ω) = ∫ x, G x ∂(ν : Measure Ω) := by
    refine integral_congr_ae ?_
    filter_upwards [mem_ae_iff.2 ((null_iff_toMeasure_null ν Kᶜ).1 hν)] with x hx
    exact (hGK x hx).symm
  rw [key μ hμ_K]
  refine ((tendsto_iff_forall_integral_tendsto.1 hμs) G).congr' ?_
  filter_upwards [hμs_K] with i hi
  exact (key _ hi).symm

end MeasureTheory.FiniteMeasure
