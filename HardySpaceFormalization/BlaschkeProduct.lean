import Mathlib.Analysis.Complex.CanonicalDecomposition
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Analysis.Meromorphic.Divisor
import HardySpaceFormalization.HardySpaceDisc
import HardySpaceFormalization.HarmonicMajorant

noncomputable section

open Complex ComplexConjugate
open scoped Real
open Set Metric Subharmonic MeromorphicOn Filter

/-- A sequence satisfies the Blaschke condition if its defects from the unit circle are summable. -/
def BlaschkeCondition (z : ℕ → ℂ) : Prop :=
  Summable fun n ↦ 1 - ‖z n‖

/-- The unnormalized Blaschke factor associated to the disk of radius `R`. -/
noncomputable def BlaschkeFactor (R : ℝ) (w : ℂ) : ℂ → ℂ :=
  fun z ↦ (R * (z - w)) / (R ^ 2 - conj w * z)

lemma BlaschkeFactor_eq_inv_canonicalFactor {R : ℝ} {w z : ℂ} :
  BlaschkeFactor R w z = (canonicalFactor R w z)⁻¹ := by simp [BlaschkeFactor, canonicalFactor]

/-- The normalized Blaschke factor associated to the disk of radius `R`. For `w ≠ 0` this differs
from `BlaschkeFactor R w` by the unimodular constant `-conj w / ‖w‖`; for `w = 0` we keep the raw
factor. -/
noncomputable def normedBlaschkeFactor (R : ℝ) (w : ℂ) : ℂ → ℂ :=
  if w = 0 then BlaschkeFactor R 0
  else (-(conj w) / ‖w‖) • BlaschkeFactor R w

/-- A sequence in the unit disc satisfying the Blaschke condition has only finitely many zero
terms. -/
theorem zeroIndexSet_finite {z : ℕ → ℂ} (hz : BlaschkeCondition z) : (z ⁻¹'{0}).Finite := by
  have hcof : (fun n => 1 - ‖z n‖) ⁻¹' (Iio (1 : ℝ)) ∈ cofinite :=
    hz.tendsto_cofinite_zero (Iio_mem_nhds (by norm_num))
  refine (Filter.mem_cofinite.mp hcof).subset ?_
  intro n hn
  rw [mem_preimage, mem_singleton_iff] at hn
  simp [mem_compl_iff, mem_preimage, mem_Iio, hn]

/-- The `n`th factor in the Blaschke product. `0`-terms are omitted from the infinite
product and accounted for by `zeroMultiplicity`. -/
noncomputable def blaschkeProductFactor (z : ℕ → ℂ) (n : ℕ) : ℂ → ℂ :=
  if z n = 0 then 1 else normedBlaschkeFactor 1 (z n)

/-- The Blaschke product associated to a sequence in the unit disc. The definition is meaningful
as a function for any sequence; convergence and the expected zero set will later be proved under
the Blaschke condition. -/
noncomputable def BlaschkeProduct (z : ℕ → ℂ) : ℂ → ℂ :=
  fun w ↦ w ^ (z ⁻¹'{0}).ncard * ∏' n, blaschkeProductFactor z n w




/-- **Theorem 2.1 (first part).** If `f` is analytic on the unit disc, not identically zero, and
`log ‖f‖` has a harmonic majorant on the disc, then the zeros
of `f`, counted with multiplicity, satisfy the Blaschke condition `∑ (1 - ‖zₙ‖) < ∞`.
-/
theorem summable_one_sub_norm_of_hasHarmonicMajorant
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (ball 0 1))
    (hf_ne : ∃ z ∈ ball 0 1, f z ≠ 0)
    (hmaj : HasHarmonicMajorant (logNormBot ∘ f) (ball 0 1)) :
    Summable (fun z : Function.support (divisor f (ball 0 1)) =>
      divisor f (ball 0 1) z * (1 - ‖z.1‖)) := by
  sorry



/-- **Theorem 2.1 (second part).** If `f` is analytic on the unit disc, not identically zero, and
`log ‖f‖` has a harmonic majorant on the disc, and moreover `f 0 ≠ 0` and `u` is the least harmonic
majorant of `log ‖f‖` on the disc, then the Blaschke sum is bounded by `u 0 - log ‖f 0‖`. -/
theorem tsum_one_sub_norm_le_of_isLeastHarmonicMajorant
    {f : ℂ → ℂ} (hf : AnalyticOn ℂ f (ball 0 1)) (hf0 : f 0 ≠ 0)
    {u : ℂ → ℝ} (hu : IsLeastHarmonicMajorant u (logNormBot ∘ f) (ball 0 1)) :
    ∑' z : Function.support (divisor f (ball 0 1)),
      divisor f (ball 0 1) z * (1 - ‖z.1‖) ≤ u 0 - Real.log ‖f 0‖ := by
  sorry
