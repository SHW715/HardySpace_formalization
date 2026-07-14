import Mathlib.Analysis.Complex.CanonicalDecomposition
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import HardySpaceFormalization.HardySpaceDisc

noncomputable section

open Complex ComplexConjugate

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
  else fun z ↦ (-(conj w) / ‖w‖) * BlaschkeFactor R w z



/-- A sequence in the unit disc satisfying the Blaschke condition has only finitely many zero
terms. -/
theorem zeroIndexSet_finite {z : ℕ → ℂ} (hzD : ∀ n, z n ∈ unitDisc)
    (hz : BlaschkeCondition z) : (z ⁻¹'{0}).Finite := by
  sorry

/-- The `n`th factor in the Blaschke product. `0`-terms are omitted from the infinite
product and accounted for by `zeroMultiplicity`. -/
noncomputable def blaschkeProductFactor (z : ℕ → ℂ) (n : ℕ) : ℂ → ℂ :=
  if z n = 0 then 1 else normedBlaschkeFactor 1 (z n)

/-- The Blaschke product associated to a sequence in the unit disc. The definition is meaningful
as a function for any sequence; convergence and the expected zero set will later be proved under
the Blaschke condition. -/
noncomputable def BlaschkeProduct (z : ℕ → ℂ) : ℂ → ℂ :=
  fun w ↦ w ^ (z ⁻¹'{0}).ncard * ∏' n, blaschkeProductFactor z n w
