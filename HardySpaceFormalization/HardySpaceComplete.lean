import HardySpaceFormalization.HardySpaceFirstDefs


/-!
# Completeness of Hardy Space over unit disc in ℂ

-/


noncomputable section

open scoped Real ENNReal
open MeasureTheory Real Complex


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

namespace HardySpace
namespace HpDisc


/-- `H^p` on unit disc is complete for `1 ≤ p`. -/
instance instCompleteSpace
  (p : ℝ≥0∞) [hp : Fact (1 ≤ p)] : CompleteSpace (HpDisc (E := E) p) where
    complete := sorry


end HpDisc
end HardySpace
