import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Classical Hardy space `H^p` on unit disc in ℂ


-/


noncomputable section

open scoped Real ENNReal

/-- The open unit disc in `ℂ`, represented as the metric ball of radius `1` around `0`. -/
def unitDisc : Set ℂ :=
  Metric.ball (0 : ℂ) 1

/-- The radial parametrization `r * exp(i θ)` used in the Hardy-space mean. -/
def radialPoint (r θ : ℝ) : ℂ :=
  (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)

namespace HardySpace

/--
The finite-exponent radial Hardy quantity on the circle of radius `r`.

For finite nonzero `p : ℝ≥0∞`, this is the normalized interval integral of
`‖f (r * exp(iθ))‖^p`, raised to the power `1 / p`.
-/
def hardyRadial {E : Type*} [NormedAddCommGroup E]
    (f : ℂ → E) (p : ℝ≥0∞) (r : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (
    Real.rpow
      ((1 / (2 * π)) *
        ∫ θ in (0 : ℝ)..(2 * π),
          Real.rpow ‖f (radialPoint r θ)‖ p.toReal)
      (1 / p.toReal))

/--
The Hardy norm quantity on the unit disc.

For `p = ∞`, this is the supremum norm on the disc. For finite nonzero `p`, this is the
supremum of the finite radial quantities over `0 < r < 1`.
-/
def hardyNorm {E : Type*} [NormedAddCommGroup E]
    (f : ℂ → E) (p : ℝ≥0∞) : ℝ≥0∞ :=
  if p = 0 then
    0
  else if p = ∞ then
    ⨆ (z : ℂ) (_ : z ∈ unitDisc), ENNReal.ofReal ‖f z‖
  else
    ⨆ (r : ℝ) (_ : 0 < r ∧ r < 1), hardyRadial f p r

/-- Membership in the Hardy space `H^p` on the unit disc. -/
def MemHpDisc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (p : ℝ≥0∞) (f : ℂ → E) : Prop :=
  p ≠ 0 ∧
    AnalyticOn ℂ f unitDisc ∧
    ∃ C : ℝ≥0∞, C < ∞ ∧ hardyNorm f p ≤ C

/-- Membership in `H^∞`, as the `p = ∞` case of the unified Hardy-space predicate. -/
abbrev MemHInfinityDisc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : ℂ → E) : Prop :=
  MemHpDisc ∞ f

end HardySpace
