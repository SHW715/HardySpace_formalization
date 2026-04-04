import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

noncomputable section

open scoped Real

/-- The open unit disc in `ℂ`, represented as the metric ball of radius `1` around `0`. -/
def unitDisc : Set ℂ :=
  Metric.ball (0 : ℂ) 1

/-- The radial parametrization `r * exp(i θ)` used in the Hardy-space mean. -/
def radialPoint (r θ : ℝ) : ℂ :=
  (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)

/-- The radial `p`-mean of `f` on the circle of radius `r`. -/
def hardyMean (p : ℝ) (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) *
    ∫ θ in (0 : ℝ)..(2 * Real.pi),
      Real.rpow ‖f (radialPoint r θ)‖ p

/-- Membership in the Hardy space `H^p` on the unit disc via bounded radial means. -/
def MemHp (p : ℝ) (f : ℂ → ℂ) : Prop :=
  0 < p ∧
    AnalyticOn ℂ f unitDisc ∧
    BddAbove {x : ℝ | ∃ r : ℝ, 0 < r ∧ r < 1 ∧ x = hardyMean p f r}

/-- Membership in `H^∞`, the bounded analytic functions on the unit disc. -/
def MemHInfinity (f : ℂ → ℂ) : Prop :=
  AnalyticOn ℂ f unitDisc ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ unitDisc, ‖f z‖ ≤ C
