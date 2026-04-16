import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

open scoped ENNReal
namespace HardySpace

/--
A real-valued scalar function has a harmonic majorant on `Ω` if it is bounded above on `Ω`
by a real-valued function that is harmonic in a neighborhood of `Ω`.
-/
def HasHarmonicMajorant
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (Ω : Set V) (g : V → ℝ) : Prop :=
  ∃ u : V → ℝ, InnerProductSpace.HarmonicOnNhd u Ω ∧ ∀ z ∈ Ω, g z ≤ u z

/--
Membership in generalized `p`-Hardy class on an unbundled domain `Ω`.

The function is required to be analytic on `Ω`, and `z ↦ ‖f z‖^p` must admit a harmonic
majorant there.
-/
def MemHp
    {V E : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (Ω : Set V) (p : ℝ≥0∞) (f : V → E) : Prop :=
  0 < p ∧
    AnalyticOn ℂ f Ω ∧
    match p with
    | ∞ =>
        ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ Ω, ‖f z‖ ≤ C
    | _ =>
        HasHarmonicMajorant Ω (fun z => Real.rpow ‖f z‖ (ENNReal.toReal p))

end HardySpace
