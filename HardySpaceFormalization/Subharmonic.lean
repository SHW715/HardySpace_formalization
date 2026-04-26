import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.Semicontinuous
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic

/-!
# Subharmonic functions

-/

-- # Important: Decide how to formalize `SubharmonicOn`
/- Remaining tasks:
  1. Formalize and Prove Lemma: if f is analytic on Ω, then |f|^p is subharmonic on Ω if 0 < p < ∞;
  2. Formalize Theorem 6.7 in Garnett's book and try to prove it;
  3. Together with Lemma and Theorem 6.7, prove `memHpDisc_iff_memHp_onDisc_of_ne_top` in `HardySpaceMajorantDefs`.
-/



open MeasureTheory Metric Set
open scoped ENNReal

noncomputable section




/-- The ball mean of an extended-real-valued function over the ball of radius `r` centered at
`x`. -/
def ballMean
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (u : E → EReal) (x : E) (r : ℝ) : EReal := sorry
  -- (∫ y in ball x r, u y ∂volume) / volume (ball x r)

  /- I don't want to endow [MeasureSpace E] as I want the `volume` to be the canonical volume measure of finite ℝ-v.s.
   But it seems that there's no such definition in mathlib? I'm not sure.-/

  /- Another issue is that: ballMean is NOT always well-defined for function `u : E → EReal`, as it might trigger the
  the issue like (∞ - ∞), which is ill-defined. But `SubharmonicOn` is actually well-defined definition due to
  semicontinuity -/

  /- Also I found that in other reference books, e.g. Rudin, Real and Complex analysis, it requires u : E → WithBot ℝ ,
  then mathematically ill-defined issue will be avoided. But I still have no idea how to define it in Lean.

  Also, two definitions are different, as one adopted ball-mean yet another adpoted spherical-mean. But they are actually
  equivalent, which needs some works to prove.

  I think it will be easier to generalize using Garnett's definition (as I think we might need to introduce measure on
  sphere when defining spherical-mean? which for me seems to be tricky)
  -/


/-- A function is subharmonic on a set if it is upper semicontinuous there and satisfies the
mean inequality with respect to ball averages on every ball contained in the set. -/
def SubharmonicOn
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (s : Set E) (u : E → EReal) : Prop :=
  UpperSemicontinuousOn u s ∧ ∀ (x : E) , ∀ (r : ℝ), ∀ (h : E → ℝ),
   closedBall x r ⊆ s → ContinuousOn h (closedBall x r) →
   InnerProductSpace.HarmonicOnNhd h (ball x r) →
   (∀ y ∈ sphere x r, u y ≤ h y) → ∀ y ∈ ball x r, u y ≤ h y


/--
A real-valued scalar function has a harmonic majorant on `Ω` if it is bounded above on `Ω`
by a real-valued function that is harmonic in a neighborhood of `Ω`.
-/
def HasHarmonicMajorant
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (Ω : Set V) (g : V → ℝ) : Prop :=
  ∃ u : V → ℝ, InnerProductSpace.HarmonicOnNhd u Ω ∧ ∀ z ∈ Ω, g z ≤ u z

-- It's a duplicate definition with the one in `HardySpaceMajorantDefs.lean`
/- I'm not sure where should I put this `HasHarmonicMajorant` at. It seems not proper to put this here as it does
 not rely on sub-harmonicity. But I can't put this in `HardySpaceMajorantDefs.lean`, as I will import `Subharmonic.lean`
 into `HardySpaceMajorantDefs.lean`, and I have to use this concept here -/
