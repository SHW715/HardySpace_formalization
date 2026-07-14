import HardySpaceFormalization.Subharmonic



open scoped Real ENNReal NNReal
open MeasureTheory Real Complex Set Metric



variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A function `g` has a harmonic majorant on `s` if some function harmonic on `s`
dominates `g` pointwise on `s`. -/
def HasHarmonicMajorant (g : V → E) (s : Set V) [LE E] : Prop :=
  ∃ u : V → E, InnerProductSpace.HarmonicOnNhd u s ∧ ∀ z ∈ s, g z ≤ u z

/-- `u` is a harmonic majorant of `g` on `s` if it is harmonic on `s` and dominates `g`
pointwise there. -/
def IsHarmonicMajorant (u g : V → E) (s : Set V) [LE E] : Prop :=
    InnerProductSpace.HarmonicOnNhd u s ∧ ∀ z ∈ s, g z ≤ u z

/-- `u` is the least harmonic majorant of `g` on `s` with respect to pointwise order on `s`. -/
def IsLeastHarmonicMajorant (u g : V → E) (s : Set V) [LE E] : Prop :=
  IsHarmonicMajorant u g s ∧ ∀ v : V → E, IsHarmonicMajorant v g s  → ∀ z ∈ s, u z ≤ v z

open Classical in
/-- A choice of the least harmonic majorant of `g` on `s`, when one exists. -/
noncomputable def leastHarmonicMajorant (g : V → E) (s : Set V) [LE E]
  := if h : ∃ u : V → E, IsLeastHarmonicMajorant u g s then Classical.choose h else 0

-- # Here's an annoying issue: if I want my `HasHarmonicMajorant` predicate to be useful for `subharmonic` function
-- # I cannot define in this way as `WithBot ℝ` is not a normed group


namespace Subharmonic

/-- The normalized radial mean of a function on the circle of radius `r` centered at the origin. -/
noncomputable def radialMean (v : ℂ → E) (r : ℝ) : E :=
  ∫ θ, v (r * exp (I * θ)) ∂angularMeasure

/- A real-valued subharmonic function on the unit disc has a harmonic majorant if and only if
its radial means are uniformly bounded above. -/
/-theorem hasHarmonicMajorant_iff_iSup_radialMean_lt_top
    {v : ℂ → WithBot ℝ}
    (hv : SubharmonicOn v (ball 0 1)) :
    HasHarmonicMajorant v (ball 0 1) ↔
      (⨆ (r : ℝ) (_ : r ∈ Ioo 0 1), radialMean v r) < ⊤ := by
  sorry-/





end Subharmonic
