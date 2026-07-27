import HardySpaceFormalization.Subharmonic
import HardySpaceFormalization.withBotIntegral
import Mathlib.Analysis.Complex.Poisson
import Mathlib.Topology.Order.WithTop



open scoped Real ENNReal NNReal
open MeasureTheory Real Complex Set Metric Filter Topology



variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

-- # Here's the coercion from `WithBot ℝ` to `EReal`:
noncomputable instance : Coe (WithBot ℝ) EReal := ⟨
  fun x =>
  if hx : x = ⊥ then ⊥
  else (x.unbot hx : EReal)
 ⟩


namespace Subharmonic

/-- A function `g` has a harmonic majorant on `s` if some function harmonic on `s`
dominates `g` pointwise on `s`. -/
def HasHarmonicMajorant (g : V → WithBot ℝ) (s : Set V) : Prop :=
  ∃ u : V → ℝ, InnerProductSpace.HarmonicOnNhd u s ∧ ∀ z ∈ s, g z ≤ u z

/-- `u` is a harmonic majorant of `g` on `s` if it is harmonic on `s` and dominates `g`
pointwise there. -/
def IsHarmonicMajorant (u : V → ℝ) (g : V → WithBot ℝ) (s : Set V) : Prop :=
    InnerProductSpace.HarmonicOnNhd u s ∧ ∀ z ∈ s, g z ≤ u z

/-- `u` is the least harmonic majorant of `g` on `s` with respect to pointwise order on `s`. -/
def IsLeastHarmonicMajorant (u : V → ℝ) (g : V → WithBot ℝ) (s : Set V) : Prop :=
  IsHarmonicMajorant u g s ∧ ∀ v : V → ℝ, IsHarmonicMajorant v g s  → ∀ z ∈ s, u z ≤ v z

open Classical in
/-- A choice of the least harmonic majorant of `g` on `s`, when one exists. -/
noncomputable def leastHarmonicMajorant' (g : V → WithBot ℝ) (s : Set V)
  := if h : ∃ u : V → ℝ, IsLeastHarmonicMajorant u g s then Classical.choose h else 0


/-- The normalized radial mean of a function on the circle of radius `r` centered at the origin. -/
noncomputable def withBotRadialMean (v : ℂ → WithBot ℝ) (r : ℝ) : WithBot ℝ :=
  ∫ᴮ θ, v (r * exp (I * θ)) ∂angularMeasure



/-- The **Poisson modification** `v_r` of a `WithBot ℝ`-valued function on the unit disc:
outside the circle of radius `r` (`r ≤ ‖z‖`) it agrees with `v`, while inside
(`‖z‖ < r`) it is replaced by the Poisson integral of the boundary values of `v` on the circle
of radius `r`. -/
noncomputable def poissonModification (v : ℂ → WithBot ℝ) (r : ℝ) : ℂ → WithBot ℝ :=
  fun z =>
    if r ≤ ‖z‖ then v z
    else ∫ᴮ θ, poissonKernel 0 (z / r) (exp (I * θ)) * v (r * exp (I * θ)) ∂angularMeasure

/-- At the centre of the disc the Poisson modification reduces to the radial mean:
`v_r(0) = withBotRadialMean v r`. -/
lemma poissonModification_zero_eq_withBotRadialMean (v : ℂ → WithBot ℝ) {r : ℝ} (hr : 0 < r) :
    poissonModification v r 0 = withBotRadialMean v r := by
  unfold poissonModification withBotRadialMean
  rw [if_neg (by simpa using not_le.mpr hr)]
  refine congrArg _ (funext fun θ => ?_)
  rw [zero_div, poissonKernel_def]
  simp [Complex.norm_exp, mul_comm]



/-!
### properties of the Poisson modification

For a subharmonic `v` on the unit disc with `v ≢ ⊥` and `0 < r < 1`, the Poisson modification
`v_r = poissonModification v r` is again subharmonic on the disc, is harmonic on `‖z‖ < r`,
dominates `v` pointwise, and increases with `r`.
-/

/-- The Poisson modification of a subharmonic function is subharmonic on the
unit disc. -/
theorem subharmonicOn_poissonModification {v : ℂ → WithBot ℝ} {r : ℝ}
    (hv : SubharmonicOn v (ball 0 1)) (hv_ne : ∃ z ∈ ball (0 : ℂ) 1, v z ≠ ⊥)
    (hr : 0 < r ∧ r < 1) :
    SubharmonicOn (poissonModification v r) (ball 0 1) := by
  sorry

/-- The Poisson modification is harmonic on the open disc of radius `r`. -/
theorem harmonicOnNhdWithBot_poissonModification {v : ℂ → WithBot ℝ} {r : ℝ}
    (hv : SubharmonicOn v (ball 0 1)) (hv_ne : ∃ z ∈ ball (0 : ℂ) 1, v z ≠ ⊥)
    (hr : 0 < r ∧ r < 1) :
    HarmonicOnNhdWithBot (poissonModification v r) (ball 0 r) := by
  sorry

/-- The Poisson modification dominates the original function pointwise on the
disc. -/
theorem le_poissonModification {v : ℂ → WithBot ℝ} {r : ℝ}
    (hv : SubharmonicOn v (ball 0 1)) (hv_ne : ∃ z ∈ ball (0 : ℂ) 1, v z ≠ ⊥)
    (hr : 0 < r ∧ r < 1) :
    ∀ z ∈ ball 0 1, v z ≤ poissonModification v r z := by
  sorry

/-- The Poisson modification is increasing in the radius `r`. -/
theorem poissonModification_mono {v : ℂ → WithBot ℝ}
    (hv : SubharmonicOn v (ball 0 1)) (hv_ne : ∃ z ∈ ball (0 : ℂ) 1, v z ≠ ⊥)
    {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : r₂ < 1) (hle : r₁ ≤ r₂) :
    ∀ z ∈ ball 0 1, poissonModification v r₁ z ≤ poissonModification v r₂ z := by
  sorry



/- A real-valued subharmonic function on the unit disc has a harmonic majorant if and only if
its radial means are uniformly bounded above. -/
theorem hasHarmonicMajorant_iff_radialMean_bddAbove
    {v : ℂ → WithBot ℝ}
    (hv : SubharmonicOn v (ball 0 1)) :
    HasHarmonicMajorant v (ball 0 1) ↔
      (⨆ (r : ℝ) (_ : r ∈ Ioo 0 1), (withBotRadialMean v r : EReal)) < ∞ := by
  sorry


/-- When a subharmonic function `v` on the unit disc has a harmonic
majorant, its least harmonic majorant `u` is recovered as the pointwise radial limit of the Poisson
modifications: `u z = lim_{r → 1⁻} v_r z`. -/
theorem exists_isLeastHarmonicMajorant_tendsto_poissonModification
    {v : ℂ → WithBot ℝ}
    (hv : SubharmonicOn v (ball 0 1))
    (hmaj : HasHarmonicMajorant v (ball 0 1)) :
    ∃ u : ℂ → ℝ, IsLeastHarmonicMajorant u v (ball 0 1) ∧
      ∀ z ∈ ball 0 1, Tendsto (fun r => poissonModification v r z)
      (𝓝[<] 1) (𝓝 (u z) ) := by
  sorry






end Subharmonic
