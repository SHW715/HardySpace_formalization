import Mathlib.Analysis.Complex.AbelLimit

/-!
# Nontangential approach regions and nontangential limits

-/

open Filter Set
open scoped Topology

namespace Complex

variable {X : Type*} [TopologicalSpace X]

#check Complex.stolzSet

/-- The **nontangential approach region** at a boundary point `ζ` with aperture parameter
`α`: `Γ_α(ζ) = {z : ‖z‖ < 1 ∧ ‖ζ - z‖ < α (1 - ‖z‖)}`. At `ζ = 1` it is mathlib's `Complex.stolzSet`,
and in general it is the rotation of that set by `ζ`.-/
def stolzSetAt (ζ : ℂ) (α : ℝ) : Set ℂ := {z | ‖z‖ < 1 ∧ ‖ζ - z‖ < α * (1 - ‖z‖)}

/-- `f` has **nontangential limit** `L` at `ζ` within a single approach region `Γ_α(ζ)` with fixed `α`. -/
def HasNontangentialLimitWithin (f : ℂ → X) (α : ℝ) (ζ : ℂ) (L : X) : Prop :=
  Tendsto f (𝓝[stolzSetAt ζ α] ζ) (𝓝 L)

/-- The **nontangential filter** at `ζ`: the supremum, in the lattice of filters, of the
neighbourhood filters of `ζ` within the approach regions `Γ_α(ζ)`, `α > 1`. -/
noncomputable def nontangentially (ζ : ℂ) : Filter ℂ := ⨆ α ∈ Ioi (1 : ℝ), 𝓝[stolzSetAt ζ α] ζ

/-- `f` has **nontangential limit** `L` at `ζ`: it tends to `L` along `nontangentially ζ`,
equivalently along `𝓝[Γ_α(ζ)] ζ` for every `α > 1`. -/
def HasNontangentialLimit (f : ℂ → X) (ζ : ℂ) (L : X) : Prop := Tendsto f (nontangentially ζ) (𝓝 L)

/-- Nontangential convergence is convergence within every approach region with `α > 1`. -/
theorem hasNontangentialLimit_iff_forall {f : ℂ → X} {ζ : ℂ} {L : X} :
    HasNontangentialLimit f ζ L ↔ ∀ α > 1, HasNontangentialLimitWithin f α ζ L := by
  simp [HasNontangentialLimit, HasNontangentialLimitWithin, nontangentially, tendsto_iSup]

/-- The boundary value of `f` at `ζ` **within the single approach region** `Γ_α(ζ)`. -/
noncomputable def boundaryValueWithin [Nonempty X] (f : ℂ → X) (α : ℝ) (ζ : ℂ) : X :=
  limUnder (𝓝[stolzSetAt ζ α] ζ) f

/-- The **boundary function** of `f` at `ζ`: the value of the nontangential limit at `ζ`. -/
noncomputable def boundaryValue [Nonempty X] (f : ℂ → X) (ζ : ℂ) : X :=
  limUnder (nontangentially ζ) f

end Complex
