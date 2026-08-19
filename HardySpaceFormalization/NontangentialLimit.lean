import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.Complex.Poisson
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Lebesgue
import HardySpaceFormalization.Poisson_lemma
import HardySpaceFormalization.circleMeasure

/-!
# Nontangential approach regions and nontangential limits

-/

open Filter Set Complex MeasureTheory Metric
open scoped Topology

variable {X : Type*} [TopologicalSpace X]

namespace Complex

#check Complex.stolzSet

/-- The **nontangential approach region** at a boundary point `ζ` with aperture parameter
`α`: `Γ_α(ζ) = {z : ‖z‖ < 1 ∧ ‖ζ - z‖ < α (1 - ‖z‖)}`. At `ζ = 1` it is mathlib's `Complex.stolzSet`,
and in general it is the rotation of that set by `ζ`.-/
def stolzSetAt (ζ : ℂ) (α : ℝ) : Set ℂ := {z | ‖z‖ < 1 ∧ ‖ζ - z‖ < α * (1 - ‖z‖)}

end Complex


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

/-- `g` is an **almost everywhere nontangential boundary value** of `f`: at `μ`-almost every `ζ`,
the function `f` has nontangential limit `g ζ` at `ζ`. -/
def IsAEBoundaryValue (μ : Measure ℂ) (f : ℂ → X) (g : ℂ → X) : Prop :=
  ∀ᵐ ζ ∂μ, HasNontangentialLimit f ζ (g ζ)

/-!
### The nontangential filter at a boundary point is nontrivial

The radial segment towards `ζ` lies in every approach region `Γ_α(ζ)` with `α > 1`, which is
what makes `nontangentially ζ` nontrivial and hence `boundaryValue` meaningful at `ζ`.
-/

/-- The radial segment towards a boundary point lies in every approach region at that point. -/
theorem radial_mem_stolzSetAt {ζ : ℂ} (hζ : ‖ζ‖ = 1) {α : ℝ} (hα : 1 < α) {r : ℝ}
    (hr₀ : 0 ≤ r) (hr₁ : r < 1) : r * ζ ∈ stolzSetAt ζ α := by
  have hnorm : ‖r * ζ‖ = r := by
    rw [norm_mul, Complex.norm_real, hζ, mul_one, Real.norm_eq_abs, abs_of_nonneg hr₀]
  have hsub : ζ - r * ζ = ((1 - r : ℝ) : ℂ)  * ζ := by push_cast; ring
  refine ⟨by rw [hnorm]; exact hr₁, ?_⟩
  rw [hsub, norm_mul, Complex.norm_real, hζ, mul_one, Real.norm_eq_abs,
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - r), hnorm]
  nlinarith

/-- At a point of the unit circle the nontangential filter is nontrivial. -/
theorem nontangentially_neBot_of_norm_eq_one {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    (nontangentially ζ).NeBot := by
  have hmem : ζ ∈ closure (stolzSetAt ζ 2) := by
    have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h1 : Tendsto (fun n : ℕ => (1 - 1 / (n + 1 : ℝ) : ℝ)) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.sub h0
    have htend : Tendsto (fun n : ℕ => ((1 - 1 / (n + 1 : ℝ) : ℝ) : ℂ) * ζ) atTop (𝓝 ζ) := by
      simpa using ((Complex.continuous_ofReal.tendsto 1).comp h1).mul
        (tendsto_const_nhds (x := ζ))
    refine mem_closure_of_tendsto htend (Eventually.of_forall fun n => ?_)
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hle : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one hpos]; linarith [Nat.cast_nonneg (α := ℝ) n]
    have hgt : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    exact radial_mem_stolzSetAt hζ one_lt_two (by linarith) (by linarith)
  have hne : (𝓝[stolzSetAt ζ 2] ζ).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hmem
  refine hne.mono ?_
  exact le_iSup₂ (f := fun α (_ : α ∈ Ioi (1 : ℝ)) => 𝓝[stolzSetAt ζ α] ζ) 2 (by norm_num)

/-!
### Bridging the pointwise, the relational and the canonical boundary function
-/

/-- Where a nontangential limit exists, the canonical boundary function takes that value. -/
theorem HasNontangentialLimit.boundaryValue_eq [T2Space X] [Nonempty X] {f : ℂ → X} {ζ : ℂ} {L : X}
    [(nontangentially ζ).NeBot] (h : HasNontangentialLimit f ζ L) : boundaryValue f ζ = L :=
  h.limUnder_eq

/-- Any almost everywhere nontangential boundary value agrees almost everywhere with the canonical
boundary function. -/
theorem IsAEBoundaryValue.ae_eq_boundaryValue [T2Space X] [Nonempty X] {μ : Measure ℂ}
    {f g : ℂ → X} (h : IsAEBoundaryValue μ f g)
    (hne : ∀ᵐ ζ ∂μ, (nontangentially ζ).NeBot) : g =ᵐ[μ] boundaryValue f := by
  filter_upwards [h, hne] with ζ hζ hζne
  haveI := hζne
  exact hζ.limUnder_eq.symm

/-- The canonical boundary function inherits measurability from any almost everywhere
nontangential boundary value.  This is why measurability of `f^*` never needs a separate
argument: it always comes from an explicit representative. -/
theorem IsAEBoundaryValue.aestronglyMeasurable_boundaryValue [T2Space X] [Nonempty X]
    {μ : Measure ℂ} {f g : ℂ → X} (h : IsAEBoundaryValue μ f g)
    (hg : AEStronglyMeasurable g μ) (hne : ∀ᵐ ζ ∂μ, (nontangentially ζ).NeBot) :
    AEStronglyMeasurable (boundaryValue f) μ :=
  hg.congr (h.ae_eq_boundaryValue hne)

/-- The nontangential filter is nontrivial at almost every point of the unit circle. -/
theorem ae_nontangentially_neBot_circleMeasure :
    ∀ᵐ ζ ∂circleMeasure 0 1, (nontangentially ζ).NeBot := by
  filter_upwards [ae_mem_sphere_circleMeasure zero_le_one] with ζ hζ
  exact nontangentially_neBot_of_norm_eq_one (mem_sphere_zero_iff_norm.1 hζ)

/-!
### Fatou's theorem

This is Garnett, *Bounded Analytic Functions*, Theorem I.5.3, in the disc form with `p = 1`, which
is the only case this project uses. -/

/-- **Fatou at Lebesgue points**: the absolutely continuous half of Theorem I.5.3.  The Poisson
integral `P[k dθ/2π]` of an `L¹` density has that density as its nontangential boundary value. -/
theorem isAEBoundaryValue_poissonIntegral {k : ℂ → ℝ}
    (hk : Integrable k (circleMeasure 0 1)) :
    IsAEBoundaryValue (circleMeasure 0 1) (poissonIntegral 0 (circleMeasure 0 1) k) k := by
  sorry

/-- **Garnett I.5.4**: the Poisson integral of a boundary measure singular with respect to
arclength has nontangential limit zero almost everywhere. -/
theorem isAEBoundaryValue_poissonIntegralSigned_zero_of_mutuallySingular
    {ν : SignedMeasure ℂ} (hν : ν.totalVariation (sphere 0 1)ᶜ = 0)
    (hsing : ν ⟂ᵥ (circleMeasure 0 1).toENNRealVectorMeasure) :
    IsAEBoundaryValue (circleMeasure 0 1) (poissonIntegralSigned 0 ν) 0 := by
  sorry

/-- **Garnett I.5.3 (Fatou), disc form, `p = 1`**: the Poisson integral of a finite signed boundary
measure `μ` has, at almost every boundary point, a nontangential limit, equal there to the
Radon--Nikodym density of `μ` with respect to normalized arclength.  Equivalently, writing the
Lebesgue decomposition `dμ = k dθ/2π + dμ_s`, the boundary function of `P[μ]` is `k`. -/
theorem isAEBoundaryValue_poissonIntegralSigned_rnDeriv {μ : SignedMeasure ℂ}
    (hμ : μ.totalVariation (sphere 0 1)ᶜ = 0) :
    IsAEBoundaryValue (circleMeasure 0 1) (poissonIntegralSigned 0 μ)
      (μ.rnDeriv (circleMeasure 0 1)) := by
  sorry

/-- The boundary function of the Poisson integral of a finite signed boundary measure is its
Radon--Nikodym density with respect to normalized arclength. -/
theorem boundaryValue_poissonIntegralSigned {μ : SignedMeasure ℂ}
    (hμ : μ.totalVariation (sphere 0 1)ᶜ = 0) :
    μ.rnDeriv (circleMeasure 0 1) =ᵐ[circleMeasure 0 1]
      boundaryValue (poissonIntegralSigned 0 μ) :=
  (isAEBoundaryValue_poissonIntegralSigned_rnDeriv hμ).ae_eq_boundaryValue
    ae_nontangentially_neBot_circleMeasure

/-- The boundary function of the Poisson integral of a finite signed boundary measure is
measurable, and is in `L¹`.  Both come from the explicit representative supplied by Fatou's
theorem, never from a separate argument about `boundaryValue` itself. -/
theorem integrable_boundaryValue_poissonIntegralSigned {μ : SignedMeasure ℂ}
    (hμ : μ.totalVariation (sphere 0 1)ᶜ = 0) :
    Integrable (boundaryValue (poissonIntegralSigned 0 μ)) (circleMeasure 0 1) :=
  (SignedMeasure.integrable_rnDeriv μ (circleMeasure 0 1)).congr
    (boundaryValue_poissonIntegralSigned hμ)

/-- **Poisson kernel bound over a Stolz region** (Garnett I.4.2, disc form): for `z` in the
approach region `Γ_α(ζ)` and `w` on the unit circle,
`P_z(w) ≤ 2 (α + 2)² (1 - ‖z‖) / ((1 - ‖z‖) + ‖w - ζ‖)²`.
Membership in the region at a boundary point forces `1 < α`, so no aperture hypothesis is
needed. -/
theorem poissonKernel_le_of_mem_stolzSetAt {ζ z w : ℂ} {α : ℝ}
    (hζ : ‖ζ‖ = 1) (hz : z ∈ stolzSetAt ζ α) (hw : ‖w‖ = 1) :
    poissonKernel 0 z w ≤ 2 * (α + 2) ^ 2 * (1 - ‖z‖) / ((1 - ‖z‖) + ‖w - ζ‖) ^ 2 := by
  -- Claude without review
  obtain ⟨hz₁, hz₂⟩ := hz
  have hd : (0 : ℝ) < 1 - ‖z‖ := sub_pos.mpr hz₁
  have hα : 1 < α := by
    have h := norm_sub_norm_le ζ z
    rw [hζ] at h
    nlinarith
  have h₁ : 1 - ‖z‖ ≤ ‖w - z‖ := by
    have h := norm_sub_norm_le w z
    rw [hw] at h
    linarith
  have htri := norm_add_le (w - z) (z - ζ)
  rw [sub_add_sub_cancel, norm_sub_rev z ζ] at htri
  have hkey : (1 - ‖z‖) + ‖w - ζ‖ ≤ (α + 2) * ‖w - z‖ := by
    nlinarith [mul_le_mul_of_nonneg_left h₁ (by linarith : (0 : ℝ) ≤ α + 1)]
  have hwz : (0 : ℝ) < ‖w - z‖ := hd.trans_le h₁
  have h0 : (0 : ℝ) ≤ (1 - ‖z‖) + ‖w - ζ‖ := by
    have := norm_nonneg (w - ζ); linarith
  have hsq := mul_self_le_mul_self h0 hkey
  simp only [poissonKernel_def, sub_zero, hw, one_pow]
  rw [div_le_div_iff₀ (pow_pos hwz 2)
    (pow_pos (by have := norm_nonneg (w - ζ); linarith) 2)]
  nlinarith [mul_le_mul_of_nonneg_left hsq (by linarith : (0 : ℝ) ≤ 2 * (1 - ‖z‖)),
    mul_nonneg (sq_nonneg (1 - ‖z‖)) (sq_nonneg ((1 - ‖z‖) + ‖w - ζ‖))]
