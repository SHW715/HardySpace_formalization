import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.Complex.Poisson
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Lebesgue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Complex.Harmonic.Poisson
import HardySpaceFormalization.Poisson_lemma
import HardySpaceFormalization.circleMeasure

/-!
# Nontangential approach regions and nontangential limits

-/

open Filter Set Real Complex MeasureTheory Metric
open scoped Topology Real ENNReal

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


-- ## It seems to be a redundant definition
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
    {f g : ℂ → X} (h : IsAEBoundaryValue μ f g) (hne : ∀ᵐ ζ ∂μ, (nontangentially ζ).NeBot) :
    g =ᵐ[μ] boundaryValue f := by
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
### Preparation: geometric and kernel estimates

The estimates the Fatou proofs below rest on: the chord/arc comparison on the unit circle, the
resulting bound on the normalized arclength of a small ball, and the Poisson-kernel majorant
over a Stolz region.
-/

/-- The chord length between two points of the unit circle. -/
theorem norm_circleMap_sub_circleMap (θ φ : ℝ) :
    ‖circleMap 0 1 θ - circleMap 0 1 φ‖ = 2 * |Real.sin ((θ - φ) / 2)| := by
  -- Claude without review
  have hfac : circleMap 0 1 θ - circleMap 0 1 φ
      = Complex.exp (φ * Complex.I) * (Complex.exp (((θ - φ : ℝ) : ℂ) * Complex.I) - 1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one]
    simp only [circleMap, zero_add, Complex.ofReal_one, one_mul]
    push_cast
    ring_nf
  rw [hfac, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  set x : ℝ := θ - φ with hxdef
  have hexp : Complex.exp ((x : ℂ) * Complex.I) - 1
      = ((Real.cos x - 1 : ℝ) : ℂ) + ((Real.sin x : ℝ) : ℂ) * Complex.I := by
    rw [Complex.exp_ofReal_mul_I]; push_cast; ring
  rw [hexp, Complex.norm_add_mul_I]
  have hhalf : Real.sin (x / 2) ^ 2 = 1 / 2 - Real.cos x / 2 := by
    have h := Real.sin_sq_eq_half_sub (x / 2)
    rwa [show 2 * (x / 2) = x by ring] at h
  have hkey : (Real.cos x - 1) ^ 2 + Real.sin x ^ 2 = (2 * |Real.sin (x / 2)|) ^ 2 := by
    rw [mul_pow, sq_abs, hhalf]
    nlinarith [Real.sin_sq_add_cos_sq x]
  rw [hkey, Real.sqrt_sq (by positivity)]

/-- **Chord controls arc.**  Within a half-turn, the angular separation of two points of the unit
circle is at most `π / 2` times their chord distance.  This is Jordan's inequality
`Real.mul_le_sin` read through `norm_circleMap_sub_circleMap`. -/
theorem abs_sub_le_norm_circleMap_sub {θ φ : ℝ} (h : |θ - φ| ≤ π) :
    |θ - φ| ≤ π / 2 * ‖circleMap 0 1 θ - circleMap 0 1 φ‖ := by
  -- Claude without review
  rw [norm_circleMap_sub_circleMap]
  set x : ℝ := θ - φ with hxdef
  have hpi : 0 < π := Real.pi_pos
  have habs : |Real.sin (x / 2)| = Real.sin (|x| / 2) := by
    rcases le_or_gt 0 x with hx | hx
    · have hxx : |x| = x := abs_of_nonneg hx
      rw [hxx, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith)
        (by rw [hxx] at h; linarith))]
    · have hxx : |x| = -x := abs_of_neg hx
      rw [hxx, show -x / 2 = -(x / 2) by ring, Real.sin_neg,
        abs_of_nonpos (Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith)
          (by rw [hxx] at h; linarith))]
  have hjordan : 2 / π * (|x| / 2) ≤ Real.sin (|x| / 2) :=
    Real.mul_le_sin (by positivity) (by linarith [abs_nonneg x])
  rw [habs]
  have h2 : |x| ≤ Real.sin (|x| / 2) * π := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hpi] at hjordan
    linarith
  linarith [h2]

/-- **Normalized arclength of a small ball.**  At a point of the unit circle, the arc cut out by a
ball of radius `h` has normalized arclength at most `h / 2`. -/
theorem circleMeasure_closedBall_le_of_norm_eq_one {x : ℂ} (hx : ‖x‖ = 1) {h : ℝ} :
    circleMeasure 0 1 (closedBall x h) ≤ ENNReal.ofReal (h / 2) := by
  -- Claude without fully review
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have h2π : (0 : ℝ) < 2 * π := by linarith
  -- the centre is a point of the parametrized circle
  obtain ⟨φ, hφ⟩ : ∃ φ : ℝ, circleMap 0 1 φ = x := by
    have hx' : x ∈ sphere (0 : ℂ) |1| := by
      rw [abs_one]
      simpa [mem_sphere_iff_norm] using hx
    rw [← range_circleMap] at hx'
    exact hx'
  have hS_meas : MeasurableSet (circleMap 0 1 ⁻¹' closedBall x h) :=
    measurable_circleMap 0 1 measurableSet_closedBall
  -- the parameter set is invariant under full turns
  have hS_inv : ∀ g : AddSubgroup.zmultiples (2 * π),
      (fun θ : ℝ => g +ᵥ θ) ⁻¹' (circleMap 0 1 ⁻¹' closedBall x h)
        = circleMap 0 1 ⁻¹' closedBall x h := by
    intro g
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp g.2
    have hper : ∀ θ : ℝ, circleMap 0 1 (θ + (g : ℝ)) = circleMap 0 1 θ := by
      intro θ
      have hzs := (periodic_circleMap 0 1).zsmul n
      rw [hn] at hzs
      exact hzs θ
    ext θ
    have hvadd : (g +ᵥ θ : ℝ) = (g : ℝ) + θ := rfl
    simp only [mem_preimage, hvadd, add_comm (g : ℝ) θ, hper]
  -- re-centre the window at `φ` using that both windows are fundamental domains
  have hshift :
      volume (circleMap 0 1 ⁻¹' closedBall x h ∩ Ioc 0 (0 + 2 * π))
        = volume (circleMap 0 1 ⁻¹' closedBall x h ∩ Ioc (φ - π) ((φ - π) + 2 * π)) :=
    (isAddFundamentalDomain_Ioc h2π 0).measure_set_eq
      (isAddFundamentalDomain_Ioc h2π (φ - π)) hS_meas hS_inv
  -- on the centred window the chord controls the arc
  have hwindow : circleMap 0 1 ⁻¹' closedBall x h ∩ Ioc (φ - π) ((φ - π) + 2 * π)
      ⊆ Icc (φ - π / 2 * h) (φ + π / 2 * h) := by
    rintro θ ⟨hθS, hθl, hθr⟩
    have hθπ : |θ - φ| ≤ π := by
      rw [abs_le]
      constructor <;> linarith
    have hchord : ‖circleMap 0 1 θ - circleMap 0 1 φ‖ ≤ h := by
      rw [hφ]
      have hmem : circleMap 0 1 θ ∈ closedBall x h := hθS
      simpa [mem_closedBall, dist_eq_norm] using hmem
    have hbound : |θ - φ| ≤ π / 2 * h :=
      (abs_sub_le_norm_circleMap_sub hθπ).trans
        (mul_le_mul_of_nonneg_left hchord (by positivity))
    rw [abs_le] at hbound
    exact ⟨by linarith [hbound.1], by linarith [hbound.2]⟩
  -- the window computation, `Ico` to `Ioc` first, then the two steps above
  have hIco : volume (circleMap 0 1 ⁻¹' closedBall x h ∩ Ico 0 (2 * π))
      ≤ ENNReal.ofReal (π * h) := by
    have hsub : circleMap 0 1 ⁻¹' closedBall x h ∩ Ico 0 (2 * π)
        ⊆ (circleMap 0 1 ⁻¹' closedBall x h ∩ Ioc 0 (0 + 2 * π)) ∪ {0} := by
      rintro θ ⟨hθS, h0, hlt⟩
      rcases eq_or_lt_of_le h0 with rfl | hpos
      · exact Or.inr rfl
      · exact Or.inl ⟨hθS, hpos, by linarith⟩
    grw [measure_mono hsub, measure_union_le _ _]
    rw [Real.volume_singleton, add_zero, hshift]
    grw [measure_mono hwindow]
    rw [Real.volume_Icc]
    gcongr
    ring_nf; simp
  -- assemble
  rw [circleMeasure, Measure.map_apply (measurable_circleMap 0 1) measurableSet_closedBall,
    angularMeasure, Measure.smul_apply, Measure.restrict_apply hS_meas, smul_eq_mul]
  grw [mul_le_mul' le_rfl hIco]
  rw [(ENNReal.ofReal_mul (by positivity)).symm]
  gcongr; field_simp; simp




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



/-!
### Fatou's theorem

This is Garnett, *Bounded Analytic Functions*, Theorem I.5.3, in the disc form with `p = 1`, which
is the only case this project uses. -/

/-- **Lebesgue points of an `L¹` boundary density**: at almost every point of the circle the average of
`|k - k ζ|` over the arc cut out by `closedBall ζ r` tends to `0` as `r → 0⁺`. -/
theorem ae_tendsto_average_abs_sub_circleMeasure {k : ℂ → ℝ}
    (hk : Integrable k (circleMeasure 0 1)) :
    ∀ᵐ ζ ∂circleMeasure 0 1,
      Tendsto (fun r : ℝ => ⨍ z in closedBall ζ r, |k z - k ζ| ∂circleMeasure 0 1)
        (𝓝[>] 0) (𝓝 0) := by
  -- Claude without review
  set v := Besicovitch.vitaliFamily (circleMeasure 0 1) with hv
  filter_upwards [v.ae_tendsto_average_norm_sub hk.locallyIntegrable] with ζ hζ
  -- shrinking closed balls do tend to `ζ` along the Vitali family
  have hball : Tendsto (fun r : ℝ => closedBall ζ r) (𝓝[>] 0) (v.filterAt ζ) := by
    rw [VitaliFamily.tendsto_filterAt_iff]
    refine ⟨?_, fun ε hε => ?_⟩
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact ⟨r, hr, rfl⟩
    · have hlt : ∀ᶠ r : ℝ in 𝓝[>] 0, r < ε := nhdsWithin_le_nhds (Iio_mem_nhds hε)
      filter_upwards [hlt] with r hr
      exact closedBall_subset_closedBall hr.le
  have hζ' : Tendsto (fun a => ⨍ y in a, |k y - k ζ| ∂circleMeasure 0 1)
      (v.filterAt ζ) (𝓝 0) := by
    simpa [Real.norm_eq_abs] using hζ
  exact hζ'.comp hball


/-- **Raw pointwise Poisson bound.**  If a finite positive measure `ν` carried by the unit circle
satisfies the *uniform* density bound `ν (closedBall ζ r) ≤ c * σ (closedBall ζ r)` for **every**
`r > 0`, then its Poisson integral is bounded by `C α * c` throughout the approach region
`stolzSetAt ζ α`, with a constant depending only on the aperture. -/
theorem integral_poissonKernel_le_of_measure_closedBall_le
    {ν : Measure ℂ} [IsFiniteMeasure ν] (hν : ν (sphere 0 1)ᶜ = 0)
    {ζ : ℂ} (hζ : ‖ζ‖ = 1) {α c : ℝ} (hc : 0 ≤ c)
    (hball : ∀ r > 0, ν (closedBall ζ r) ≤ ENNReal.ofReal c * circleMeasure 0 1 (closedBall ζ r))
    {z : ℂ} (hz : z ∈ stolzSetAt ζ α) :
    ∫ w, poissonKernel 0 z w ∂ν ≤ 8 * (α + 2) ^ 2 * c := by
  -- Claude without review
  classical
  obtain ⟨hz1, hz2⟩ := hz
  have hzΓ : z ∈ stolzSetAt ζ α := ⟨hz1, hz2⟩
  set δ : ℝ := 1 - ‖z‖ with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hα2 : (0:ℝ) < α + 2 := by nlinarith [norm_nonneg (ζ - z), norm_nonneg z]
  set A : ℝ := 2 * (α + 2) ^ 2 with hAdef
  have hA : 0 < A := by rw [hAdef]; positivity
  have hzball : z ∈ ball (0:ℂ) 1 := mem_ball_zero_iff.mpr hz1
  set B : ℕ → Set ℂ := fun j => closedBall ζ (2 ^ j * δ) with hBdef
  set S : ℕ → Set ℂ := fun j => if j = 0 then B 0 else B j \ B (j - 1) with hSdef
  -- (1) cover
  have hcover : (univ : Set ℂ) ⊆ ⋃ j, S j := by
    intro w _
    have hex : ∃ j : ℕ, w ∈ B j := by
      obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (‖w - ζ‖ / δ) (one_lt_two (α := ℝ))
      refine ⟨j, ?_⟩
      rw [hBdef]
      simp only [mem_closedBall, dist_eq_norm]
      rw [div_lt_iff₀ hδ] at hj
      nlinarith
    refine mem_iUnion.mpr ⟨Nat.find hex, ?_⟩
    have hjmem : w ∈ B (Nat.find hex) := Nat.find_spec hex
    rw [hSdef]
    by_cases hj0 : Nat.find hex = 0
    · simp only [hj0, if_pos]
      rw [hj0] at hjmem; exact hjmem
    · simp only [hj0, if_false]
      refine ⟨hjmem, ?_⟩
      exact Nat.find_min hex (Nat.sub_lt (Nat.pos_of_ne_zero hj0) one_pos)
  -- (2) kernel bound on each piece
  have hker : ∀ j : ℕ, ∀ w ∈ S j, ‖w‖ = 1 →
      ENNReal.ofReal (poissonKernel 0 z w) ≤ ENNReal.ofReal (4 * A / (4 ^ j * δ)) := by
    intro j w hw hw1
    refine ENNReal.ofReal_le_ofReal ?_
    have hbase := poissonKernel_le_of_mem_stolzSetAt hζ hzΓ hw1
    have hnum : (0:ℝ) ≤ A * δ := by positivity
    have hlow : ∀ s : ℝ, 0 < s → s ≤ δ + ‖w - ζ‖ →
        A * δ / ((δ + ‖w - ζ‖)) ^ 2 ≤ A * δ / s ^ 2 := by
      intro s hs hle
      exact div_le_div_of_nonneg_left hnum (pow_pos hs 2) (pow_le_pow_left₀ hs.le hle 2)
    have hrw : 2 * (α + 2) ^ 2 * (1 - ‖z‖) = A * δ := by rw [hAdef, hδdef]
    rw [hrw] at hbase
    by_cases hj0 : j = 0
    · subst hj0
      simp only [hSdef, if_pos rfl, hBdef, pow_zero, one_mul, mem_closedBall, dist_eq_norm] at hw
      have hδle : δ ≤ δ + ‖w - ζ‖ := le_add_of_nonneg_right (norm_nonneg _)
      have h1 : A * δ / (δ + ‖w - ζ‖) ^ 2 ≤ A * δ / δ ^ 2 := hlow δ hδ hδle
      have h2 : A * δ / δ ^ 2 = A / δ := by field_simp
      have h3 : A / δ ≤ 4 * A / (4 ^ (0:ℕ) * δ) := by
        simp only [pow_zero, one_mul]
        rw [div_le_div_iff₀ hδ hδ]; nlinarith
      linarith [hbase, h1, h2.le, h2.ge, h3]
    · simp only [hSdef, if_neg hj0, hBdef, Set.mem_sdiff, mem_closedBall, dist_eq_norm,
        not_le] at hw
      obtain ⟨-, hout⟩ := hw
      have hpow : (0:ℝ) < 2 ^ (j - 1) * δ := by positivity
      have hle2 : 2 ^ (j - 1) * δ ≤ δ + ‖w - ζ‖ := by linarith [hδ.le, hout]
      have h1 : A * δ / (δ + ‖w - ζ‖) ^ 2 ≤ A * δ / (2 ^ (j - 1) * δ) ^ 2 :=
        hlow (2 ^ (j - 1) * δ) hpow hle2
      have hj1 : j - 1 + 1 = j := Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hj0)
      have h4 : ((4:ℝ) ^ j) = 4 * 4 ^ (j - 1) := by
        conv_lhs => rw [← hj1]
        rw [pow_succ]; ring
      have h5 : ((2:ℝ) ^ (j - 1)) ^ 2 = 4 ^ (j - 1) := by
        rw [← pow_mul, mul_comm, pow_mul]; norm_num
      have h6 : (0:ℝ) < 4 ^ (j - 1) := by positivity
      have hδ' : δ ≠ 0 := hδ.ne'
      have h6' : ((4:ℝ) ^ (j - 1)) ≠ 0 := h6.ne'
      have h2 : A * δ / (2 ^ (j - 1) * δ) ^ 2 = 4 * A / (4 ^ j * δ) := by
        rw [mul_pow, h5, h4]
        field_simp
      linarith [hbase, h1, h2.le, h2.ge]
  -- (3) measure of each piece
  have hmeasS : ∀ j : ℕ, ν (S j) ≤ ENNReal.ofReal (c * (2 ^ j * δ) / 2) := by
    intro j
    have hsub : S j ⊆ B j := by
      rw [hSdef]; by_cases hj0 : j = 0
      · simp [hj0]
      · simp only [hj0, if_false]; exact sdiff_subset
    have hr : (0:ℝ) < 2 ^ j * δ := by positivity
    calc ν (S j) ≤ ν (B j) := measure_mono hsub
      _ ≤ ENNReal.ofReal c * circleMeasure 0 1 (closedBall ζ (2 ^ j * δ)) := hball _ hr
      _ ≤ ENNReal.ofReal c * ENNReal.ofReal ((2 ^ j * δ) / 2) :=
          mul_le_mul' le_rfl (circleMeasure_closedBall_le_of_norm_eq_one hζ)
      _ = ENNReal.ofReal (c * (2 ^ j * δ) / 2) := by
          rw [← ENNReal.ofReal_mul hc]; ring_nf
  -- (4) measurability of the pieces
  have hSmeas : ∀ j : ℕ, MeasurableSet (S j) := by
    intro j
    rw [hSdef]
    by_cases hj0 : j = 0
    · simp only [hj0, if_pos, hBdef]; exact measurableSet_closedBall
    · simp only [hj0, if_false, hBdef]
      exact measurableSet_closedBall.diff measurableSet_closedBall
  -- (5) per-piece lintegral bound
  have hpiece : ∀ j : ℕ, ∫⁻ w in S j, ENNReal.ofReal (poissonKernel 0 z w) ∂ν
      ≤ ENNReal.ofReal (2 * A * c) / 2 ^ j := by
    intro j
    have hstep : ∫⁻ w in S j, ENNReal.ofReal (poissonKernel 0 z w) ∂ν
        ≤ ENNReal.ofReal (4 * A / (4 ^ j * δ)) * ν (S j) := by
      calc ∫⁻ w in S j, ENNReal.ofReal (poissonKernel 0 z w) ∂ν
          ≤ ∫⁻ _ in S j, ENNReal.ofReal (4 * A / (4 ^ j * δ)) ∂ν := by
            refine setLIntegral_mono_ae measurable_const.aemeasurable ?_
            filter_upwards [ae_iff.2 hν] with w hwsph hwS
            exact hker j w hwS (mem_sphere_zero_iff_norm.mp hwsph)
        _ = ENNReal.ofReal (4 * A / (4 ^ j * δ)) * ν (S j) := setLIntegral_const _ _
    have harith : ENNReal.ofReal (4 * A / (4 ^ j * δ)) * ENNReal.ofReal (c * (2 ^ j * δ) / 2)
        = ENNReal.ofReal (2 * A * c) / 2 ^ j := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      have hval : 4 * A / (4 ^ j * δ) * (c * (2 ^ j * δ) / 2) = 2 * A * c / 2 ^ j := by
        have h2j : (0:ℝ) < 2 ^ j := by positivity
        have h4j : ((4:ℝ) ^ j) = 2 ^ j * 2 ^ j := by
          rw [← mul_pow]; norm_num
        rw [h4j]
        field_simp
        ring
      rw [hval, ENNReal.ofReal_div_of_pos (by positivity)]
      congr 1
      rw [ENNReal.ofReal_pow (by norm_num)]
      norm_num
    calc ∫⁻ w in S j, ENNReal.ofReal (poissonKernel 0 z w) ∂ν
        ≤ ENNReal.ofReal (4 * A / (4 ^ j * δ)) * ν (S j) := hstep
      _ ≤ ENNReal.ofReal (4 * A / (4 ^ j * δ)) * ENNReal.ofReal (c * (2 ^ j * δ) / 2) :=
          mul_le_mul' le_rfl (hmeasS j)
      _ = ENNReal.ofReal (2 * A * c) / 2 ^ j := harith
  -- (6) sum up
  have hlint : ∫⁻ w, ENNReal.ofReal (poissonKernel 0 z w) ∂ν
      ≤ ENNReal.ofReal (8 * (α + 2) ^ 2 * c) := by
    have hgeom : ∑' j : ℕ, ENNReal.ofReal (2 * A * c) / 2 ^ j
        = ENNReal.ofReal (2 * A * c) * 2 := by
      have : ∀ j : ℕ, ENNReal.ofReal (2 * A * c) / 2 ^ j
          = ENNReal.ofReal (2 * A * c) * (2:ℝ≥0∞)⁻¹ ^ j := by
        intro j; rw [ENNReal.div_eq_inv_mul, ENNReal.inv_pow, mul_comm]
      simp only [this]
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
      congr 1
      rw [show (1 : ℝ≥0∞) - 2⁻¹ = 2⁻¹ from ENNReal.sub_eq_of_eq_add (by simp)
        (by rw [ENNReal.inv_two_add_inv_two])]
      simp
    calc ∫⁻ w, ENNReal.ofReal (poissonKernel 0 z w) ∂ν
        = ∫⁻ w in univ, ENNReal.ofReal (poissonKernel 0 z w) ∂ν := (setLIntegral_univ _).symm
      _ ≤ ∫⁻ w in ⋃ j, S j, ENNReal.ofReal (poissonKernel 0 z w) ∂ν :=
          lintegral_mono_set hcover
      _ ≤ ∑' j, ∫⁻ w in S j, ENNReal.ofReal (poissonKernel 0 z w) ∂ν :=
          lintegral_iUnion_le _ _
      _ ≤ ∑' j : ℕ, ENNReal.ofReal (2 * A * c) / 2 ^ j := ENNReal.tsum_le_tsum hpiece
      _ = ENNReal.ofReal (2 * A * c) * 2 := hgeom
      _ = ENNReal.ofReal (8 * (α + 2) ^ 2 * c) := by
          rw [show (2:ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [hAdef]; ring
  -- (7) transfer to the Bochner integral
  have hnonneg : 0 ≤ᵐ[ν] fun w => poissonKernel 0 z w := by
    filter_upwards [ae_iff.2 hν] with w hw
    exact poissonKernel_nonneg hzball hw
  have hint : Integrable (fun w => poissonKernel 0 z w) ν := integrable_poissonKernel hν hzball
  rw [integral_eq_lintegral_of_nonneg_ae hnonneg hint.1]
  grw [ENNReal.toReal_mono ENNReal.ofReal_ne_top hlint]
  rw [ENNReal.toReal_ofReal (by positivity)]


/-- **Density zero forces the Poisson integral to vanish nontangentially** (Rudin, *Real and
Complex Analysis*, 11.22).  If a finite positive measure `ν` carried by the unit circle has
vanishing density at `ζ` with respect to normalized arclength, then `P[ν]` tends to `0` along the
nontangential filter at `ζ`.-/
theorem hasNontangentialLimit_integral_poissonKernel_of_density_zero
    {ν : Measure ℂ} [IsFiniteMeasure ν] (hν : ν (sphere 0 1)ᶜ = 0) {ζ : ℂ} (hζ : ‖ζ‖ = 1)
    (hdens : Tendsto (fun r : ℝ => ν (closedBall ζ r) / circleMeasure 0 1 (closedBall ζ r))
      (𝓝[>] 0) (𝓝 0)) :
    HasNontangentialLimit (poissonIntegralSigned 0 ν.toSignedMeasure) ζ 0 := by
  -- Claude without review
  rw [poissonIntegralSigned_toSignedMeasure, hasNontangentialLimit_iff_forall]
  intro α hα
  have hα2 : (0 : ℝ) < α + 2 := by linarith
  have hApos : (0 : ℝ) < 8 * (α + 2) ^ 2 :=
    mul_pos (by norm_num) (pow_pos hα2 2)
  rw [HasNontangentialLimitWithin, Metric.tendsto_nhds]
  intro ε hε
  -- choose ε' so that the near part is ≤ ε / 4
  set ε' : ℝ := ε / (4 * (8 * (α + 2) ^ 2)) with hε'def
  have hε'pos : 0 < ε' := by
    rw [hε'def]; positivity
  -- from density zero: a uniform bound below scale R
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ν (closedBall ζ r) / circleMeasure 0 1 (closedBall ζ r) ≤ ENNReal.ofReal ε' :=
    ENNReal.tendsto_nhds_zero.mp hdens _ (ENNReal.ofReal_pos.mpr hε'pos)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨R, hRpos, hR⟩ := hev
  have hRuse : ∀ r : ℝ, 0 < r → r < R →
      ν (closedBall ζ r) ≤ ENNReal.ofReal ε' * circleMeasure 0 1 (closedBall ζ r) := by
    intro r hr0 hrR
    have hd : dist r 0 < R := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hr0]; exact hrR
    exact (ENNReal.div_le_iff_le_mul (Or.inr ENNReal.ofReal_ne_top)
      (Or.inl (measure_ne_top _ _))).mp (hR hd (mem_Ioi.mpr hr0))
  -- split at radius R' = R / 2
  set R' : ℝ := R / 2 with hR'def
  have hR'pos : 0 < R' := by rw [hR'def]; positivity
  have hR'lt : R' < R := by rw [hR'def]; linarith
  have hB : MeasurableSet (closedBall ζ R') := measurableSet_closedBall
  haveI hfin_n : IsFiniteMeasure (ν.restrict (closedBall ζ R')) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_lt_top ν _⟩
  haveI hfin_f : IsFiniteMeasure (ν.restrict (closedBall ζ R')ᶜ) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_lt_top ν _⟩
  have hνn_car : ν.restrict (closedBall ζ R') (sphere 0 1)ᶜ = 0 := by
    rw [Measure.restrict_apply (isClosed_sphere.measurableSet).compl]
    exact measure_mono_null inter_subset_left hν
  have hνf_car : ν.restrict (closedBall ζ R')ᶜ (sphere 0 1)ᶜ = 0 := by
    rw [Measure.restrict_apply (isClosed_sphere.measurableSet).compl]
    exact measure_mono_null inter_subset_left hν
  -- the near part satisfies the uniform ball bound at every scale
  have hball : ∀ r > 0, ν.restrict (closedBall ζ R') (closedBall ζ r)
      ≤ ENNReal.ofReal ε' * circleMeasure 0 1 (closedBall ζ r) := by
    intro r hr
    rcases le_or_gt r R' with hcase | hcase
    · calc ν.restrict (closedBall ζ R') (closedBall ζ r)
          ≤ ν (closedBall ζ r) := Measure.restrict_le_self _
        _ ≤ _ := hRuse r hr (lt_of_le_of_lt hcase hR'lt)
    · calc ν.restrict (closedBall ζ R') (closedBall ζ r)
          ≤ ν.restrict (closedBall ζ R') univ := measure_mono (subset_univ _)
        _ = ν (closedBall ζ R') := Measure.restrict_apply_univ _
        _ ≤ ENNReal.ofReal ε' * circleMeasure 0 1 (closedBall ζ R') :=
            hRuse R' hR'pos hR'lt
        _ ≤ ENNReal.ofReal ε' * circleMeasure 0 1 (closedBall ζ r) :=
            mul_le_mul' le_rfl (measure_mono (closedBall_subset_closedBall hcase.le))
  -- constants for the far part
  set K : ℝ := 2 * (α + 2) ^ 2 / R' ^ 2 * ((ν univ).toReal + 1) with hKdef
  have hKpos : 0 < K := by
    rw [hKdef]
    exact mul_pos (div_pos (mul_pos two_pos (pow_pos hα2 2)) (pow_pos hR'pos 2))
      (add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg one_pos)
  set δ : ℝ := (ε / 2) / K with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; exact div_pos (half_pos hε) hKpos
  -- the two eventual facts
  have hev1 : ∀ᶠ z in 𝓝[stolzSetAt ζ α] ζ, z ∈ stolzSetAt ζ α := self_mem_nhdsWithin
  have hev2 : ∀ᶠ z in 𝓝[stolzSetAt ζ α] ζ, z ∈ ball ζ δ :=
    nhdsWithin_le_nhds (Metric.ball_mem_nhds ζ hδpos)
  filter_upwards [hev1, hev2] with z hzΓ hzδ
  have hz1 : ‖z‖ < 1 := hzΓ.1
  have hzball : z ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr hz1
  have h1z : (0 : ℝ) ≤ 1 - ‖z‖ := by linarith
  -- global integrability, restricted to the pieces
  have hint : Integrable (fun w => poissonKernel 0 z w) ν :=
    integrable_poissonKernel hν hzball
  have hint_n : Integrable (fun w => poissonKernel 0 z w) (ν.restrict (closedBall ζ R')) :=
    hint.restrict
  have hint_f : Integrable (fun w => poissonKernel 0 z w) (ν.restrict (closedBall ζ R')ᶜ) :=
    hint.restrict
  -- split the integral
  have hsplit : ∫ w, poissonKernel 0 z w ∂ν
      = (∫ w, poissonKernel 0 z w ∂(ν.restrict (closedBall ζ R')))
        + ∫ w, poissonKernel 0 z w ∂(ν.restrict (closedBall ζ R')ᶜ) := by
    conv_lhs => rw [← Measure.restrict_add_restrict_compl (μ := ν) hB]
    exact integral_add_measure hint_n hint_f
  -- near estimate via the raw pointwise bound
  have hnear : ∫ w, poissonKernel 0 z w ∂(ν.restrict (closedBall ζ R'))
      ≤ 8 * (α + 2) ^ 2 * ε' :=
    integral_poissonKernel_le_of_measure_closedBall_le hνn_car hζ hε'pos.le hball hzΓ
  have hnear_eq : 8 * (α + 2) ^ 2 * ε' = ε / 4 := by
    rw [hε'def]
    field_simp
  -- far estimate: kernel bound at fixed distance
  have hbound : ∀ᵐ w ∂(ν.restrict (closedBall ζ R')ᶜ),
      poissonKernel 0 z w ≤ 2 * (α + 2) ^ 2 * (1 - ‖z‖) / R' ^ 2 := by
    filter_upwards [ae_restrict_mem hB.compl, ae_iff.2 hνf_car] with w hwB hwS
    have hw1 : ‖w‖ = 1 := mem_sphere_zero_iff_norm.mp hwS
    have hwR' : R' < ‖w - ζ‖ := by
      have hnot : ¬ w ∈ closedBall ζ R' := hwB
      rw [mem_closedBall, not_le, dist_eq_norm] at hnot
      exact hnot
    have hker := poissonKernel_le_of_mem_stolzSetAt hζ hzΓ hw1
    have hnum : (0 : ℝ) ≤ 2 * (α + 2) ^ 2 * (1 - ‖z‖) :=
      mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) h1z
    have hdenom : R' ≤ (1 - ‖z‖) + ‖w - ζ‖ := by nlinarith
    calc poissonKernel 0 z w
        ≤ 2 * (α + 2) ^ 2 * (1 - ‖z‖) / ((1 - ‖z‖) + ‖w - ζ‖) ^ 2 := hker
      _ ≤ 2 * (α + 2) ^ 2 * (1 - ‖z‖) / R' ^ 2 :=
          div_le_div_of_nonneg_left hnum (pow_pos hR'pos 2)
            (pow_le_pow_left₀ hR'pos.le hdenom 2)
  have hfar1 : ∫ w, poissonKernel 0 z w ∂(ν.restrict (closedBall ζ R')ᶜ)
      ≤ ((ν.restrict (closedBall ζ R')ᶜ) univ).toReal
          * (2 * (α + 2) ^ 2 * (1 - ‖z‖) / R' ^ 2) := by
    calc ∫ w, poissonKernel 0 z w ∂(ν.restrict (closedBall ζ R')ᶜ)
        ≤ ∫ _, 2 * (α + 2) ^ 2 * (1 - ‖z‖) / R' ^ 2 ∂(ν.restrict (closedBall ζ R')ᶜ) :=
          integral_mono_ae hint_f (integrable_const _) hbound
      _ = ((ν.restrict (closedBall ζ R')ᶜ) univ).toReal
            * (2 * (α + 2) ^ 2 * (1 - ‖z‖) / R' ^ 2) := by
          simp [integral_const, smul_eq_mul, measureReal_def]
  have hνf_le : ((ν.restrict (closedBall ζ R')ᶜ) univ).toReal ≤ (ν univ).toReal := by
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    rw [Measure.restrict_apply_univ]
    exact measure_mono (subset_univ _)
  have hdist : 1 - ‖z‖ < δ := by
    have h1 : 1 - ‖z‖ ≤ dist z ζ := by
      have h2 := norm_sub_norm_le ζ z
      rw [hζ] at h2
      rw [dist_eq_norm, norm_sub_rev]
      exact h2
    exact lt_of_le_of_lt h1 (mem_ball.mp hzδ)
  have hM_nonneg : (0 : ℝ) ≤ 2 * (α + 2) ^ 2 * (1 - ‖z‖) / R' ^ 2 :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) h1z) (sq_nonneg _)
  have hfar : ∫ w, poissonKernel 0 z w ∂(ν.restrict (closedBall ζ R')ᶜ) < ε / 2 := by
    have hchain : ∫ w, poissonKernel 0 z w ∂(ν.restrict (closedBall ζ R')ᶜ)
        ≤ K * (1 - ‖z‖) := by
      have hstep : ((ν.restrict (closedBall ζ R')ᶜ) univ).toReal
          * (2 * (α + 2) ^ 2 * (1 - ‖z‖) / R' ^ 2)
          ≤ ((ν univ).toReal + 1) * (2 * (α + 2) ^ 2 * (1 - ‖z‖) / R' ^ 2) := by
        apply mul_le_mul_of_nonneg_right _ hM_nonneg
        linarith
      have hre : ((ν univ).toReal + 1) * (2 * (α + 2) ^ 2 * (1 - ‖z‖) / R' ^ 2)
          = K * (1 - ‖z‖) := by
        rw [hKdef]; ring
      linarith [hfar1, hstep, hre.le, hre.ge]
    have hKδ : K * δ = ε / 2 := by
      rw [hδdef]
      field_simp
    calc ∫ w, poissonKernel 0 z w ∂(ν.restrict (closedBall ζ R')ᶜ)
        ≤ K * (1 - ‖z‖) := hchain
      _ < K * δ := by exact mul_lt_mul_of_pos_left hdist hKpos
      _ = ε / 2 := hKδ
  -- combine
  have hnonneg : 0 ≤ ∫ w, poissonKernel 0 z w ∂ν :=
    integral_poissonKernel_nonneg hν hzball
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg, hsplit]
  have := hnear_eq ▸ hnear
  linarith


/-- **Fatou at a Lebesgue point.**  At a point `ζ` of the unit circle at which the boundary density
`k` has vanishing mean oscillation in the sense of `ae_tendsto_average_abs_sub_circleMeasure`, the
Poisson integral `P[k dθ/2π]` has nontangential limit `k ζ`.-/
theorem hasNontangentialLimit_poissonIntegral_of_lebesguePoint {k : ℂ → ℝ}
    (hk : Integrable k (circleMeasure 0 1)) {ζ : ℂ} (hζ : ‖ζ‖ = 1)
    (hleb : Tendsto (fun r : ℝ => ⨍ z in closedBall ζ r, |k z - k ζ| ∂circleMeasure 0 1)
      (𝓝[>] 0) (𝓝 0)) :
    HasNontangentialLimit (poissonIntegral 0 (circleMeasure 0 1) k) ζ (k ζ) := by
  -- Claude without review
  set σ := circleMeasure 0 1 with hσdef
  set ρ := σ.withDensity (fun w => ENNReal.ofReal |k w - k ζ|) with hρdef
  haveI hfin : IsFiniteMeasure ρ :=
    isFiniteMeasure_withDensity_ofReal ((hk.sub (integrable_const (k ζ))).abs).2
  have hcar : σ (sphere (0:ℂ) 1)ᶜ = 0 := ae_iff.1 (ae_mem_sphere_circleMeasure zero_le_one)
  have hρcar : ρ (sphere (0:ℂ) 1)ᶜ = 0 := withDensity_absolutelyContinuous σ _ hcar
  have hseam : ∀ r : ℝ, ρ (closedBall ζ r) / σ (closedBall ζ r)
      = ENNReal.ofReal (⨍ z in closedBall ζ r, |k z - k ζ| ∂σ) := by
    intro r
    set B := closedBall ζ r
    have hint : Integrable (fun w => |k w - k ζ|) (σ.restrict B) :=
      ((hk.sub (integrable_const (k ζ))).abs).restrict
    have hbridge : ρ B = ENNReal.ofReal (∫ w in B, |k w - k ζ| ∂σ) := by
      rw [hρdef, withDensity_apply _ measurableSet_closedBall,
        ← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun w => abs_nonneg _)]
    have hσtop : σ B ≠ ⊤ := measure_ne_top σ B
    rw [hbridge, setAverage_eq, smul_eq_mul, ← ENNReal.ofReal_toReal hσtop, measureReal_def]
    rcases eq_or_lt_of_le (ENNReal.toReal_nonneg (a := σ B)) with hb | hb
    · have hσ0 : σ B = 0 := by
        have := (ENNReal.toReal_eq_zero_iff (σ B)).1 hb.symm
        tauto
      have hI0 : ∫ w in B, |k w - k ζ| ∂σ = 0 := by
        rw [Measure.restrict_eq_zero.2 hσ0, integral_zero_measure]
      simp [hI0, ← hb]
    · rw [← ENNReal.ofReal_div_of_pos hb]
      congr 1
      field_simp
  have hdens : Tendsto (fun r : ℝ => ρ (closedBall ζ r) / σ (closedBall ζ r)) (𝓝[>] 0) (𝓝 0) := by
    simp only [hseam]; simpa using ENNReal.tendsto_ofReal hleb
  have hL3 : HasNontangentialLimit (fun z => ∫ w, poissonKernel 0 z w ∂ρ) ζ 0 := by
    simpa using hasNontangentialLimit_integral_poissonKernel_of_density_zero hρcar hζ hdens
  have hball : ∀ᶠ z in nontangentially ζ, z ∈ ball (0:ℂ) 1 := by
    rw [nontangentially, eventually_iSup]
    intro α
    rw [eventually_iSup]
    intro _
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact mem_ball_zero_iff.2 hz.1
  have hle : ∀ᶠ z in nontangentially ζ,
      ‖poissonIntegral 0 σ k z - k ζ‖ ≤ ∫ w, poissonKernel 0 z w ∂ρ := by
    filter_upwards [hball] with z hz
    have hPk : Integrable (fun w => poissonKernel 0 z w * k w) σ :=
      integrable_poissonKernel_mul hcar hz hk
    have hPc : Integrable (fun w => poissonKernel 0 z w * k ζ) σ :=
      integrable_poissonKernel_mul hcar hz (integrable_const _)
    have hone : ∫ w, poissonKernel 0 z w * k ζ ∂σ = k ζ := by
      rw [integral_mul_const, integral_poissonKernel_circleMeasure_eq_one hz, one_mul]
    have hdiff : poissonIntegral 0 σ k z - k ζ
        = ∫ w, poissonKernel 0 z w * (k w - k ζ) ∂σ := by
      have hsplit : ∫ w, poissonKernel 0 z w * (k w - k ζ) ∂σ
          = (∫ w, poissonKernel 0 z w * k w ∂σ) - ∫ w, poissonKernel 0 z w * k ζ ∂σ := by
        rw [← integral_sub hPk hPc]
        congr 1; funext w; ring
      rw [hsplit, hone, poissonIntegral]
      simp [smul_eq_mul]
    have habs : |∫ w, poissonKernel 0 z w * (k w - k ζ) ∂σ|
      ≤ ∫ w, poissonKernel 0 z w * |k w - k ζ| ∂σ := by
      calc |∫ w, poissonKernel 0 z w * (k w - k ζ) ∂σ|
          ≤ ∫ w, |poissonKernel 0 z w * (k w - k ζ)| ∂σ := abs_integral_le_integral_abs
        _ = ∫ w, poissonKernel 0 z w * |k w - k ζ| ∂σ := by
            refine integral_congr_ae ?_
            filter_upwards [ae_mem_sphere_circleMeasure (c := 0) (R := 1) zero_le_one] with w hw
            rw [abs_mul, abs_of_nonneg (poissonKernel_nonneg hz hw)]
    have hbridge2 : ∫ w, poissonKernel 0 z w ∂ρ
        = ∫ w, poissonKernel 0 z w * |k w - k ζ| ∂σ := by
      have hmeas : AEMeasurable (fun w => ENNReal.ofReal |k w - k ζ|) σ :=
        ((hk.sub (integrable_const (k ζ))).abs).1.aemeasurable.ennreal_ofReal
      rw [hρdef, integral_withDensity_eq_integral_toReal_smul₀ hmeas
        (Eventually.of_forall fun w => ENNReal.ofReal_lt_top)]
      refine integral_congr_ae (Eventually.of_forall fun w => ?_)
      simp [ENNReal.toReal_ofReal (abs_nonneg _), smul_eq_mul, mul_comm]
    rw [Real.norm_eq_abs, hdiff, hbridge2]
    exact habs
  have hzero : Tendsto (fun z => poissonIntegral 0 σ k z - k ζ) (nontangentially ζ) (𝓝 0) :=
    squeeze_zero_norm' hle hL3
  have hfin' := hzero.add_const (k ζ)
  simp only [sub_add_cancel, zero_add] at hfin'
  exact hfin'

/-- **The absolutely continuous half of Theorem I.5.3**: The Poisson integral `P[k dθ/2π]`
of an `L¹` density has that density as its nontangential boundary value. -/
theorem isAEBoundaryValue_poissonIntegral {k : ℂ → ℝ}
    (hk : Integrable k (circleMeasure 0 1)) :
    IsAEBoundaryValue (circleMeasure 0 1) (poissonIntegral 0 (circleMeasure 0 1) k) k := by
  filter_upwards [ae_tendsto_average_abs_sub_circleMeasure hk,
    ae_mem_sphere_circleMeasure zero_le_one] with ζ hleb hmem
  exact hasNontangentialLimit_poissonIntegral_of_lebesguePoint hk
    (mem_sphere_zero_iff_norm.1 hmem) hleb

/-- **Garnett I.5.4**: the Poisson integral of a boundary measure singular with respect to
arclength has nontangential limit zero almost everywhere. -/
theorem isAEBoundaryValue_poissonIntegralSigned_zero_of_mutuallySingular
    {ν : SignedMeasure ℂ} (hν : ν.totalVariation (sphere 0 1)ᶜ = 0)
    (hsing : ν ⟂ᵥ (circleMeasure 0 1).toENNRealVectorMeasure) :
    IsAEBoundaryValue (circleMeasure 0 1) (poissonIntegralSigned 0 ν) 0 := by
  have hsing_total : ν.totalVariation ⟂ₘ circleMeasure 0 1 := by
    rw [SignedMeasure.mutuallySingular_ennreal_iff,
      VectorMeasure.ennrealToMeasure_toENNRealVectorMeasure] at hsing
    exact hsing
  have hvariation_le : ν.variation ≤ ν.totalVariation := by
    conv_lhs => rw [← ν.toSignedMeasure_toJordanDecomposition]
    rw [JordanDecomposition.toSignedMeasure, sub_eq_add_neg]
    grw [VectorMeasure.variation_add_le]
    simp [SignedMeasure.totalVariation]
  have hvariation_carried : ν.variation (sphere 0 1)ᶜ = 0 :=
    hvariation_le.absolutelyContinuous hν
  have hvariation_singular : ν.variation ⟂ₘ circleMeasure 0 1 :=
    hsing_total.mono hvariation_le le_rfl
  haveI htotal_finite : IsFiniteMeasure ν.totalVariation := by
    rw [SignedMeasure.totalVariation]
    infer_instance
  haveI : IsFiniteMeasure ν.variation := by
    constructor
    exact lt_of_le_of_lt (hvariation_le univ) (measure_lt_top ν.totalVariation univ)
  let v := Besicovitch.vitaliFamily (circleMeasure 0 1)
  have hdensity_vitali : ∀ᵐ ζ ∂circleMeasure 0 1,
      Tendsto (fun a => ν.variation a / circleMeasure 0 1 a) (v.filterAt ζ) (𝓝 0) :=
    v.ae_eventually_measure_zero_of_singular hvariation_singular
  have hdensity : ∀ᵐ ζ ∂circleMeasure 0 1,
      Tendsto
        (fun r : ℝ => ν.variation (closedBall ζ r) /
          circleMeasure 0 1 (closedBall ζ r))
        (𝓝[>] 0) (𝓝 0) := by
    filter_upwards [hdensity_vitali] with ζ hζ
    exact hζ.comp (Besicovitch.tendsto_filterAt (circleMeasure 0 1) ζ)
  filter_upwards [hdensity,
    ae_mem_sphere_circleMeasure (c := 0) (R := 1) zero_le_one] with ζ hdensityζ hζ
  have hζnorm : ‖ζ‖ = 1 := mem_sphere_zero_iff_norm.1 hζ
  have hvariation_limit : HasNontangentialLimit
      (poissonIntegralSigned 0 ν.variation.toSignedMeasure) ζ 0 :=
    hasNontangentialLimit_integral_poissonKernel_of_density_zero
      hvariation_carried hζnorm hdensityζ
  have hball : ∀ᶠ z in nontangentially ζ, z ∈ ball (0 : ℂ) 1 := by
    rw [nontangentially, eventually_iSup]
    intro α
    rw [eventually_iSup]
    intro _
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact mem_ball_zero_iff.2 hz.1
  have hle : ∀ᶠ z in nontangentially ζ,
      ‖poissonIntegralSigned 0 ν z‖ ≤
        poissonIntegralSigned 0 ν.variation.toSignedMeasure z := by
    filter_upwards [hball] with z hz
    rw [poissonIntegralSigned_toSignedMeasure, poissonIntegralSigned]
    have hnonneg : ∀ᵐ w ∂ν.variation, 0 ≤ poissonKernel 0 z w := by
      filter_upwards [ae_iff.2 hvariation_carried] with w hw
      exact poissonKernel_nonneg hz hw
    calc
      ‖∫ᵛ w, poissonKernel 0 z w ∂<•ν‖
          ≤ ‖(ContinuousLinearMap.lsmul ℝ ℝ).flip‖ *
              ∫ w, ‖poissonKernel 0 z w‖ ∂ν.variation :=
        VectorMeasure.norm_integral_le_integral_norm
      _ = ∫ w, ‖poissonKernel 0 z w‖ ∂ν.variation := by simp
      _ = ∫ w, poissonKernel 0 z w ∂ν.variation := by
        refine integral_congr_ae ?_
        filter_upwards [hnonneg] with w hw
        exact norm_of_nonneg hw
  exact squeeze_zero_norm' hle hvariation_limit

/-- **Garnett I.5.3 (Fatou), disc form, `p = 1`**: the Poisson integral of a finite signed boundary
measure `μ` has, at almost every boundary point, a nontangential limit, equal there to the
Radon--Nikodym density of `μ` with respect to normalized arclength.  Equivalently, writing the
Lebesgue decomposition `dμ = k dθ/2π + dμ_s`, the boundary function of `P[μ]` is `k`. -/
theorem isAEBoundaryValue_poissonIntegralSigned_rnDeriv {μ : SignedMeasure ℂ}
    (hμ : μ.totalVariation (sphere 0 1)ᶜ = 0) :
    IsAEBoundaryValue (circleMeasure 0 1) (poissonIntegralSigned 0 μ)
      (μ.rnDeriv (circleMeasure 0 1)) := by
  let σ := circleMeasure 0 1
  let k := μ.rnDeriv σ
  have hk : Integrable k σ := SignedMeasure.integrable_rnDeriv μ σ
  have hσcar : σ (sphere (0 : ℂ) 1)ᶜ = 0 :=
    ae_iff.mp (ae_mem_sphere_circleMeasure (c := 0) (R := 1) zero_le_one)
  have hsing_le : (μ.singularPart σ).totalVariation ≤ μ.totalVariation := by
    rw [SignedMeasure.singularPart_totalVariation, SignedMeasure.totalVariation]
    exact add_le_add (Measure.singularPart_le _ _) (Measure.singularPart_le _ _)
  have hsing_car : (μ.singularPart σ).totalVariation (sphere 0 1)ᶜ = 0 :=
    hsing_le.absolutelyContinuous hμ
  have hsing_ae :
      IsAEBoundaryValue σ (poissonIntegralSigned 0 (μ.singularPart σ)) 0 :=
    isAEBoundaryValue_poissonIntegralSigned_zero_of_mutuallySingular hsing_car
      (SignedMeasure.mutuallySingular_singularPart μ σ)
  have hac_ae : IsAEBoundaryValue σ (poissonIntegral 0 σ k) k :=
    isAEBoundaryValue_poissonIntegral hk
  have hdecomp : μ.singularPart σ + σ.withDensityᵥ k = μ :=
    SignedMeasure.singularPart_add_withDensity_rnDeriv_eq σ μ
  have hdensity_eq : σ.withDensityᵥ k = μ - μ.singularPart σ := by
    apply eq_sub_iff_add_eq.mpr
    simpa only [add_comm] using hdecomp
  change IsAEBoundaryValue σ (poissonIntegralSigned 0 μ) k
  filter_upwards [hsing_ae, hac_ae] with ζ hsingζ hacζ
  have hsum : HasNontangentialLimit
      (fun z => poissonIntegralSigned 0 (μ.singularPart σ) z + poissonIntegral 0 σ k z)
      ζ (k ζ) := by
    change Tendsto _ (nontangentially ζ) (𝓝 (k ζ))
    simpa only [Pi.zero_apply, zero_add] using hsingζ.add hacζ
  have hinside : ∀ᶠ z in nontangentially ζ, z ∈ ball (0 : ℂ) 1 := by
    rw [nontangentially, eventually_iSup]
    intro α
    rw [eventually_iSup]
    intro _
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact mem_ball_zero_iff.2 hz.1
  have heq :
      (fun z => poissonIntegralSigned 0 (μ.singularPart σ) z + poissonIntegral 0 σ k z)
        =ᶠ[nontangentially ζ] poissonIntegralSigned 0 μ := by
    filter_upwards [hinside] with z hz
    have hsing_int : (μ.singularPart σ).Integrable (fun w => poissonKernel 0 z w) :=
      integrable_poissonKernel_totalVariation hsing_car hz
    have hμ_int : μ.Integrable (fun w => poissonKernel 0 z w) :=
      integrable_poissonKernel_totalVariation hμ hz
    have hdensity_int : (σ.withDensityᵥ k).Integrable (fun w => poissonKernel 0 z w) := by
      rw [hdensity_eq]
      exact hμ_int.sub_vectorMeasure hsing_int
    rw [poissonIntegral_eq_poissonIntegralSigned_withDensityᵥ hσcar hz hk,
      poissonIntegralSigned]
    calc
      _ = ∫ᵛ w, poissonKernel 0 z w ∂<•(μ.singularPart σ + σ.withDensityᵥ k) :=
        (VectorMeasure.integral_add_vectorMeasure hsing_int hdensity_int).symm
      _ = _ := by rw [hdecomp]; rfl
  exact hsum.congr' heq

/-- The boundary function of the Poisson integral of a finite signed boundary measure is its
Radon--Nikodym density with respect to normalized arclength. -/
theorem boundaryValue_poissonIntegralSigned {μ : SignedMeasure ℂ}
    (hμ : μ.totalVariation (sphere 0 1)ᶜ = 0) :
    μ.rnDeriv (circleMeasure 0 1) =ᵐ[circleMeasure 0 1]
      boundaryValue (poissonIntegralSigned 0 μ) :=
  (isAEBoundaryValue_poissonIntegralSigned_rnDeriv hμ).ae_eq_boundaryValue
    ae_nontangentially_neBot_circleMeasure

/-- The boundary function of the Poisson integral of a finite signed boundary measure is
measurable, and is in `L¹`. -/
theorem integrable_boundaryValue_poissonIntegralSigned {μ : SignedMeasure ℂ}
    (hμ : μ.totalVariation (sphere 0 1)ᶜ = 0) :
    Integrable (boundaryValue (poissonIntegralSigned 0 μ)) (circleMeasure 0 1) :=
  (SignedMeasure.integrable_rnDeriv μ (circleMeasure 0 1)).congr
    (boundaryValue_poissonIntegralSigned hμ)
