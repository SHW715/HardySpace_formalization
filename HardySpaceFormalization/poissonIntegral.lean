import HardySpaceFormalization.Poisson_lemma
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
import HardySpaceFormalization.Harmonic_max_principle
import HardySpaceFormalization.circleMeasure
import HardySpaceFormalization.HardySpaceDisc
import HardySpaceFormalization.LpDuality
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.MeasureTheory.VectorMeasure.Integral
import Mathlib.MeasureTheory.VectorMeasure.WithDensity

noncomputable section

open Complex Metric Real Set MeasureTheory HardySpace Filter
open scoped Topology ENNReal

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : ℂ → E} {R : ℝ} {w c : ℂ} {s : Set ℂ}


/-!
### Integrals of parameterized harmonic families

The purpose is to reach `harmonicOnNhd_poissonIntegral`: a compact-parameter
interval integral of a jointly continuous family is continuous; ball averages commute with such an
integral; hence interval integrals, and then circle averages, of a harmonic family stay harmonic.
-/

/-- Joint continuity on `s ×ˢ uIcc a b` implies continuity of the compact-parameter interval
integral in the base variable. -/
theorem ContinuousOn.intervalIntegral_uIcc
    {a b : ℝ} {Φ : ℂ → ℝ → E} {s : Set ℂ}
    (hcont : ContinuousOn (fun p : ℂ × ℝ => Φ p.1 p.2) (s ×ˢ uIcc a b)) :
    ContinuousOn (fun w : ℂ => ∫ θ in a..b, Φ w θ) s := by
  -- codex without review
  rw [continuousOn_iff_continuous_restrict]
  by_cases hab : a ≤ b
  · let Ψ : s → ℝ → E := fun w θ =>
      Φ w ((Set.projIcc a b hab θ : Set.Icc a b) : ℝ)
    have hΨcont : Continuous (Function.uncurry Ψ) := by
      dsimp [Ψ, Function.uncurry]
      have hmap : Continuous fun p : s × ℝ =>
          ((p.1 : ℂ), ((Set.projIcc a b hab p.2 : Set.Icc a b) : ℝ)) :=
        (continuous_subtype_val.comp continuous_fst).prodMk
          (continuous_subtype_val.comp (continuous_projIcc.comp continuous_snd))
      exact hcont.comp_continuous
        hmap
        (fun (p : s × ℝ) => by
          exact ⟨p.1.2, by
            simp [Set.uIcc_of_le hab, (Set.projIcc a b hab p.2).2]⟩)
    have hΨint_cont : Continuous fun w : s => ∫ θ in a..b, Ψ w θ :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hΨcont a b
    refine hΨint_cont.congr fun w => ?_
    exact intervalIntegral.integral_congr fun θ hθ => by
      have hθIcc : θ ∈ Set.Icc a b := by
        simpa [Set.uIcc_of_le hab] using hθ
      simp [Ψ, Set.projIcc_of_mem hab hθIcc]
  · have hba : b ≤ a := le_of_not_ge hab
    let Ψ : s → ℝ → E := fun w θ =>
      Φ w ((Set.projIcc b a hba θ : Set.Icc b a) : ℝ)
    have hΨcont : Continuous (Function.uncurry Ψ) := by
      dsimp [Ψ, Function.uncurry]
      have hmap : Continuous fun p : s × ℝ =>
          ((p.1 : ℂ), ((Set.projIcc b a hba p.2 : Set.Icc b a) : ℝ)) :=
        (continuous_subtype_val.comp continuous_fst).prodMk
          (continuous_subtype_val.comp (continuous_projIcc.comp continuous_snd))
      exact hcont.comp_continuous
        hmap
        (fun (p : s × ℝ) => by
          exact ⟨p.1.2, by
            simp [Set.uIcc_of_ge hba, (Set.projIcc b a hba p.2).2]⟩)
    have hΨint_cont : Continuous fun w : s => ∫ θ in a..b, Ψ w θ :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hΨcont a b
    refine hΨint_cont.congr fun w => ?_
    exact intervalIntegral.integral_congr fun θ hθ => by
      have hθIcc : θ ∈ Set.Icc b a := by
        simpa [Set.uIcc_of_ge hba] using hθ
      simp [Ψ, Set.projIcc_of_mem hba hθIcc]


/-- Ball averages commute with compact-parameter interval integrals for jointly continuous
integrands. -/
theorem ballAverage_intervalIntegral_comm
    {a b r : ℝ} {x : ℂ} {Φ : ℂ → ℝ → E}
    (hcont : ContinuousOn (fun p : ℂ × ℝ => Φ p.1 p.2)
      (closedBall x |r| ×ˢ uIcc a b)) :
    ballAverage (fun w : ℂ => ∫ θ in a..b, Φ w θ) x r =
      ∫ θ in a..b, ballAverage (fun w : ℂ => Φ w θ) x r := by
  -- codex without review
  have hcont_swap : ContinuousOn (fun p : ℝ × ℂ => Φ p.2 p.1)
      (uIcc a b ×ˢ closedBall x |r|) := by
    exact hcont.comp (f := fun p : ℝ × ℂ => (p.2, p.1))
     (continuous_snd.prodMk continuous_fst).continuousOn (fun p hp => ⟨hp.2, hp.1⟩)
  have hcompact_int : IntegrableOn (fun p : ℝ × ℂ => Φ p.2 p.1)
      (uIcc a b ×ˢ closedBall x |r|) (volume.prod volume) := by
    exact hcont_swap.integrableOn_compact (isCompact_uIcc.prod (isCompact_closedBall x |r|))
  have hsmall_int : IntegrableOn (fun p : ℝ × ℂ => Φ p.2 p.1)
      (uIoc a b ×ˢ ball x r) (volume.prod volume) := by
    refine hcompact_int.mono_set (Set.prod_mono Set.uIoc_subset_uIcc ?_)
    intro y hy
    rw [Metric.mem_closedBall]
    exact (le_of_lt (by simpa [Metric.mem_ball] using hy)).trans (le_abs_self r)
  have hint : Integrable (Function.uncurry (fun θ w => Φ w θ))
      ((volume.restrict (Set.uIoc a b)).prod (volume.restrict (ball x r))) := by
    rw [Measure.prod_restrict]
    exact hsmall_int
  unfold ballAverage
  conv_rhs => rw [intervalIntegral.integral_smul]
  have hfub := MeasureTheory.intervalIntegral_integral_swap
    (μ := volume.restrict (ball x r)) (f := fun θ w => Φ w θ) hint
  rw [hfub]

/-- Interval-integrating a jointly continuous compact-parameter family of harmonic functions
preserves harmonicity. -/
theorem harmonicOnNhd_intervalIntegral_of_harmonicOnNhd
    {a b : ℝ} {Φ : ℂ → ℝ → E} {s : Set ℂ} (hs : IsOpen s)
    (hcont : ContinuousOn (fun p : ℂ × ℝ => Φ p.1 p.2) (s ×ˢ uIcc a b))
    (hΦ : ∀ θ ∈ uIcc a b,
      InnerProductSpace.HarmonicOnNhd (fun w : ℂ => Φ w θ) s) :
    InnerProductSpace.HarmonicOnNhd (fun w : ℂ => ∫ θ in a..b, Φ w θ) s := by
  -- codex without review
  have hcont_int : ContinuousOn (fun w : ℂ => ∫ θ in a..b, Φ w θ) s :=
    hcont.intervalIntegral_uIcc
  refine HarmonicOnNhd_of_ballAverage_eq (E := ℂ) (F := E) hs hcont_int ?_
  intro x hx
  rcases Metric.isOpen_iff.mp hs x hx with ⟨ε, hε_pos, hε_sub⟩
  refine ⟨ε, hε_pos, ?_⟩
  intro r hr
  have hclosed_sub : closedBall x |r| ⊆ s := by
    intro y hy
    refine hε_sub ?_
    rw [Metric.mem_ball]
    refine lt_of_le_of_lt ?_ hr.2
    simp [Metric.mem_closedBall] at hy
    simpa [abs_of_pos hr.1] using hy
  have hslice_mean : ∀ θ ∈ uIcc a b, ballAverage (fun w : ℂ => Φ w θ) x r = Φ x θ := by
    intro θ hθ
    simpa [abs_of_pos hr.1] using HarmonicOnNhd.ballAverage_eq ((hΦ θ hθ).mono hclosed_sub)
  have hswap : ballAverage (fun w : ℂ => ∫ θ in a..b, Φ w θ) x r =
        ∫ θ in a..b, ballAverage (fun w : ℂ => Φ w θ) x r :=
      ballAverage_intervalIntegral_comm (hcont.mono (fun p hp => ⟨hclosed_sub hp.1, hp.2⟩))
  have hcollapse :
      (∫ θ in a..b, ballAverage (fun w : ℂ => Φ w θ) x r) = ∫ θ in a..b, Φ x θ := by
    exact intervalIntegral.integral_congr fun θ hθ => hslice_mean θ hθ
  exact hswap.trans hcollapse


/-!
### The scalar pairing on `ℝ`

The Poisson kernel is real-valued while the boundary data is `E`-valued, so `poissonIntegral` pairs
them with `∂•`. Mathlib's lemmas for a positive measure are stated for the opposite pairing `∂<•`;
for `E = ℝ` the two coincide, which is what transports them.
-/

/-- On `ℝ`, scalar multiplication agrees with its own flip: this is commutativity of
multiplication. -/
theorem ContinuousLinearMap.lsmul_flip_real :
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).flip
      = ContinuousLinearMap.lsmul ℝ ℝ := by ext; simp

/-- For a real-valued integrand against a signed measure the two scalar pairings agree. -/
theorem integral_smul_eq_integral_flip {X : Type*} [MeasurableSpace X]
    {μ : SignedMeasure X} {f : X → ℝ} :
    ∫ᵛ x, f x ∂•μ = ∫ᵛ x, f x ∂<•μ := by rw [ContinuousLinearMap.lsmul_flip_real]


/-!
### The Poisson integral

Boundary data is a vector measure. Data given as a function `f` against a reference measure `μ` is
the case `μ.withDensityᵥ f`, and a finite positive measure `ν` is the case `ν.toSignedMeasure`.
-/

/-- The Poisson integral of the boundary vector measure `ν` at the point `w`, for the Poisson kernel
centred at `c`. -/
noncomputable def poissonIntegral (c : ℂ) (ν : VectorMeasure ℂ E) (w : ℂ) : E :=
  ∫ᵛ z, poissonKernel c w z ∂•ν


/-! ### Notation

Two notations for `poissonIntegral`: `P[c; ν]` is the Poisson integral with boundary data given as a
vector measure; `P[c; f ∂ᵥμ]` is the Poisson integral with boundary data given as a function `f` on
the boundary against a reference measure `μ`, i.e. `μ.withDensityᵥ f`. -/

namespace PoissonIntegral

/-- `f ∂ᵥμ` is `μ.withDensityᵥ f`. -/
scoped notation:70 f " ∂ᵥ" μ:70 => MeasureTheory.Measure.withDensityᵥ μ f
-- This is not Poisson-specific, just an upstream candidate.

scoped notation "P[" c "; " ν "]" => poissonIntegral c ν

end PoissonIntegral

open scoped PoissonIntegral

variable {ν : VectorMeasure ℂ E} {μ : Measure ℂ} [IsFiniteMeasure μ] {f : ℂ → E}

#check P[c ; ν]  -- Poisson integral for signed measure
#check P[c ; f ∂ᵥμ] -- Poisson integral for function
#check P[c ; μ.toSignedMeasure]  -- Poisson integral for (positive) measure


/-!
### Bridges to the Bochner integral

Boundary data given as a finite positive measure or as a density enters the definition through
`toSignedMeasure` and `withDensityᵥ`; these identify the results with ordinary Bochner integrals.
A signed boundary measure splits along its Jordan decomposition.
-/

/-- The Poisson integral of a finite positive boundary measure is the plain Bochner integral. -/
@[simp]
theorem poissonIntegral_toSignedMeasure {ν : Measure ℂ} [IsFiniteMeasure ν] :
    poissonIntegral c ν.toSignedMeasure = fun w => ∫ z, poissonKernel c w z ∂ν :=
  funext fun _ => by
    rw [poissonIntegral, integral_smul_eq_integral_flip,
      MeasureTheory.VectorMeasure.integral_toSignedMeasure]

/-- The pointwise form of `poissonIntegral_toSignedMeasure`. -/
@[simp]
theorem poissonIntegral_toSignedMeasure_apply {ν : Measure ℂ} [IsFiniteMeasure ν] :
    P[c; ν.toSignedMeasure] w = ∫ z, poissonKernel c w z ∂ν := by
  rw [poissonIntegral_toSignedMeasure]

/-- The Poisson integral of a density function is the weighted Bochner integral with Poisson kernel. -/
theorem poissonIntegral_withDensityᵥ {μ : Measure ℂ} [IsFiniteMeasure μ]
    {k : ℂ → ℝ} (hμ : μ (sphere c R)ᶜ = 0) (hw : w ∈ ball c R) (hk : Integrable k μ) :
    poissonIntegral c (μ.withDensityᵥ k) w = ∫ z, poissonKernel c w z • k z ∂μ := by
  -- Claude without review
  set P : ℂ → ℝ := fun z => poissonKernel c w z with hP
  -- The two positive parts of `k dμ`, as finite measures carried by the circle.
  set μ₁ : Measure ℂ := μ.withDensity fun x => ENNReal.ofReal (k x) with hμ₁
  set μ₂ : Measure ℂ := μ.withDensity fun x => ENNReal.ofReal (-k x) with hμ₂
  haveI hfin₁ : IsFiniteMeasure μ₁ := isFiniteMeasure_withDensity_ofReal hk.2
  haveI hfin₂ : IsFiniteMeasure μ₂ := isFiniteMeasure_withDensity_ofReal hk.neg.2
  have hcar₁ : μ₁ (sphere c R)ᶜ = 0 := withDensity_absolutelyContinuous μ _ hμ
  have hcar₂ : μ₂ (sphere c R)ᶜ = 0 := withDensity_absolutelyContinuous μ _ hμ
  -- Integrability of the kernel against each part, in the measure and the vector-measure sense.
  have hV₁ : (μ₁.toSignedMeasure).Integrable P := by
    show Integrable P (μ₁.toSignedMeasure).variation
    rw [Measure.variation_toSignedMeasure]
    exact integrable_poissonKernel hcar₁ hw
  have hV₂ : (μ₂.toSignedMeasure).Integrable P := by
    show Integrable P (μ₂.toSignedMeasure).variation
    rw [Measure.variation_toSignedMeasure]
    exact integrable_poissonKernel hcar₂ hw
  -- The two weighted integrals over `μ`, which the difference has to be reassembled from.
  have hsm₁ : Integrable (fun z : ℂ => (ENNReal.ofReal (k z)).toReal • P z) μ := by
    simpa [hP, ENNReal.toReal_ofReal', mul_comm] using
      integrable_poissonKernel_mul hμ hw hk.pos_part
  have hsm₂ : Integrable (fun z : ℂ => (ENNReal.ofReal (-k z)).toReal • P z) μ := by
    simpa [hP, ENNReal.toReal_ofReal', mul_comm] using
      integrable_poissonKernel_mul hμ hw hk.neg_part
  -- The densities have to be presented in exactly the form appearing in `μ₁`, `μ₂`.
  have hm₁ : AEMeasurable (fun x : ℂ => ENNReal.ofReal (k x)) μ :=
    hk.1.aemeasurable.ennreal_ofReal
  have hm₂ : AEMeasurable (fun x : ℂ => ENNReal.ofReal (-k x)) μ :=
    hk.1.aemeasurable.neg.ennreal_ofReal
  rw [poissonIntegral, integral_smul_eq_integral_flip,
    withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part hk,
    VectorMeasure.integral_sub_vectorMeasure hV₁ hV₂,
    VectorMeasure.integral_toSignedMeasure, VectorMeasure.integral_toSignedMeasure,
    integral_withDensity_eq_integral_toReal_smul₀ hm₁
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) P,
    integral_withDensity_eq_integral_toReal_smul₀ hm₂
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) P,
    ← integral_sub hsm₁ hsm₂]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [hP, ENNReal.toReal_ofReal', smul_eq_mul]
  by_cases h : 0 ≤ k z
  · rw [max_eq_left h, max_eq_right (by linarith : -k z ≤ 0)]
    ring
  · have h' : k z < 0 := not_le.mp h
    rw [max_eq_right h'.le, max_eq_left (by linarith : (0 : ℝ) ≤ -k z)]
    ring

/-- For an interior point, the Poisson kernel is integrable against the total variation of a signed
measure carried by the boundary circle. -/
theorem integrable_poissonKernel_totalVariation {μ : SignedMeasure ℂ}
    (hμ : μ.totalVariation (sphere c R)ᶜ = 0) (hw : w ∈ ball c R) :
    μ.Integrable (fun z : ℂ => poissonKernel c w z) := by
  -- Claude without review
  haveI : IsFiniteMeasure μ.totalVariation := by
    rw [SignedMeasure.totalVariation]; infer_instance
  have hint : Integrable (fun z : ℂ => poissonKernel c w z) μ.totalVariation := by
    have h := (integrable_herglotzRieszKernel (μ := μ.totalVariation) hμ hw).re
    simpa [poissonKernel_eq_re_herglotzRieszKernel, RCLike.re_eq_complex_re] using h
  refine hint.mono_measure (VectorMeasure.variation_le_of_forall_enorm_le ?_)
  intro E hE
  set a := μ.toJordanDecomposition.posPart E with ha
  set b := μ.toJordanDecomposition.negPart E with hb
  have ha_ne : a ≠ ⊤ := measure_ne_top _ _
  have hb_ne : b ≠ ⊤ := measure_ne_top _ _
  have hEeq : μ E = a.toReal - b.toReal := by
    conv_lhs => rw [← μ.toSignedMeasure_toJordanDecomposition]
    simp [JordanDecomposition.toSignedMeasure, Measure.toSignedMeasure_apply_measurable hE,
      measureReal_def, ha, hb]
  have habs : |a.toReal - b.toReal| ≤ a.toReal + b.toReal := by
    rw [abs_le]
    constructor <;> linarith [ENNReal.toReal_nonneg (a := a), ENNReal.toReal_nonneg (a := b)]
  rw [SignedMeasure.totalVariation, Measure.add_apply, ← ha, ← hb, Real.enorm_eq_ofReal_abs, hEeq]
  grw [ENNReal.ofReal_le_ofReal habs]
  rw [ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal ha_ne, ENNReal.ofReal_toReal hb_ne]

/-- Both parts of the Jordan decomposition of a signed measure are bounded by its variation. -/
theorem toJordanDecomposition_le_variation {α : Type*} [MeasurableSpace α] (μ : SignedMeasure α) :
    μ.toJordanDecomposition.posPart ≤ μ.variation ∧
      μ.toJordanDecomposition.negPart ≤ μ.variation := by
  -- Claude without review
  obtain ⟨i, hi₁, hi₂, hi₃, hpos, hneg⟩ := μ.toJordanDecomposition_spec
  constructor <;> refine Measure.le_intro fun E hE _ => ?_
  · calc μ.toJordanDecomposition.posPart E
        ≤ ‖μ (i ∩ E)‖ₑ := by
          rw [hpos, SignedMeasure.toMeasureOfZeroLE_apply _ hi₂ hi₁ hE, Real.enorm_eq_ofReal_abs,
            ← ENNReal.ofReal_eq_coe_nnreal]
          exact ENNReal.ofReal_le_ofReal (le_abs_self _)
      _ ≤ μ.variation (i ∩ E) := VectorMeasure.enorm_measure_le_variation _ _
      _ ≤ μ.variation E := measure_mono Set.inter_subset_right
  · calc μ.toJordanDecomposition.negPart E
        ≤ ‖μ (iᶜ ∩ E)‖ₑ := by
          rw [hneg, SignedMeasure.toMeasureOfLEZero_apply _ hi₃ hi₁.compl hE,
            Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_eq_coe_nnreal]
          exact ENNReal.ofReal_le_ofReal (neg_le_abs _)
      _ ≤ μ.variation (iᶜ ∩ E) := VectorMeasure.enorm_measure_le_variation _ _
      _ ≤ μ.variation E := measure_mono Set.inter_subset_right

/-- The Poisson integral of a signed boundary measure splits along the Jordan decomposition
`μ = μ⁺ - μ⁻`, whenever the Poisson kernel is integrable against the total variation of `μ`. -/
theorem poissonIntegral_eq_posPart_sub_negPart {μ : SignedMeasure ℂ}
    (hint : μ.Integrable (fun z : ℂ => poissonKernel c w z)) :
    poissonIntegral c μ w =
      (∫ z, poissonKernel c w z ∂μ.toJordanDecomposition.posPart) -
        ∫ z, poissonKernel c w z ∂μ.toJordanDecomposition.negPart := by
  -- Claude without review
  obtain ⟨hpos_le, hneg_le⟩ := toJordanDecomposition_le_variation μ
  have hpos : Integrable (fun z : ℂ => poissonKernel c w z) μ.toJordanDecomposition.posPart :=
    hint.mono_measure hpos_le
  have hneg : Integrable (fun z : ℂ => poissonKernel c w z) μ.toJordanDecomposition.negPart :=
    hint.mono_measure hneg_le
  have hpos' : (μ.toJordanDecomposition.posPart.toSignedMeasure).Integrable
      (fun z : ℂ => poissonKernel c w z) := by
    show Integrable (fun z : ℂ => poissonKernel c w z)
      (μ.toJordanDecomposition.posPart.toSignedMeasure).variation
    rwa [Measure.variation_toSignedMeasure]
  have hneg' : (μ.toJordanDecomposition.negPart.toSignedMeasure).Integrable
      (fun z : ℂ => poissonKernel c w z) := by
    show Integrable (fun z : ℂ => poissonKernel c w z)
      (μ.toJordanDecomposition.negPart.toSignedMeasure).variation
    rwa [Measure.variation_toSignedMeasure]
  rw [poissonIntegral, integral_smul_eq_integral_flip]
  conv_lhs => rw [← μ.toSignedMeasure_toJordanDecomposition]
  rw [show μ.toJordanDecomposition.toSignedMeasure
      = μ.toJordanDecomposition.posPart.toSignedMeasure
        - μ.toJordanDecomposition.negPart.toSignedMeasure from rfl,
    VectorMeasure.integral_sub_vectorMeasure hpos' hneg',
    VectorMeasure.integral_toSignedMeasure, VectorMeasure.integral_toSignedMeasure]

/-- The total variation of a difference of finite measures vanishes on every set on which both
measures vanish. -/
theorem totalVariation_toSignedMeasure_sub_eq_zero {α : Type*} [MeasurableSpace α]
    {μ₁ μ₂ : Measure α} [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] {S : Set α}
    (h₁ : μ₁ S = 0) (h₂ : μ₂ S = 0) :
    (μ₁.toSignedMeasure - μ₂.toSignedMeasure).totalVariation S = 0 := by
  set μ := μ₁.toSignedMeasure - μ₂.toSignedMeasure
  have hvar : μ.variation ≤ μ₁ + μ₂ := by
    refine VectorMeasure.variation_le_of_forall_enorm_le fun E hE => ?_
    have habs : |μ₁.real E - μ₂.real E| ≤ μ₁.real E + μ₂.real E := by
      rw [abs_le]
      constructor <;> linarith [measureReal_nonneg (μ := μ₁) (s := E),
        measureReal_nonneg (μ := μ₂) (s := E)]
    simp only [μ, sub_apply, Measure.toSignedMeasure_apply_measurable hE,
      Real.enorm_eq_ofReal_abs, Measure.add_apply]
    grw [ENNReal.ofReal_le_ofReal habs]
    rw [ENNReal.ofReal_add measureReal_nonneg measureReal_nonneg, ofReal_measureReal,
      ofReal_measureReal]
  have hS : μ.variation S = 0 :=
    le_zero_iff.mp ((Measure.le_iff'.mp hvar S).trans (by simp [h₁, h₂]))
  obtain ⟨hpos, hneg⟩ := toJordanDecomposition_le_variation μ
  rw [SignedMeasure.totalVariation, Measure.add_apply,
    le_zero_iff.mp ((Measure.le_iff'.mp hpos S).trans hS.le),
    le_zero_iff.mp ((Measure.le_iff'.mp hneg S).trans hS.le), add_zero]

/-- The Poisson integral of a difference of finite measures carried by the boundary circle is the
difference of their Poisson integrals. -/
theorem poissonIntegral_toSignedMeasure_sub {μ₁ μ₂ : Measure ℂ} [IsFiniteMeasure μ₁]
    [IsFiniteMeasure μ₂] (hμ₁ : μ₁ (sphere c R)ᶜ = 0) (hμ₂ : μ₂ (sphere c R)ᶜ = 0)
    (hw : w ∈ ball c R) :
    P[c; μ₁.toSignedMeasure - μ₂.toSignedMeasure] w =
      P[c; μ₁.toSignedMeasure] w - P[c; μ₂.toSignedMeasure] w := by
  have hint : ∀ (ν : Measure ℂ) [IsFiniteMeasure ν], ν (sphere c R)ᶜ = 0 →
      (ν.toSignedMeasure).Integrable (fun z : ℂ => poissonKernel c w z) := by
    intro ν _ hν
    show Integrable (fun z : ℂ => poissonKernel c w z) (ν.toSignedMeasure).variation
    rw [Measure.variation_toSignedMeasure]
    simpa [poissonKernel_eq_re_herglotzRieszKernel, RCLike.re_eq_complex_re] using
      (integrable_herglotzRieszKernel hν hw).re
  rw [poissonIntegral, integral_smul_eq_integral_flip,
    VectorMeasure.integral_sub_vectorMeasure (hint μ₁ hμ₁) (hint μ₂ hμ₂),
    VectorMeasure.integral_toSignedMeasure, VectorMeasure.integral_toSignedMeasure,
    poissonIntegral_toSignedMeasure_apply, poissonIntegral_toSignedMeasure_apply]

/-!
### The Poisson extension theorem
-/

/-- The circle average of a jointly continuous parameterized family of harmonic functions is
harmonic. -/
theorem harmonicOnNhd_circleAverage_of_harmonicOnNhd
    {Φ : ℂ → ℂ → E} {s : Set ℂ} (hR : 0 ≤ R) (hs : IsOpen s)
    (hcont : ContinuousOn (fun p : ℂ × ℂ => Φ p.1 p.2) (s ×ˢ sphere c R))
    (hΦ : ∀ z ∈ sphere c R, InnerProductSpace.HarmonicOnNhd (fun w : ℂ => Φ w z) s) :
    InnerProductSpace.HarmonicOnNhd (fun w : ℂ => circleAverage (fun z : ℂ => Φ w z) c R) s := by
  -- codex without review
  have hcont' : ContinuousOn
      (fun p : ℂ × ℝ => Φ p.1 (circleMap c R p.2))
      (s ×ˢ Set.uIcc 0 (2 * π)) := by
    refine hcont.comp
      (by fun_prop :
        ContinuousOn (fun p : ℂ × ℝ => (p.1, circleMap c R p.2))
          (s ×ˢ Set.uIcc 0 (2 * π))) ?_
    intro p hp
    exact ⟨hp.1, circleMap_mem_sphere c hR p.2⟩
  change InnerProductSpace.HarmonicOnNhd
    (fun w : ℂ => (2 * π)⁻¹ • ∫ θ in 0..2 * π, Φ w (circleMap c R θ)) s
  exact (harmonicOnNhd_intervalIntegral_of_harmonicOnNhd
    (Φ := fun w θ => Φ w (circleMap c R θ))
    (a := 0) (b := 2 * π) (s := s) hs hcont'
    (fun θ _hθ => hΦ (circleMap c R θ) (circleMap_mem_sphere c hR θ))).const_smul

/-- For continuous boundary data at an interior point, the integral of the kernel times the data
against the normalized circle measure is the corresponding circle average. -/
theorem integral_poissonKernel_smul_circleMeasure_eq_circleAverage (hR : 0 ≤ R)
  (hw : w ∈ ball c R) (hf : ContinuousOn f (sphere c R)) :
  ∫ z, poissonKernel c w z • f z ∂circleMeasure c R
    = circleAverage (fun z : ℂ => poissonKernel c w z • f z) c R :=
  (circleAverage_eq_integral_circleMeasure (ContinuousOn.circleIntegrable hR
    ((continuousOn_poissonKernel_right_of_mem_ball hw).smul hf))).symm

/-- For continuous real boundary data, the Poisson integral of the associated density against the
circle measure is the corresponding circle average.  This is the real-valued form of
`integral_poissonKernel_smul_circleMeasure_eq_circleAverage` phrased through `poissonIntegral`. -/
theorem poissonIntegral_circleMeasure_withDensityᵥ_eq_circleAverage {k : ℂ → ℝ} (hR : 0 ≤ R)
    (hw : w ∈ ball c R) (hk : ContinuousOn k (sphere c R)) :
    P[c; k ∂ᵥcircleMeasure c R] w
      = circleAverage (fun z : ℂ => poissonKernel c w z • k z) c R := by
  rw [poissonIntegral_withDensityᵥ (circleMeasure_compl_sphere hR) hw
      (hk.integrable_circleMeasure hR),
    integral_poissonKernel_smul_circleMeasure_eq_circleAverage hR hw hk]

/-- **Poisson integral formula**, in `circleMeasure` form.  A function harmonic on a neighbourhood
of the closed disk is reproduced at every interior point by its Poisson integral against the
normalized circle measure.

This is mathlib's `InnerProductSpace.HarmonicOnNhd.circleAverage_poissonKernel_smul` transported
along `poissonIntegral_circleMeasure_withDensityᵥ_eq_circleAverage`.  It is real-valued only:
mathlib states the Poisson formula for `f : ℂ → ℝ` and leaves the vector-valued version as an open
TODO. -/
theorem poissonIntegral_circleMeasure_eq_self {u : ℂ → ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u (closedBall c R)) (hw : w ∈ ball c R) :
    P[c; u ∂ᵥcircleMeasure c R] w = u w := by
  have hR : 0 ≤ R := dist_nonneg.trans (mem_ball.mp hw).le
  have hcont : ContinuousOn u (sphere c R) :=
    hu.continuousOn.mono sphere_subset_closedBall
  rw [poissonIntegral_circleMeasure_withDensityᵥ_eq_circleAverage hR hw hcont]
  exact InnerProductSpace.HarmonicOnNhd.circleAverage_poissonKernel_smul hu hw

/-- **The Poisson kernel has total mass one.**  At an interior point, integrating the kernel
against normalized arclength gives `1`.

This is the `u ≡ 1` case of `poissonIntegral_circleMeasure_eq_self`.  It is what turns
`P[k](w) - k ζ` into `∫ P_w (k - k ζ) dσ`, the starting point of every approximate-identity
estimate. -/
theorem poissonIntegral_circleMeasure_eq_one (hw : w ∈ ball c R) :
    P[c; (circleMeasure c R).toSignedMeasure] w = 1 := by
  have hR : 0 ≤ R := dist_nonneg.trans (mem_ball.mp hw).le
  have h := poissonIntegral_circleMeasure_eq_self (u := fun _ => 1)
    (by simp [InnerProductSpace.HarmonicOnNhd]) hw
  rw [poissonIntegral_withDensityᵥ (circleMeasure_compl_sphere hR) hw (integrable_const 1)] at h
  simpa using h

/--The circle average of the kernel times continuous boundary data on a circle is harmonic in the
open disk.-/
theorem harmonicOnNhd_circleAverage_poissonKernel_smul (hf : ContinuousOn f (sphere c R)) :
    InnerProductSpace.HarmonicOnNhd
      (fun w : ℂ => circleAverage (fun z : ℂ => poissonKernel c w z • f z) c R) (ball c R) := by
  -- Claude without review
  intro w hw
  have hR : 0 ≤ R := dist_nonneg.trans (mem_ball.mp hw).le
  have hCA : InnerProductSpace.HarmonicOnNhd
      (fun w : ℂ => circleAverage (fun z : ℂ => poissonKernel c w z • f z) c R) (ball c R) := by
    have hcont : ContinuousOn (fun p : ℂ × ℂ => poissonKernel c p.1 p.2 • f p.2)
      ((ball c R) ×ˢ sphere c R) := by
      unfold poissonKernel
      refine ContinuousOn.smul ?_ ?_
      · refine ContinuousOn.div ?_ ?_ ?_
        · fun_prop
        · fun_prop
        · intro p hp hden
          rcases hp with ⟨hp_ball, hp_sphere⟩
          simp [sub_eq_zero] at hden
          simp at hp_ball
          simp [← dist_eq_norm] at hp_sphere
          rw [hden] at hp_sphere
          linarith
      · exact hf.comp continuous_snd.continuousOn (fun p hp => hp.2)
    refine harmonicOnNhd_circleAverage_of_harmonicOnNhd (E := E) (R := R) (c := c)
      (s := ball c R) hR (isOpen_ball) hcont ?_
    intro z hz
    convert
      (harmonicOnNhd_poissonKernel (c := c) (R := R) (w := z) hz).comp_CLM
        (ContinuousLinearMap.toSpanSingleton ℝ (f z) : ℝ →L[ℝ] E) using 1
    ext w
    simp [Function.comp_apply]
  exact hCA w hw

/-- The Poisson integral of continuous real-valued boundary data has a continuous extension to the
closed disk whose boundary values are the original boundary data. -/
theorem poissonIntegral_continuousOn_closedBall_eq_boundary
    {u : ℂ → ℝ} (hu_cont : ContinuousOn u (sphere c R)) :
    ∃ h : ℂ → ℝ, ContinuousOn h (closedBall c R) ∧ InnerProductSpace.HarmonicOnNhd h (ball c R)
    ∧ (∀ w ∈ ball c R, h w = P[c; u ∂ᵥcircleMeasure c R] w)
    ∧ (∀ y ∈ sphere c R, h y = u y) := by
  sorry



-- The rest is given in the help of Claude

/-!
### Harmonic functions as Poisson integrals

The disc form of Garnett, *Bounded Analytic Functions*, Theorem I.3.5.
-/


/-- The Poisson integral of a finite measure carried by the boundary circle is nonnegative on the
open disc. -/
theorem poissonIntegral_toSignedMeasure_nonneg {μ : Measure ℂ} [IsFiniteMeasure μ]
    (hμ : μ (sphere c R)ᶜ = 0) (hw : w ∈ ball c R) :
    0 ≤ P[c; μ.toSignedMeasure] w := by
  rw [poissonIntegral_toSignedMeasure]
  refine integral_nonneg_of_ae ?_
  filter_upwards [ae_iff.2 hμ] with z hz using poissonKernel_nonneg hw hz

/-- The Poisson integral of a finite measure carried by the boundary circle is harmonic on the open
disc.  This is the easy direction of Garnett I.3.5(c), disc form. -/
theorem harmonicOnNhd_poissonIntegral_toSignedMeasure {μ : Measure ℂ} [IsFiniteMeasure μ]
    (hμ : μ (sphere c R)ᶜ = 0) :
    InnerProductSpace.HarmonicOnNhd P[c; μ.toSignedMeasure] (ball c R) := by
  rw [poissonIntegral_toSignedMeasure]
  intro w hw
  have hharm := (analyticOnNhd_integral_herglotzRieszKernel hμ w hw).harmonicAt_re
  refine (InnerProductSpace.harmonicAt_congr_nhds ?_).2 hharm
  filter_upwards [isOpen_ball.mem_nhds hw] with x hx
  show (∫ z, poissonKernel c x z ∂μ) = (∫ z, herglotzRieszKernel c x z ∂μ).re
  rw [← RCLike.re_eq_complex_re,
    ← integral_re (integrable_herglotzRieszKernel hμ hx)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simpa [RCLike.re_eq_complex_re] using
    congrFun (poissonKernel_eq_re_herglotzRieszKernel (c := c) (w := x)) z

/-- The Poisson integral of an integrable density against a finite measure carried by the circle is
harmonic on the open disc. -/
theorem harmonicOnNhd_poissonIntegral_withDensityᵥ {μ : Measure ℂ} [IsFiniteMeasure μ]
    {k : ℂ → ℝ} (hμ : μ (sphere c R)ᶜ = 0) (hk : Integrable k μ) :
    InnerProductSpace.HarmonicOnNhd P[c; k ∂ᵥμ] (ball c R) := by
  -- Claude without review
  set μ₁ : Measure ℂ := μ.withDensity fun x => ENNReal.ofReal (k x) with hμ₁
  set μ₂ : Measure ℂ := μ.withDensity fun x => ENNReal.ofReal (-k x) with hμ₂
  haveI : IsFiniteMeasure μ₁ := isFiniteMeasure_withDensity_ofReal hk.2
  haveI : IsFiniteMeasure μ₂ := isFiniteMeasure_withDensity_ofReal hk.neg.2
  have hcar₁ : μ₁ (sphere c R)ᶜ = 0 := withDensity_absolutelyContinuous μ _ hμ
  have hcar₂ : μ₂ (sphere c R)ᶜ = 0 := withDensity_absolutelyContinuous μ _ hμ
  -- `k dμ = k⁺ dμ - k⁻ dμ`, so `P[k dμ]` is a difference of Poisson integrals of measures.
  have heq (x : ℂ) (hx : x ∈ ball c R) :
      P[c; k ∂ᵥμ] x = P[c; μ₁.toSignedMeasure] x - P[c; μ₂.toSignedMeasure] x := by
    have hV₁ : (μ₁.toSignedMeasure).Integrable fun z => poissonKernel c x z := by
      show Integrable _ (μ₁.toSignedMeasure).variation
      rw [Measure.variation_toSignedMeasure]
      exact integrable_poissonKernel hcar₁ hx
    have hV₂ : (μ₂.toSignedMeasure).Integrable fun z => poissonKernel c x z := by
      show Integrable _ (μ₂.toSignedMeasure).variation
      rw [Measure.variation_toSignedMeasure]
      exact integrable_poissonKernel hcar₂ hx
    simp only [poissonIntegral, integral_smul_eq_integral_flip]
    rw [withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part hk,
      VectorMeasure.integral_sub_vectorMeasure hV₁ hV₂]
  intro x hx
  refine (InnerProductSpace.harmonicAt_congr_nhds ?_).2
    (((harmonicOnNhd_poissonIntegral_toSignedMeasure hcar₁).sub
      (harmonicOnNhd_poissonIntegral_toSignedMeasure hcar₂)) x hx)
  filter_upwards [isOpen_ball.mem_nhds hx] with y hy using heq y hy



/- Now we'd like to show the **Hardy norm of the poisson integral** will be bounded by
the **Lp-norm of its boundary function**, which will be useful for proving one direction
of Garnett 1.3.5(a).-/


/-- The total mass one of the Poisson kernel, in `lintegral` form. -/
lemma lintegral_ofReal_poissonKernel_circleMeasure (hw : w ∈ ball c R) :
    ∫⁻ z, ENNReal.ofReal (poissonKernel c w z) ∂circleMeasure c R = 1 := by
  have hR : 0 ≤ R := dist_nonneg.trans (mem_ball.mp hw).le
  have h := poissonIntegral_circleMeasure_eq_one hw
  rw [poissonIntegral_toSignedMeasure_apply] at h
  have hnn : 0 ≤ᵐ[circleMeasure c R] fun z => poissonKernel c w z := by
    filter_upwards [ae_mem_sphere_circleMeasure hR] with z hz using poissonKernel_nonneg hw hz
  rw [← ofReal_integral_eq_lintegral_ofReal
      ((continuousOn_poissonKernel_right_of_mem_ball hw).integrable_circleMeasure hR) hnn,
    h, ENNReal.ofReal_one]

/-- The Poisson integral of integrable data is bounded by the Poisson integral of its modulus. -/
lemma enorm_poissonIntegral_le_lintegral {U : ℂ → ℝ} (hU : Integrable U (circleMeasure c R))
    (hw : w ∈ ball c R) :
    ‖P[c; U ∂ᵥcircleMeasure c R] w‖ₑ ≤
      ∫⁻ z, ENNReal.ofReal (poissonKernel c w z) * ‖U z‖ₑ ∂circleMeasure c R := by
  have hR : 0 ≤ R := dist_nonneg.trans (mem_ball.mp hw).le
  rw [poissonIntegral_withDensityᵥ (circleMeasure_compl_sphere hR) hw hU]
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono_ae ?_)
  filter_upwards [ae_mem_sphere_circleMeasure hR] with z hz
  rw [enorm_smul, Real.enorm_eq_ofReal (poissonKernel_nonneg hw hz)]

/-- Jensen's inequality for the probability measure `P_w dσ`: for `1 ≤ p < ∞`,
`|P[U](w)|ᵖ ≤ P[|U|ᵖ](w)`. -/
lemma enorm_poissonIntegral_rpow_le_lintegral {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    {U : ℂ → ℝ} (hU : MemLp U p (circleMeasure c R)) (hw : w ∈ ball c R) :
    ‖P[c; U ∂ᵥcircleMeasure c R] w‖ₑ ^ p.toReal ≤
      ∫⁻ z, ENNReal.ofReal (poissonKernel c w z) * ‖U z‖ₑ ^ p.toReal ∂circleMeasure c R := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp_top
  have hdm : Measurable fun z => ENNReal.ofReal (poissonKernel c w z) :=
    (measurable_poissonKernel c w).ennreal_ofReal
  haveI : IsProbabilityMeasure
      ((circleMeasure c R).withDensity fun z => ENNReal.ofReal (poissonKernel c w z)) :=
    ⟨by rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      lintegral_ofReal_poissonKernel_circleMeasure hw]⟩
  -- Jensen, in the form `‖U‖_{L¹(P_w dσ)} ≤ ‖U‖_{Lᵖ(P_w dσ)}`.
  have hJ := eLpNorm_le_eLpNorm_of_exponent_le hp
    (hU.1.mono_ac (withDensity_absolutelyContinuous (circleMeasure c R)
      fun z => ENNReal.ofReal (poissonKernel c w z)))
  rw [eLpNorm_one_eq_lintegral_enorm, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_top,
    lintegral_withDensity_eq_lintegral_mul₀ hdm.aemeasurable hU.1.aemeasurable.enorm,
    lintegral_withDensity_eq_lintegral_mul₀ hdm.aemeasurable
      (hU.1.aemeasurable.enorm.pow_const _)] at hJ
  simp only [Pi.mul_apply] at hJ
  grw [ENNReal.rpow_le_rpow (enorm_poissonIntegral_le_lintegral (hU.integrable hp) hw) hq.le,
    ENNReal.rpow_le_rpow hJ hq.le]
  rw [← ENNReal.rpow_mul, one_div_mul_cancel hq.ne', ENNReal.rpow_one]


/-- For a boundary point `z`, the Poisson kernel `P_{re^{iθ}}(z)` has total mass one as a function
of `θ`. -/
lemma lintegral_ofReal_poissonKernel_radial {z : ℂ} (hz : ‖z‖ = 1) {r : ℝ}
    (hr : 0 < r ∧ r < 1) :
    ∫⁻ θ : ℝ, ENNReal.ofReal (poissonKernel 0 (r * exp (I * θ)) z) ∂angularMeasure = 1 := by
  have hrz : (r : ℂ) * z ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_mul, hz, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr.1]
    exact hr.2
  have hsymm (θ : ℝ) :
      poissonKernel 0 (r * exp (I * θ)) z = poissonKernel 0 (r * z) (circleMap 0 1 θ) := by
    have hθ : circleMap 0 1 θ = exp (I * θ) := by simp [circleMap, mul_comm]
    have h := poissonKernel_symm_of_mem_sphere (mem_sphere_zero_iff_norm.2 hz)
      (circleMap_mem_sphere 0 zero_le_one θ) r
    simp only [zero_add, sub_zero] at h
    rwa [← hθ]
  simp_rw [hsymm]
  rw [(lintegral_map (measurable_poissonKernel 0 _).ennreal_ofReal
  (measurable_circleMap 0 1)).symm, ← lintegral_ofReal_poissonKernel_circleMeasure hrz, circleMeasure]


/-- For `1 ≤ p ≤ ∞` and `U ∈ Lᵖ(σ)`, the Poisson integral of `U` restricted to the circle of
radius `r < 1` has `Lᵖ` norm at most `‖U‖_p`. -/
theorem eLpNorm_poissonIntegral_radial_le {p : ℝ≥0∞} (hp : 1 ≤ p) {U : ℂ → ℝ}
    (hU : MemLp U p (circleMeasure 0 1)) {r : ℝ} (hr : 0 < r ∧ r < 1) :
    eLpNorm (fun θ : ℝ => P[0; U ∂ᵥcircleMeasure 0 1] (r * exp (I * θ))) p angularMeasure
      ≤ eLpNorm U p (circleMeasure 0 1) := by
  -- Claude with review
  -- Garnett proves (3.5) with Minkowski's integral inequality, which mathlib lacks; we use
  -- Jensen for `P_w dσ`, Tonelli, and the symmetry of the kernel instead.
  have hw (θ : ℝ) : (r : ℂ) * exp (I * θ) ∈ ball (0 : ℂ) 1 :=
    radial_point_mem_unitDisc hr.1 hr.2
  rcases eq_or_ne p ∞ with rfl | hp_top
  · rw [eLpNorm_exponent_top, eLpNorm_exponent_top]
    refine eLpNormEssSup_le_of_ae_enorm_bound (Filter.Eventually.of_forall fun θ => ?_)
    refine (enorm_poissonIntegral_le_lintegral (hU.integrable hp) (hw θ)).trans ?_
    grw [lintegral_mono_ae (ae_le_eLpNormEssSup.mono fun z hz => mul_le_mul_right hz _)]
    rw [lintegral_mul_const _ (measurable_poissonKernel _ _).ennreal_ofReal,
            lintegral_ofReal_poissonKernel_circleMeasure (hw θ), one_mul]
  · have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
    have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp_top
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_top,
      eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_top]
    refine ENNReal.rpow_le_rpow ?_ (by positivity)
    have hFm : AEMeasurable (Function.uncurry fun (θ : ℝ) (z : ℂ) =>
        ENNReal.ofReal (poissonKernel 0 (r * exp (I * θ)) z) * ‖U z‖ₑ ^ p.toReal)
        (angularMeasure.prod (circleMeasure 0 1)) := by
      refine AEMeasurable.mul (Measurable.aemeasurable (Measurable.ennreal_ofReal ?_))
        (hU.1.aemeasurable.enorm.pow_const _).comp_snd
      unfold poissonKernel; fun_prop
    grw [lintegral_mono fun θ => enorm_poissonIntegral_rpow_le_lintegral hp hp_top hU (hw θ)]
    rw [lintegral_lintegral_swap hFm]
    refine (lintegral_congr_ae ?_).le
    filter_upwards [ae_mem_sphere_circleMeasure zero_le_one] with z hz
    rw [lintegral_mul_const' _ _ (ENNReal.rpow_ne_top_of_nonneg hq.le enorm_ne_top),
        lintegral_ofReal_poissonKernel_radial (mem_sphere_zero_iff_norm.1 hz) hr, one_mul]

/-- The Hardy `p`-norm of the Poisson integral of `Lᵖ` boundary data is at most the `Lᵖ` norm of
the data, for `1 ≤ p ≤ ∞`. -/
theorem hardyNorm_poissonIntegral_le {p : ℝ≥0∞} (hp : 1 ≤ p) {U : ℂ → ℝ}
    (hU : MemLp U p (circleMeasure 0 1)) :
    hardyNorm P[0; U ∂ᵥcircleMeasure 0 1] p ≤ eLpNorm U p (circleMeasure 0 1) := by
  have hp' : p ∉ Ioo 0 1 := fun h => absurd h.2 (not_lt.mpr hp)
  unfold hardyNorm
  refine iSup₂_le fun r hr => ?_
  rw [eLpNormFixed, if_neg hp']
  exact eLpNorm_poissonIntegral_radial_le hp hU hr


/-- The Poisson formula for radial boundary data, with the kernel on the unit circle. -/
lemma integral_poissonKernel_mul_radial_eq {u : ℂ → ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u (ball 0 1)) {r : ℝ}
    (hr : 0 < r ∧ r < 1) {w : ℂ} (hw : w ∈ ball 0 1) :
    ∫ z, poissonKernel 0 w z * u (r * z) ∂circleMeasure 0 1 = u (r * w) := by
  have hmaps : MapsTo (fun z : ℂ => (r : ℂ) * z) (sphere 0 1) (ball 0 1) := by
    intro z hz
    simp only [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr.1, mem_sphere_zero_iff_norm.mp hz, mul_one]
    exact hr.2
  have hc : ContinuousOn (fun z : ℂ => u (r * z)) (sphere 0 1) :=
    hu.continuousOn.comp (by fun_prop) hmaps
  have hur : InnerProductSpace.HarmonicOnNhd u (closedBall 0 r) :=
    fun z hz => hu z ((closedBall_subset_ball hr.2) hz)
  have hwr : (r : ℂ) * w ∈ ball (0 : ℂ) r := by
    rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr.1]
    simpa using mul_lt_mul_of_pos_left (mem_ball_zero_iff.mp hw) hr.1
  change (∫ z, poissonKernel 0 w z • u (r * z) ∂circleMeasure 0 1) = _
  rw [integral_poissonKernel_smul_circleMeasure_eq_circleAverage zero_le_one hw hc]
  rw [← hur.circleAverage_poissonKernel_smul hwr]
  simp only [circleAverage, smul_eq_mul]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  have heq : circleMap 0 r θ = (r : ℂ) * circleMap 0 1 θ := by simp [circleMap]
  dsimp only [Pi.mul_apply]
  rw [heq, poissonKernel_zero_mul (by exact_mod_cast hr.1.ne')]

/-- **Garnett I.3.5(a), disc form.** For `1 < p ≤ ∞`, harmonic functions with uniformly bounded
radial `Lᵖ` norms are exactly the Poisson integrals of `Lᵖ` boundary data. -/
theorem harmonicOnNhd_hardyNorm_lt_top_iff_exists_memLp_eq_poissonIntegral
    {p : ℝ≥0∞} (hp : 1 < p) {u : ℂ → ℝ} :
    (InnerProductSpace.HarmonicOnNhd u (ball 0 1) ∧ hardyNorm u p < ∞) ↔
      ∃ U : ℂ → ℝ, MemLp U p (circleMeasure 0 1) ∧
        ∀ w ∈ ball 0 1, u w = P[0; U ∂ᵥcircleMeasure 0 1] w := by
  constructor
  · -- codex without review
    rintro ⟨hu, hbdd⟩
    let q : ℝ≥0∞ := (1 - p⁻¹)⁻¹
    letI : Fact (1 ≤ p) := ⟨hp.le⟩
    letI : p.HolderConjugate q := ENNReal.holderConjugate_iff.mpr (by
      dsimp [q]
      rw [inv_inv, add_tsub_cancel_of_le (ENNReal.inv_le_one.mpr hp.le)])
    letI : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
    have hq : q ≠ ∞ := ((ENNReal.HolderConjugate.lt_top_iff_one_lt q p).2 hp).ne
    have hc (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) 1) :
        ContinuousOn (fun z : ℂ => u (r * z)) (sphere 0 1) := by
      refine hu.continuousOn.comp (by fun_prop) ?_
      intro z hz
      simpa only [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hr.1, mem_sphere_zero_iff_norm.mp hz, mul_one] using hr.2
    let f (r : ℝ) : Lp ℝ p (circleMeasure 0 1) :=
      if hr : r ∈ Ioo (0 : ℝ) 1 then
        ((hc r hr).memLp_circleMeasure zero_le_one p).toLp (fun z : ℂ => u (r * z))
      else 0
    have hf_norm (r : ℝ) : ‖f r‖ ≤ (hardyNorm u p).toReal := by
      dsimp [f]
      split_ifs with hr
      · rw [Lp.norm_toLp]
        apply ENNReal.toReal_mono hbdd.ne
        have hm := ((hc r hr).memLp_circleMeasure zero_le_one p).aestronglyMeasurable
        rw [circleMeasure, eLpNorm_map_measure hm (measurable_circleMap 0 1).aemeasurable]
        have hp' : p ∉ Ioo 0 1 := fun h => (not_lt_of_ge hp.le) h.2
        simpa [eLpNormFixed, hp', angularMeasure, Function.comp_def, circleMap, mul_comm]
          using hardyNorm_radial_le u p hr
      · simp
    let F (r : ℝ) : WeakDual ℝ (Lp ℝ q (circleMeasure 0 1)) :=
      StrongDual.toWeakDual ((ContinuousLinearMap.mul ℝ ℝ).lpPairing (circleMeasure 0 1) p q (f r))
    obtain ⟨Λ, _, hΛ⟩ :=
      (WeakDual.isCompact_closedBall (0 : StrongDual ℝ (Lp ℝ q (circleMeasure 0 1)))
        (hardyNorm u p).toReal).exists_mapClusterPt
        (f := 𝓝[<] (1 : ℝ)) (u := F) (by
          rw [Filter.le_principal_iff]
          change ∀ᶠ r in 𝓝[<] (1 : ℝ), F r ∈
            WeakDual.toStrongDual ⁻¹' closedBall 0 (hardyNorm u p).toReal
          exact Filter.Eventually.of_forall fun r => by
            change WeakDual.toStrongDual (F r) ∈ closedBall 0 (hardyNorm u p).toReal
            rw [mem_closedBall, dist_zero_right]
            exact (Lp.norm_lpPairing_mul_apply_le (q := q) (f r)).trans (hf_norm r))
    obtain ⟨U, _, hU⟩ := Lp.exists_eq_integral_mul_of_isFiniteMeasure (p := p) hq Λ.toStrongDual
    refine ⟨U, Lp.memLp U, fun w hw => ?_⟩
    have hK := (continuousOn_poissonKernel_right_of_mem_ball hw).memLp_circleMeasure zero_le_one q
    let K : Lp ℝ q (circleMeasure 0 1) := hK.toLp (poissonKernel 0 w)
    have hFr (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) 1) : F r K = u (r * w) := by
      change (ContinuousLinearMap.mul ℝ ℝ).lpPairing (circleMeasure 0 1) p q (f r) K = _
      rw [ContinuousLinearMap.lpPairing_eq_integral]
      refine (integral_congr_ae ?_).trans (integral_poissonKernel_mul_radial_eq hu hr hw)
      have hfr : (f r : ℂ → ℝ) =ᵐ[circleMeasure 0 1] fun z => u (r * z) := by
        dsimp [f]
        rw [dif_pos hr]
        exact MemLp.coeFn_toLp _
      filter_upwards [hfr, MemLp.coeFn_toLp hK] with z hz hk
      simp [K, hz, hk, mul_comm]
    have hlim : Tendsto (fun r : ℝ => F r K) (𝓝[<] 1) (𝓝 (u w)) := by
      have ht : Tendsto (fun r : ℝ => u (r * w)) (𝓝[<] 1) (𝓝 (u w)) := by
        have hmul : Tendsto (fun r : ℝ => (r : ℂ) * w) (𝓝 1) (𝓝 w) := by
          simpa using (Complex.continuous_ofReal.tendsto 1).mul_const w
        exact ((hu w hw).1.continuousAt.tendsto.comp hmul).mono_left nhdsWithin_le_nhds
      apply ht.congr'
      filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
      exact (hFr r hr).symm
    have heval : Λ K = u w := eq_of_nhds_neBot
      (((hΛ.continuousAt_comp (WeakDual.eval_continuous K).continuousAt).clusterPt.mono hlim))
    rw [← heval, ← WeakDual.toStrongDual_apply, hU, ContinuousLinearMap.lpPairing_eq_integral,
      poissonIntegral_withDensityᵥ (circleMeasure_compl_sphere zero_le_one) hw ((Lp.memLp U).integrable hp.le)]
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp hK] with z hz
    simp [K, hz, mul_comm]
  · -- Claude without review
    rintro ⟨U, hU, hu⟩
    refine ⟨fun w hw => ?_, ?_⟩
    · refine (InnerProductSpace.harmonicAt_congr_nhds ?_).2
        (harmonicOnNhd_poissonIntegral_withDensityᵥ (circleMeasure_compl_sphere zero_le_one)
          (hU.integrable hp.le) w hw)
      filter_upwards [isOpen_ball.mem_nhds hw] with x hx using hu x hx
    · have hcongr : hardyNorm u p = hardyNorm P[0; U ∂ᵥcircleMeasure 0 1] p := by
        unfold hardyNorm
        refine iSup_congr fun r => iSup_congr fun hr => ?_
        congr 1
        funext θ
        exact hu _ (radial_point_mem_unitDisc hr.1 hr.2)
      rw [hcongr]
      exact (hardyNorm_poissonIntegral_le hp.le hU).trans_lt hU.eLpNorm_lt_top

/-- **Garnett I.3.5(b), disc form, existence half.** A harmonic function on the unit disc whose
radial `L¹` means are uniformly bounded is the Poisson integral of a finite signed measure carried
by the unit circle. -/
theorem exists_eq_poissonIntegral_of_hardyNorm_lt_top {u : ℂ → ℝ}
  (hu : InnerProductSpace.HarmonicOnNhd u (ball 0 1)) (hbdd : hardyNorm u 1 < ∞) :
    ∃ ν : SignedMeasure ℂ, ν.totalVariation (sphere 0 1)ᶜ = 0 ∧
      ∀ w ∈ ball 0 1, u w = P[0; ν] w := by
  sorry

/-- **Garnett I.3.5(b), disc form.** The harmonic functions on the unit disc with uniformly bounded
radial `L¹` means are exactly the Poisson integrals of finite signed measures carried by
the unit circle. -/
theorem harmonicOnNhd_hardyNorm_lt_top_iff_exists_eq_poissonIntegral {u : ℂ → ℝ} :
    (InnerProductSpace.HarmonicOnNhd u (ball 0 1) ∧ hardyNorm u 1 < ∞) ↔
      ∃ ν : SignedMeasure ℂ, ν.totalVariation (sphere 0 1)ᶜ = 0 ∧
        ∀ w ∈ ball 0 1, u w = P[0; ν] w := by
  sorry


/-- **Garnett I.3.5(c), disc form**: the nonnegative harmonic functions
on `ball c R` are exactly the Poisson integrals of finite nonnegative measures carried by
`sphere c R`. -/
theorem harmonicOnNhd_nonneg_iff_exists_eq_poissonIntegral (hR : 0 < R) {u : ℂ → ℝ} :
    (InnerProductSpace.HarmonicOnNhd u (ball c R) ∧ ∀ w ∈ ball c R, 0 ≤ u w) ↔
      ∃ (μ : Measure ℂ) (_ : IsFiniteMeasure μ), μ (sphere c R)ᶜ = 0 ∧
        ∀ w ∈ ball c R, u w = P[c; μ.toSignedMeasure] w := by
  sorry















end
