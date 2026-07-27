import HardySpaceFormalization.HardySpaceDisc

/-!
# The Nevanlinna class on the unit disc

-/

noncomputable section

open scoped Real ENNReal NNReal
open MeasureTheory Real Complex Set Metric HardySpace



namespace Nevanlinna

variable {E F : Type*} [NormedAddCommGroup E] [NormedCommRing F]

/-- The radial Nevanlinna mean at radius `r`. -/
def nevanlinnaRadialMean (f : ℂ → E) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ θ, ENNReal.ofReal (log ‖f (r * exp (I * θ))‖) ∂angularMeasure

/-- The Nevanlinna characteristic used here: the supremum of radial `log⁺` means. -/
def nevanlinnaCharacteristic (f : ℂ → E) : ℝ≥0∞ :=
  ⨆ (r : ℝ) (_ : 0 < r ∧ r < 1), nevanlinnaRadialMean f r

lemma nevanlinnaRadialMean_le_characteristic (f : ℂ → E) {r : ℝ}
    (hr : 0 < r ∧ r < 1) :
    nevanlinnaRadialMean f r ≤ nevanlinnaCharacteristic f := by
  unfold nevanlinnaCharacteristic
  exact (le_iSup (fun hr : 0 < r ∧ r < 1 => nevanlinnaRadialMean f r) hr).trans
    (le_iSup (fun r : ℝ => ⨆ (_ : 0 < r ∧ r < 1), nevanlinnaRadialMean f r) r)

/-- Measurability of the radial `log⁺` integrand, for `f` continuous on the disc. -/
lemma radial_ofReal_log_measurable {f : ℂ → E} (hf : ContinuousOn f unitDisc)
    {r : ℝ} (hr : 0 < r ∧ r < 1) :
    Measurable fun θ : ℝ => ENNReal.ofReal (Real.log ‖f (r * exp (I * θ))‖) :=
  ENNReal.measurable_ofReal.comp
    (Real.measurable_log.comp (radial_cont hf hr).norm.measurable)


/-- The radial Nevanlinna mean of the zero function vanishes. -/
lemma nevanlinnaRadialMean_zero (r : ℝ) :
    nevanlinnaRadialMean (0 : ℂ → E) r = 0 := by simp [nevanlinnaRadialMean]

/-- The Nevanlinna characteristic of the zero function vanishes. -/
lemma nevanlinnaCharacteristic_zero :
    nevanlinnaCharacteristic (0 : ℂ → E) = 0 := by
  simp [nevanlinnaCharacteristic, nevanlinnaRadialMean]

-- # Here we prove some properties of `log^+` functions:

/-- The elementary estimate behind the inclusion `H^p ⊆ N`:
`log x ≤ x^p / p` for `0 < p` and `0 ≤ x`. Applying `ENNReal.ofReal` to the
left-hand side automatically takes its positive part. -/
lemma log_le_inv_mul_rpow {p x : ℝ} (hp : 0 < p) (hx : 0 ≤ x) :
    Real.log x ≤ p⁻¹ * x ^ p := by
  simpa [div_eq_inv_mul] using Real.log_le_rpow_div hx hp

/-- Pointwise form of `log ‖x‖ ≤ ‖x‖^p / p`. -/
lemma log_norm_le_inv_mul_norm_rpow {p : ℝ} (hp : 0 < p) (x : E) :
    Real.log ‖x‖ ≤ p⁻¹ * ‖x‖ ^ p :=
  log_le_inv_mul_rpow hp (norm_nonneg x)

/-- `x ↦ (log x)⁺` (encoded via `ENNReal.ofReal`) is monotone on `[0, ∞)`. -/
lemma ofReal_log_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    ENNReal.ofReal (Real.log x) ≤ ENNReal.ofReal (Real.log y) := by
  rcases le_total x 1 with h1 | h1
  · simp [ENNReal.ofReal_eq_zero.mpr (Real.log_nonpos hx h1)]
  · exact ENNReal.ofReal_le_ofReal
      (Real.log_le_log (lt_of_lt_of_le one_pos h1) hxy)

/-- Subadditivity of `log⁺` under multiplication:
`log⁺(xy) ≤ log⁺x + log⁺y` for nonnegative reals. -/
lemma ofReal_log_mul_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ENNReal.ofReal (Real.log (x * y)) ≤
      ENNReal.ofReal (Real.log x) + ENNReal.ofReal (Real.log y) := by
  rcases hx.eq_or_lt with rfl | hx
  · simp
  rcases hy.eq_or_lt with rfl | hy
  · simp
  · rw [Real.log_mul (ne_of_gt hx) (ne_of_gt hy)]
    exact ENNReal.ofReal_add_le

/-- Almost-subadditivity of `log⁺` under addition:
`log⁺(x + y) ≤ log 2 + log⁺x + log⁺y` for nonnegative reals. -/
lemma ofReal_log_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ENNReal.ofReal (Real.log (x + y)) ≤
    ENNReal.ofReal (Real.log 2) + (ENNReal.ofReal (Real.log x)+ ENNReal.ofReal (Real.log y))
  := by
  have hmax : x + y ≤ 2 * max x y := by
    rcases le_total x y with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  grw [ofReal_log_mono (by positivity) hmax, ofReal_log_mul_le
  (by norm_num) (hx.trans (le_max_left x y))]
  refine add_le_add le_rfl ?_
  rcases le_total x y with h | h
  . rw [max_eq_right h]; exact le_add_self
  . rw [max_eq_left h]; exact le_self_add

-- # Here are some useful estimate for `nevanlinnaRadialMean` and `nevanlinnaCharacteristic`:

/-- For `0 < p < 1`, radial Nevanlinna means are controlled by radial Hardy `p`-means.
This is just an auxiliary lemma for proving `H^p ≤ N` for `0 < p < 1`.-/
lemma nevanlinnaRadialMean_le_inv_mul_hardyRadialMean_of_lt_one {p : ℝ≥0∞}
    (hp : p ∈ Ioo (0 : ℝ≥0∞) 1) (f : ℂ → E) (r : ℝ) :
    nevanlinnaRadialMean f r ≤
      ENNReal.ofReal p.toReal⁻¹ * hardyRadialMean f p r := by
  have hp_ne_zero : p ≠ 0 := ne_of_gt hp.1
  have hp_ne_top : p ≠ ∞ := ne_of_lt (hp.2.trans ENNReal.one_lt_top)
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp_ne_zero hp_ne_top
  unfold nevanlinnaRadialMean hardyRadialMean eLpNormFixed
  rw [if_pos hp, eLpNorm_eq_eLpNorm' hp_ne_zero hp_ne_top,
     ← lintegral_rpow_enorm_eq_rpow_eLpNorm' hp_pos,
     ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun θ => ?_
  grw [ENNReal.ofReal_le_ofReal (log_norm_le_inv_mul_norm_rpow
      hp_pos (f (r * exp (I * θ))))]
  rw [ENNReal.ofReal_mul (inv_nonneg.mpr hp_pos.le),
  ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp_pos.le]
  simp [ofReal_norm]


/-- Radial Nevanlinna means are subadditive under pointwise multiplication. -/
lemma nevanlinnaRadialMean_mul_le {f : ℂ → F} (g : ℂ → F)
    (hf : ContinuousOn f unitDisc) {r : ℝ} (hr : 0 < r ∧ r < 1) :
    nevanlinnaRadialMean (f * g) r ≤
      nevanlinnaRadialMean f r + nevanlinnaRadialMean g r := by
  unfold nevanlinnaRadialMean
  rw [← lintegral_add_left (radial_ofReal_log_measurable hf hr)]
  refine lintegral_mono fun θ => ?_
  rw [Pi.mul_apply]
  exact (ofReal_log_mono (norm_nonneg _) (norm_mul_le _ _)).trans
    (ofReal_log_mul_le (norm_nonneg _) (norm_nonneg _))


/-- Radial Nevanlinna means are almost subadditive under pointwise addition,
up to the additive constant `log 2`. -/
lemma nevanlinnaRadialMean_add_le {f : ℂ → E} (g : ℂ → E)
    (hf : ContinuousOn f unitDisc) {r : ℝ} (hr : 0 < r ∧ r < 1) :
    nevanlinnaRadialMean (f + g) r ≤
      ENNReal.ofReal (Real.log 2) +
        (nevanlinnaRadialMean f r + nevanlinnaRadialMean g r) := by
  haveI : IsProbabilityMeasure angularMeasure :=
    isProbabilityMeasure_angularProbabilityMeasure
  unfold nevanlinnaRadialMean
  rw [← lintegral_add_left (radial_ofReal_log_measurable hf hr),
    ← mul_one (ENNReal.ofReal (Real.log 2)), ← measure_univ (μ := angularMeasure),
    ← lintegral_const, ← lintegral_add_left measurable_const]
  refine lintegral_mono fun θ => ?_
  exact (ofReal_log_mono (norm_nonneg _) (norm_add_le _ _)).trans
    (ofReal_log_add_le (norm_nonneg _) (norm_nonneg _))


/-- The Nevanlinna characteristic is almost subadditive under pointwise addition. -/
lemma nevanlinnaCharacteristic_add_le {f : ℂ → E} (g : ℂ → E)
    (hf : ContinuousOn f unitDisc) :
    nevanlinnaCharacteristic (f + g) ≤
      ENNReal.ofReal (Real.log 2) +
        (nevanlinnaCharacteristic f + nevanlinnaCharacteristic g) := by
  refine iSup₂_le fun r hr => ?_
  refine (nevanlinnaRadialMean_add_le g hf hr).trans ?_
  exact add_le_add le_rfl (add_le_add (nevanlinnaRadialMean_le_characteristic f hr)
    (nevanlinnaRadialMean_le_characteristic g hr))



-- # Now we'd like to define Nevanlinna class over unitDisc and prove `H^p ≤ N`:

variable [NormedSpace ℂ E]

/-- Membership in the Nevanlinna class on the unit disc, using radial `log⁺` means. -/
def MemNevanlinnaDisc (f : ℂ → E) : Prop :=
  AnalyticOn ℂ f unitDisc ∧ nevanlinnaCharacteristic f < ∞ ∧
    ∀ z ∉ unitDisc, f z = 0

/-- Every Hardy `p`-function with `0 < p < 1` belongs to the Nevanlinna class on the disc. -/
theorem memNevanlinnaDisc_of_memHpDisc_of_lt_one {p : ℝ≥0∞}
    (hp : p ∈ Ioo (0 : ℝ≥0∞) 1)
    {f : ℂ → E} (hf : MemHpDisc (E := E) p f) :
    MemNevanlinnaDisc f := by
  rcases hf with ⟨hf_an, hf_norm, hf_zero⟩
  refine ⟨hf_an, ?_, hf_zero⟩
  let C : ℝ≥0∞ := ENNReal.ofReal p.toReal⁻¹ * hardyNorm f p
  have hC_lt : C < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf_norm
  refine lt_of_le_of_lt ?_ hC_lt
  unfold nevanlinnaCharacteristic
  refine iSup_le ?_
  intro r
  refine iSup_le ?_
  intro hr
  have hradial := hardyRadialMean_le_hardyNorm (p := p) f hr
  exact (nevanlinnaRadialMean_le_inv_mul_hardyRadialMean_of_lt_one hp f r).trans
    (mul_le_mul_right hradial (ENNReal.ofReal p.toReal⁻¹))

/-- Every Hardy `p`-function belongs to the Nevanlinna class on the disc for all `p > 0`, including `p = ∞`.
For `p ≥ 1` this reduces to the `p < 1` case via the inclusion `H^p ⊆ H^{1/2}`. -/
theorem memNevanlinnaDisc_of_memHpDisc {p : ℝ≥0∞} (hp : 0 < p)
    {f : ℂ → E} (hf : MemHpDisc (E := E) p f) : MemNevanlinnaDisc f := by
  by_cases hp_lt_one : p < 1
  · exact memNevanlinnaDisc_of_memHpDisc_of_lt_one ⟨hp, hp_lt_one⟩ hf
  · have hhalf : 2⁻¹ ≤ p := le_trans (by norm_num) (le_of_not_gt hp_lt_one)
    exact memNevanlinnaDisc_of_memHpDisc_of_lt_one (p := 2⁻¹) ⟨by norm_num, by norm_num⟩
      (HpDisc_mono (by norm_num) hhalf hf)



/-!
### Algebraic structure of the Nevanlinna class

`N` is closed under addition, scalar multiplication and multiplication, so it
carries a `Submodule` structure over `ℂ` and, on top of that, a
`NonUnitalSubalgebra` structure inside `ℂ → ℂ`.  (It is *not* a unital
subalgebra with the present encoding: functions in `N` vanish outside the
disc, so the constant function `1` does not belong to it.)

The analytic content is the subadditivity of `log⁺`:
`log⁺(xy) ≤ log⁺x + log⁺y` and `log⁺(x + y) ≤ log 2 + log⁺x + log⁺y`.
-/

/-- Radial Nevanlinna means under scalar multiplication. -/
lemma nevanlinnaRadialMean_smul_le (c : ℂ) (f : ℂ → E) (r : ℝ) :
    nevanlinnaRadialMean (c • f) r ≤
      ENNReal.ofReal (log ‖c‖) + nevanlinnaRadialMean f r := by
  haveI : IsProbabilityMeasure angularMeasure :=
    isProbabilityMeasure_angularProbabilityMeasure
  unfold nevanlinnaRadialMean
  rw [← mul_one (ENNReal.ofReal (log ‖c‖)), ← measure_univ (μ := angularMeasure),
    ← lintegral_const, ← lintegral_add_left measurable_const]
  refine lintegral_mono fun θ => ?_
  simpa [Pi.smul_apply, norm_smul] using
    ofReal_log_mul_le (norm_nonneg c) (norm_nonneg (f (r * exp (I * θ))))

/-- The Nevanlinna characteristic is subadditive under pointwise multiplication. -/
lemma nevanlinnaCharacteristic_mul_le {f : ℂ → F} (g : ℂ → F)
    (hf : ContinuousOn f unitDisc):
    nevanlinnaCharacteristic (f * g) ≤
      nevanlinnaCharacteristic f + nevanlinnaCharacteristic g := by
  refine iSup₂_le fun r hr => ?_
  exact (nevanlinnaRadialMean_mul_le g hf hr).trans
    (add_le_add (nevanlinnaRadialMean_le_characteristic f hr)
      (nevanlinnaRadialMean_le_characteristic g hr))





/-- The Nevanlinna characteristic under scalar multiplication. -/
lemma nevanlinnaCharacteristic_smul_le (c : ℂ) (f : ℂ → E) :
    nevanlinnaCharacteristic (c • f) ≤
      ENNReal.ofReal (Real.log ‖c‖) + nevanlinnaCharacteristic f := by
  refine iSup₂_le fun r hr => ?_
  exact (nevanlinnaRadialMean_smul_le c f r).trans
    (add_le_add le_rfl (nevanlinnaRadialMean_le_characteristic f hr))

/-- The zero function belongs to the Nevanlinna class. -/
theorem MemNevanlinnaDisc.zero : MemNevanlinnaDisc (0 : ℂ → E) := by
  refine ⟨analyticOn_const, ?_, fun z _ => rfl⟩
  simp [nevanlinnaCharacteristic_zero]

/-- The Nevanlinna class is closed under addition. -/
theorem MemNevanlinnaDisc.add {f g : ℂ → E}
    (hf : MemNevanlinnaDisc f) (hg : MemNevanlinnaDisc g) :
    MemNevanlinnaDisc (f + g) := by
  obtain ⟨hf_an, hf_char, hf_zero⟩ := hf
  obtain ⟨hg_an, hg_char, hg_zero⟩ := hg
  refine ⟨hf_an.add hg_an, ?_, fun z hz => by
    simp [Pi.add_apply, hf_zero z hz, hg_zero z hz]⟩
  refine lt_of_le_of_lt (nevanlinnaCharacteristic_add_le g hf_an.continuousOn) ?_
  exact ENNReal.add_lt_top.mpr
    ⟨ENNReal.ofReal_lt_top, ENNReal.add_lt_top.mpr ⟨hf_char, hg_char⟩⟩

/-- The Nevanlinna class is closed under scalar multiplication. -/
theorem MemNevanlinnaDisc.smul {f : ℂ → E}
    (hf : MemNevanlinnaDisc f) (c : ℂ) : MemNevanlinnaDisc (c • f) := by
  obtain ⟨hf_an, hf_char, hf_zero⟩ := hf
  refine ⟨hf_an.const_smul, ?_, fun z hz => by simp [Pi.smul_apply, hf_zero z hz]⟩
  refine lt_of_le_of_lt (nevanlinnaCharacteristic_smul_le c f) ?_
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, hf_char⟩

/-- The Nevanlinna class is closed under pointwise multiplication. -/
theorem MemNevanlinnaDisc.mul {f g : ℂ → F} [NormedAlgebra ℂ F]
    (hf : MemNevanlinnaDisc f) (hg : MemNevanlinnaDisc g) :
    MemNevanlinnaDisc (f * g) := by
  obtain ⟨hf_an, hf_char, hf_zero⟩ := hf
  obtain ⟨hg_an, hg_char, hg_zero⟩ := hg
  refine ⟨hf_an.mul hg_an, ?_, fun z hz => by simp [Pi.mul_apply, hf_zero z hz]⟩
  exact lt_of_le_of_lt (nevanlinnaCharacteristic_mul_le g hf_an.continuousOn)
    (ENNReal.add_lt_top.mpr ⟨hf_char, hg_char⟩)

-- # Here's the definition of `NevanlinnaDisc` for Nevanlinna class over unitDisc

variable [NormedAlgebra ℂ F]

/-- The Nevanlinna class on the unit disc as a non-unital `ℂ`-subalgebra of
`ℂ → F`.  It is not a `Subalgebra`: the *ambient* unit, the constant function
`1`, does not vanish outside the disc, hence is not a member.  It is, however,
a unital ring in its own right, with unit the idempotent
`unitDisc.indicator 1`. -/
def NevanlinnaDisc : NonUnitalSubalgebra ℂ (ℂ → F) where
  carrier := {f | MemNevanlinnaDisc f}
  add_mem' hf hg := MemNevanlinnaDisc.add hf hg
  zero_mem' := MemNevanlinnaDisc.zero
  smul_mem' c _ hf := MemNevanlinnaDisc.smul hf c
  mul_mem' hf hg := MemNevanlinnaDisc.mul hf hg

@[simp] lemma memNevanlinnaDisc_iff {f : ℂ → F} :
    f ∈ NevanlinnaDisc ↔ MemNevanlinnaDisc f := Iff.rfl

/-- As `ℂ`-submodules, `H^p ≤ N` for all `p > 0`, including `p = ∞`. -/
theorem hpDisc_le_nevanlinnaDisc {p : ℝ≥0∞} (hp : 0 < p) :
    HpDisc (E := F) p ≤ NevanlinnaDisc.toSubmodule := by
  intro f hf
  exact memNevanlinnaDisc_of_memHpDisc hp hf


/-!
### The local identity of the Nevanlinna class

Although `N` is not a *unital subalgebra* of `ℂ → ℂ` (the ambient unit, the
constant function `1`, does not vanish outside the disc so it is not a member),
`N` is a unital ring in its own right.  Its unit is the idempotent
`unitDisc.indicator 1`, the indicator of the disc: for `f ∈ N` (which vanishes
outside the disc) one has `unitDisc.indicator 1 * f = f` on the nose.  This is
the standard "corner ring `eRe`" phenomenon for an idempotent `e` of the
ambient ring.
-/

omit [NormedAlgebra ℂ F] in
/-- The disc indicator `unitDisc.indicator 1` is a local left identity:
`unitDisc.indicator 1 * f = f` for every `f` vanishing outside the disc (in
particular for every `f ∈ N`). -/
theorem indicator_unitDisc_mul {f : ℂ → F} (hf : ∀ z ∉ unitDisc, f z = 0) :
    unitDisc.indicator 1 * f = f := by
  ext z
  by_cases hz : z ∈ unitDisc
  · simp [Pi.mul_apply, Set.indicator_of_mem hz]
  · simp [Pi.mul_apply, Set.indicator_of_notMem hz, hf z hz]

/-- The disc indicator belongs to the Nevanlinna class; it is the unit of `N`.
Its characteristic is the finite constant `log ‖(1 : F)‖` (which is `0` when
`‖1‖ = 1`, e.g. for `F = ℂ`). -/
theorem memNevanlinnaDisc_indicator_unitDisc :
    MemNevanlinnaDisc (unitDisc.indicator (1 : ℂ → F)) := by
  refine ⟨?_, ?_, fun z hz => by simp [Set.indicator_of_notMem hz]⟩
  · have h1 : AnalyticOn ℂ (fun _ : ℂ => (1 : F)) unitDisc := analyticOn_const
    exact h1.congr fun z hz => by rw [Set.indicator_of_mem hz]; rfl
  · haveI : IsProbabilityMeasure angularMeasure :=
      isProbabilityMeasure_angularProbabilityMeasure
    have hle : nevanlinnaCharacteristic (unitDisc.indicator (1 : ℂ → F))
        ≤ ENNReal.ofReal (Real.log ‖(1 : F)‖) := by
      refine iSup₂_le fun r hr => le_of_eq ?_
      unfold nevanlinnaRadialMean
      simp_rw [Set.indicator_of_mem (radial_point_mem_unitDisc hr.1 hr.2), Pi.one_apply]
      rw [lintegral_const, measure_univ, mul_one]
    exact lt_of_le_of_lt hle ENNReal.ofReal_lt_top

/-- The unit of `↥N`: the disc indicator.  Note this is *not* the ambient unit
`(1 : ℂ → F)`, which does not belong to `N`. -/
instance : One (NevanlinnaDisc (F := F)) :=
  ⟨⟨unitDisc.indicator 1, memNevanlinnaDisc_indicator_unitDisc⟩⟩

@[simp] lemma coe_one :
    ((1 : NevanlinnaDisc (F := F)) : ℂ → F) = unitDisc.indicator 1 := rfl

/-- `↥N` is a unital commutative ring in its own right — with unit the disc
indicator, not the ambient `1`.  The `NonUnitalCommRing` structure is supplied
for free by the `NonUnitalSubalgebra` bundle; we only add the unit. -/
instance : CommRing (NevanlinnaDisc (F := F)) where
  __ := (inferInstance : NonUnitalCommRing (NevanlinnaDisc (F := F)))
  one := 1
  one_mul a := Subtype.ext (indicator_unitDisc_mul (memNevanlinnaDisc_iff.mp a.2).2.2)
  mul_one a := Subtype.ext (by
    show a.1 * unitDisc.indicator 1 = a.1
    rw [mul_comm]; exact indicator_unitDisc_mul (memNevanlinnaDisc_iff.mp a.2).2.2)

/-- `N` is a commutative `ℂ`-algebra, with `algebraMap c = c • (unitDisc.indicator 1)`. -/
instance : Algebra ℂ (NevanlinnaDisc (F := F)) :=
  Algebra.ofModule
    (fun r x y => Subtype.ext (smul_mul_assoc r x.1 y.1))
    (fun r x y => Subtype.ext (mul_smul_comm r x.1 y.1))


end Nevanlinna
