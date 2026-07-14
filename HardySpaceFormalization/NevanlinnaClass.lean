import HardySpaceFormalization.HardySpaceDisc
import Mathlib.Algebra.Order.Group.PosPart

/-!
# The Nevanlinna class on the unit disc

-/

noncomputable section

open scoped Real ENNReal NNReal
open MeasureTheory Real Complex Set Metric HardySpace



namespace Nevanlinna

/-- The radial Nevanlinna mean at radius `r`. -/
def nevanlinnaRadialMean (f : ℂ → ℂ) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ θ, ENNReal.ofReal (log ‖f (r * exp (I * θ))‖) ∂angularMeasure



/-- The Nevanlinna characteristic used here: the supremum of radial `log⁺` means. -/
def nevanlinnaCharacteristic (f : ℂ → ℂ) : ℝ≥0∞ :=
  ⨆ (r : ℝ) (_ : 0 < r ∧ r < 1), nevanlinnaRadialMean f r

lemma nevanlinnaRadialMean_le_characteristic (f : ℂ → ℂ) {r : ℝ}
    (hr : 0 < r ∧ r < 1) :
    nevanlinnaRadialMean f r ≤ nevanlinnaCharacteristic f := by
  unfold nevanlinnaCharacteristic
  exact (le_iSup (fun hr : 0 < r ∧ r < 1 => nevanlinnaRadialMean f r) hr).trans
    (le_iSup (fun r : ℝ => ⨆ (_ : 0 < r ∧ r < 1), nevanlinnaRadialMean f r) r)

/-- Membership in the Nevanlinna class on the unit disc, using radial `log⁺` means. -/
def MemNevanlinnaDisc (f : ℂ → ℂ) : Prop :=
  AnalyticOn ℂ f unitDisc ∧ nevanlinnaCharacteristic f < ∞ ∧
    ∀ z ∉ unitDisc, f z = 0

/-- The Nevanlinna class on the unit disc as a set of ambient functions `ℂ → ℂ`. -/
def NevanlinnaDisc : Set (ℂ → ℂ) := {f | MemNevanlinnaDisc f}

lemma memNevanlinnaDisc_iff {f : ℂ → ℂ} :
    f ∈ NevanlinnaDisc ↔ MemNevanlinnaDisc f := by rfl

/-- The elementary estimate behind the inclusion `H^p ⊆ N`:
`log⁺ x ≤ x^p / p` for `0 < p` and `0 ≤ x`. -/
lemma log_posPart_le_inv_mul_rpow {p x : ℝ} (hp : 0 < p) (hx : 0 ≤ x) :
    (Real.log x)⁺ ≤ p⁻¹ * x ^ p := by
  rw [posPart]
  refine max_le ?_ ?_
  · simpa [div_eq_inv_mul] using Real.log_le_rpow_div hx hp
  · exact mul_nonneg (inv_nonneg.mpr hp.le) (Real.rpow_nonneg hx p)

/-- Pointwise form of `log⁺ |z| ≤ |z|^p / p`. -/
lemma log_norm_posPart_le_inv_mul_norm_rpow {p : ℝ} (hp : 0 < p) (z : ℂ) :
    (Real.log ‖z‖)⁺ ≤ p⁻¹ * ‖z‖ ^ p :=
  log_posPart_le_inv_mul_rpow hp (norm_nonneg z)

/-- For `0 < p < 1`, radial Nevanlinna means are controlled by radial Hardy `p`-means. -/
lemma nevanlinnaRadialMean_le_inv_mul_hardyRadialMean_of_lt_one {p : ℝ≥0∞}
    (hp : p ∈ Ioo (0 : ℝ≥0∞) 1) (f : ℂ → ℂ) (r : ℝ) :
    nevanlinnaRadialMean f r ≤
      ENNReal.ofReal p.toReal⁻¹ * hardyRadialMean f p r := by
  -- codex without review
  have hp_ne_zero : p ≠ 0 := ne_of_gt hp.1
  have hp_ne_top : p ≠ ∞ := ne_of_lt (hp.2.trans ENNReal.one_lt_top)
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp_ne_zero hp_ne_top
  let g : ℝ → ℂ := fun θ => f (r * exp (I * θ))
  have hnorm_power :
      ∫⁻ θ, ‖g θ‖ₑ ^ p.toReal ∂angularMeasure =
        eLpNorm g p angularMeasure ^ p.toReal := by
    rw [eLpNorm_eq_eLpNorm' hp_ne_zero hp_ne_top]
    exact lintegral_rpow_enorm_eq_rpow_eLpNorm' hp_pos
  unfold nevanlinnaRadialMean hardyRadialMean eLpNormFixed
  rw [if_pos hp]
  rw [← hnorm_power]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun θ => ?_
  have hreal := log_norm_posPart_le_inv_mul_norm_rpow hp_pos (g θ)
  grw [ENNReal.ofReal_le_ofReal hreal]
  rw [ENNReal.ofReal_mul (inv_nonneg.mpr hp_pos.le)]
  rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp_pos.le]
  simp [ofReal_norm]

/-- Radial Nevanlinna means are controlled by radial Hardy `1`-means. -/
lemma nevanlinnaRadialMean_le_hardyRadialMean_one (f : ℂ → ℂ) (r : ℝ) :
    nevanlinnaRadialMean f r ≤ hardyRadialMean f 1 r := by
  -- codex without review
  unfold nevanlinnaRadialMean hardyRadialMean
  simp only [eLpNormFixed, show ¬(1 : ℝ≥0∞) ∈ Ioo 0 1 by simp, if_false,
    eLpNorm_one_eq_lintegral_enorm]
  refine lintegral_mono fun θ => ?_
  have hreal := log_norm_posPart_le_inv_mul_norm_rpow (p := 1) zero_lt_one
    (f (r * exp (I * θ)))
  simpa [ofReal_norm] using ENNReal.ofReal_le_ofReal hreal

/-- The fixed radial Hardy mean is controlled by the Hardy norm. -/
lemma hardyRadialMean_le_hardyNorm {p : ℝ≥0∞} (f : ℂ → ℂ)
    {r : ℝ} (hr : 0 < r ∧ r < 1) :
    hardyRadialMean f p r ≤ hardyNorm f p := by
  simpa [hardyRadialMean, angularMeasure, div_eq_mul_inv, mul_comm, mul_left_comm,
    mul_assoc] using hardyNorm_radial_le f p hr

/-- Every Hardy `p`-function with `0 < p < 1` belongs to the Nevanlinna class on the disc. -/
theorem memNevanlinnaDisc_of_memHpDisc_of_lt_one {p : ℝ≥0∞}
    (hp : p ∈ Ioo (0 : ℝ≥0∞) 1)
    {f : ℂ → ℂ} (hf : MemHpDisc (E := ℂ) p f) :
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

/-- Every Hardy `1`-function belongs to the Nevanlinna class on the disc. -/
theorem memNevanlinnaDisc_of_memHpDisc_one {f : ℂ → ℂ}
    (hf : MemHpDisc (E := ℂ) 1 f) : MemNevanlinnaDisc f := by
  rcases hf with ⟨hf_an, hf_norm, hf_zero⟩
  refine ⟨hf_an, ?_, hf_zero⟩
  refine lt_of_le_of_lt ?_ hf_norm
  unfold nevanlinnaCharacteristic
  refine iSup_le ?_
  intro r
  refine iSup_le ?_
  intro hr
  exact (nevanlinnaRadialMean_le_hardyRadialMean_one f r).trans
    (hardyRadialMean_le_hardyNorm f hr)

/-- Every Hardy `p`-function belongs to the Nevanlinna class on the disc for all `p > 0`, including `p = ∞`. -/
theorem memNevanlinnaDisc_of_memHpDisc {p : ℝ≥0∞} (hp : 0 < p)
    {f : ℂ → ℂ} (hf : MemHpDisc (E := ℂ) p f) :
    MemNevanlinnaDisc f := by
  by_cases hp_lt_one : p < 1
  · exact memNevanlinnaDisc_of_memHpDisc_of_lt_one ⟨hp, hp_lt_one⟩ hf
  · exact memNevanlinnaDisc_of_memHpDisc_one (HpDisc_mono (le_of_not_gt hp_lt_one) hf)

/-- As a set, `H^p ⊆ N` for all `p > 0`, including `p = ∞`. -/
theorem hpDisc_subset_nevanlinnaDisc {p : ℝ≥0∞} (hp : 0 < p) :
    ↑(HpDisc (E := ℂ) p) ⊆ NevanlinnaDisc := by
  intro f hf
  exact memNevanlinnaDisc_of_memHpDisc hp hf







end Nevanlinna
