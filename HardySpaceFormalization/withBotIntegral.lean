import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

/-- A positive constant can be pulled through the auxiliary real representative of a
`WithBot ℝ` value. -/
lemma unbotD_const_mul_of_pos {p : ℝ} (hp : 0 < p) (x : WithBot ℝ) :
    (WithBot.unbotD 0) ((p : WithBot ℝ) * x) = p * (WithBot.unbotD 0) x := by
  cases x with
  | bot =>
      have hp_ne : (p : WithBot ℝ) ≠ 0 := by exact_mod_cast hp.ne'
      simp [WithBot.unbotD, WithBot.mul_bot hp_ne]
  | coe a =>
      simp [WithBot.unbotD, ← WithBot.coe_mul]

/-- The auxiliary real representative of a sum is pointwise bounded by the sum of the norms of
the two auxiliary representatives. -/
lemma norm_unbotD_add_le (x y : WithBot ℝ) :
    ‖(WithBot.unbotD 0) (x + y)‖ ≤ ‖(WithBot.unbotD 0) x‖ + ‖(WithBot.unbotD 0) y‖ := by
  cases x with
  | bot => simp [WithBot.unbotD]
  | coe a =>
      cases y with
      | bot => simp [WithBot.unbotD]
      | coe b =>
          simpa [WithBot.unbotD, ← WithBot.coe_add] using norm_add_le a b

/-- For a positive constant, multiplying by that constant preserves and reflects `⊥`. -/
lemma const_mul_eq_bot_iff_of_pos {p : ℝ} (hp : 0 < p) (x : WithBot ℝ) :
    (p : WithBot ℝ) * x = ⊥ ↔ x = ⊥ := by
  cases x with
  | bot =>
      have hp_ne : (p : WithBot ℝ) ≠ 0 := by exact_mod_cast hp.ne'
      simp [WithBot.mul_bot hp_ne]
  | coe a =>
      rw [WithBot.mul_eq_bot_iff]
      simp

/-- Positive constant multiplication is monotone on `WithBot ℝ`. -/
lemma WithBot.const_mul_le_const_mul_of_pos {p : ℝ} (hp : 0 < p)
    {x y : WithBot ℝ} (hxy : x ≤ y) :
    (p : WithBot ℝ) * x ≤ (p : WithBot ℝ) * y := by
  cases x with
  | bot =>
      have hp_ne : (p : WithBot ℝ) ≠ 0 := by exact_mod_cast hp.ne'
      cases y <;> simp [WithBot.mul_bot hp_ne]
  | coe a =>
      cases y with
      | bot =>
          simp at hxy
      | coe b =>
          exact WithBot.coe_le_coe.mpr
            (mul_le_mul_of_nonneg_left (WithBot.coe_le_coe.mp hxy) hp.le)

/-- A real scalar coerced to `WithBot ℝ` distributes over `WithBot` addition. This is not a global
`mul_add` instance for `WithBot ℝ`; it is the finite scalar case needed below. -/
lemma WithBot.coe_mul_add (q : ℝ) (x y : WithBot ℝ) :
    (q : WithBot ℝ) * (x + y) = (q : WithBot ℝ) * x + (q : WithBot ℝ) * y := by
  by_cases hq : q = 0
  · simp [hq]
  · cases x with
    | bot =>
        have hq_wb : (q : WithBot ℝ) ≠ 0 := by exact_mod_cast hq
        cases y with
        | bot => simp [WithBot.mul_bot hq_wb]
        | coe b => simp [WithBot.mul_bot hq_wb]
    | coe a =>
        have hq_wb : (q : WithBot ℝ) ≠ 0 := by exact_mod_cast hq
        cases y with
        | bot => simp [WithBot.mul_bot hq_wb]
        | coe b =>
            norm_num [← WithBot.coe_add, ← WithBot.coe_mul]
            ring

lemma WithBot.add_neg_coe_le_zero_iff (x : WithBot ℝ) (a : ℝ) :
    x + ((-a : ℝ) : WithBot ℝ) ≤ 0 ↔ x ≤ a := by
  cases x with
  | bot => simp
  | coe b =>
      constructor
      · intro h
        exact WithBot.coe_le_coe.mpr (by
          have hreal : b + -a ≤ 0 := WithBot.coe_le_coe.mp (by simpa using h)
          linarith)
      · intro h
        have hreal : b ≤ a := WithBot.coe_le_coe.mp h
        exact WithBot.coe_le_coe.mpr (by linarith)

-- # Now we'd like to define `withBotIntegral` to integrate `WithBot ℝ`-valued function:

open Classical in
/-- The integral of a `WithBot ℝ`-valued function. If the `⊥` set has positive measure and the
integrand is integrable, the integral is defined to be `⊥`; otherwise we integrate the real-valued
representative obtained by sending `⊥` to `0`. -/
def withBotIntegral {α : Type*} [MeasurableSpace α] (μ : Measure α) (u : α → WithBot ℝ) :
    WithBot ℝ :=
  if μ {x | u x = ⊥} = 0 ∧ Integrable ((WithBot.unbotD 0) ∘ u) μ then
      ((∫ x, (u x).unbotD 0 ∂μ : ℝ) : WithBot ℝ)
  else ⊥

notation3 "∫ᴮ " (...) ", " r:60:(scoped f => f) " ∂" μ:70 => withBotIntegral μ r
notation3 "∫ᴮ " (...) ", " r:60:(scoped f => withBotIntegral volume f) => r
notation3 "∫ᴮ " (...) " in " s ", " r:60:(scoped f => f) " ∂" μ:70 =>
  withBotIntegral (Measure.restrict μ s) r
notation3 "∫ᴮ " (...) " in " s ", " r:60:(scoped f => withBotIntegral (Measure.restrict volume s) f) =>
  r

/-- For a real-valued function coerced to `WithBot ℝ`, the `WithBot` integral is just the ordinary
Bochner integral, coerced to `WithBot ℝ`. -/
lemma withBotIntegral_coe {α : Type*} [MeasurableSpace α] (u : α → ℝ) (A : Set α)
  (μ : Measure α)
  (hu : IntegrableOn u A μ) :
  ∫ᴮ x in A, (u x : WithBot ℝ) ∂μ = ((∫ x in A, u x ∂μ : ℝ) : WithBot ℝ) := by
  have hint : Integrable ((WithBot.unbotD 0) ∘ fun x => (u x : WithBot ℝ)) (μ.restrict A) := by
    simpa [Function.comp_def, WithBot.unbotD] using hu.integrable
  simp [withBotIntegral, hint, WithBot.unbotD]

/-- If a `WithBot ℝ`-valued function agrees almost everywhere with a real-valued representative,
then the auxiliary real representative obtained by `(WithBot.unbotD 0)` is integrable wherever the
real representative is integrable. -/
lemma integrableOn_unbotD_of_eq_coe_ae {α : Type*} [MeasurableSpace α]
    {u : α → WithBot ℝ} {v : α → ℝ} {A : Set α} {μ : Measure α}
    (hv : IntegrableOn v A μ)(huv : ∀ᵐ x ∂μ.restrict A, u x = v x) :
    IntegrableOn ((WithBot.unbotD 0) ∘ u) A μ := by
  refine hv.congr_fun_ae ?_
  filter_upwards [huv] with x hx
  simp [hx, WithBot.unbotD]

/-- Positive constant multiplication commutes with the `WithBot` integral. -/
lemma withBotIntegral_const_mul_of_pos {α : Type*} [MeasurableSpace α] {p : ℝ} (hp : 0 < p)
    (u : α → WithBot ℝ) (μ : Measure α) :
    withBotIntegral μ (fun x => (p : WithBot ℝ) * u x) =
      (p : WithBot ℝ) * withBotIntegral μ u := by
  have hint_iff :
      Integrable ((WithBot.unbotD 0) ∘ fun x => (p : WithBot ℝ) * u x) μ ↔
        Integrable ((WithBot.unbotD 0) ∘ u) μ := by
    simpa [Function.comp_def, unbotD_const_mul_of_pos hp] using
      (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hp.ne')
        (fun x => (u x).unbotD 0) (μ := μ))
  have hbotset :
      {x | (p : WithBot ℝ) * u x = ⊥} = {x | u x = ⊥} := by
    ext x
    simp [const_mul_eq_bot_iff_of_pos hp]
  unfold withBotIntegral
  rw [hbotset]
  rw [hint_iff]
  by_cases hcond :
      μ {x | u x = ⊥} = 0 ∧ Integrable ((WithBot.unbotD 0) ∘ u) μ
  · simp [hcond, unbotD_const_mul_of_pos hp, integral_const_mul]
  · simp [hcond]
    have hp_ne : (p : WithBot ℝ) ≠ 0 := by exact_mod_cast hp.ne'
    simp [WithBot.mul_bot hp_ne]

/-- The auxiliary real representative of a sum is integrable if both representatives are integrable
and both summands are finite almost everywhere on the integration set. -/
lemma integrableOn_unbotD_add_of_bot_null {α : Type*} [MeasurableSpace α]
    {u v : α → WithBot ℝ} {A : Set α}
    {μ : Measure α} (hA : MeasurableSet A)
    (hu_bot : μ (A ∩ {x | u x = ⊥}) = 0)
    (hv_bot : μ (A ∩ {x | v x = ⊥}) = 0)
    (hu_int : IntegrableOn ((WithBot.unbotD 0) ∘ u) A μ)
    (hv_int : IntegrableOn ((WithBot.unbotD 0) ∘ v) A μ) :
    IntegrableOn ((WithBot.unbotD 0) ∘ (u + v)) A μ := by
  refine (hu_int.add hv_int).congr_fun_ae ?_
  have hu_ne : ∀ᵐ x ∂μ.restrict A, u x ≠ ⊥ := by
    rw [ae_iff, Measure.restrict_apply_eq_zero' hA]
    simpa [inter_comm] using hu_bot
  have hv_ne : ∀ᵐ x ∂μ.restrict A, v x ≠ ⊥ := by
    rw [ae_iff, Measure.restrict_apply_eq_zero' hA]
    simpa [inter_comm] using hv_bot
  filter_upwards [hu_ne, hv_ne] with x hux hvx
  cases hux' : u x with
  | bot => exact False.elim (hux hux')
  | coe a =>
      cases hvx' : v x with
      | bot => exact False.elim (hvx hvx')
      | coe b =>
          simp [Function.comp_def, WithBot.unbotD, hux', hvx', ← WithBot.coe_add]

/-- Linearity of the `WithBot` integral under addition.  If either summand is `⊥` on a set of
positive measure, both sides reduce to `⊥`; otherwise this is ordinary Bochner integral linearity
for the real representatives. -/
lemma withBotIntegral_add {α : Type*} [MeasurableSpace α] {u v : α → WithBot ℝ}
    {μ : Measure α}
    (hu_int : Integrable ((WithBot.unbotD 0) ∘ u) μ)
    (hv_int : Integrable ((WithBot.unbotD 0) ∘ v) μ) :
    (∫ᴮ x, u x + v x ∂μ) = (∫ᴮ x, u x ∂μ) + (∫ᴮ x, v x ∂μ) := by
  unfold withBotIntegral
  by_cases hu_bot : μ {x | u x = ⊥} = 0
  · by_cases hv_bot : μ {x | v x = ⊥} = 0
    · have hu_cond :
          μ {x | u x = ⊥} = 0 ∧ Integrable ((WithBot.unbotD 0) ∘ u) μ := by
        exact ⟨hu_bot, hu_int⟩
      have hv_cond :
          μ {x | v x = ⊥} = 0 ∧ Integrable ((WithBot.unbotD 0) ∘ v) μ := by
        exact ⟨hv_bot, hv_int⟩
      have hu_ne : ∀ᵐ x ∂μ, u x ≠ ⊥ := by
        rw [ae_iff]
        simpa using hu_bot
      have hv_ne : ∀ᵐ x ∂μ, v x ≠ ⊥ := by
        rw [ae_iff]
        simpa using hv_bot
      have hsum_int :
          Integrable ((WithBot.unbotD 0) ∘ fun x => u x + v x) μ := by
        refine (hu_int.add hv_int).congr ?_
        filter_upwards [hu_ne, hv_ne] with x hux hvx
        cases hux' : u x with
        | bot => exact False.elim (hux hux')
        | coe a =>
            cases hvx' : v x with
            | bot => exact False.elim (hvx hvx')
            | coe b =>
                simp [Function.comp_def, WithBot.unbotD, hux', hvx', ← WithBot.coe_add]
      have hsum_bot : μ {x | u x + v x = ⊥} = 0 := by
        refine measure_mono_null ?_ (measure_union_null hu_bot hv_bot)
        intro x hx
        rw [mem_union, mem_setOf_eq, mem_setOf_eq]
        simpa [WithBot.add_eq_bot] using hx
      have hsum_bot_or : μ {x | u x = ⊥ ∨ v x = ⊥} = 0 := by
        simpa [setOf_or] using measure_union_null hu_bot hv_bot
      have hsum_cond :
          μ {x | u x + v x = ⊥} = 0 ∧
            Integrable ((WithBot.unbotD 0) ∘ fun x => u x + v x) μ := by
        exact ⟨hsum_bot, hsum_int⟩
      simp [hsum_cond, hu_cond, hv_cond, hsum_bot_or]
      have hsum_eq :
          (fun x => (WithBot.unbotD 0) (u x + v x)) =ᵐ[μ]
            fun x => (WithBot.unbotD 0) (u x) + (WithBot.unbotD 0) (v x) := by
        filter_upwards [hu_ne, hv_ne] with x hux hvx
        cases hux' : u x with
        | bot => exact False.elim (hux hux')
        | coe a =>
            cases hvx' : v x with
            | bot => exact False.elim (hvx hvx')
            | coe b =>
                simp [WithBot.unbotD, ← WithBot.coe_add]
      rw [integral_congr_ae hsum_eq]
      rw [integral_add]
      · simp
      · simpa [Function.comp_def] using hu_int
      · simpa [Function.comp_def] using hv_int
    · have hv_cond_not :
          ¬(μ {x | v x = ⊥} = 0 ∧ Integrable ((WithBot.unbotD 0) ∘ v) μ) := by
        exact fun h => hv_bot h.1
      have hsum_bot_or_ne : μ {x | u x = ⊥ ∨ v x = ⊥} ≠ 0 := by
        intro hsum_bot_or
        apply hv_bot
        refine measure_mono_null ?_ hsum_bot_or
        intro x hx
        exact Or.inr hx
      have hsum_bot_ne : μ {x | u x + v x = ⊥} ≠ 0 := by
        intro hsum_bot
        apply hv_bot
        refine measure_mono_null ?_ hsum_bot
        intro x hx
        change u x + v x = ⊥
        rw [WithBot.add_eq_bot]
        exact Or.inr hx
      have hsum_cond_not :
          ¬(μ {x | u x + v x = ⊥} = 0 ∧
              Integrable ((WithBot.unbotD 0) ∘ fun x => u x + v x) μ) := by
        exact fun h => hsum_bot_ne h.1
      simp [hsum_bot_or_ne, hv_cond_not]
  · have hu_cond_not :
        ¬(μ {x | u x = ⊥} = 0 ∧ Integrable ((WithBot.unbotD 0) ∘ u) μ) := by
      exact fun h => hu_bot h.1
    have hsum_bot_or_ne : μ {x | u x = ⊥ ∨ v x = ⊥} ≠ 0 := by
      intro hsum_bot_or
      apply hu_bot
      refine measure_mono_null ?_ hsum_bot_or
      intro x hx
      exact Or.inl hx
    have hsum_bot_ne : μ {x | u x + v x = ⊥} ≠ 0 := by
      intro hsum_bot
      apply hu_bot
      refine measure_mono_null ?_ hsum_bot
      intro x hx
      change u x + v x = ⊥
      rw [WithBot.add_eq_bot]
      exact Or.inl hx
    have hsum_cond_not :
        ¬(μ {x | u x + v x = ⊥} = 0 ∧
            Integrable ((WithBot.unbotD 0) ∘ fun x => u x + v x) μ) := by
      exact fun h => hsum_bot_ne h.1
    simp [hsum_bot_or_ne, hu_cond_not]

/-- Set-notation wrapper for `withBotIntegral_add`; this is just the measure-level statement
applied to `μ.restrict A`. -/
lemma withBotIntegral_add_set {α : Type*} [MeasurableSpace α] {u v : α → WithBot ℝ}
    {A : Set α} {μ : Measure α}
    (hu_int : IntegrableOn ((WithBot.unbotD 0) ∘ u) A μ)
    (hv_int : IntegrableOn ((WithBot.unbotD 0) ∘ v) A μ) :
    (∫ᴮ x in A, u x + v x ∂μ) = (∫ᴮ x in A, u x ∂μ) + (∫ᴮ x in A, v x ∂μ) := by
  exact withBotIntegral_add (μ := μ.restrict A) hu_int.integrable hv_int.integrable

/-- `withBotIntegral` is monotone: an a.e. pointwise `≤` implies the `WithBot`-integrals compare.
The key cases are:
· if the lower function has positive `⊥`-set or nonintegrable real representative, the left side
  is `⊥`;
· otherwise the comparison is the standard integral monotonicity for the real representatives. -/
lemma withBotIntegral_mono {α : Type*} [MeasurableSpace α] {u v : α → WithBot ℝ}
    {μ : Measure α}
    (h : ∀ᵐ x ∂μ, u x ≤ v x)
    (hv_int : Integrable (fun x => (WithBot.unbotD 0) (v x)) μ) :
    withBotIntegral μ u ≤ withBotIntegral μ v := by
  unfold withBotIntegral
  by_cases hu_cond :
      μ {x | u x = ⊥} = 0 ∧ Integrable ((WithBot.unbotD 0) ∘ u) μ
  · have hu_bot : μ {x | u x = ⊥} = 0 := hu_cond.1
    have hu_int : Integrable (fun x => (WithBot.unbotD 0) (u x)) μ := by
      simpa [Function.comp_def] using hu_cond.2
    have hu_ne_bot : ∀ᵐ x ∂μ, u x ≠ ⊥ := by
      rw [ae_iff]
      simpa using hu_bot
    have hv_ne_bot : ∀ᵐ x ∂μ, v x ≠ ⊥ := by
      filter_upwards [h, hu_ne_bot] with x huv hux_ne
      intro hvx
      exact hux_ne (le_antisymm (hvx ▸ huv) bot_le)
    have hv_bot : μ {x | v x = ⊥} = 0 := by
      simpa using (ae_iff.mp hv_ne_bot)
    have hv_cond :
        μ {x | v x = ⊥} = 0 ∧ Integrable ((WithBot.unbotD 0) ∘ v) μ := by
      simpa [Function.comp_def] using And.intro hv_bot hv_int
    simp [hu_cond, hv_cond]
    have hv_ne_bot : ∀ᵐ x ∂μ, v x ≠ ⊥ := by
      rw [ae_iff]
      simpa using hv_bot
    have hle_real :
        (fun x => (WithBot.unbotD 0) (u x)) ≤ᵐ[μ]
          fun x => (WithBot.unbotD 0) (v x) := by
      filter_upwards [h, hu_ne_bot, hv_ne_bot] with x huv hux_ne hvx_ne
      cases hux : u x with
      | bot => exact False.elim (hux_ne hux)
      | coe a =>
          cases hvx : v x with
          | bot => exact False.elim (hvx_ne hvx)
          | coe b =>
              simpa [WithBot.unbotD, hux, hvx] using
                WithBot.coe_le_coe.mp (by simpa [hux, hvx] using huv)
    exact integral_mono_ae hu_int hv_int hle_real
  · simp [hu_cond]

/-- Set-notation wrapper for `withBotIntegral_mono`; this is just the measure-level statement
applied to `μ.restrict A`. -/
lemma withBotIntegral_mono_set {α : Type*} [MeasurableSpace α] {u v : α → WithBot ℝ}
    {A : Set α} {μ : Measure α}
    (h : ∀ᵐ x ∂μ.restrict A, u x ≤ v x)
    (hv_int : IntegrableOn (fun x => (WithBot.unbotD 0) (v x)) A μ) :
    withBotIntegral (μ.restrict A) u ≤ withBotIntegral (μ.restrict A) v := by
  exact withBotIntegral_mono (μ := μ.restrict A) h hv_int.integrable
