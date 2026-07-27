import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Complete


noncomputable section

open scoped NNReal ENNReal Topology

open MeasureTheory Set Filter

variable {α ε ε' E F G 𝕜 : Type*} {m m0 : MeasurableSpace α} {p : ℝ≥0∞} {q : ℝ} {f : α → E}
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
  [NormedDivisionRing 𝕜] [Module 𝕜 F] [NormSMulClass 𝕜 F]
  {μ : Measure α} {f g : α → ε}




/-- Fixed `eLpNorm` where raised to the power `p` when `0 < p < 1`. -/
def eLpNormFixed [ENorm ε] {_ : MeasurableSpace α}
    (f : α → ε) (p : ℝ≥0∞) (μ : Measure α := by volume_tac) : ℝ≥0∞ :=
  if p ∈ Ioo 0 1 then (eLpNorm f p μ) ^ p.toReal else eLpNorm f p μ

/-- `eLpNormFixed` is the usual `eLpNorm` raised to `min p 1`. -/
lemma eLpNormFixed_eq_eLpNorm_rpow_min_one [ENorm ε]
    {f : α → ε} (hp : 0 < p) :
    eLpNormFixed f p μ = eLpNorm f p μ ^ (min p 1).toReal := by
  by_cases hp_lt_one : p < 1
  · have hp_small : p ∈ Ioo (0 : ℝ≥0∞) 1 := ⟨hp, hp_lt_one⟩
    rw [eLpNormFixed, if_pos hp_small, min_eq_left hp_lt_one.le]
  · have hp_one_le : 1 ≤ p := le_of_not_gt hp_lt_one
    have hp_not_small : p ∉ Ioo (0 : ℝ≥0∞) 1 := fun hp_small ↦ hp_lt_one hp_small.2
    rw [eLpNormFixed, if_neg hp_not_small, min_eq_right hp_one_le,
      ENNReal.toReal_one, ENNReal.rpow_one]



/-- Raising `eLpNormFixed` to `max p 1` recovers the usual finite `p`-moment. -/
lemma eLpNormFixed_rpow_max_one [ENorm ε]
    {f : α → ε} (hp : 0 < p) (hp_ne_top : p ≠ ∞) :
    eLpNormFixed f p μ ^ max p.toReal 1 = eLpNorm f p μ ^ p.toReal := by
  by_cases hp_lt_one : p < 1
  · have hp_small : p ∈ Ioo (0 : ℝ≥0∞) 1 := ⟨hp, hp_lt_one⟩
    have hp_toReal_le_one : p.toReal ≤ 1 := by
      rw [← ENNReal.toReal_one]
      exact ENNReal.toReal_mono ENNReal.one_ne_top hp_lt_one.le
    rw [eLpNormFixed, if_pos hp_small, max_eq_right hp_toReal_le_one, ENNReal.rpow_one]
  · have hp_one_le : 1 ≤ p := le_of_not_gt hp_lt_one
    have hp_not_small : p ∉ Ioo (0 : ℝ≥0∞) 1 := fun hp_small ↦ hp_lt_one hp_small.2
    have hp_toReal_one_le : 1 ≤ p.toReal := by
      rw [← ENNReal.toReal_one]
      exact (ENNReal.toReal_le_toReal ENNReal.one_ne_top hp_ne_top).2 hp_one_le
    rw [eLpNormFixed, if_neg hp_not_small, max_eq_left hp_toReal_one_le]




theorem eLpNormFixed_neg (f : α → F) (p : ℝ≥0∞) (μ : Measure α) :
    eLpNormFixed (-f) p μ = eLpNormFixed f p μ := by simp [eLpNormFixed, eLpNorm_neg]


def eLpFixedScalar (c : 𝕜) (p : ℝ≥0∞) : ℝ≥0∞ :=
  if p ∈ Ioo 0 1 then ‖c‖ₑ ^ p.toReal else ‖c‖ₑ


theorem eLpNormFixed_const_smul
    (c : 𝕜) (f : α → F) (p : ℝ≥0∞) (μ : Measure α) :
    eLpNormFixed (c • f) p μ = (eLpFixedScalar c p) * eLpNormFixed f p μ := by
  by_cases hp : p ∈ Ioo (0 : ℝ≥0∞) 1
  · simp [eLpNormFixed, eLpFixedScalar, hp, eLpNorm_const_smul, ENNReal.mul_rpow_of_nonneg]
  · simp [eLpNormFixed, eLpFixedScalar, hp, eLpNorm_const_smul]

theorem eLpNormFixed_eq_zero_iff
    [TopologicalSpace ε] [ENormedAddMonoid ε]
    {f : α → ε} (hf : AEStronglyMeasurable f μ) (h0 : p ≠ 0) :
    eLpNormFixed f p μ = 0 ↔ f =ᵐ[μ] 0 := by
  by_cases hp : p ∈ Ioo (0 : ℝ≥0∞) 1
  · have hp_ne_top : p ≠ ∞ := ne_of_lt (hp.2.trans ENNReal.one_lt_top)
    have hpt : 0 < p.toReal := ENNReal.toReal_pos h0 hp_ne_top
    simp only [eLpNormFixed, hp, if_true]
    constructor
    · intro h
      have he : eLpNorm f p μ = 0 := (ENNReal.rpow_eq_zero_iff_of_pos hpt).1 h
      exact (eLpNorm_eq_zero_iff hf h0).1 he
    · intro h
      have he : eLpNorm f p μ = 0 := (eLpNorm_eq_zero_iff hf h0).2 h
      exact (ENNReal.rpow_eq_zero_iff_of_pos hpt).2 he
  · simp only [eLpNormFixed, hp, if_false]
    exact eLpNorm_eq_zero_iff hf h0

theorem eLpNormFixed_add_le
    [TopologicalSpace ε] [ESeminormedAddMonoid ε]
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
     : eLpNormFixed (f + g) p μ ≤ eLpNormFixed f p μ + eLpNormFixed g p μ := by
  by_cases hp0 : p = 0
  · simp [eLpNormFixed, hp0]
  by_cases hp1 : 1 ≤ p
  · have hp_not_mem_Ioo : p ∉ Ioo (0 : ℝ≥0∞) 1 := by
      intro hp; exact (not_lt_of_ge hp1) hp.2
    simpa [eLpNormFixed, hp_not_mem_Ioo] using eLpNorm_add_le hf hg hp1
  · have hp_mem_Ioo : p ∈ Ioo (0 : ℝ≥0∞) 1 := by
      exact ⟨pos_iff_ne_zero.mpr hp0, lt_of_not_ge hp1⟩
    simp [eLpNormFixed, hp_mem_Ioo]
    -- The rest is given by codex
    have hp_ne_top : p ≠ ∞ := (ne_of_lt (hp_mem_Ioo.2.trans ENNReal.one_lt_top))
    have hq_pos : 0 < p.toReal := ENNReal.toReal_pos hp0 hp_ne_top
    have hq_le_one : p.toReal ≤ 1 := by
      exact (ENNReal.toReal_le_toReal hp_ne_top (by simp)).2 hp_mem_Ioo.2.le
    rw [eLpNorm_eq_eLpNorm' hp0 hp_ne_top,
      eLpNorm_eq_eLpNorm' hp0 hp_ne_top,
      eLpNorm_eq_eLpNorm' hp0 hp_ne_top]
    rw [← lintegral_rpow_enorm_eq_rpow_eLpNorm' (μ := μ) (f := f + g) hq_pos,
      ← lintegral_rpow_enorm_eq_rpow_eLpNorm' (μ := μ) (f := f) hq_pos,
      ← lintegral_rpow_enorm_eq_rpow_eLpNorm' (μ := μ) (f := g) hq_pos]
    calc
      (∫⁻ x, ‖(f + g) x‖ₑ ^ p.toReal ∂μ)
          ≤ ∫⁻ x, ‖f x‖ₑ ^ p.toReal + ‖g x‖ₑ ^ p.toReal ∂μ := by
        refine lintegral_mono ?_
        intro x
        have hnorm : ‖(f + g) x‖ₑ ≤ ‖f x‖ₑ + ‖g x‖ₑ := by
          simpa [Pi.add_apply] using enorm_add_le (f x) (g x)
        calc
          ‖(f + g) x‖ₑ ^ p.toReal
              ≤ (‖f x‖ₑ + ‖g x‖ₑ) ^ p.toReal := by
            exact ENNReal.rpow_le_rpow hnorm hq_pos.le
          _ ≤ ‖f x‖ₑ ^ p.toReal + ‖g x‖ₑ ^ p.toReal := by
            exact ENNReal.rpow_add_le_add_rpow (‖f x‖ₑ) (‖g x‖ₑ) hq_pos.le hq_le_one
      _ = (∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ) + ∫⁻ x, ‖g x‖ₑ ^ p.toReal ∂μ := by
        rw [lintegral_add_left' (hf.enorm.pow_const p.toReal)]

theorem eLpNormFixed_le_eLpNormFixed_of_exponent_le
    [TopologicalSpace ε] [ContinuousENorm ε]
    {f : α → ε} {p q : ℝ≥0∞} (hpq : p ≤ q) [Fact (1 ≤ p)] [IsProbabilityMeasure μ]
    (hf : AEStronglyMeasurable f μ) :
    eLpNormFixed f p μ ≤ eLpNormFixed f q μ := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hq1 : (1 : ℝ≥0∞) ≤ q := hp1.trans hpq
  have hp_not_mem_Ioo : p ∉ Ioo (0 : ℝ≥0∞) 1 := by
    intro hp
    exact (not_lt_of_ge hp1) hp.2
  have hq_not_mem_Ioo : q ∉ Ioo (0 : ℝ≥0∞) 1 := by
    intro hq
    exact (not_lt_of_ge hq1) hq.2
  simpa [eLpNormFixed, hp_not_mem_Ioo, hq_not_mem_Ioo] using
    eLpNorm_le_eLpNorm_of_exponent_le hpq hf

/-- Unconditional version of `eLpNormFixed_le_eLpNormFixed_of_exponent_le` for `0 < p ≤ q`:
since `eLpNormFixed` is `eLpNorm` raised to the fixed positive power `min p 1` (resp. `min q 1`),
comparing exponents across the `p < 1` boundary only gives a comparison up to a further fixed
positive power, not a literal `≤`. -/
theorem eLpNormFixed_le_eLpNormFixed_rpow_of_exponent_le
    [TopologicalSpace ε] [ContinuousENorm ε]
    {f : α → ε} {p q : ℝ≥0∞} (hp : p ≠ 0) (hpq : p ≤ q) [IsProbabilityMeasure μ]
    (hf : AEStronglyMeasurable f μ) :
    eLpNormFixed f p μ ≤ eLpNormFixed f q μ ^ ((min p 1).toReal / (min q 1).toReal) := by
  have hp_pos : 0 < p := pos_iff_ne_zero.mpr hp
  have hq_pos : 0 < q := hp_pos.trans_le hpq
  have hkq_pos : 0 < (min q 1).toReal :=
    ENNReal.toReal_pos (lt_min hq_pos one_pos).ne'
      (lt_of_le_of_lt (min_le_right q 1) ENNReal.one_lt_top).ne
  have hkey : (min q 1).toReal * ((min p 1).toReal / (min q 1).toReal) = (min p 1).toReal := by
    field_simp
  rw [eLpNormFixed_eq_eLpNorm_rpow_min_one hp_pos, eLpNormFixed_eq_eLpNorm_rpow_min_one hq_pos,
    ← ENNReal.rpow_mul, hkey]
  exact ENNReal.rpow_le_rpow (eLpNorm_le_eLpNorm_of_exponent_le hpq hf) ENNReal.toReal_nonneg

theorem eLpNormFixed_le_of_ae_bound_of_one_le
    {f : α → E} {C : ℝ} (hp : 1 ≤ p) [IsProbabilityMeasure μ]
    (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
    eLpNormFixed f p μ ≤ ENNReal.ofReal C := by
  have hp_not_mem_Ioo : p ∉ Ioo (0 : ℝ≥0∞) 1 := by
    intro hp_mem
    exact (not_lt_of_ge hp) hp_mem.2
  simpa [eLpNormFixed, hp_not_mem_Ioo, measure_univ] using
    (eLpNorm_le_of_ae_bound (p := p) (μ := μ) hfC)

/-- Fatou/lower-semicontinuity for `eLpNormFixed`. -/
theorem eLpNormFixed_lim_le_liminf_eLpNormFixed
    {u : ℕ → α → E} (hu : ∀ n, AEStronglyMeasurable (u n) μ) (u_lim : α → E)
    (h_lim : ∀ᵐ x : α ∂μ, Tendsto (fun n => u n x) atTop (𝓝 (u_lim x))) :
    eLpNormFixed u_lim p μ ≤ atTop.liminf fun n => eLpNormFixed (u n) p μ := by
  by_cases hp : p ∈ Ioo (0 : ℝ≥0∞) 1
  · have hp_ne_zero : p ≠ 0 := ne_of_gt hp.1
    have hp_ne_top : p ≠ ∞ := ne_of_lt (hp.2.trans ENNReal.one_lt_top)
    have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp_ne_zero hp_ne_top
    have hfatou :
        eLpNorm u_lim p μ ≤ atTop.liminf fun n => eLpNorm (u n) p μ :=
      Lp.eLpNorm_lim_le_liminf_eLpNorm (p := p) hu u_lim h_lim
    have hpow_liminf :
        (atTop.liminf fun n => eLpNorm (u n) p μ) ^ p.toReal =
          atTop.liminf fun n => (eLpNorm (u n) p μ) ^ p.toReal := by
      have h_rpow_mono := ENNReal.strictMono_rpow_of_pos hp_pos
      have h_rpow_surj := (ENNReal.rpow_left_bijective hp_pos.ne.symm).2
      refine (h_rpow_mono.orderIsoOfSurjective _ h_rpow_surj).liminf_apply ?_ ?_ ?_ ?_
      all_goals isBoundedDefault
    simpa [eLpNormFixed, hp, hpow_liminf] using
      ENNReal.rpow_le_rpow hfatou hp_pos.le
  · simpa [eLpNormFixed, hp] using
      (Lp.eLpNorm_lim_le_liminf_eLpNorm (p := p) hu u_lim h_lim)

/-- Fatou/lower-semicontinuity for `eLpNormFixed` along a countably generated filter. -/
theorem eLpNormFixed_le_liminf_filter
    {ι : Type*} {l : Filter ι} [NeBot l] [l.IsCountablyGenerated]
    {u : ι → α → E} (hu : ∀ i, AEStronglyMeasurable (u i) μ) (u_lim : α → E)
    (h_lim : ∀ᵐ x : α ∂μ, Tendsto (fun i => u i x) l (𝓝 (u_lim x))) :
    eLpNormFixed u_lim p μ ≤ l.liminf fun i => eLpNormFixed (u i) p μ := by
  refine le_of_forall_lt_imp_le_of_dense fun c hc => ?_
  have heventually : ∀ᶠ i in l, c ≤ eLpNormFixed (u i) p μ := by
    by_contra hnot
    have hfreq : ∃ᶠ i in l, eLpNormFixed (u i) p μ < c := by
      simpa [not_le] using hnot
    rcases Filter.exists_seq_forall_of_frequently hfreq with ⟨v, hv, hv_lt⟩
    have hseq_lim :
        ∀ᵐ x : α ∂μ, Tendsto (fun n => u (v n) x) atTop (𝓝 (u_lim x)) :=
      h_lim.mono fun x hx => hx.comp hv
    have hseq_fatou :
        eLpNormFixed u_lim p μ ≤
          atTop.liminf fun n => eLpNormFixed (u (v n)) p μ :=
      eLpNormFixed_lim_le_liminf_eLpNormFixed (fun n => hu (v n)) u_lim hseq_lim
    have hseq_liminf_le :
        atTop.liminf (fun n => eLpNormFixed (u (v n)) p μ) ≤ c := by
      refine Filter.liminf_le_of_le
        (f := atTop) (u := fun n => eLpNormFixed (u (v n)) p μ) (a := c) (h := ?_)
      intro b hb
      rcases (hb.and (Eventually.of_forall fun n => (hv_lt n).le)).exists with ⟨n, hbn, hnc⟩
      exact hbn.trans hnc
    exact (not_lt_of_ge (hseq_fatou.trans hseq_liminf_le)) hc
  exact Filter.le_liminf_of_le
    (f := l) (u := fun i => eLpNormFixed (u i) p μ) (a := c) (h := heventually)
