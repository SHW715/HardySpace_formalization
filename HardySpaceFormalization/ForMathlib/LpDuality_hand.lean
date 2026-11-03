import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import HardySpaceFormalization.ForMathlib.CompLpIsometry_hand
import HardySpaceFormalization.ForMathlib.Semifinite_hand

open ENNReal MeasureTheory ComplexConjugate

-- Target: `Mathlib/MeasureTheory/Function/Holder.lean`, after `lpPairing_eq_integral`
-- (`SemiFinite` comes from `Semifinite_hand.lean`, i.e. mathlib PR #35671.)


noncomputable section

variable {α 𝕜 E F G : Type*} {m : MeasurableSpace α} {μ : Measure α} {p q : ENNReal}
    [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [NormedSpace 𝕜 G]
    (B : E →L[𝕜] F →L[𝕜] 𝕜)

variable [Fact (1 ≤ p)] [Fact (1 ≤ q)]
variable [HolderConjugate p q] [NormedSpace ℝ G] [SMulCommClass ℝ 𝕜 G] [CompleteSpace G]

#check Isometry
#check Function.Surjective


namespace MeasureTheory

#check SigmaFinite

end MeasureTheory

namespace ContinuousLinearMap

/- ## Isometry of L^p pairing : for general `Isometry B` -/

-- # We first prove one direction of inequality

-- This one is missing in `Holder.lean`.
theorem norm_lpPairing_le (B : E →L[𝕜] F →L[𝕜] G) : ‖B.lpPairing μ p q‖ ≤ ‖B‖ := by
  -- Proof helped by Claude
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg B) fun f => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun g => ?_
  have h : B.lpPairing μ p q f g = L1.integral (B.holderL μ p q 1 f g) := by
    simp [ContinuousLinearMap.lpPairing, L1.integral_eq' 𝕜]
  rw [h]
  exact (L1.norm_integral_le _).trans (B.norm_holder_apply_apply_le f g)


-- # Now we'd like to show that `Isometry (B.lpPairing μ q p)` if `Isometry B` (when `SemiFinite μ`).

lemma norm_lpPairing_inclusionInDoubleDual_flip_apply_one_top_le (g : Lp (StrongDual 𝕜 F) p μ) :
    ‖(NormedSpace.inclusionInDoubleDual 𝕜 F).flip.lpPairing μ p q g‖ ≤ ‖g‖ := by
  -- Proof helped by Claude
  calc
    ‖(NormedSpace.inclusionInDoubleDual 𝕜 F).flip.lpPairing μ p q g‖
      ≤ ‖(NormedSpace.inclusionInDoubleDual 𝕜 F).flip.lpPairing μ p q‖ * ‖g‖
        := le_opNorm _ g
    _ ≤ ‖(NormedSpace.inclusionInDoubleDual 𝕜 F).flip‖ * ‖g‖ := by
      gcongr; exact norm_lpPairing_le _
    _ ≤ 1 * ‖g‖ := by gcongr; rw [opNorm_flip]; exact NormedSpace.inclusionInDoubleDual_norm_le 𝕜 F
    _ = ‖g‖ := one_mul _


lemma exists_norm_le_one_mul_norm_le_re {t : ℝ} (φ : StrongDual 𝕜 F) (ht : t < 1)  :
    ∃ v : F, ‖v‖ < 1 ∧ t * ‖φ‖ ≤ RCLike.re (φ v) := by
    -- Proof helped by Claude
    have : ∃ v : F, ‖v‖ < 1 ∧ t * ‖φ‖ ≤ ‖φ v‖  := by
      by_cases h : t * ‖φ‖ < ‖φ‖
      · obtain ⟨v, hv1, hv2⟩ := φ.exists_lt_apply_of_lt_opNorm h
        exact ⟨v, hv1, hv2.le⟩
      · have hφ : ‖φ‖ = 0 := by
          by_contra hne
          have hpos : 0 < ‖φ‖ := (norm_nonneg φ).lt_of_ne (Ne.symm hne)
          have : t * ‖φ‖ < ‖φ‖ := by grw [mul_lt_mul_of_pos_right ht hpos]; simp
          exact h this
        exact ⟨0, by simp, by simp [hφ]⟩
    obtain ⟨v, hv1, hv2⟩ := this
    by_cases h0 : ‖φ v‖ = 0
    . refine ⟨v, hv1, ?_⟩
      grw [hv2, h0]; rw [norm_eq_zero] at h0; simp [h0]
    set c : 𝕜 := conj (φ v) / ‖φ v‖ with hc
    have hc1 : ‖c‖ = 1 := by
      rw [hc, norm_div, RCLike.norm_conj, RCLike.norm_ofReal, abs_norm, div_self h0]
    have hφc : φ (c • v) = ‖φ v‖ := by
      rw [map_smul, smul_eq_mul, hc, div_mul_eq_mul_div, RCLike.conj_mul, ← RCLike.ofReal_pow,
        ← RCLike.ofReal_div, pow_two, mul_div_cancel_right₀ _ h0]
    refine ⟨c • v, ?_, ?_⟩
    · rw [norm_smul, hc1, one_mul]; exact hv1
    · rw [hφc, RCLike.ofReal_re]; exact hv2

lemma mul_norm_le_norm_lpPairing_inclusionInDoubleDual_flip_apply_simpleFunc
    (hp : p ≠ ∞) (s : Lp.simpleFunc (StrongDual 𝕜 F) p μ) {t : ℝ} (ht : t < 1) :
    t * ‖s‖ ≤ ‖(NormedSpace.inclusionInDoubleDual 𝕜 F).flip.lpPairing μ p q s‖ := by
    -- Proof helped by Claude
    set J := (NormedSpace.inclusionInDoubleDual 𝕜 F).flip.lpPairing μ p q
    -- # Excluding trivial cases
    have hp0 : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
    have hq0 : q ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
    by_cases hle : t ≤ 0
    · exact (mul_nonpos_of_nonpos_of_nonneg hle (norm_nonneg _)).trans (norm_nonneg _)
    by_cases heq : 0 = ‖s‖
    · rw [← heq, mul_zero]; exact norm_nonneg _
    have hs0 : 0 < ‖s‖ := (norm_nonneg s).lt_of_ne heq
    -- # Nontrivial case: `0 < ‖s‖` and `0 < t`:
    -- pick up a `SimpleFunc` representative from equivalence class `s` and prove properties of s'
    set s' := Lp.simpleFunc.toSimpleFunc s
    have hs'_ae : s' =ᵐ[μ] s := Lp.simpleFunc.toSimpleFunc_eq_toFun s
    have hs_memLp : MemLp s' p μ := Lp.simpleFunc.memLp s
    /- make `exists_norm_le_one_mul_norm_le_re` into a function `v : StrongDual 𝕜 F → F`, which
    picks corresponding `v φ` for `φ : StrongDual 𝕜 F` s.t. `‖v φ‖ < 1` and `t * ‖φ‖ ≤ RCLike.re (φ (v φ)).`-/
    -- suggested by Claude
    choose v hv1 hv2 using fun φ => exists_norm_le_one_mul_norm_le_re (𝕜 := 𝕜) (F := F) φ ht
    -- Define `g` to be `((‖s'‖ ^ (p.toReal - 1) : ℝ) : 𝕜) • v s'`, use `s'.map` to preserve its `SimpleFunc` structure
    set g : SimpleFunc α F := s'.map fun φ => ((‖φ‖ ^ (p.toReal - 1) : ℝ) : 𝕜) • v φ
    -- properties of `g`:
    have hg_memLq : MemLp g q μ := by
      by_cases hq : q = ∞
      · rw [hq]; exact g.memLp_top μ
      have hp1 : p ≠ 1 := (HolderConjugate.ne_top_iff_ne_one q p).1 hq
      have hr : 1 < p.toReal := by
        rw [← ENNReal.toReal_one, ENNReal.toReal_lt_toReal one_ne_top hp]
        exact lt_of_le_of_ne Fact.out hp1.symm
      apply (SimpleFunc.memLp_iff_finMeasSupp hq0 hq).2
      refine ((SimpleFunc.memLp_iff_finMeasSupp hp0 hp).1 hs_memLp).map ?_
      rw [norm_zero, Real.zero_rpow (by linarith)]; simp
    -- # Pointwise upperbound for `g`:
    have hg_le : ∀ x, ‖g x‖ ≤ ‖s' x‖ ^ (p.toReal - 1) := by
      intro x
      rw [SimpleFunc.map_apply, norm_smul, RCLike.norm_ofReal,
        abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      refine mul_le_of_le_one_right ?_ ?_
      . exact Real.rpow_nonneg (norm_nonneg _) _
      . exact (hv1 _).le
    -- # Pointwise lowerbound for `g`:
    have hg_re : ∀ x, t * ‖s' x‖ ^ p.toReal ≤ RCLike.re (s' x (g x)) := by
      intro x
      rw [SimpleFunc.map_apply, map_smul, smul_eq_mul, RCLike.re_ofReal_mul]
      calc
        t * ‖s' x‖ ^ p.toReal = t * (‖s' x‖ * ‖s' x‖ ^ (p.toReal - 1)) := by
          rw [← Real.rpow_one_add' ?_ ?_, add_sub_cancel]
          . exact norm_nonneg _
          . rw [add_sub_cancel]; exact (ENNReal.toReal_pos hp0 hp).ne'
        _  = (t * ‖s' x‖) * ‖s' x‖ ^ (p.toReal - 1) := by ring
        _ = ‖s' x‖ ^ (p.toReal - 1) * (t * ‖s' x‖) := by ring
        _ ≤ ‖s' x‖ ^ (p.toReal - 1) * RCLike.re (s' x (v (s' x))) := by gcongr; exact hv2 _
    -- # upper bound for norm of `g`:
    have hg_norm : ‖hg_memLq.toLp g‖ ≤ ‖s‖ ^ (p.toReal - 1) := by
      rw [Lp.norm_toLp, Lp.simpleFunc.norm_toSimpleFunc s]
      by_cases hq : q = ∞
      · -- case p = 1, q = ∞ : ‖g‖_∞ ≤ ‖s‖ ^ 0 = 1
        have hp1 : p = 1 := (HolderConjugate.eq_top_iff_eq_one q p).1 hq
        have hp10 : p.toReal - 1 = 0 := by simp [hp1]
        subst hq
        rw [hp10, Real.rpow_zero, eLpNorm_exponent_top (g.aestronglyMeasurable)]
        apply ENNReal.toReal_le_of_le_ofReal zero_le_one
        apply eLpNormEssSup_le_of_ae_bound
        apply Filter.Eventually.of_forall
        intro x; grw [hg_le x]; simp [hp10]
      · -- 1 < p < ∞ : ‖g‖_q ≤ ‖ ‖s'‖^(r-1) ‖_q = ‖s'‖_p ^ (r-1)
        have hp1 : p ≠ 1 := (HolderConjugate.ne_top_iff_ne_one q p).1 hq
        have h1p : 1 < p.toReal := by
          rw [← ENNReal.toReal_one, ENNReal.toReal_lt_toReal one_ne_top hp]
          exact lt_of_le_of_ne Fact.out hp1.symm
        have hsub_one_mul_conj : (p.toReal - 1) * q.toReal = p.toReal :=
          (HolderConjugate.toReal h1p).sub_one_mul_conj
        have hq_mul_sub_one : q * ENNReal.ofReal (p.toReal - 1) = p := by
          rw [← ENNReal.ofReal_toReal hq, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg, mul_comm,
            hsub_one_mul_conj, ENNReal.ofReal_toReal hp]
        have hmono : eLpNorm g q μ ≤ eLpNorm (fun x => ‖s' x‖ ^ (p.toReal - 1)) q μ := by
          apply eLpNorm_mono_real g.aestronglyMeasurable
          intro x
          exact hg_le x
        rw [eLpNorm_norm_rpow _ s'.aestronglyMeasurable (by linarith), hq_mul_sub_one] at hmono
        calc (eLpNorm g q μ).toReal
            ≤ (eLpNorm s' p μ ^ (p.toReal - 1)).toReal :=
              ENNReal.toReal_mono (ENNReal.rpow_ne_top_of_nonneg (by linarith)
                hs_memLp.eLpNorm_ne_top) hmono
          _ = (eLpNorm s' p μ).toReal ^ (p.toReal - 1) := (ENNReal.toReal_rpow _ _).symm
    -- # Expansion for `‖s‖ ^ p.toReal`:
    have hs_norm : ‖s‖ ^ p.toReal = ∫ x, ‖s' x‖ ^ p.toReal ∂μ := by
      have hp0 : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
      rw [Lp.simpleFunc.norm_toSimpleFunc s, hs_memLp.eLpNorm_eq_integral_rpow_norm hp0 hp,
       ENNReal.toReal_ofReal (by positivity),Real.rpow_inv_rpow ?_ ?_]
      . apply integral_nonneg; intro x; positivity
      . rw [toReal_ne_zero]; constructor <;> assumption
    -- # Expansion for `J s (hg_memLp.toLp g)`:
    have hint : Integrable (fun x => s' x (g x)) μ := by
      apply memLp_one_iff_integrable.1
      exact (NormedSpace.inclusionInDoubleDual 𝕜 F).flip.memLp_of_bilin 1 hs_memLp hg_memLq
    have hJ : J s (hg_memLq.toLp g) = ∫ x, s' x (g x) ∂μ := by
      rw [lpPairing_eq_integral]
      apply integral_congr_ae
      filter_upwards [hs'_ae, hg_memLq.coeFn_toLp] with x hs'x hgx
      rw [flip_apply, NormedSpace.dual_def, hs'x, hgx]
    -- # assemble everything together:
    have key : t * ‖s‖ ^ p.toReal ≤ ‖J s‖ * ‖s‖ ^ (p.toReal - 1) :=
      calc
        t * ‖s‖ ^ p.toReal = ∫ x, t * ‖s' x‖ ^ p.toReal ∂μ := by
            rw [hs_norm, integral_const_mul]
        _ ≤ ∫ x, RCLike.re (s' x (g x)) ∂μ := by
            refine integral_mono ?_ ?_ hg_re
            . exact (hs_memLp.integrable_norm_rpow hp0 hp).const_mul t
            . exact hint.re
        _ = RCLike.re (J s (hg_memLq.toLp g)) := by rw [hJ, integral_re hint]
        _ ≤ ‖J s (hg_memLq.toLp g)‖ := RCLike.re_le_norm _
        _ ≤ ‖J s‖ * ‖hg_memLq.toLp g‖ := (J s).le_opNorm _
        _ ≤ ‖J s‖ * ‖s‖ ^ (p.toReal - 1) := by gcongr
    calc
      t * ‖s‖ = (t * ‖s‖ ^ p.toReal) * ‖s‖ ^ (1 - p.toReal) := by
       rw [mul_assoc, ← Real.rpow_add hs0]; simp
      _ ≤ (‖J s‖ * ‖s‖ ^ (p.toReal - 1)) * ‖s‖ ^ (1 - p.toReal) := by gcongr
      _ = ‖J s‖ := by rw [mul_assoc, ← Real.rpow_add hs0]; simp


lemma norm_le_norm_lpPairing_inclusionInDoubleDual_flip_apply_simpleFunc (hp : p ≠ ∞)
    (s : Lp.simpleFunc (StrongDual 𝕜 F) p μ) :
    ‖s‖ ≤ ‖(NormedSpace.inclusionInDoubleDual 𝕜 F).flip.lpPairing μ p q s‖ := by
  -- Proof helped by Claude
  by_contra h
  obtain ⟨c, hc1, hc2⟩ := exists_between (not_le.1 h)
  have hpos : 0 < ‖s‖ := ((norm_nonneg _).trans_lt hc1).trans hc2
  have := mul_norm_le_norm_lpPairing_inclusionInDoubleDual_flip_apply_simpleFunc (q := q) hp s
    ((div_lt_one hpos).2 hc2)
  rw [div_mul_cancel₀ c hpos.ne'] at this
  linarith

theorem norm_lpPairing_inclusionInDoubleDual_flip_apply_ne_top (hp : p ≠ ∞) (g : Lp (StrongDual 𝕜 F) p μ) :
    ‖(NormedSpace.inclusionInDoubleDual 𝕜 F).flip.lpPairing μ p q g‖ = ‖g‖ := by
  -- Proof helped by Claude
  set J := (NormedSpace.inclusionInDoubleDual 𝕜 F).flip.lpPairing μ p q
  refine le_antisymm (norm_lpPairing_inclusionInDoubleDual_flip_apply_one_top_le g) ?_
  refine (Lp.simpleFunc.denseRange hp).induction_on g ?_ ?_
  . exact isClosed_le continuous_norm (continuous_norm.comp J.continuous)
  . exact norm_le_norm_lpPairing_inclusionInDoubleDual_flip_apply_simpleFunc hp

theorem isometry_lpPairing_inclusionInDoubleDual_flip_of_ne_top (hp : p ≠ ∞) :
    Isometry ((NormedSpace.inclusionInDoubleDual 𝕜 F).flip.lpPairing μ p q) :=
  AddMonoidHomClass.isometry_of_norm _ (norm_lpPairing_inclusionInDoubleDual_flip_apply_ne_top hp)

-- # Now we'd like to show the case for `1 ≤ p ≤ ∞` with `SemiFinite μ`:

lemma setAverage_norm_le_norm_lpPairing_inclusionInDoubleDual_flip_apply_top
  (g : Lp (StrongDual 𝕜 F) ∞ μ) (s : Set α) (hsm : MeasurableSet s) (hs : 0 < μ s ∧ μ s < ∞) :
    (μ s).toReal⁻¹ * ∫ x in s, ‖g x‖ ∂μ  ≤ ‖(NormedSpace.inclusionInDoubleDual 𝕜 F).flip.lpPairing μ ∞ 1 g‖ := by
    set J := (NormedSpace.inclusionInDoubleDual 𝕜 F).flip.lpPairing μ ∞ 1
    set J' := (NormedSpace.inclusionInDoubleDual 𝕜 F).flip.lpPairing μ 1 ∞
    have : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.2 hs.2.ne
    have hg1 : MemLp (s.indicator g) 1 μ :=
      (memLp_indicator_iff_restrict hsm.nullMeasurableSet).2
        (((Lp.memLp g).restrict s).mono_exponent le_top)
    let u : Lp (StrongDual 𝕜 F) 1 μ := hg1.toLp _
    have hJu : ‖J' u‖ = ∫ x in s, ‖g x‖ ∂μ := by
      rw [norm_lpPairing_inclusionInDoubleDual_flip_apply_ne_top (by simp) u,
        L1.norm_eq_integral_norm u, ← integral_indicator hsm]
      apply integral_congr_ae
      filter_upwards [hg1.coeFn_toLp] with x hx
      rw [hx, norm_indicator_eq_indicator_norm]
    have hf1 (f : Lp F ∞ μ) : MemLp (s.indicator f) 1 μ :=
      (memLp_indicator_iff_restrict hsm.nullMeasurableSet).2
        (((Lp.memLp f).restrict s).mono_exponent le_top)
    have key (f : Lp F ∞ μ) : J' u f = J g ((hf1 f).toLp _) := by
      simp only [J, J', lpPairing_eq_integral]
      apply integral_congr_ae
      filter_upwards [hg1.coeFn_toLp, (hf1 f).coeFn_toLp] with x hx1 hx2
      rw [hx1, hx2]
      by_cases hx : x ∈ s <;> simp [hx]
    have hJ'uf (f : Lp F ∞ μ) : ‖J' u f‖ ≤ (μ s).toReal * ‖J g‖ * ‖f‖ := by
      rw [key]
      -- `hfb` might be a useful lemma to put it outside
      have hfb : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖f‖ := by
        have hne : eLpNormEssSup f μ ≠ ∞ := by
          simpa [eLpNorm_exponent_top (Lp.aestronglyMeasurable f)] using Lp.eLpNorm_ne_top f
        filter_upwards [ae_le_eLpNormEssSup (f := f)] with x hx
        rw [Lp.norm_def, eLpNorm_exponent_top (Lp.aestronglyMeasurable f), ← toReal_enorm]
        exact ENNReal.toReal_mono hne hx
      have hw : ‖(hf1 f).toLp _‖ ≤ (μ s).toReal * ‖f‖ := by
        rw [L1.norm_eq_integral_norm]
        calc
          ∫ x, ‖(hf1 f).toLp _ x‖ ∂μ = ∫ x in s, ‖f x‖ ∂μ := by
              rw [← integral_indicator hsm]
              apply integral_congr_ae
              filter_upwards [(hf1 f).coeFn_toLp] with x hx
              rw [hx, norm_indicator_eq_indicator_norm]
          _ ≤ ∫ x in s, ‖f‖ ∂μ := by
              refine integral_mono_ae ?_ ?_ ?_
              . exact ((Lp.memLp f).norm.restrict s).integrable le_top
              . exact integrable_const _
              . exact ae_restrict_of_ae hfb
          _ = (μ s).toReal * ‖f‖ := by simp [measureReal_def]
      calc ‖J g ((hf1 f).toLp _)‖ ≤ ‖J g‖ * ‖(hf1 f).toLp _‖ := le_opNorm _ _
        _ ≤ ‖J g‖ * ((μ s).toReal * ‖f‖) := by gcongr
        _ = (μ s).toReal * ‖J g‖ * ‖f‖ := by ring
    have hJ'u : ‖J' u‖ ≤ (μ s).toReal * ‖J g‖ := opNorm_le_bound _ (by positivity) hJ'uf
    rw [← hJu]; grw [hJ'u]
    rw [inv_mul_cancel_left₀ ((ENNReal.toReal_pos hs.1.ne' hs.2.ne).ne') ‖J g‖]


lemma norm_sub_le_norm_lpPairing_inclusionInDoubleDual_flip_apply_top
  [SemiFinite μ] (g : Lp (StrongDual 𝕜 F) ∞ μ) {ε : ℝ} (hε : 0 < ε) :
    ‖g‖ - ε ≤ ‖(NormedSpace.inclusionInDoubleDual 𝕜 F).flip.lpPairing μ ∞ 1 g‖ := by
  by_cases hnorm : ‖g‖ ≤ ε
  . grw [hnorm]; simp
  . let A := {x : α | ‖g‖ - ε < ‖g x‖}
    have hA : 0 < μ A := by
      apply pos_iff_ne_zero.2
      intro h0
      have hae : ∀ᵐ x ∂μ, ‖g x‖ ≤ ‖g‖ - ε := by rw [ae_iff]; simpa
      have key : eLpNorm g ∞ μ ≤ ENNReal.ofReal (‖g‖ - ε) := by
        rw [eLpNorm_exponent_top (Lp.aestronglyMeasurable g)]
        exact eLpNormEssSup_le_of_ae_bound hae
      have : ‖g‖ ≤ ‖g‖ - ε := ENNReal.toReal_le_of_le_ofReal (by linarith) key
      linarith
    have hAm : MeasurableSet A :=
      measurableSet_lt measurable_const (Lp.stronglyMeasurable g).norm.measurable
    obtain ⟨s, hsm, hsA, hs0, hstop⟩ := SemiFinite.iff.1 ‹SemiFinite μ› A hAm hA
    have hgs : ∀ x ∈ s, ‖g‖ - ε < ‖g x‖ := fun _ hx => hsA hx
    have hint : IntegrableOn (fun x => ‖g x‖) s μ := by
      have : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.2 hstop.ne
      exact ((Lp.memLp g).norm.restrict s).integrable le_top
    calc
      ‖g‖ - ε ≤ (μ s).toReal⁻¹ * ∫ x in s, ‖g x‖ ∂μ := by
        rw [le_inv_mul_iff₀ (ENNReal.toReal_pos hs0.ne' hstop.ne), mul_comm]
        exact setIntegral_ge_of_const_le_real hsm hstop.ne (fun x hx => (hgs x hx).le) hint
      _ ≤  ‖(NormedSpace.inclusionInDoubleDual 𝕜 F).flip.lpPairing μ ∞ 1 g‖ :=
        setAverage_norm_le_norm_lpPairing_inclusionInDoubleDual_flip_apply_top g s hsm ⟨hs0, hstop⟩

theorem norm_lpPairing_inclusionInDoubleDual_flip_apply [SemiFinite μ] (g : Lp (StrongDual 𝕜 F) p μ) :
    ‖(NormedSpace.inclusionInDoubleDual 𝕜 F).flip.lpPairing μ p q g‖ = ‖g‖ := by
  set J := (NormedSpace.inclusionInDoubleDual 𝕜 F).flip.lpPairing μ p q
  by_cases hp : p = ∞
  . subst hp
    have hq : q = 1 := (HolderConjugate.eq_top_iff_eq_one ∞ q).1 rfl
    subst hq
    refine le_antisymm (norm_lpPairing_inclusionInDoubleDual_flip_apply_one_top_le g) ?_
    exact le_of_forall_sub_le fun _ hε => norm_sub_le_norm_lpPairing_inclusionInDoubleDual_flip_apply_top g hε
  . exact norm_lpPairing_inclusionInDoubleDual_flip_apply_ne_top hp g


theorem isometry_lpPairing_inclusionInDoubleDual_flip [SemiFinite μ] :
    Isometry ((NormedSpace.inclusionInDoubleDual 𝕜 F).flip.lpPairing μ p q) :=
  AddMonoidHomClass.isometry_of_norm _ (norm_lpPairing_inclusionInDoubleDual_flip_apply)


theorem lpPairing_eq_compLpL :
  B.lpPairing μ q p = ((NormedSpace.inclusionInDoubleDual 𝕜 F).flip.lpPairing μ q p).comp (B.compLpL q μ) := by
  -- Proof helped by Claude
  ext f g
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.lpPairing_eq_integral,
    ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [ContinuousLinearMap.coeFn_compLpL B f] with x hx
  simp [hx]

theorem lpPairing_isometry_of_isometry_of_ne_top (hq : q ≠ ∞) (hB : Isometry B) :
    Isometry (B.lpPairing μ q p) := by
  rw [lpPairing_eq_compLpL]
  exact (isometry_lpPairing_inclusionInDoubleDual_flip_of_ne_top hq).comp
    (ContinuousLinearMap.isometry_compLpL hB)

theorem lpPairing_isometry_of_isometry [SemiFinite μ] (hB : Isometry B):
  Isometry (B.lpPairing μ q p) := by
  rw [lpPairing_eq_compLpL]
  exact isometry_lpPairing_inclusionInDoubleDual_flip.comp (ContinuousLinearMap.isometry_compLpL hB)

-- # Here are two corollary for specific case where `B` is standard multipliction:

theorem norm_mul_lpPairing_apply_of_ne_top (hp : p ≠ ∞) (f : Lp 𝕜 p μ) :
    ‖(ContinuousLinearMap.mul 𝕜 𝕜).lpPairing μ p q f‖ = ‖f‖ :=
  (AddMonoidHomClass.isometry_iff_norm _).1
    (lpPairing_isometry_of_isometry_of_ne_top (mul 𝕜 𝕜) hp
      (AddMonoidHomClass.isometry_of_norm _ (opNorm_mul_apply 𝕜 𝕜))) f

theorem norm_mul_lpPairing_apply [SemiFinite μ] (f : Lp 𝕜 p μ) :
    ‖(ContinuousLinearMap.mul 𝕜 𝕜).lpPairing μ p q f‖ = ‖f‖ :=
  (AddMonoidHomClass.isometry_iff_norm _).1
    (lpPairing_isometry_of_isometry (mul 𝕜 𝕜)
      (AddMonoidHomClass.isometry_of_norm _ (opNorm_mul_apply 𝕜 𝕜))) f



/- ## Surjectivity of L^p pairing : specifically for standard multipliction -/

lemma mul_lpPairing_surjective_of_finite [IsFiniteMeasure μ] (hq : q ≠ ∞) :
    Function.Surjective ((ContinuousLinearMap.mul 𝕜 𝕜).lpPairing μ p q) := by sorry

theorem mul_lpPairing_surjective_of_sigmaFinite [SigmaFinite μ] (hq : q ≠ ∞) :
    Function.Surjective ((ContinuousLinearMap.mul 𝕜 𝕜).lpPairing μ p q) := by sorry

theorem mul_lpPairing_surjective_of_ne_top (hp : p ≠ ∞) (hq : q ≠ ∞) :
    Function.Surjective ((ContinuousLinearMap.mul 𝕜 𝕜).lpPairing μ p q) := by sorry



end ContinuousLinearMap



namespace MeasureTheory

namespace Lp

#check LinearIsometry

variable (𝕜 μ p q) in
/-- `Lᵖ-duality` for `1 < p < ∞`: `Lᵖ(μ; 𝕜) ≃ₗᵢ (L^q(μ; 𝕜))*` for any measure. -/
def dualEquiv (hp : p ≠ ∞) (hq : q ≠ ∞) : Lp 𝕜 p μ ≃ₗᵢ[𝕜] StrongDual 𝕜 (Lp 𝕜 q μ) :=
  LinearIsometryEquiv.ofSurjective
    ⟨((ContinuousLinearMap.mul 𝕜 𝕜).lpPairing μ p q).toLinearMap,
      ContinuousLinearMap.norm_mul_lpPairing_apply_of_ne_top hp⟩
    (ContinuousLinearMap.mul_lpPairing_surjective_of_ne_top hp hq)

variable (𝕜 μ p q) in
/-- `Lᵖ-duality` for `1 < p ≤ ∞`: `Lᵖ(μ; 𝕜) ≃ₗᵢ (L^q(μ; 𝕜))*` for `μ`: σ-finite. -/
def dualEquivOfSigmaFinite [SigmaFinite μ] (hq : q ≠ ∞) : Lp 𝕜 p μ ≃ₗᵢ[𝕜] StrongDual 𝕜 (Lp 𝕜 q μ) :=
  LinearIsometryEquiv.ofSurjective
    ⟨((ContinuousLinearMap.mul 𝕜 𝕜).lpPairing μ p q).toLinearMap,
      ContinuousLinearMap.norm_mul_lpPairing_apply⟩
    (ContinuousLinearMap.mul_lpPairing_surjective_of_sigmaFinite hq)


end Lp

end MeasureTheory

end
