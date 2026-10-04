import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym

open MeasureTheory Filter Set
open scoped ENNReal Topology

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [NormedSpace 𝕜 G]
    [NormedSpace ℝ G] [SMulCommClass ℝ 𝕜 G] [CompleteSpace G]

/-! # Lp duality

We'd like to show: `(L^q)^* ≅ L^p` for `1/p + 1/q = 1`, where `1 ≤ q < ∞`.
-/

/-- Hölder's inequality for the integral pairing: for Hölder conjugate `p, q`, the bilinear map
`(f, g) ↦ ∫ B (f x) (g x) ∂μ` on `Lp E p μ × Lp F q μ` has norm at most `‖B‖`. -/
theorem ContinuousLinearMap.norm_lpPairing_le
    (B : E →L[𝕜] F →L[𝕜] G) : ‖B.lpPairing μ p q‖ ≤ ‖B‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg B) fun f => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun g => ?_
  have h : B.lpPairing μ p q f g = L1.integral (B.holderL μ p q 1 f g) := by
    simp [ContinuousLinearMap.lpPairing, L1.integral_eq' 𝕜]
  rw [h]
  exact (L1.norm_integral_le _).trans (B.norm_holder_apply_apply_le (r := 1) f g)

/-- For `U ∈ Lp ℝ p μ`, the functional `f ↦ ∫ U f ∂μ` on `Lp ℝ q μ` has norm at most `‖U‖`. -/
theorem MeasureTheory.Lp.norm_lpPairing_mul_apply_le (U : Lp ℝ p μ) :
    ‖(ContinuousLinearMap.mul ℝ ℝ).lpPairing μ p q U‖ ≤ ‖U‖ :=
  ((ContinuousLinearMap.mul ℝ ℝ).lpPairing μ p q).le_of_opNorm_le
    ((ContinuousLinearMap.norm_lpPairing_le _).trans (ContinuousLinearMap.opNorm_mul_le ℝ ℝ)) U
    |>.trans_eq (one_mul _)

/-- Uniqueness of the representing function: for σ-finite `μ` and `1 ≤ p`, if
`∫ U f ∂μ = ∫ V f ∂μ` for all `f ∈ Lp ℝ q μ`, then `U = V` in `Lp ℝ p μ`. -/
theorem MeasureTheory.Lp.eq_of_forall_integral_mul_eq
  {p q : ℝ≥0∞} [Fact (1 ≤ p)] [SigmaFinite μ] {U V : Lp ℝ p μ}
  (h : ∀ f : Lp ℝ q μ, ∫ x, U x * f x ∂μ = ∫ x, V x * f x ∂μ) : U = V := by
  apply Lp.ext
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
    (fun s _ hs => integrableOn_Lp_of_measure_ne_top U (Fact.out : 1 ≤ p) hs.ne)
    (fun s _ hs => integrableOn_Lp_of_measure_ne_top V (Fact.out : 1 ≤ p) hs.ne) ?_
  intro s hs hμs
  have h_integral (W : Lp ℝ p μ) :
      ∫ x, W x * indicatorConstLp q hs hμs.ne (1 : ℝ) x ∂μ = ∫ x in s, W x ∂μ := by
    rw [← integral_indicator hs]
    apply integral_congr_ae
    filter_upwards [indicatorConstLp_coeFn (p := q) (hs := hs) (hμs := hμs.ne)
      (c := (1 : ℝ))] with x hx
    rw [hx, ← Set.indicator_mul_right]
    simp
  simpa only [h_integral] using h (indicatorConstLp q hs hμs.ne (1 : ℝ))

/-- The real Lp integral pairing is injective for sigma-finite measures. -/
theorem MeasureTheory.Lp.lpPairing_mul_injective [SigmaFinite μ] :
    Function.Injective ((ContinuousLinearMap.mul ℝ ℝ).lpPairing μ p q) := by
  intro U V h
  apply MeasureTheory.Lp.eq_of_forall_integral_mul_eq (q := q)
  intro f
  simpa [ContinuousLinearMap.lpPairing_eq_integral] using DFunLike.congr_fun h f

section

variable {q : ℝ≥0∞} [Fact (1 ≤ q)] [IsFiniteMeasure μ]

private theorem tendsto_toLp_of_bounded {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] (hq : q ≠ ∞) {f : ι → α → ℝ} {g : α → ℝ}
    (hf : ∀ i, MemLp (f i) q μ) (hg : MemLp g q μ) {C : ℝ}
    (hb : ∀ i, ∀ᵐ x ∂μ, ‖f i x‖ ≤ C)
    (hbg : ∀ᵐ x ∂μ, ‖g x‖ ≤ C)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun i => f i x) l (𝓝 (g x))) :
    Tendsto (fun i => (hf i).toLp (f i)) l (𝓝 (hg.toLp g)) := by
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'']
  have hq0 : q ≠ 0 := (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ q)).ne'
  have hqr : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
  have hi : Tendsto (fun i => ∫⁻ x, ‖f i x - g x‖ₑ ^ q.toReal ∂μ) l (𝓝 0) := by
    have h := tendsto_lintegral_filter_of_dominated_convergence'
      (μ := μ) (l := l) (F := fun i x => ‖f i x - g x‖ₑ ^ q.toReal) (f := fun _ => 0)
      (fun _ => ENNReal.ofReal (2 * C) ^ q.toReal)
    apply (by simpa using h)
    · exact .of_forall fun i => ((hf i).1.sub hg.1).enorm.pow_const _
    · refine .of_forall fun i => ?_
      filter_upwards [hb i, hbg] with x hx hy
      apply ENNReal.rpow_le_rpow _ ENNReal.toReal_nonneg
      rw [← ofReal_norm]
      simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat] using
        ENNReal.ofReal_le_ofReal ((norm_sub_le (f i x) (g x)).trans
          (show ‖f i x‖ + ‖g x‖ ≤ 2 * C by linarith))
    · exact (by finiteness)
    · filter_upwards [ht] with x hx
      have h := (ENNReal.continuous_rpow_const (y := q.toReal)).tendsto
        (‖g x - g x‖ₑ) |>.comp ((hx.sub_const (g x)).enorm)
      simpa [Function.comp_def, ENNReal.zero_rpow_of_pos hqr] using h
  simp only [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hq]
  have h := (ENNReal.continuous_rpow_const (y := 1 / q.toReal)).tendsto (0 : ℝ≥0∞) |>.comp hi
  simpa [Function.comp_def, ENNReal.zero_rpow_of_pos (inv_pos.mpr hqr)] using h

/-- A functional on Lq defines an absolutely continuous signed measure on indicators. -/
private theorem exists_signedMeasure_of_dual (hq : q ≠ ∞) (Λ : Lp ℝ q μ →L[ℝ] ℝ) :
    ∃ ν : SignedMeasure α, ν ≪ᵥ μ.toENNRealVectorMeasure ∧
      ∀ (s : Set α) (hs : MeasurableSet s),
        ν s = Λ (indicatorConstLp q hs (measure_ne_top μ s) (1 : ℝ)) := by
  classical
  let I (s : Set α) (hs : MeasurableSet s) : Lp ℝ q μ :=
    indicatorConstLp q hs (measure_ne_top μ s) (1 : ℝ)
  let ν : SignedMeasure α := {
    measureOf' := fun s => if hs : MeasurableSet s then Λ (I s hs) else 0
    empty' := by simp [I, indicatorConstLp, Set.indicator_empty]
    not_measurable' := fun _ hs => dif_neg hs
    m_iUnion' := by
      intro s hs hd
      simp only [dif_pos (hs _), dif_pos (MeasurableSet.iUnion hs)]
      have hsum (t : Finset ℕ) : ∑ i ∈ t, I (s i) (hs i) =
          I (⋃ i ∈ t, s i) (Finset.measurableSet_biUnion t fun i _ => hs i) := by
        apply Lp.ext
        have he : ⇑(∑ i ∈ t, I (s i) (hs i)) =ᵐ[μ]
            fun x => ∑ i ∈ t, I (s i) (hs i) x := by
          induction t using Finset.induction with
          | empty => simpa only [Finset.sum_empty, Pi.zero_def] using (Lp.coeFn_zero ℝ q μ)
          | @insert i t hi ih =>
            simpa only [Finset.sum_insert hi, Pi.add_def] using
              (Lp.coeFn_add (I (s i) (hs i)) (∑ j ∈ t, I (s j) (hs j))).trans
                (Filter.EventuallyEq.rfl.add ih)
        filter_upwards [he,
          ae_all_iff.mpr (fun i => indicatorConstLp_coeFn (p := q) (hs := hs i)
            (hμs := measure_ne_top μ _) (c := (1 : ℝ))),
          indicatorConstLp_coeFn (p := q)
            (hs := Finset.measurableSet_biUnion t fun i _ => hs i)
            (hμs := measure_ne_top μ _) (c := (1 : ℝ))] with x hx hi ht
        rw [hx, ht, Finset.indicator_biUnion_apply _ _ (fun i _ j _ hij => hd hij)]
        exact Finset.sum_congr rfl fun i _ => hi i
      have ht : Tendsto (fun t : Finset ℕ => I (⋃ i ∈ t, s i)
          (Finset.measurableSet_biUnion t fun i _ => hs i)) atTop
          (𝓝 (I (⋃ i, s i) (MeasurableSet.iUnion hs))) := by
        apply tendsto_toLp_of_bounded hq
          (fun t => memLp_indicator_const q
            (Finset.measurableSet_biUnion t fun i _ => hs i) (1 : ℝ) (Or.inr (measure_ne_top μ _)))
          (memLp_indicator_const q (MeasurableSet.iUnion hs) (1 : ℝ)
            (Or.inr (measure_ne_top μ _))) (C := 1)
        · intro t
          exact .of_forall fun x => by simp [Set.indicator_apply]; split_ifs <;> norm_num
        · exact .of_forall fun x => by simp [Set.indicator_apply]; split_ifs <;> norm_num
        · refine .of_forall fun x => ?_
          apply tendsto_const_nhds.congr'
          by_cases hx : x ∈ ⋃ i, s i
          · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
            filter_upwards [eventually_finset_mem_atTop i] with t ht
            have ht' : x ∈ ⋃ j ∈ t, s j := Set.mem_iUnion₂.mpr ⟨i, ht, hi⟩
            simp [Set.indicator_of_mem hx, Set.indicator_of_mem ht']
          · exact .of_forall fun t => by
              have ht : x ∉ ⋃ i ∈ t, s i := fun h => hx (by
                obtain ⟨i, _, hi⟩ := Set.mem_iUnion₂.mp h
                exact Set.mem_iUnion.mpr ⟨i, hi⟩)
              simp [Set.indicator_of_notMem hx, Set.indicator_of_notMem ht]
      simpa only [HasSum, SummationFilter.unconditional_filter, Function.comp_def, ← map_sum, hsum] using
        Λ.continuous.tendsto _ |>.comp ht }
  refine ⟨ν, ?_, fun s hs => dif_pos hs⟩
  intro s hzero
  by_cases hs : MeasurableSet s
  · have hμ : μ s = 0 := by simpa [Measure.toENNRealVectorMeasure_apply_measurable hs] using hzero
    have hI : I s hs = 0 := by
      apply Lp.ext
      filter_upwards [indicatorConstLp_coeFn (p := q) (hs := hs)
        (hμs := measure_ne_top μ _) (c := (1 : ℝ)), Lp.coeFn_zero ℝ q μ,
        (show ∀ᵐ x ∂μ, x ∉ s from by
          simpa only [ae_iff, not_not, Set.setOf_mem_eq] using hμ)] with x hx hz hn
      change I s hs x = (0 : Lp ℝ q μ) x
      rw [hz]
      simpa [I, Set.indicator_of_notMem hn] using hx
    simp [ν, hs, hI]
  · simp [ν, hs]

/-- Extend indicator representation to bounded strongly measurable test functions. -/
private theorem dual_eq_integral_of_bounded (hq : q ≠ ∞)
    (Λ : Lp ℝ q μ →L[ℝ] ℝ) {U : α → ℝ} (hU : Integrable U μ)
    (hind : ∀ (s : Set α) (hs : MeasurableSet s),
      Λ (indicatorConstLp q hs (measure_ne_top μ s) (1 : ℝ)) = ∫ x in s, U x ∂μ)
    {f : α → ℝ} (hf : StronglyMeasurable f) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
    Λ ((MemLp.of_bound hf.aestronglyMeasurable C hb).toLp f) = ∫ x, U x * f x ∂μ := by
  classical
  have hsimp (f : SimpleFunc α ℝ) :
      Λ ((f.memLp_of_isFiniteMeasure q μ).toLp f) = ∫ x, U x * f x ∂μ := by
    induction f using SimpleFunc.induction with
    | @const c s hs =>
      have he : ((SimpleFunc.piecewise s hs
          (SimpleFunc.const α c) (SimpleFunc.const α 0)).memLp_of_isFiniteMeasure q μ).toLp _ =
          c • indicatorConstLp q hs (measure_ne_top μ s) (1 : ℝ) := by
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp ((SimpleFunc.piecewise s hs
          (SimpleFunc.const α c) (SimpleFunc.const α 0)).memLp_of_isFiniteMeasure q μ),
          Lp.coeFn_smul c (indicatorConstLp q hs (measure_ne_top μ s) (1 : ℝ)),
          indicatorConstLp_coeFn (p := q) (hs := hs) (hμs := measure_ne_top μ s) (c := (1 : ℝ))] with x hx hy hz
        rw [hx, hy]
        simp [hz, SimpleFunc.piecewise, Set.indicator_apply]
      rw [he, map_smul, hind s hs]
      simp only [smul_eq_mul]
      rw [← integral_const_mul]
      rw [← integral_indicator hs]
      apply integral_congr_ae
      exact .of_forall fun x => by
        simp [SimpleFunc.piecewise, Set.indicator_apply]
        split_ifs <;> ring
    | @add f g _ ihf ihg =>
      have he : ((f + g).memLp_of_isFiniteMeasure q μ).toLp _ =
          (f.memLp_of_isFiniteMeasure q μ).toLp f + (g.memLp_of_isFiniteMeasure q μ).toLp g := rfl
      rw [he, map_add, ihf, ihg, ← integral_add]
      · congr 1
        ext x
        simp [mul_add]
      · exact hU.mul_of_top_left (f.memLp_of_isFiniteMeasure ∞ μ)
      · exact hU.mul_of_top_left (g.memLp_of_isFiniteMeasure ∞ μ)
  let fs := hf.approxBounded C
  have hfs n : MemLp (fs n) q μ := (fs n).memLp_of_isFiniteMeasure q μ
  have hfb n : ∀ᵐ x ∂μ, ‖fs n x‖ ≤ C := .of_forall fun x => hf.norm_approxBounded_le hC n x
  have hft := hf.tendsto_approxBounded_ae hb
  have hΛ := Λ.continuous.tendsto _ |>.comp
    (tendsto_toLp_of_bounded hq hfs (MemLp.of_bound hf.aestronglyMeasurable C hb) hfb hb hft)
  have hint : Tendsto (fun n => ∫ x, U x * fs n x ∂μ) atTop
      (𝓝 (∫ x, U x * f x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖U x‖ * C)
    · intro n
      exact hU.aestronglyMeasurable.mul (fs n).stronglyMeasurable.aestronglyMeasurable
    · exact hU.norm.mul_const C
    · intro n
      filter_upwards [hfb n] with x hx
      simpa only [norm_mul] using mul_le_mul_of_nonneg_left hx (norm_nonneg (U x))
    · filter_upwards [hft] with x hx using tendsto_const_nhds.mul hx
  apply tendsto_nhds_unique hΛ
  simpa only [Function.comp_def, hsimp] using hint

end

/-- The case of `MeasureTheory.Lp.exists_eq_integral_mul` for a finite measure; the first step of
its proof. -/
theorem MeasureTheory.Lp.exists_eq_integral_mul_of_isFiniteMeasure [IsFiniteMeasure μ]
    (hq : q ≠ ∞) (Λ : Lp ℝ q μ →L[ℝ] ℝ) :
    ∃ U : Lp ℝ p μ, ‖U‖ = ‖Λ‖ ∧ Λ = (ContinuousLinearMap.mul ℝ ℝ).lpPairing μ p q U := by
  obtain ⟨ν, hνac, hν⟩ := exists_signedMeasure_of_dual hq Λ
  let U := ν.rnDeriv μ
  have hU : Integrable U μ := ν.integrable_rnDeriv μ
  have hUm : StronglyMeasurable U := (ν.measurable_rnDeriv μ).stronglyMeasurable
  have hind (s : Set α) (hs : MeasurableSet s) :
      Λ (indicatorConstLp q hs (measure_ne_top μ s) (1 : ℝ)) = ∫ x in s, U x ∂μ := by
    rw [← hν s hs, ← ν.withDensityᵥ_rnDeriv_eq μ hνac]
    exact withDensityᵥ_apply hU hs
  have hnorm : eLpNorm U p μ ≤ ENNReal.ofReal ‖Λ‖ := by
    classical
    by_cases hp : p = ∞
    · subst p
      have hq1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one ∞ q).mp rfl
      subst q
      have hi (s : Set α) (hs : MeasurableSet s) : |∫ x in s, U x ∂μ| ≤ ‖Λ‖ * μ.real s := by
        rw [← hind s hs, ← Real.norm_eq_abs]
        simpa [norm_indicatorConstLp one_ne_zero ENNReal.one_ne_top] using
          Λ.le_opNorm (indicatorConstLp 1 hs (measure_ne_top μ s) (1 : ℝ))
      have hu : U ≤ᵐ[μ] fun _ => ‖Λ‖ :=
        ae_le_of_forall_setIntegral_le hU (integrable_const _) fun s hs _ => by
          simpa [mul_comm] using (le_abs_self _).trans (hi s hs)
      have hl : (fun _ => -‖Λ‖) ≤ᵐ[μ] U :=
        ae_le_of_forall_setIntegral_le (integrable_const _) hU fun s hs _ => by
          have h := (neg_le_abs _).trans (hi s hs)
          simp only [integral_const, MeasurableSet.univ, Measure.restrict_apply,
            Set.univ_inter, smul_eq_mul, Measure.real] at *
          linarith
      apply eLpNormEssSup_le_of_ae_bound
      filter_upwards [hu, hl] with x hx hy
      exact abs_le.mpr ⟨hy, hx⟩
    · have hp0 := ENNReal.HolderConjugate.ne_zero p q
      have hq0 := ENNReal.HolderConjugate.ne_zero q p
      have hp1 : 1 < p := (ENNReal.HolderConjugate.lt_top_iff_one_lt q p).mp hq.lt_top
      have hpr : 1 < p.toReal := by
        exact_mod_cast (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp).mpr hp1
      have hpq := ENNReal.HolderConjugate.toReal (q := q) hpr
      let s (n : ℕ) := {x | ‖U x‖ ≤ (n : ℝ)}
      have hs n : MeasurableSet (s n) := measurableSet_le hUm.measurable.norm measurable_const
      let W (n : ℕ) := (s n).indicator U
      have hWm n : StronglyMeasurable (W n) := hUm.indicator (hs n)
      have hWb n (x : α) : ‖W n x‖ ≤ (n : ℝ) := by
        by_cases hx : x ∈ s n
        · simpa only [W, Set.indicator_of_mem hx] using (show ‖U x‖ ≤ (n : ℝ) from hx)
        · simp [W, Set.indicator_of_notMem hx]
      have hW n : MemLp (W n) p μ := MemLp.of_bound (hWm n).aestronglyMeasurable n (.of_forall (hWb n))
      have hbound n : eLpNorm (W n) p μ ≤ ENNReal.ofReal ‖Λ‖ := by
        let ε (x : α) : ℝ := if 0 ≤ U x then 1 else -1
        have hε : Measurable ε :=
          measurable_const.ite (measurableSet_le measurable_const hUm.measurable) measurable_const
        have hεnorm x : ‖ε x‖ = 1 := by simp [ε]; split_ifs <;> norm_num
        have hεmul x : U x * ε x = ‖U x‖ := by
          by_cases hx : 0 ≤ U x <;> simp [ε, hx, Real.norm_eq_abs, abs_of_nonneg, abs_of_neg, lt_of_not_ge]
        let f := (s n).indicator (fun x => ‖U x‖ ^ (p.toReal - 1) * ε x)
        have hfm : StronglyMeasurable f :=
          ((hUm.measurable.norm.pow_const _).mul hε).stronglyMeasurable.indicator (hs n)
        have hfb x : ‖f x‖ ≤ (n : ℝ) ^ (p.toReal - 1) := by
          by_cases hx : x ∈ s n
          · simp only [f, Set.indicator_of_mem hx, norm_mul, hεnorm, mul_one,
              Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
            exact Real.rpow_le_rpow (norm_nonneg _) hx hpq.sub_one_pos.le
          · rw [show f x = 0 from Set.indicator_of_notMem hx _]
            simpa only [_root_.norm_zero] using Real.rpow_nonneg (Nat.cast_nonneg n) (p.toReal - 1)
        have hfp : MemLp f q μ := MemLp.of_bound hfm.aestronglyMeasurable _ (.of_forall hfb)
        have hprod x : U x * f x = ‖W n x‖ ^ p.toReal := by
          by_cases hx : x ∈ s n
          · simp only [f, W, Set.indicator_of_mem hx]
            rw [mul_left_comm, hεmul]
            by_cases hz : ‖U x‖ = 0
            · simp [hz, Real.zero_rpow (ne_of_gt (zero_lt_one.trans hpr))]
            · calc
                ‖U x‖ ^ (p.toReal - 1) * ‖U x‖ =
                    ‖U x‖ ^ (p.toReal - 1) * ‖U x‖ ^ (1 : ℝ) := by rw [Real.rpow_one]
                _ = ‖U x‖ ^ p.toReal := by
                  rw [← Real.rpow_add (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz))]
                  congr 1
                  ring
          · simp [f, W, Set.indicator_of_notMem hx, Real.zero_rpow (ne_of_gt (zero_lt_one.trans hpr))]
        have hpow x : ‖f x‖ ^ q.toReal = ‖W n x‖ ^ p.toReal := by
          by_cases hx : x ∈ s n
          · simp only [f, W, Set.indicator_of_mem hx, norm_mul, hεnorm, mul_one,
              Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
            rw [← Real.rpow_mul (norm_nonneg _), hpq.sub_one_mul_conj]
          · simp [f, W, Set.indicator_of_notMem hx,
              Real.zero_rpow hpq.pos.ne', Real.zero_rpow hpq.symm.pos.ne']
        let I := ∫ x, ‖W n x‖ ^ p.toReal ∂μ
        have hI : 0 ≤ I := integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
        have hnorm : ‖hfp.toLp f‖ = I ^ q.toReal⁻¹ := by
          rw [Lp.norm_toLp, hfp.eLpNorm_eq_integral_rpow_norm hq0 hq]
          simp only [hpow]
          exact ENNReal.toReal_ofReal (Real.rpow_nonneg hI _)
        have heq : Λ (hfp.toLp f) = I := by
          rw [dual_eq_integral_of_bounded hq Λ hU hind hfm (by positivity) (.of_forall hfb)]
          simp only [hprod, I]
        have hle : I ≤ ‖Λ‖ * I ^ q.toReal⁻¹ := by
          simpa [heq, hnorm, Real.norm_eq_abs, abs_of_nonneg hI] using Λ.le_opNorm (hfp.toLp f)
        have hroot : I ^ p.toReal⁻¹ ≤ ‖Λ‖ := by
          rcases hI.eq_or_lt with hz | hz
          · simp [← hz, Real.zero_rpow (inv_pos.mpr hpq.pos).ne']
          · apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hz q.toReal⁻¹)).mp
            rw [← Real.rpow_add hz, hpq.inv_add_inv_eq_one, Real.rpow_one]
            simpa [mul_comm] using hle
        rw [(hW n).eLpNorm_eq_integral_rpow_norm hp0 hp]
        exact ENNReal.ofReal_le_ofReal hroot
      apply Lp.eLpNorm_le_of_ae_tendsto (u := atTop) (.of_forall hbound)
        (fun n => (hWm n).aestronglyMeasurable)
      refine .of_forall fun x => tendsto_const_nhds.congr' ?_
      obtain ⟨N, hN⟩ := exists_nat_ge ‖U x‖
      filter_upwards [eventually_ge_atTop N] with n hn
      have hx : x ∈ s n := hN.trans (Nat.cast_le.mpr hn)
      simp [W, Set.indicator_of_mem hx]
  have hUp : MemLp U p μ := ⟨hUm.aestronglyMeasurable, hnorm.trans_lt ENNReal.ofReal_lt_top⟩
  let Up := hUp.toLp U
  have heq : Λ = (ContinuousLinearMap.mul ℝ ℝ).lpPairing μ p q Up := by
    apply ContinuousLinearMap.ext
    refine Lp.induction hq (fun f => Λ f = (ContinuousLinearMap.mul ℝ ℝ).lpPairing μ p q Up f) ?_ ?_ ?_
    · intro c s hs hμs
      change Λ (indicatorConstLp q hs hμs.ne c) = _
      have hfm : StronglyMeasurable (s.indicator (fun _ : α => c)) := stronglyMeasurable_const.indicator hs
      have hfb : ∀ᵐ x ∂μ, ‖s.indicator (fun _ : α => c) x‖ ≤ ‖c‖ :=
        .of_forall fun x => by
          by_cases hx : x ∈ s <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]
      have h := dual_eq_integral_of_bounded hq Λ hU hind hfm (norm_nonneg c) hfb
      change Λ (indicatorConstLp q hs hμs.ne c) = _ at h
      rw [h, ContinuousLinearMap.lpPairing_eq_integral]
      apply integral_congr_ae
      filter_upwards [hUp.coeFn_toLp, indicatorConstLp_coeFn (p := q) (hs := hs)
        (hμs := hμs.ne) (c := c)] with x hx hy
      simp [Up, hx, hy]
    · intro f g hf hg _ ihf ihg
      simp only [map_add, ihf, ihg]
    · exact isClosed_eq Λ.continuous (((ContinuousLinearMap.mul ℝ ℝ).lpPairing μ p q Up).continuous)
  refine ⟨Up, le_antisymm ?_ ?_, heq⟩
  · rw [Lp.norm_toLp]
    exact ENNReal.toReal_le_of_le_ofReal (norm_nonneg Λ) hnorm
  · rw [heq]
    exact Lp.norm_lpPairing_mul_apply_le Up

/-- Riesz representation of `(L^q)*` (Rudin, *Real and Complex Analysis*, Thm. 6.16, real case,
with `p` and `q` interchanged): for σ-finite `μ`, `1 ≤ q < ∞` and `p` conjugate to `q`, every
bounded linear functional `Λ` on `Lp ℝ q μ` is `f ↦ ∫ U f ∂μ` for some `U ∈ Lp ℝ p μ` with
`‖U‖ = ‖Λ‖`. -/
theorem MeasureTheory.Lp.exists_eq_integral_mul [SigmaFinite μ]
    (hq : q ≠ ∞) (Λ : Lp ℝ q μ →L[ℝ] ℝ) :
    ∃ U : Lp ℝ p μ, ‖U‖ = ‖Λ‖ ∧ Λ = (ContinuousLinearMap.mul ℝ ℝ).lpPairing μ p q U := by
  sorry
