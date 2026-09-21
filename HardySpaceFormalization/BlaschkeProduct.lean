import Mathlib.Analysis.Complex.CanonicalDecomposition
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.Analysis.Meromorphic.Divisor
import HardySpaceFormalization.HardySpaceDisc
import HardySpaceFormalization.HarmonicMajorant
import HardySpaceFormalization.NontangentialLimit

noncomputable section

open Complex ComplexConjugate
open scoped Real Topology ENNReal
open Set Metric Subharmonic MeromorphicOn Filter

/-- The Blaschke sum of the zeros of `f` in the unit disc, counted with multiplicity. -/
def blaschkeSum (f : ℂ → ℂ) : ℝ≥0∞ :=
  ∑' z : Function.support (divisor f (ball 0 1)),
    ENNReal.ofReal (divisor f (ball 0 1) z * (1 - ‖z.1‖))

/-- The zeros of `f` in the unit disc satisfy Blaschke's condition when their Blaschke sum is
finite. -/
def BlaschkeCondition (f : ℂ → ℂ) : Prop := blaschkeSum f < ∞


/-- The unnormalized Blaschke factor associated to the disk of radius `R`. -/
noncomputable def BlaschkeFactor (R : ℝ) (w : ℂ) : ℂ → ℂ :=
  fun z ↦ (R * (z - w)) / (R ^ 2 - conj w * z)

lemma BlaschkeFactor_eq_inv_canonicalFactor {R : ℝ} {w z : ℂ} :
  BlaschkeFactor R w z = (canonicalFactor R w z)⁻¹ := by simp [BlaschkeFactor, canonicalFactor]

/-- The normalized Blaschke factor associated to the disk of radius `R`. For `w ≠ 0` this differs
from `BlaschkeFactor R w` by the unimodular constant `-conj w / ‖w‖`; for `w = 0` we keep the raw
factor. -/
noncomputable def normedBlaschkeFactor (R : ℝ) (w : ℂ) : ℂ → ℂ :=
  if w = 0 then BlaschkeFactor R 0
  else (-(conj w) / ‖w‖) • BlaschkeFactor R w

/-- A sequence with summable defects from the unit circle has only finitely many zero terms. -/
theorem zeroIndexSet_finite {z : ℕ → ℂ} (hz : Summable fun n ↦ 1 - ‖z n‖) :
    (z ⁻¹'{0}).Finite := by
  have hcof : (fun n => 1 - ‖z n‖) ⁻¹' (Iio (1 : ℝ)) ∈ cofinite :=
    hz.tendsto_cofinite_zero (Iio_mem_nhds (by norm_num))
  refine (Filter.mem_cofinite.mp hcof).subset ?_
  intro n hn
  rw [mem_preimage, mem_singleton_iff] at hn
  simp [mem_compl_iff, mem_preimage, mem_Iio, hn]

/-- The `n`th factor in the Blaschke product. `0`-terms are omitted from the infinite
product and accounted for by `zeroMultiplicity`. -/
noncomputable def blaschkeProductFactor (z : ℕ → ℂ) (n : ℕ) : ℂ → ℂ :=
  if z n = 0 then 1 else normedBlaschkeFactor 1 (z n)

/-- The Blaschke product associated to a sequence in the unit disc. The definition is meaningful
as a function for any sequence; convergence and the expected zero set will later be proved under
the Blaschke condition. -/
noncomputable def BlaschkeProduct (z : ℕ → ℂ) : ℂ → ℂ :=
  fun w ↦ w ^ (z ⁻¹'{0}).ncard * ∏' n, blaschkeProductFactor z n w


-- The proofs of the rest codes are given by codex without fully review


/-- **Theorem 2.1 (second part).** If `f` is analytic on the unit disc, not identically zero, and
`log ‖f‖` has a harmonic majorant on the disc, and moreover `f 0 ≠ 0` and `u` is the least harmonic
majorant of `log ‖f‖` on the disc, then the Blaschke sum is bounded by `u 0 - log ‖f 0‖`. -/
theorem blaschkeSum_le_of_isLeastHarmonicMajorant
    {f : ℂ → ℂ} (hf : AnalyticOn ℂ f (ball 0 1)) (hf0 : f 0 ≠ 0)
    {u : ℂ → ℝ} (hu : IsLeastHarmonicMajorant u (logNormBot ∘ f) (ball 0 1)) :
    blaschkeSum f ≤ ENNReal.ofReal (u 0 - Real.log ‖f 0‖) := by
  -- codex without review (test version)
  have hfa : AnalyticOnNhd ℂ f (ball 0 1) := isOpen_ball.analyticOn_iff_analyticOnNhd.mp hf
  have hne : ∀ᶠ z in codiscreteWithin (ball (0 : ℂ) 1), f z ≠ 0 := by
    refine (hfa.eqOn_zero_or_eventually_ne_zero_of_preconnected
      (convex_ball (0 : ℂ) 1).isPreconnected).resolve_left ?_
    intro h
    exact hf0 (h (by simp))
  -- Compare circle averages after changing the logarithm only at isolated zeros.
  have havg (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
      Real.circleAverage (fun z => Real.log ‖f z‖) 0 r ≤ u 0 := by
    have hsub : closedBall (0 : ℂ) |r| ⊆ ball 0 1 :=
      closedBall_subset_ball (by simpa [abs_of_pos hr] using hr1)
    let v : ℂ → ℝ := fun z => if f z = 0 then u z else Real.log ‖f z‖
    have heq : (fun z => Real.log ‖f z‖) =ᶠ[codiscreteWithin (sphere (0 : ℂ) |r|)] v := by
      filter_upwards [codiscreteWithin_mono (sphere_subset_closedBall.trans hsub) hne] with z hz
      simp [v, hz]
    rw [Real.circleAverage_congr_codiscreteWithin heq hr.ne']
    calc
      Real.circleAverage v 0 r ≤ Real.circleAverage u 0 r := by
        apply Real.circleAverage_mono
          ((hfa.mono (sphere_subset_closedBall.trans hsub)).meromorphicOn.circleIntegrable_log_norm
            |>.congr_codiscreteWithin heq)
          ((hu.1.1.continuousOn.mono (sphere_subset_closedBall.trans hsub)).circleIntegrable')
        intro z hz
        dsimp [v]
        split_ifs with hfz
        · exact le_rfl
        · simpa [Function.comp_def, logNormBot, hfz] using
            hu.1.2 z (hsub (sphere_subset_closedBall hz))
      _ = u 0 := HarmonicOnNhd.circleAverage_eq (hu.1.1.mono hsub)
  let d := divisor f (ball (0 : ℂ) 1)
  have hdnonneg (z : ℂ) : 0 ≤ (d z : ℝ) := by exact_mod_cast hfa.divisor_nonneg z
  have hdmem {z : ℂ} (hz : d z ≠ 0) : ‖z‖ < 1 := by
    simpa [mem_ball, dist_zero_right] using d.supportWithinDomain hz
  have hd0 : d 0 = 0 := by
    change divisor f (ball 0 1) 0 = 0
    rw [hfa.divisor_apply (by simp : (0 : ℂ) ∈ ball 0 1),
      (hfa 0 (by simp)).analyticOrderAt_eq_zero.mpr hf0]
    rfl
  -- Jensen bounds every finite collection of zeros contained in a smaller disc.
  have hpartial (s : Finset ℂ) (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
      (hs : ∀ z ∈ s, d z ≠ 0 → ‖z‖ < r) :
      (∑ z ∈ s, (d z : ℝ) * Real.log (r * ‖z‖⁻¹)) ≤ u 0 - Real.log ‖f 0‖ := by
    have hsub : closedBall (0 : ℂ) |r| ⊆ ball 0 1 :=
      closedBall_subset_ball (by simpa [abs_of_pos hr] using hr1)
    have hfr := hfa.mono hsub
    let dr := divisor f (closedBall (0 : ℂ) |r|)
    have hdr (z : ℂ) : dr z = if ‖z‖ ≤ r then d z else 0 := by
      by_cases hz : ‖z‖ ≤ r
      · have hzmem : z ∈ closedBall (0 : ℂ) |r| := by simpa [abs_of_pos hr] using hz
        simp only [if_pos hz]
        exact (hfr.divisor_apply hzmem).trans (hfa.divisor_apply (hsub hzmem)).symm
      · have hzmem : z ∉ closedBall (0 : ℂ) |r| := by simpa [abs_of_pos hr] using hz
        simp [dr, hzmem, hz]
    have hfinite : Function.HasFiniteSupport (fun z => (dr z : ℝ) * Real.log (r * ‖z‖⁻¹)) := by
      apply (dr.finiteSupport (isCompact_closedBall ..)).subset
      intro z hz
      contrapose! hz
      simp only [Function.mem_support] at hz ⊢
      simp [hz]
    have hnonneg (z : ℂ) : 0 ≤ (dr z : ℝ) * Real.log (r * ‖z‖⁻¹) := by
      by_cases hz : ‖z‖ ≤ r
      · rw [hdr, if_pos hz]
        by_cases hz0 : z = 0
        · simp [hz0, hd0]
        · apply mul_nonneg (hdnonneg z)
          apply Real.log_nonneg
          rw [← div_eq_mul_inv]
          exact (le_div_iff₀ (norm_pos_iff.mpr hz0)).mpr (by simpa using hz)
      · simp [hdr, hz]
    have hsum : (∑ z ∈ s, (d z : ℝ) * Real.log (r * ‖z‖⁻¹)) =
        ∑ z ∈ s, (dr z : ℝ) * Real.log (r * ‖z‖⁻¹) := by
      apply Finset.sum_congr rfl
      intro z hz
      by_cases hdz : d z = 0
      · simp [hdr, hdz]
      · rw [hdr, if_pos (hs z hz hdz).le]
    have hj := hfr.circleAverage_log_norm hr.ne' hf0
    simp only [zero_sub, norm_neg] at hj
    rw [hsum]
    calc
      _ ≤ ∑' z, (dr z : ℝ) * Real.log (r * ‖z‖⁻¹) :=
        (summable_of_hasFiniteSupport hfinite).sum_le_tsum s (fun z _ => hnonneg z)
      _ = ∑ᶠ z, (dr z : ℝ) * Real.log (r * ‖z‖⁻¹) := tsum_eq_finsum hfinite
      _ ≤ u 0 - Real.log ‖f 0‖ := by linarith [havg r hr hr1]
  -- Let the radius tend to one while keeping that finite collection fixed.
  have hlogsum (s : Finset ℂ) :
      (∑ z ∈ s, (d z : ℝ) * (-Real.log ‖z‖)) ≤ u 0 - Real.log ‖f 0‖ := by
    have ht : Tendsto (fun r : ℝ => ∑ z ∈ s, (d z : ℝ) * Real.log (r * ‖z‖⁻¹))
        (𝓝[<] 1) (𝓝 (∑ z ∈ s, (d z : ℝ) * (-Real.log ‖z‖))) := by
      apply tendsto_finsetSum
      intro z hz
      by_cases hdz : d z = 0
      · simp [hdz]
      · have hz0 : z ≠ 0 := by intro hz0; exact hdz (hz0 ▸ hd0)
        have ht : Tendsto (fun r : ℝ => r * ‖z‖⁻¹) (𝓝 1) (𝓝 (1 * ‖z‖⁻¹)) :=
          tendsto_id.mul_const _
        have htlog := (ht.log (by simpa using inv_ne_zero (norm_ne_zero_iff.mpr hz0))).const_mul
          (d z : ℝ)
        simpa using htlog.mono_left nhdsWithin_le_nhds
    apply le_of_tendsto ht
    have hs : ∀ᶠ r : ℝ in 𝓝[<] 1, ∀ z ∈ s, d z ≠ 0 → ‖z‖ < r := by
      apply (eventually_all_finset s).mpr
      intro z hz
      by_cases hdz : d z = 0
      · simp [hdz]
      · filter_upwards [(eventually_gt_nhds (hdmem hdz)).filter_mono nhdsWithin_le_nhds] with r hr
        exact fun _ => hr
    filter_upwards [hs, (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
      nhdsWithin_le_nhds, self_mem_nhdsWithin] with r hs hr hr1
    exact hpartial s r hr hr1 hs
  have hterm (z : ℂ) : 0 ≤ (d z : ℝ) * (1 - ‖z‖) := by
    by_cases hz : d z = 0
    · simp [hz]
    · exact mul_nonneg (hdnonneg z) (sub_nonneg.mpr (hdmem hz).le)
  have hsum : blaschkeSum f = ∑' z : ℂ, ENNReal.ofReal ((d z : ℝ) * (1 - ‖z‖)) := by
    unfold blaschkeSum
    apply tsum_subtype_eq_of_support_subset
      (f := fun z : ℂ => ENNReal.ofReal ((d z : ℝ) * (1 - ‖z‖)))
    intro z hz
    by_contra h
    have hz0 : divisor f (ball 0 1) z = 0 := not_not.mp h
    exact hz (by simp [d, hz0])
  -- The ENNReal sum is bounded once every finite partial sum is bounded.
  rw [hsum]
  apply ENNReal.summable.tsum_le_of_sum_le
  intro s
  rw [← ENNReal.ofReal_sum_of_nonneg (fun z _ => hterm z)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ∑ z ∈ s, (d z : ℝ) * (-Real.log ‖z‖) := by
      apply Finset.sum_le_sum
      intro z hz
      by_cases hdz : d z = 0
      · simp [hdz]
      · have hz0 : z ≠ 0 := by intro hz0; exact hdz (hz0 ▸ hd0)
        apply mul_le_mul_of_nonneg_left _ (hdnonneg z)
        linarith [Real.log_le_sub_one_of_pos (norm_pos_iff.mpr hz0)]
    _ ≤ u 0 - Real.log ‖f 0‖ := hlogsum s



/-- Factor out the finite analytic order at `a`, with an analytic remaining factor on `s`. -/
theorem AnalyticOnNhd.exists_eq_sub_pow_mul_of_order_ne_top
    {f : ℂ → ℂ} {s : Set ℂ} {a : ℂ}
    (hf : AnalyticOnNhd ℂ f s) (ha : a ∈ s) (horder : analyticOrderAt f a ≠ ⊤) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g s ∧ g a ≠ 0 ∧
      ∀ z ∈ s, f z = (z - a) ^ analyticOrderNatAt f a * g z := by
  obtain ⟨g₀, hg₀, hg₀_ne, heq⟩ := (hf a ha).analyticOrderAt_ne_top.mp horder
  let n := analyticOrderNatAt f a
  let g : ℂ → ℂ := fun z => if z = a then g₀ a else f z / (z - a) ^ n
  have hnear : g₀ =ᶠ[𝓝 a] g := by
    filter_upwards [heq] with z hz
    by_cases hza : z = a
    · simp [g, hza]
    · simp only [smul_eq_mul] at hz
      simp [g, hza, hz, n, pow_ne_zero _ (sub_ne_zero.mpr hza)]
  refine ⟨g, ?_, by simpa [g] using hg₀_ne, ?_⟩
  · intro z hz
    by_cases hza : z = a
    · subst z
      exact hg₀.congr hnear
    · apply ((hf z hz).div ((analyticAt_id.sub analyticAt_const).pow n)
        (pow_ne_zero _ (sub_ne_zero.mpr hza))).congr
      filter_upwards [eventually_ne_nhds hza] with w hw
      simp [g, hw]
  · intro z hz
    by_cases hza : z = a
    · subst z
      simpa [g, n] using heq.self_of_nhds
    · simp only [g, if_neg hza]
      change f z = (z - a) ^ n * (f z / (z - a) ^ n)
      field_simp

/-- Remove the zero at the origin from a nonzero analytic function on the unit disc. -/
lemma AnalyticOnNhd.exists_eq_pow_mul_unitDisc {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (ball 0 1)) (hf_ne : ∃ z ∈ ball 0 1, f z ≠ 0) :
    ∃ (n : ℕ) (g : ℂ → ℂ), AnalyticOnNhd ℂ g (ball 0 1) ∧ g 0 ≠ 0 ∧
      ∀ z ∈ ball 0 1, f z = z ^ n * g z := by
  obtain ⟨w, hw, hfw⟩ := hf_ne
  have horder : analyticOrderAt f 0 ≠ ⊤ :=
    hf.analyticOrderAt_ne_top_of_isPreconnected (convex_ball (0 : ℂ) 1).isPreconnected
      hw (by simp) (by rw [(hf w hw).analyticOrderAt_eq_zero.mpr hfw]; simp)
  obtain ⟨g, hg, hg0, hfg⟩ := hf.exists_eq_sub_pow_mul_of_order_ne_top (by simp) horder
  exact ⟨analyticOrderNatAt f 0, g, hg, hg0, by simpa only [sub_zero] using hfg⟩

/-- Removing a power of `z` preserves the existence of a harmonic majorant of the logarithm. -/
lemma hasHarmonicMajorant_logNormBot_of_eq_pow_mul {f g : ℂ → ℂ} {n : ℕ}
    (hg : AnalyticOnNhd ℂ g (ball 0 1))
    (hfg : ∀ z ∈ ball 0 1, f z = z ^ n * g z)
    (hmaj : HasHarmonicMajorant (logNormBot ∘ f) (ball 0 1)) :
    HasHarmonicMajorant (logNormBot ∘ g) (ball 0 1) := by
  obtain ⟨u, hu, hle⟩ := hmaj
  have hsub : closedBall (0 : ℂ) (1 / 2) ⊆ ball 0 1 :=
    closedBall_subset_ball (by norm_num)
  obtain ⟨A, hA⟩ := (isCompact_closedBall (0 : ℂ) (1 / 2)).bddAbove_image
    ((hg.continuousOn.mono hsub).norm.sub (hu.continuousOn.mono hsub))
  let C : ℝ := max A (-(n : ℝ) * Real.log (1 / 2))
  refine ⟨fun z => u z + C, hu.add (InnerProductSpace.harmonicOnNhd_const C), ?_⟩
  intro z hz
  by_cases hgz : g z = 0
  · simp [logNormBot, hgz]
  simp only [Function.comp_def, logNormBot, if_neg hgz, WithBot.coe_le_coe]
  by_cases hzsmall : z ∈ closedBall (0 : ℂ) (1 / 2)
  · have hbound : ‖g z‖ - u z ≤ A := hA (mem_image_of_mem _ hzsmall)
    have hAC : A ≤ C := le_max_left _ _
    have hlog := Real.log_le_self (norm_nonneg (g z))
    linarith
  · have hznorm : (1 / 2 : ℝ) ≤ ‖z‖ := le_of_lt (by
      simpa [mem_closedBall, dist_zero_right] using hzsmall)
    have hz0 : z ≠ 0 := norm_pos_iff.mp (by linarith)
    have hfz : f z ≠ 0 := by rw [hfg z hz]; exact mul_ne_zero (pow_ne_zero _ hz0) hgz
    have hlogf : Real.log ‖f z‖ ≤ u z := by
      simpa [Function.comp_def, logNormBot, hfz] using hle z hz
    rw [hfg z hz, norm_mul, norm_pow, Real.log_mul
      (pow_ne_zero _ (norm_ne_zero_iff.mpr hz0)) (norm_ne_zero_iff.mpr hgz),
      Real.log_pow] at hlogf
    have hlogz : Real.log (1 / 2) ≤ Real.log ‖z‖ :=
      Real.log_le_log (by norm_num) hznorm
    have hmul := mul_le_mul_of_nonneg_left hlogz (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    have hC : -(n : ℝ) * Real.log (1 / 2) ≤ C := le_max_right _ _
    linarith

/-- Adding a zero of finite multiplicity at the origin preserves the Blaschke condition. -/
lemma BlaschkeCondition.of_eq_pow_mul {f g : ℂ → ℂ} {n : ℕ}
    (hgB : BlaschkeCondition g) (hf : AnalyticOnNhd ℂ f (ball 0 1))
    (hg : AnalyticOnNhd ℂ g (ball 0 1))
    (hfg : ∀ z ∈ ball 0 1, f z = z ^ n * g z) : BlaschkeCondition f := by
  have hdiv : ∀ z ≠ 0, divisor f (ball 0 1) z = divisor g (ball 0 1) z := by
    intro z hz0
    by_cases hz : z ∈ ball 0 1
    · rw [hf.divisor_apply hz, hg.divisor_apply hz]
      have heq : f =ᶠ[𝓝 z] (fun w => w ^ n) * g := by
        filter_upwards [isOpen_ball.mem_nhds hz] with w hw using hfg w hw
      have hp : AnalyticAt ℂ (fun w : ℂ => w ^ n) z := by fun_prop
      rw [analyticOrderAt_congr heq, analyticOrderAt_mul hp (hg z hz),
        hp.analyticOrderAt_eq_zero.mpr (pow_ne_zero _ hz0), zero_add]
    · simp [hz]
  have hsum (k : ℂ → ℂ) : blaschkeSum k =
      ∑' z : ℂ, ENNReal.ofReal (divisor k (ball 0 1) z * (1 - ‖z‖)) := by
    unfold blaschkeSum
    apply tsum_subtype_eq_of_support_subset
      (f := fun z : ℂ => ENNReal.ofReal (divisor k (ball 0 1) z * (1 - ‖z‖)))
    intro z hz
    by_contra h
    have hz0 : divisor k (ball 0 1) z = 0 := not_not.mp h
    exact hz (by simp [hz0])
  have hrest : (∑' z : ℂ, if z = 0 then 0 else
      ENNReal.ofReal (divisor f (ball 0 1) z * (1 - ‖z‖))) ≤ blaschkeSum g := by
    rw [hsum g]
    apply ENNReal.tsum_le_tsum
    intro z
    split_ifs with hz
    · exact bot_le
    · rw [hdiv z hz]
  rw [BlaschkeCondition, hsum f, ENNReal.tsum_eq_add_tsum_ite 0]
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, hrest.trans_lt hgB⟩

/-- **Theorem 2.1 (first part).** If `f` is analytic on the unit disc, not identically zero, and
`log ‖f‖` has a harmonic majorant on the disc, then the zeros
of `f`, counted with multiplicity, satisfy the Blaschke condition `∑ (1 - ‖zₙ‖) < ∞`.
-/
theorem blaschkeCondition_of_hasHarmonicMajorant {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (ball 0 1)) (hf_ne : ∃ z ∈ ball 0 1, f z ≠ 0)
    (hmaj : HasHarmonicMajorant (logNormBot ∘ f) (ball 0 1)) :
    BlaschkeCondition f := by
  obtain ⟨n, g, hg, hg0, hfg⟩ := hf.exists_eq_pow_mul_unitDisc hf_ne
  have hgmaj := hasHarmonicMajorant_logNormBot_of_eq_pow_mul hg hfg hmaj
  obtain ⟨u, hu, _⟩ := exists_isLeastHarmonicMajorant_tendsto_poissonModification
    (logNormBot_comp_analytic_subharmonicOn_scalar isOpen_ball hg.analyticOn) hgmaj
  have hsum := blaschkeSum_le_of_isLeastHarmonicMajorant hg.analyticOn hg0 hu
  have hgB : BlaschkeCondition g := hsum.trans_lt ENNReal.ofReal_lt_top
  exact hgB.of_eq_pow_mul hf hg hfg

/-! ## Theorem 2.2: convergence, zeros, and boundary values of Blaschke products -/

/-- The products omitting zero terms converge locally uniformly on the unit disc. -/
theorem tendstoLocallyUniformlyOn_blaschkeProductFactor {a : ℕ → ℂ}
    (ha : ∀ n, a n ∈ ball 0 1) (hsum : Summable (fun n ↦ 1 - ‖a n‖)) :
    TendstoLocallyUniformlyOn
      (fun N w => ∏ n ∈ Finset.range N, blaschkeProductFactor a n w)
      (fun w => ∏' n, blaschkeProductFactor a n w) atTop (ball 0 1) := by
  sorry

/-- The finite products, including the full power accounting for zeros at the origin,
converge locally uniformly to the Blaschke product on the unit disc. -/
theorem tendstoLocallyUniformlyOn_blaschkeProduct {a : ℕ → ℂ}
    (ha : ∀ n, a n ∈ ball 0 1) (hsum : Summable (fun n ↦ 1 - ‖a n‖)) :
    TendstoLocallyUniformlyOn
      (fun N w => w ^ (a ⁻¹' {0}).ncard *
        ∏ n ∈ Finset.range N, blaschkeProductFactor a n w)
      (BlaschkeProduct a) atTop (ball 0 1) := by
  sorry

/-- A Blaschke product is analytic on the unit disc. -/
theorem analyticOnNhd_blaschkeProduct {a : ℕ → ℂ}
    (ha : ∀ n, a n ∈ ball 0 1) (hsum : Summable (fun n ↦ 1 - ‖a n‖)) :
    AnalyticOnNhd ℂ (BlaschkeProduct a) (ball 0 1) := by
  sorry

/-- A Blaschke product has modulus at most one on the unit disc. -/
theorem norm_blaschkeProduct_le_one {a : ℕ → ℂ}
    (ha : ∀ n, a n ∈ ball 0 1) (hsum : Summable (fun n ↦ 1 - ‖a n‖))
    {w : ℂ} (hw : w ∈ ball 0 1) : ‖BlaschkeProduct a w‖ ≤ 1 := by
  sorry

/-- The order at a point of the unit disc equals its number of occurrences in the sequence. -/
theorem analyticOrderAt_blaschkeProduct {a : ℕ → ℂ}
    (ha : ∀ n, a n ∈ ball 0 1) (hsum : Summable (fun n ↦ 1 - ‖a n‖))
    {w : ℂ} (hw : w ∈ ball 0 1) :
    analyticOrderAt (BlaschkeProduct a) w = (a ⁻¹' {w}).encard := by
  sorry

/-- The zeros in the unit disc are exactly the points of the defining sequence. -/
theorem blaschkeProduct_eq_zero_iff {a : ℕ → ℂ}
    (ha : ∀ n, a n ∈ ball 0 1) (hsum : Summable (fun n ↦ 1 - ‖a n‖))
    {w : ℂ} (hw : w ∈ ball 0 1) :
    BlaschkeProduct a w = 0 ↔ ∃ n, a n = w := by
  sorry

/-- Extended by zero outside the unit disc, a Blaschke product belongs to `H∞`. -/
theorem memHpDisc_blaschkeProduct {a : ℕ → ℂ}
    (ha : ∀ n, a n ∈ ball 0 1) (hsum : Summable (fun n ↦ 1 - ‖a n‖)) :
    HardySpace.MemHpDisc ∞ ((ball (0 : ℂ) 1).indicator (BlaschkeProduct a)) := by
  sorry

/-- A Blaschke product has nontangential boundary values of modulus one almost everywhere. -/
theorem ae_hasNontangentialLimit_blaschkeProduct {a : ℕ → ℂ}
    (ha : ∀ n, a n ∈ ball 0 1) (hsum : Summable (fun n ↦ 1 - ‖a n‖)) :
    ∀ᵐ ζ ∂circleMeasure 0 1,
      HasNontangentialLimit (BlaschkeProduct a) ζ
        (boundaryValue (BlaschkeProduct a) ζ) ∧
      ‖boundaryValue (BlaschkeProduct a) ζ‖ = 1 := by
  sorry
