import Mathlib.Analysis.Complex.CanonicalDecomposition
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.Analysis.Meromorphic.Divisor
import HardySpaceFormalization.HardySpaceDisc
import HardySpaceFormalization.HardySpaceBoundary
import HardySpaceFormalization.HarmonicMajorant
import HardySpaceFormalization.NontangentialLimit

noncomputable section

open Complex ComplexConjugate
open scoped Real Topology ENNReal
open Set Metric Subharmonic MeromorphicOn Filter


/-- The Blaschke sum of a multiplicity function on the unit disc.
For an analytic function use `m := analyticOrderAt f`; for a family `a : ι → ℂ`
use `m := Multiplicity a`. -/
def blaschkeSum (m : ℂ → ℕ∞) : ℝ≥0∞ := ∑' z : ball (0 : ℂ) 1, (m z) * (1 - ‖z.1‖ₑ)

/-- A multiplicity function satisfies the Blaschke condition on the unit disc if its
Blaschke sum is finite. For a family of points, membership in the unit disc is a separate
assumption. -/
def BlaschkeCondition (m : ℂ → ℕ∞) : Prop := blaschkeSum m < ∞


/-- Under the Blaschke condition the multiplicity is finite at every point of the unit disc. -/
theorem BlaschkeCondition.ne_top {m : ℂ → ℕ∞} (hm : BlaschkeCondition m) {w : ℂ}
    (hw : w ∈ ball 0 1) : m w ≠ ⊤ := by
  intro h
  have hterm : (m w : ℝ≥0∞) * (1 - ‖w‖ₑ) ≤ blaschkeSum m :=
    ENNReal.le_tsum (f := fun a : ball (0 : ℂ) 1 => (m a : ℝ≥0∞) * (1 - ‖a.1‖ₑ)) ⟨w, hw⟩
  have hw1 : ‖w‖ₑ < 1 := by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_lt_one.mpr (mem_ball_zero_iff.mp hw)
  rw [h, ENat.toENNReal_top, ENNReal.top_mul (tsub_pos_of_lt hw1).ne'] at hterm
  exact lt_irrefl _ (hterm.trans_lt hm)

/-- The Blaschke condition passes to smaller multiplicity functions. -/
theorem BlaschkeCondition.mono {m m' : ℂ → ℕ∞} (hm : BlaschkeCondition m) (h : m' ≤ m) :
    BlaschkeCondition m' :=
  lt_of_le_of_lt (ENNReal.tsum_le_tsum fun a => by gcongr; exact h a) hm



/-- The unnormalized Blaschke factor associated to the disk of radius `R`. -/
noncomputable def BlaschkeFactor (R : ℝ) (w : ℂ) : ℂ → ℂ :=
  fun z ↦ (R * (z - w)) / (R ^ 2 - conj w * z)

lemma BlaschkeFactor_eq_inv_canonicalFactor {R : ℝ} {w z : ℂ} :
  BlaschkeFactor R w z = (canonicalFactor R w z)⁻¹ := by simp [BlaschkeFactor, canonicalFactor]

/-- A unit-disc Blaschke factor has modulus at most one on the unit disc. -/
lemma norm_BlaschkeFactor_one_le_one {a z : ℂ}
    (ha : a ∈ ball 0 1) (hz : z ∈ ball 0 1) : ‖BlaschkeFactor 1 a z‖ ≤ 1 := by
  have ha2 : normSq a ≤ 1 := by
    rw [normSq_eq_norm_sq]
    exact pow_le_one₀ (norm_nonneg a) (mem_ball_zero_iff.mp ha).le
  have hz2 : normSq z ≤ 1 := by
    rw [normSq_eq_norm_sq]
    exact pow_le_one₀ (norm_nonneg z) (mem_ball_zero_iff.mp hz).le
  have hid : normSq (1 - conj a * z) - normSq (z - a) =
      (1 - normSq a) * (1 - normSq z) := by
    simp only [normSq_apply, sub_re, sub_im, mul_re, mul_im, conj_re, conj_im,
      one_re, one_im]
    ring
  have hle : ‖z - a‖ ≤ ‖1 - conj a * z‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [Complex.sq_norm, Complex.sq_norm]
    nlinarith [mul_nonneg (sub_nonneg.mpr ha2) (sub_nonneg.mpr hz2)]
  simpa [BlaschkeFactor, norm_div] using div_le_one_of_le₀ hle (norm_nonneg _)

/-- The normalized Blaschke factor associated to the disk of radius `R`. For `w ≠ 0` this differs
from `BlaschkeFactor R w` by the unimodular constant `-conj w / ‖w‖`; for `w = 0` we keep the raw
factor. -/
noncomputable def normedBlaschkeFactor (R : ℝ) (w : ℂ) : ℂ → ℂ :=
  if w = 0 then BlaschkeFactor R 0
  else (-(conj w) / ‖w‖) • BlaschkeFactor R w

/-- A normalized unit-disc Blaschke factor has modulus one on the unit circle. -/
lemma norm_normedBlaschkeFactor_eq_one {a ζ : ℂ} (ha : a ∈ ball 0 1) (hζ : ζ ∈ sphere 0 1) :
    ‖normedBlaschkeFactor 1 a ζ‖ = 1 := by
  have hb : ‖BlaschkeFactor 1 a ζ‖ = 1 := by
    rw [BlaschkeFactor_eq_inv_canonicalFactor, norm_inv,
      norm_canonicalFactor_eval_circle_eq_one ha hζ, inv_one]
  by_cases ha0 : a = 0
  · subst a
    simpa [normedBlaschkeFactor] using hb
  · have hn : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha0
    simp [normedBlaschkeFactor, ha0, hb, hn]

/-- A normalized unit-disc Blaschke factor has a simple zero at its defining point. -/
lemma analyticOrderAt_normedBlaschkeFactor {a : ℂ} (ha : a ∈ ball 0 1) :
    analyticOrderAt (normedBlaschkeFactor 1 a) a = 1 := by
  by_cases ha0 : a = 0
  · subst a
    have hfactor : normedBlaschkeFactor 1 0 = id := by
      ext z
      simp [normedBlaschkeFactor, BlaschkeFactor]
    rw [hfactor, analyticOrderAt_id]
  have hden : 1 - conj a * a ≠ 0 := by
    have haa : ‖conj a * a‖ < 1 := by
      rw [norm_mul, norm_conj]
      nlinarith [mem_ball_zero_iff.mp ha, norm_nonneg a]
    intro heq
    rw [← sub_eq_zero.mp heq, norm_one] at haa
    exact (lt_irrefl _ haa)
  let g : ℂ → ℂ := fun z => (-(conj a) / ‖a‖) / (1 - conj a * z)
  have hg : AnalyticAt ℂ g a := by
    dsimp [g]
    fun_prop
  have hg0 : g a ≠ 0 := by
    have hn : (‖a‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr ha0)
    exact div_ne_zero (div_ne_zero (by simpa using ha0) hn) hden
  have hfactor : normedBlaschkeFactor 1 a = (fun z => z - a) * g := by
    ext z
    simp only [normedBlaschkeFactor, ite_eq_right ha0, BlaschkeFactor, ofReal_one,
      one_pow, one_mul, Pi.smul_apply, smul_eq_mul, Pi.mul_apply, g]
    ring
  rw [hfactor, analyticOrderAt_mul (by fun_prop) hg,
    analyticOrderAt_id_sub_const_self, hg.analyticOrderAt_eq_zero.mpr hg0, add_zero]



/-- The factor of the Blaschke product at a point `a` with multiplicity `m a`: the normalized
Blaschke factor at `a` raised to the power `m a`. The point `0` is excluded here; it is accounted
for by the power of `w` in `BlaschkeProduct`. -/
noncomputable def blaschkeProductFactor (m : ℂ → ℕ∞) (a : ℂ) : ℂ → ℂ :=
  if a = 0 then 1 else fun w ↦ normedBlaschkeFactor 1 a w ^ (m a).toNat

/-- The Blaschke product with zero multiplicities `m` in the unit disc,
`B(w) = w ^ m(0) * ∏_{a ∈ 𝔻, a ≠ 0} b_a(w) ^ m(a)`.
For an analytic function `f` use `m := analyticOrderAt f`; for a family `a : ι → ℂ`, finite or
infinite, use `m := Multiplicity a`. Points outside the disc are ignored, as are infinite
multiplicities (which the Blaschke condition excludes in the disc). Convergence and the expected
zero set will later be proved under the Blaschke condition. -/
noncomputable def BlaschkeProduct (m : ℂ → ℕ∞) : ℂ → ℂ :=
  fun w ↦ w ^ (m 0).toNat * ∏' a : ball (0 : ℂ) 1, blaschkeProductFactor m a w

variable {f : ℂ → ℂ}
#check BlaschkeCondition (analyticOrderAt f)
#check BlaschkeProduct (analyticOrderAt f)




-- The proofs of the rest codes are given by codex without fully review


/-- **Theorem 2.1 (second part).** If `f` is analytic on the unit disc, not identically zero, and
`log ‖f‖` has a harmonic majorant on the disc, and moreover `f 0 ≠ 0` and `u` is the least harmonic
majorant of `log ‖f‖` on the disc, then the Blaschke sum is bounded by `u 0 - log ‖f 0‖`. -/
theorem blaschkeSum_le_of_isLeastHarmonicMajorant
    {f : ℂ → ℂ} (hf : AnalyticOn ℂ f (ball 0 1)) (hf0 : f 0 ≠ 0)
    {u : ℂ → ℝ} (hu : IsLeastHarmonicMajorant u (logNormBot ∘ f) (ball 0 1)) :
    blaschkeSum (analyticOrderAt f) ≤ ENNReal.ofReal (u 0 - Real.log ‖f 0‖) := by
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
    rw [Real.circleAverage_congr_codiscreteWithin heq hr.ne', ← InnerProductSpace.HarmonicOnNhd.circleAverage_eq (hu.1.1.mono hsub)]
    apply Real.circleAverage_mono
          ((hfa.mono (sphere_subset_closedBall.trans hsub)).meromorphicOn.circleIntegrable_log_norm
            |>.congr_codiscreteWithin heq)
          ((hu.1.1.continuousOn.mono (sphere_subset_closedBall.trans hsub)).circleIntegrable')
    intro z hz; dsimp [v]
    split_ifs with hfz
    · exact le_rfl
    · simpa [Function.comp_def, logNormBot, hfz] using hu.1.2 z (hsub (sphere_subset_closedBall hz))
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
        simp only [ite_eq_left hz]
        exact (hfr.divisor_apply hzmem).trans (hfa.divisor_apply (hsub hzmem)).symm
      · have hzmem : z ∉ closedBall (0 : ℂ) |r| := by simpa [abs_of_pos hr] using hz
        simp [dr, hzmem, hz]
    have hfinite : Function.HasFiniteSupport (fun z => (dr z : ℝ) * Real.log (r * ‖z‖⁻¹)) := by
      apply (dr.finiteSupport (isCompact_closedBall ..)).subset
      intro z hz
      contrapose hz
      simp only [Function.mem_support] at hz ⊢
      simp [hz]
    have hnonneg (z : ℂ) : 0 ≤ (dr z : ℝ) * Real.log (r * ‖z‖⁻¹) := by
      by_cases hz : ‖z‖ ≤ r
      · rw [hdr, ite_eq_left hz]
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
      · rw [hdr, ite_eq_left (hs z hz hdz).le]
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
  have horder (z : ℂ) (hz : z ∈ ball 0 1) : analyticOrderAt f z ≠ ⊤ :=
    hfa.analyticOrderAt_ne_top_of_isPreconnected (convex_ball (0 : ℂ) 1).isPreconnected
      (show (0 : ℂ) ∈ ball 0 1 by simp) hz
      (by rw [(hfa 0 (by simp)).analyticOrderAt_eq_zero.mpr hf0]; simp)
  have hsum : blaschkeSum (analyticOrderAt f) =
      ∑' z : ℂ, ENNReal.ofReal ((d z : ℝ) * (1 - ‖z‖)) := by
    calc
      _ = ∑' z : ball (0 : ℂ) 1,
          ENNReal.ofReal ((d z : ℝ) * (1 - ‖z.1‖)) := by
        apply tsum_congr
        intro z
        obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (horder z z.property)
        have hd : d z = (m : ℤ) := by
          simp [d, hfa.divisor_apply z.property, ← hm]
        simp [← hm, hd, ENNReal.ofReal_mul, ENNReal.ofReal_sub _ (norm_nonneg _)]
      _ = _ := by
        apply tsum_subtype_eq_of_support_subset
          (f := fun z : ℂ => ENNReal.ofReal ((d z : ℝ) * (1 - ‖z‖)))
        intro z hz
        by_contra hzmem
        have hdz : d z = 0 := by simp [d, hzmem]
        exact hz (by simp [hdz])
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
    · simp only [g, ite_eq_right hza]
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
    (hg : AnalyticOnNhd ℂ g (ball 0 1)) (hfg : ∀ z ∈ ball 0 1, f z = z ^ n * g z)
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
  simp only [Function.comp_def, logNormBot, ite_eq_right hgz, WithBot.coe_le_coe]
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
    (hgB : BlaschkeCondition (analyticOrderAt g)) (hg : AnalyticOnNhd ℂ g (ball 0 1))
    (hfg : ∀ z ∈ ball 0 1, f z = z ^ n * g z) : BlaschkeCondition (analyticOrderAt f) := by
  let origin : ball (0 : ℂ) 1 := ⟨0, by simp⟩
  have horder (z : ℂ) (hz : z ∈ ball 0 1) :
      analyticOrderAt f z = (if z = 0 then (n : ℕ∞) else 0) + analyticOrderAt g z := by
    have heq : f =ᶠ[𝓝 z] (fun w => w ^ n) * g := by
      filter_upwards [isOpen_ball.mem_nhds hz] with w hw using hfg w hw
    have hp : AnalyticAt ℂ (fun w : ℂ => w ^ n) z := by fun_prop
    rw [analyticOrderAt_congr heq, analyticOrderAt_mul hp (hg z hz)]
    by_cases hz0 : z = 0
    · subst z
      congr 1
      rw [ite_eq_left rfl]
      change analyticOrderAt (id ^ n : ℂ → ℂ) 0 = n
      simp [analyticOrderAt_pow analyticAt_id, nsmul_eq_mul]
    · rw [ite_eq_right hz0, hp.analyticOrderAt_eq_zero.mpr (pow_ne_zero _ hz0)]
  have hterm (z : ball (0 : ℂ) 1) :
      (analyticOrderAt f z : ℝ≥0∞) * (1 - ‖z.1‖ₑ) =
        (if z = origin then (n : ℝ≥0∞) else 0) +
          (analyticOrderAt g z : ℝ≥0∞) * (1 - ‖z.1‖ₑ) := by
    rw [horder z z.property]
    by_cases hz : z = origin
    · subst z
      simp [origin]
    · have hz0 : (z : ℂ) ≠ 0 := fun h => hz (Subtype.ext h)
      simp [hz, hz0]
  have hsum : blaschkeSum (analyticOrderAt f) = n + blaschkeSum (analyticOrderAt g) := by
    unfold blaschkeSum
    simp_rw [hterm]
    rw [ENNReal.tsum_add]
    simp
  change blaschkeSum (analyticOrderAt f) < ∞
  rw [hsum]
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.natCast_lt_top n, hgB⟩

/-- **Theorem 2.1 (first part).** If `f` is analytic on the unit disc, not identically zero, and
`log ‖f‖` has a harmonic majorant on the disc, then the zeros
of `f`, counted with multiplicity, satisfy the Blaschke condition `∑ (1 - ‖zₙ‖) < ∞`.
-/
theorem blaschkeCondition_of_hasHarmonicMajorant {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (ball 0 1)) (hf_ne : ∃ z ∈ ball 0 1, f z ≠ 0)
    (hmaj : HasHarmonicMajorant (logNormBot ∘ f) (ball 0 1)) :
    BlaschkeCondition (analyticOrderAt f) := by
  obtain ⟨n, g, hg, hg0, hfg⟩ := hf.exists_eq_pow_mul_unitDisc hf_ne
  have hgmaj := hasHarmonicMajorant_logNormBot_of_eq_pow_mul hg hfg hmaj
  obtain ⟨u, hu, _⟩ := exists_isLeastHarmonicMajorant_tendsto_poissonModification
    (logNormBot_comp_analytic_subharmonicOn_scalar isOpen_ball hg.analyticOn)
    ⟨0, by simp, by simp [logNormBot, hg0]⟩ hgmaj
  have hsum := blaschkeSum_le_of_isLeastHarmonicMajorant hg.analyticOn hg0 hu
  have hgB : BlaschkeCondition (analyticOrderAt g) := hsum.trans_lt ENNReal.ofReal_lt_top
  exact hgB.of_eq_pow_mul hg hfg

/-! ## Theorem 2.2: convergence, zeros, and boundary values of Blaschke products -/

/-- Garnett's pointwise estimate for the deviation of a normalized Blaschke factor from one. -/
lemma norm_one_sub_normedBlaschkeFactor_le {a z : ℂ}
    (ha : a ∈ ball 0 1) (ha0 : a ≠ 0) (hz : z ∈ ball 0 1) :
    ‖1 - normedBlaschkeFactor 1 a z‖ ≤ (1 + ‖z‖) / (1 - ‖z‖) * (1 - ‖a‖) := by
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  have ha1 : ‖a‖ < 1 := mem_ball_zero_iff.mp ha
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  -- `|1 - conj a * z| ≥ 1 - |a| |z| ≥ 1 - |z|`.
  have hden : 1 - ‖z‖ ≤ ‖1 - conj a * z‖ := by
    calc 1 - ‖z‖ ≤ 1 - ‖a‖ * ‖z‖ := by nlinarith [norm_nonneg z]
      _ = ‖(1 : ℂ)‖ - ‖conj a * z‖ := by simp
      _ ≤ ‖1 - conj a * z‖ := norm_sub_norm_le _ _
  have hden0 : 1 - conj a * z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hden
    linarith
  have hn : (‖a‖ : ℂ) ≠ 0 := by exact_mod_cast hna.ne'
  have hconj : conj a * a = (‖a‖ : ℂ) ^ 2 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  -- Garnett's calculation: `1 - b_a(z) = (1 - |a|) (|a| + conj a * z) / (|a| (1 - conj a * z))`.
  have hid : 1 - normedBlaschkeFactor 1 a z =
      ((1 - ‖a‖ : ℝ) : ℂ) * (‖a‖ + conj a * z) / (‖a‖ * (1 - conj a * z)) := by
    simp only [normedBlaschkeFactor, ite_eq_right ha0, BlaschkeFactor, ofReal_one, one_pow,
      one_mul, Pi.smul_apply, smul_eq_mul]
    field_simp
    push_cast
    linear_combination (-1 : ℂ) * hconj
  have hnum : ‖(‖a‖ : ℂ) + conj a * z‖ ≤ ‖a‖ * (1 + ‖z‖) := by
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_norm, norm_mul, Complex.norm_conj]
    ring
  rw [hid, norm_div, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos (sub_pos.mpr ha1), abs_norm]
  calc (1 - ‖a‖) * ‖(‖a‖ : ℂ) + conj a * z‖ / (‖a‖ * ‖1 - conj a * z‖)
      ≤ (1 - ‖a‖) * (‖a‖ * (1 + ‖z‖)) / (‖a‖ * (1 - ‖z‖)) := by
        gcongr
    _ = (1 + ‖z‖) / (1 - ‖z‖) * (1 - ‖a‖) := by
        field_simp

/-- The pointwise deviation estimate for a Blaschke factor with multiplicity. -/
lemma norm_one_sub_blaschkeProductFactor_le {m : ℂ → ℕ∞} {a z : ℂ}
    (ha : a ∈ ball 0 1) (hz : z ∈ ball 0 1) :
    ‖1 - blaschkeProductFactor m a z‖ ≤
      (1 + ‖z‖) / (1 - ‖z‖) * (m a).toNat * (1 - ‖a‖) := by
  have ha1 : ‖a‖ < 1 := mem_ball_zero_iff.mp ha
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  by_cases ha0 : a = 0
  · simp only [blaschkeProductFactor, ha0, ite_true, Pi.one_apply, sub_self, norm_zero]
    positivity
  have hb : ‖normedBlaschkeFactor 1 a z‖ ≤ 1 := by
    simpa [normedBlaschkeFactor, ha0, norm_smul, norm_div, norm_ne_zero_iff.mpr ha0] using
      norm_BlaschkeFactor_one_le_one ha hz
  have hpow (k : ℕ) : ‖1 - normedBlaschkeFactor 1 a z ^ k‖ ≤
      k * ‖1 - normedBlaschkeFactor 1 a z‖ := by
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        ‖1 - normedBlaschkeFactor 1 a z ^ (k + 1)‖ =
            ‖(1 - normedBlaschkeFactor 1 a z ^ k) * normedBlaschkeFactor 1 a z +
              (1 - normedBlaschkeFactor 1 a z)‖ := by
                congr 1
                ring
        _ ≤ ‖1 - normedBlaschkeFactor 1 a z ^ k‖ * ‖normedBlaschkeFactor 1 a z‖ +
            ‖1 - normedBlaschkeFactor 1 a z‖ := by
              simpa only [norm_mul] using norm_add_le
                ((1 - normedBlaschkeFactor 1 a z ^ k) * normedBlaschkeFactor 1 a z)
                (1 - normedBlaschkeFactor 1 a z)
        _ ≤ ‖1 - normedBlaschkeFactor 1 a z ^ k‖ +
            ‖1 - normedBlaschkeFactor 1 a z‖ := by
              gcongr
              exact mul_le_of_le_one_right (norm_nonneg _) hb
        _ ≤ (k + 1 : ℕ) * ‖1 - normedBlaschkeFactor 1 a z‖ := by
              push_cast
              nlinarith [ih]
  simp only [blaschkeProductFactor, ite_eq_right ha0]
  calc
    _ ≤ (m a).toNat * ‖1 - normedBlaschkeFactor 1 a z‖ := hpow _
    _ ≤ (m a).toNat * ((1 + ‖z‖) / (1 - ‖z‖) * (1 - ‖a‖)) :=
      mul_le_mul_of_nonneg_left (norm_one_sub_normedBlaschkeFactor_le ha ha0 hz)
        (Nat.cast_nonneg _)
    _ = _ := by ring

/-- The finite partial products of the factors at nonzero points converge locally uniformly
on the unit disc, along finite sets of points of the disc (unconditional convergence). -/
lemma tendstoLocallyUniformlyOn_blaschkeProductFactor {m : ℂ → ℕ∞} (hm : BlaschkeCondition m) :
  TendstoLocallyUniformlyOn
    (fun (s : Finset (ball (0 : ℂ) 1)) w => ∏ a ∈ s, blaschkeProductFactor m a w)
      (fun w => ∏' a : ball (0 : ℂ) 1, blaschkeProductFactor m a w) atTop (ball 0 1) := by
  -- Convert the Blaschke sum to a summable real-valued majorant.
  have hsum : Summable (fun a : ball (0 : ℂ) 1 =>
      ((m a).toNat : ℝ) * (1 - ‖(a : ℂ)‖)) := by
    have hs := ENNReal.summable_toReal (ne_of_lt hm)
    apply hs.congr
    intro a
    have ha : ‖(a : ℂ)‖ₑ ≤ 1 := by
      rw [← ofReal_norm]
      exact (ENNReal.ofReal_lt_one.mpr (mem_ball_zero_iff.mp a.2)).le
    have hmcast : (m a : ℝ≥0∞) = (m a).toNat := by
      conv_lhs => rw [← ENat.natCast_toNat (hm.ne_top a.2)]
      simp
    simp only [ENNReal.toReal_mul, hmcast, ENNReal.toReal_natCast,
      ENNReal.toReal_sub_of_le ha ENNReal.one_ne_top, ENNReal.toReal_one, toReal_enorm]
  -- Around each point, work on a larger closed disc contained in the unit disc.
  apply hasProdLocallyUniformlyOn_of_of_forall_exists_nhds
  intro z hz
  obtain ⟨r, hzr, hr⟩ := exists_between (mem_ball_zero_iff.mp hz)
  have hK : closedBall (0 : ℂ) r ⊆ ball 0 1 := by
    intro w hw
    exact mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hw).trans_lt hr)
  refine ⟨closedBall (0 : ℂ) r,
    nhdsWithin_le_nhds (closedBall_mem_nhds_of_mem (mem_ball_zero_iff.mpr hzr)), ?_⟩
  have hcts (a : ball (0 : ℂ) 1) : ContinuousOn (blaschkeProductFactor m a) (closedBall 0 r) := by
    by_cases ha0 : (a : ℂ) = 0
    · convert (continuousOn_const : ContinuousOn (fun _ : ℂ => (1 : ℂ))
        (closedBall 0 r)) using 1
      ext w
      simp [blaschkeProductFactor, ha0]
    have hden (w : ℂ) (hw : w ∈ closedBall (0 : ℂ) r) : 1 - conj (a : ℂ) * w ≠ 0 := by
      have hab : ‖conj (a : ℂ) * w‖ < 1 := by
        rw [norm_mul, norm_conj]
        nlinarith [mem_ball_zero_iff.mp a.2, mem_ball_zero_iff.mp (hK hw),
          norm_nonneg (a : ℂ), norm_nonneg w]
      intro heq
      rw [← sub_eq_zero.mp heq, norm_one] at hab
      exact (lt_irrefl _ hab)
    have hd : ContinuousOn (fun w : ℂ => (w - (a : ℂ)) / (1 - conj (a : ℂ) * w))
        (closedBall 0 r) :=
      (continuousOn_id.sub continuousOn_const).div
        (continuousOn_const.sub (continuousOn_const.mul continuousOn_id)) hden
    convert ((continuousOn_const : ContinuousOn
      (fun _ : ℂ => -(conj (a : ℂ)) / ‖(a : ℂ)‖) (closedBall 0 r)).mul hd).pow
        (m a).toNat using 1
    ext w
    simp [blaschkeProductFactor, normedBlaschkeFactor, ha0, BlaschkeFactor, smul_eq_mul]
  -- The pointwise estimate has a summable uniform bound on this closed disc.
  have hbound : ∀ᶠ a : ball (0 : ℂ) 1 in cofinite, ∀ w ∈ closedBall (0 : ℂ) r,
      ‖blaschkeProductFactor m a w - 1‖ ≤
        (1 + r) / (1 - r) * (((m a).toNat : ℝ) * (1 - ‖(a : ℂ)‖)) := by
    apply Filter.Eventually.of_forall
    intro a w hw
    have hwle : ‖w‖ ≤ r := mem_closedBall_zero_iff.mp hw
    have hratio : (1 + ‖w‖) / (1 - ‖w‖) ≤ (1 + r) / (1 - r) := by
      apply div_le_div₀ (by linarith [norm_nonneg z]) (by linarith) (by linarith) (by linarith)
    rw [norm_sub_rev]
    calc
      _ ≤ (1 + ‖w‖) / (1 - ‖w‖) * (m a).toNat * (1 - ‖(a : ℂ)‖) :=
        norm_one_sub_blaschkeProductFactor_le a.2 (hK hw)
      _ ≤ (1 + r) / (1 - r) * (m a).toNat * (1 - ‖(a : ℂ)‖) := by
        gcongr
        · exact sub_nonneg.mpr (mem_ball_zero_iff.mp a.2).le
      _ = _ := by ring
  have hprod := Summable.hasProdUniformlyOn_one_add (isCompact_closedBall (0 : ℂ) r)
    (hsum.mul_left ((1 + r) / (1 - r))) hbound (fun a => (hcts a).sub continuousOn_const)
  simpa only [add_sub_cancel] using hprod

/-- The finite products, including the full power accounting for zeros at the origin,
converge locally uniformly to the Blaschke product on the unit disc. -/
theorem tendstoLocallyUniformlyOn_blaschkeProduct {m : ℂ → ℕ∞} (hm : BlaschkeCondition m) :
  TendstoLocallyUniformlyOn (fun (s : Finset (ball (0 : ℂ) 1)) w => w ^ (m 0).toNat *
    ∏ a ∈ s, blaschkeProductFactor m a w) (BlaschkeProduct m) atTop (ball 0 1) := by
  -- codex with review
  have hconv := Metric.tendstoLocallyUniformlyOn_iff.mp
    (tendstoLocallyUniformlyOn_blaschkeProductFactor hm)
  apply Metric.tendstoLocallyUniformlyOn_iff.mpr
  intro ε hε z hz
  obtain ⟨t, ht, hN⟩ := hconv ε hε z hz
  refine ⟨t ∩ ball 0 1, inter_mem ht self_mem_nhdsWithin, ?_⟩
  filter_upwards [hN] with s hN w hw
  have hw1 : ‖w‖ ≤ 1 := (mem_ball_zero_iff.mp hw.2).le
  simp only [BlaschkeProduct, dist_eq_norm, ← mul_sub, norm_mul, norm_pow]
  refine lt_of_le_of_lt ?_ (hN w hw.1)
  rw [dist_eq_norm]
  exact mul_le_of_le_one_left (norm_nonneg (_ : ℂ)) (pow_le_one₀ (norm_nonneg w) hw1)

/-- A Blaschke product is analytic on the unit disc. -/
theorem analyticOnNhd_blaschkeProduct {m : ℂ → ℕ∞} (hm : BlaschkeCondition m) :
  AnalyticOnNhd ℂ (BlaschkeProduct m) (ball 0 1) := by
  -- codex without review
  have hfactor (a : ball (0 : ℂ) 1) :
      DifferentiableOn ℂ (blaschkeProductFactor m a) (ball 0 1) := by
    intro z hz
    by_cases ha0 : (a : ℂ) = 0
    · simp only [blaschkeProductFactor, ha0, ite_eq_left]
      fun_prop
    · have hnorm : ‖conj (a : ℂ) * z‖ < 1 := by
        rw [norm_mul, norm_conj]
        nlinarith [mem_ball_zero_iff.mp a.2, mem_ball_zero_iff.mp hz,
          norm_nonneg (a : ℂ), norm_nonneg z]
      have hden : 1 - conj (a : ℂ) * z ≠ 0 := by
        intro h
        rw [← sub_eq_zero.mp h, norm_one] at hnorm
        exact (lt_irrefl _ hnorm)
      simp only [blaschkeProductFactor, normedBlaschkeFactor, ite_eq_right ha0]
      unfold BlaschkeFactor
      simp only [ofReal_one, one_pow, one_mul, Pi.smul_apply, smul_eq_mul]
      apply DifferentiableAt.differentiableWithinAt
      fun_prop
  apply DifferentiableOn.analyticOnNhd _ isOpen_ball
  apply (tendstoLocallyUniformlyOn_blaschkeProduct hm).differentiableOn _ isOpen_ball
  exact Filter.Eventually.of_forall fun s => by fun_prop

-- # Now we'd like to show that

/-- A Blaschke product has modulus at most one on the unit disc. -/
theorem norm_blaschkeProduct_le_one {m : ℂ → ℕ∞} (hm : BlaschkeCondition m)
  {w : ℂ} (hw : w ∈ ball 0 1) : ‖BlaschkeProduct m w‖ ≤ 1 := by
  -- codex without review
  have hfactor (a : ball (0 : ℂ) 1) : ‖blaschkeProductFactor m a w‖ ≤ 1 := by
    by_cases ha0 : (a : ℂ) = 0
    · simp [blaschkeProductFactor, ha0]
    · have hb : ‖normedBlaschkeFactor 1 a w‖ ≤ 1 := by
        simpa [normedBlaschkeFactor, ha0, norm_smul, norm_div, norm_ne_zero_iff.mpr ha0] using
          norm_BlaschkeFactor_one_le_one a.2 hw
      simp only [blaschkeProductFactor, ite_eq_right ha0, norm_pow]
      exact pow_le_one₀ (norm_nonneg _) hb
  apply le_of_tendsto ((tendstoLocallyUniformlyOn_blaschkeProduct hm).tendsto_at hw).norm
  filter_upwards [] with s
  rw [norm_mul, norm_pow, norm_prod]
  exact (mul_le_of_le_one_left (Finset.prod_nonneg fun a _ => norm_nonneg _)
      (pow_le_one₀ (norm_nonneg w) (mem_ball_zero_iff.mp hw).le)).trans
    (Finset.prod_le_one₀ (fun a _ => norm_nonneg _) (fun a _ => hfactor a))

/-- A finite partial Blaschke product is continuous on the closed unit disc. -/
lemma continuousOn_partialBlaschkeProduct (m : ℂ → ℕ∞) (s : Finset (ball (0 : ℂ) 1)) :
    ContinuousOn (fun z => z ^ (m 0).toNat * ∏ a ∈ s, blaschkeProductFactor m a z)
      (closedBall 0 1) := by
  refine (continuousOn_id.pow _).mul (continuousOn_finsetProd s fun a _ => ?_)
  by_cases ha0 : (a : ℂ) = 0
  · simp only [blaschkeProductFactor, ha0, ite_true]
    exact continuousOn_const
  -- The denominator `1 - conj a * z` does not vanish on the closed disc.
  have hden (w : ℂ) (hw : w ∈ closedBall (0 : ℂ) 1) : 1 - conj (a : ℂ) * w ≠ 0 := by
    have hab : ‖conj (a : ℂ) * w‖ < 1 := by
      rw [norm_mul, norm_conj]
      nlinarith [mem_ball_zero_iff.mp a.2, mem_closedBall_zero_iff.mp hw,
        norm_nonneg (a : ℂ), norm_nonneg w]
    intro heq
    rw [← sub_eq_zero.mp heq, norm_one] at hab
    exact lt_irrefl _ hab
  have hd : ContinuousOn (fun w : ℂ => (w - (a : ℂ)) / (1 - conj (a : ℂ) * w))
      (closedBall 0 1) :=
    (continuousOn_id.sub continuousOn_const).div
      (continuousOn_const.sub (continuousOn_const.mul continuousOn_id)) hden
  convert ((continuousOn_const : ContinuousOn
    (fun _ : ℂ => -(conj (a : ℂ)) / ‖(a : ℂ)‖) (closedBall 0 1)).mul hd).pow
      (m a).toNat using 1
  ext w
  simp [blaschkeProductFactor, normedBlaschkeFactor, ha0, BlaschkeFactor, smul_eq_mul]

/-- A Blaschke product does not vanish at a point with prescribed multiplicity zero. -/
lemma blaschkeProduct_ne_zero_of_multiplicity_eq_zero {m : ℂ → ℕ∞}
    (hm : BlaschkeCondition m) {w : ℂ} (hw : w ∈ ball 0 1) (hmw : m w = 0) :
    BlaschkeProduct m w ≠ 0 := by
  have hsum : Summable (fun a : ball (0 : ℂ) 1 =>
      ((m a).toNat : ℝ) * (1 - ‖(a : ℂ)‖)) := by
    have hs := ENNReal.summable_toReal (ne_of_lt hm)
    apply hs.congr
    intro a
    have ha : ‖(a : ℂ)‖ₑ ≤ 1 := by
      rw [← ofReal_norm]
      exact (ENNReal.ofReal_lt_one.mpr (mem_ball_zero_iff.mp a.2)).le
    have hmcast : (m a : ℝ≥0∞) = (m a).toNat := by
      conv_lhs => rw [← ENat.natCast_toNat (hm.ne_top a.2)]
      simp
    simp only [ENNReal.toReal_mul, hmcast, ENNReal.toReal_natCast,
      ENNReal.toReal_sub_of_le ha ENNReal.one_ne_top, ENNReal.toReal_one, toReal_enorm]
  have hdev : Summable (fun a : ball (0 : ℂ) 1 => ‖blaschkeProductFactor m a w - 1‖) := by
    apply (hsum.mul_left ((1 + ‖w‖) / (1 - ‖w‖))).of_nonneg_of_le (fun a => norm_nonneg _)
    intro a
    simpa only [norm_sub_rev, mul_assoc] using norm_one_sub_blaschkeProductFactor_le (m := m) a.2 hw
  have hfactor (a : ball (0 : ℂ) 1) : blaschkeProductFactor m a w ≠ 0 := by
    by_cases ha0 : (a : ℂ) = 0
    · simp [blaschkeProductFactor, ha0]
    by_cases haw : (a : ℂ) = w
    · simp only [blaschkeProductFactor, ite_eq_right ha0]
      simp [haw, hmw]
    have hden : 1 - conj (a : ℂ) * w ≠ 0 := by
      have hab : ‖conj (a : ℂ) * w‖ < 1 := by
        rw [norm_mul, norm_conj]
        nlinarith [mem_ball_zero_iff.mp a.2, mem_ball_zero_iff.mp hw,
          norm_nonneg (a : ℂ), norm_nonneg w]
      intro heq
      rw [← sub_eq_zero.mp heq, norm_one] at hab
      exact (lt_irrefl _ hab)
    have hn : (‖(a : ℂ)‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr ha0)
    simp only [blaschkeProductFactor, normedBlaschkeFactor, ite_eq_right ha0,
      BlaschkeFactor, ofReal_one, one_pow, one_mul, Pi.smul_apply, smul_eq_mul]
    exact pow_ne_zero _ (mul_ne_zero (div_ne_zero (by simpa using ha0) hn)
      (div_ne_zero (sub_ne_zero.mpr (Ne.symm haw)) hden))
  have hprod : (∏' a : ball (0 : ℂ) 1, blaschkeProductFactor m a w) ≠ 0 := by
    simpa only [add_sub_cancel] using
      tprod_one_add_ne_zero_of_summable (f := fun a : ball (0 : ℂ) 1 =>
        blaschkeProductFactor m a w - 1)
        (fun a => by simpa only [add_sub_cancel] using hfactor a) hdev
  apply mul_ne_zero _ hprod
  by_cases hw0 : w = 0
  · subst w
    simp [hmw]
  · exact pow_ne_zero _ hw0

/-- Splitting off the zeros at a point `w` of the unit disc: on the disc, the Blaschke product is
the normalized Blaschke factor at `w` to the power `m w` times the Blaschke product whose
multiplicity at `w` is set to zero. -/
lemma blaschkeProduct_eq_normedBlaschkeFactor_pow_mul {m : ℂ → ℕ∞} (hm : BlaschkeCondition m)
    {w : ℂ} (hw : w ∈ ball 0 1) {z : ℂ} (hz : z ∈ ball 0 1) :
    BlaschkeProduct m z =
      normedBlaschkeFactor 1 w z ^ (m w).toNat * BlaschkeProduct (Function.update m w 0) z := by
  set m' : ℂ → ℕ∞ := Function.update m w 0
  by_cases hw0 : w = 0
  · -- At the origin the factors agree and only the power of `z` changes.
    subst hw0
    have hf (a : ball (0 : ℂ) 1) : blaschkeProductFactor m' a = blaschkeProductFactor m a := by
      by_cases ha0 : (a : ℂ) = 0
      · simp [blaschkeProductFactor, ha0]
      · simp [blaschkeProductFactor, ha0, m']
    simp [BlaschkeProduct, hf, m', normedBlaschkeFactor, BlaschkeFactor]
  -- Otherwise split off the factor at `w` from the infinite product.
  have hm' : BlaschkeCondition m' := hm.mono fun a => by
    by_cases h : a = w <;> simp [m', h]
  set f : ball (0 : ℂ) 1 → ℂ := fun a => blaschkeProductFactor m a z
  have hupd : (fun a : ball (0 : ℂ) 1 => blaschkeProductFactor m' a z) =
      Function.update f ⟨w, hw⟩ 1 := by
    ext a
    by_cases ha : a = ⟨w, hw⟩
    · subst ha
      simp [f, blaschkeProductFactor, hw0, m']
    · have ha' : (a : ℂ) ≠ w := fun h => ha (Subtype.ext h)
      simp [Function.update_of_ne ha, f, blaschkeProductFactor, m', ha']
  have hmul : Multipliable (Function.update f ⟨w, hw⟩ 1) := by
    rw [← hupd]
    exact ⟨_, (tendstoLocallyUniformlyOn_blaschkeProductFactor hm').tendsto_at hz⟩
  have hsplit : ∏' a, f a = f ⟨w, hw⟩ * ∏' a, Function.update f ⟨w, hw⟩ 1 a := by
    rw [Multipliable.tprod_eq_mul_tprod_ite' (f := f) ⟨w, hw⟩ hmul]
    congr 2
    ext a
    by_cases ha : a = ⟨w, hw⟩ <;> simp [ha]
  have hm0 : m' 0 = m 0 := by simp [m', Ne.symm hw0]
  have hfw : f ⟨w, hw⟩ = normedBlaschkeFactor 1 w z ^ (m w).toNat := by
    show blaschkeProductFactor m w z = _
    simp [blaschkeProductFactor, hw0]
  simp only [BlaschkeProduct, hm0]
  rw [show (∏' a : ball (0 : ℂ) 1, blaschkeProductFactor m a z) = ∏' a, f a from rfl,
    hsplit, hfw, ← hupd]
  ring

/-- Splitting off a finite partial product: on the unit disc, the Blaschke product is the partial
product over a finite set `s` of points of the disc (including the zeros at the origin) times the
Blaschke product whose multiplicities on `s` and at the origin are set to zero. -/
lemma blaschkeProduct_eq_partialProd_mul {m : ℂ → ℕ∞} (hm : BlaschkeCondition m)
    (s : Finset (ball (0 : ℂ) 1)) {z : ℂ} (hz : z ∈ ball 0 1) :
    BlaschkeProduct m z =
      (z ^ (m 0).toNat * ∏ a ∈ s, blaschkeProductFactor m a z) *
        BlaschkeProduct ((insert 0 (Subtype.val '' (s : Set (ball (0 : ℂ) 1))))ᶜ.indicator m) z := by
  classical
  -- Split off one point at a time, starting with the origin.
  induction s using Finset.induction_on with
  | empty =>
    have hupd : (insert 0 (Subtype.val '' ((∅ : Finset (ball (0 : ℂ) 1)) :
        Set (ball (0 : ℂ) 1))))ᶜ.indicator m = Function.update m 0 0 := by
      ext w
      by_cases hw : w = 0
      · simp [hw]
      · simp [hw]
    rw [hupd, blaschkeProduct_eq_normedBlaschkeFactor_pow_mul hm (mem_ball_self one_pos) hz]
    simp [normedBlaschkeFactor, BlaschkeFactor]
  | insert a s ha ih =>
    set ms := (insert 0 (Subtype.val '' (s : Set (ball (0 : ℂ) 1))))ᶜ.indicator m with hms_def
    have hms : BlaschkeCondition ms := hm.mono (Set.indicator_le_self _ _)
    have hupd : (insert 0 (Subtype.val '' ((insert a s : Finset (ball (0 : ℂ) 1)) :
        Set (ball (0 : ℂ) 1))))ᶜ.indicator m = Function.update ms a 0 := by
      ext w
      by_cases hw : w = a
      · subst hw
        simp [ms]
      · simp [ms, hw, Set.indicator_apply]
    have hfa : normedBlaschkeFactor 1 a z ^ (ms a).toNat = blaschkeProductFactor m a z := by
      by_cases ha0 : (a : ℂ) = 0
      · simp [ms, ha0, blaschkeProductFactor]
      · have hma : ms a = m a := by
          simp [ms, ha0, ha]
        simp [blaschkeProductFactor, ha0, hma]
    rw [ih, hupd, blaschkeProduct_eq_normedBlaschkeFactor_pow_mul hms a.2 hz, hfa,
      Finset.prod_insert ha]
    ring

/-- The order at a point of the unit disc equals the prescribed multiplicity there. -/
theorem analyticOrderAt_blaschkeProduct {m : ℂ → ℕ∞} (hm : BlaschkeCondition m)
  {w : ℂ} (hw : w ∈ ball 0 1) : analyticOrderAt (BlaschkeProduct m) w = m w := by
  -- `m'` removes the zeros at `w`.
  set m' : ℂ → ℕ∞ := Function.update m w 0
  have hm' : BlaschkeCondition m' := hm.mono fun a => by
    by_cases h : a = w <;> simp [m', h]
  have hev : BlaschkeProduct m =ᶠ[𝓝 w]
      normedBlaschkeFactor 1 w ^ (m w).toNat * BlaschkeProduct m' := by
    filter_upwards [isOpen_ball.mem_nhds hw] with z hz
    exact blaschkeProduct_eq_normedBlaschkeFactor_pow_mul hm hw hz
  have hb : AnalyticAt ℂ (normedBlaschkeFactor 1 w) w :=
    (analyticOrderAt_ne_zero.mp (by simp [analyticOrderAt_normedBlaschkeFactor hw])).1
  have hB' : AnalyticAt ℂ (BlaschkeProduct m') w := analyticOnNhd_blaschkeProduct hm' w hw
  have hB'w : BlaschkeProduct m' w ≠ 0 :=
    blaschkeProduct_ne_zero_of_multiplicity_eq_zero hm' hw (by simp [m'])
  rw [analyticOrderAt_congr hev, analyticOrderAt_mul (hb.pow _) hB', analyticOrderAt_pow hb,
    analyticOrderAt_normedBlaschkeFactor hw, hB'.analyticOrderAt_eq_zero.mpr hB'w]
  simp [ENat.natCast_toNat (hm.ne_top hw)]

/-- The zeros in the unit disc are exactly the points of positive multiplicity. -/
theorem blaschkeProduct_eq_zero_iff {m : ℂ → ℕ∞} (hm : BlaschkeCondition m)
  {w : ℂ} (hw : w ∈ ball 0 1) : BlaschkeProduct m w = 0 ↔ m w ≠ 0 := by
  have h := analyticOrderAt_ne_zero (f := BlaschkeProduct m) (z₀ := w)
  rw [analyticOrderAt_blaschkeProduct hm hw,
    and_iff_right (analyticOnNhd_blaschkeProduct hm w hw)] at h
  exact h.symm

/-- Extended by zero outside the unit disc, a Blaschke product belongs to `H∞`. -/
theorem memHpDisc_blaschkeProduct {m : ℂ → ℕ∞} (hm : BlaschkeCondition m) :
  HardySpace.MemHpDisc ∞ ((ball 0 1).indicator (BlaschkeProduct m)) := by
  have han : AnalyticOn ℂ ((ball 0 1).indicator (BlaschkeProduct m)) (ball 0 1) :=
    (analyticOnNhd_blaschkeProduct hm).analyticOn.congr fun z hz => indicator_of_mem hz _
  refine ⟨han, ?_, fun z hz => indicator_of_notMem hz _⟩
  refine lt_of_le_of_lt (iSup₂_le fun r hr => ?_) (ENNReal.ofReal_lt_top (r := 1))
  simp only [eLpNormFixed, mem_Ioo, not_top_lt, and_false, ite_false]
  rw [MeasureTheory.eLpNorm_exponent_top (radial_aestronglyMeasurable han.continuousOn hr _)]
  refine MeasureTheory.eLpNormEssSup_le_of_ae_bound (MeasureTheory.ae_of_all _ fun θ => ?_)
  have hz : (r : ℂ) * exp (I * θ) ∈ ball 0 1 := radial_point_mem_unitDisc hr.1 hr.2
  rw [indicator_of_mem hz]
  exact norm_blaschkeProduct_le_one hm hz

/-- Garnett II.2.2: the tails of a Blaschke product tend to one at the origin. The tail over a
finite set `s` of points of the disc clears the multiplicities on `s` and at the origin. -/
lemma tendsto_blaschkeProduct_tail_zero {m : ℂ → ℕ∞} (hm : BlaschkeCondition m) :
    Tendsto (fun s : Finset (ball (0 : ℂ) 1) =>
      BlaschkeProduct ((insert 0 (Subtype.val '' (s : Set (ball (0 : ℂ) 1))))ᶜ.indicator m) 0)
      atTop (𝓝 1) := by
  let ms : Finset (ball (0 : ℂ) 1) → ℂ → ℕ∞ := fun s =>
    (insert 0 (Subtype.val '' (s : Set (ball (0 : ℂ) 1))))ᶜ.indicator m
  -- To avoid dividing by zero, first remove the zeros at the origin.
  set m₀ : ℂ → ℕ∞ := Function.update m 0 0 with hm₀
  have hm₀B : BlaschkeCondition m₀ := hm.mono fun a => by
    by_cases h : a = 0 <;> simp [m₀, h]
  have hfac : ∀ a, blaschkeProductFactor m₀ a = blaschkeProductFactor m a := by
    intro a
    by_cases ha0 : a = 0
    · simp [blaschkeProductFactor, ha0]
    · simp [blaschkeProductFactor, ha0, m₀]
  have hms₀ : ∀ s : Finset (ball (0 : ℂ) 1),
      (insert 0 (Subtype.val '' (s : Set (ball (0 : ℂ) 1))))ᶜ.indicator m₀ = ms s := by
    intro s
    ext a
    by_cases ha : a ∈ (insert 0 (Subtype.val '' (s : Set (ball (0 : ℂ) 1))))ᶜ
    · have ha0 : a ≠ 0 := by
        rintro rfl
        exact ha (mem_insert _ _)
      simp only [ms, Set.indicator_of_mem ha, m₀, Function.update_of_ne ha0]
    · simp only [ms, Set.indicator_of_notMem ha]
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  set T := ∏' a : ball (0 : ℂ) 1, blaschkeProductFactor m a 0 with hT_def
  have hB0 : BlaschkeProduct m₀ 0 = T := by
    simp [BlaschkeProduct, hfac, m₀, T]
  have hT : T ≠ 0 := by
    rw [← hB0]
    exact blaschkeProduct_ne_zero_of_multiplicity_eq_zero hm₀B h0 (by simp [m₀])
  -- `T = Q_s * G_s(0)`, where the partial products `Q_s` converge to `T ≠ 0`.
  have hsplit (s : Finset (ball (0 : ℂ) 1)) :
      T = (∏ a ∈ s, blaschkeProductFactor m a 0) * BlaschkeProduct (ms s) 0 := by
    have := blaschkeProduct_eq_partialProd_mul hm₀B s h0
    rw [hB0, hms₀ s] at this
    simpa [hfac, m₀] using this
  have hQ : Tendsto (fun s : Finset (ball (0 : ℂ) 1) => ∏ a ∈ s, blaschkeProductFactor m a 0)
      atTop (𝓝 T) :=
    (tendstoLocallyUniformlyOn_blaschkeProductFactor hm).tendsto_at h0
  have hlim := (tendsto_const_nhds (x := T)).div hQ hT
  rw [div_self hT] at hlim
  refine hlim.congr fun s => ?_
  have hQs : ∏ a ∈ s, blaschkeProductFactor m a 0 ≠ 0 := by
    intro h
    apply hT
    rw [hsplit s, h, zero_mul]
  simp only [Pi.div_apply]
  rw [hsplit s, mul_div_cancel_left₀ _ hQs]

open MeasureTheory in
/-- A Blaschke product has nontangential boundary values of modulus one almost everywhere. -/
theorem ae_hasNontangentialLimit_blaschkeProduct {m : ℂ → ℕ∞} (hm : BlaschkeCondition m) :
    ∀ᵐ ζ ∂circleMeasure 0 1, ‖boundaryValue (BlaschkeProduct m) ζ‖ = 1 := by
  set F := BlaschkeProduct m with hF_def
  have hFan : AnalyticOnNhd ℂ F (ball 0 1) := analyticOnNhd_blaschkeProduct hm
  have hFle : ∀ z ∈ ball (0 : ℂ) 1, ‖F z‖ ≤ 1 := fun z hz => norm_blaschkeProduct_le_one hm hz
  have hnt_le (ζ : ℂ) : nontangentially ζ ≤ 𝓝 ζ := iSup₂_le fun _ _ => nhdsWithin_le_nhds
  -- `|F*| ≤ 1` almost everywhere, since `|F| ≤ 1` on the disc.
  have hFbv_le : ∀ᵐ ζ ∂circleMeasure 0 1, ‖boundaryValue F ζ‖ ≤ 1 := by
    filter_upwards [hFan.ae_nontangentiallyConvergentAt_of_bounded hFle,
      ae_nontangentially_neBot_circleMeasure] with ζ hζ hne
    exact le_of_tendsto hζ.hasNontangentialLimit.norm
      (by filter_upwards [eventually_mem_ball_nontangentially ζ] with z hz using hFle z hz)
  -- `ms s` removes the zeros on a finite set `s` and at the origin; `B_{ms s}` is the tail `B / B_s`.
  let ms : Finset (ball (0 : ℂ) 1) → ℂ → ℕ∞ := fun s =>
    (insert 0 (Subtype.val '' (s : Set (ball (0 : ℂ) 1))))ᶜ.indicator m
  -- Garnett: `|B(0) / B_n(0)| ≤ ∫ |B / B_n| = ∫ |B|`, since `|B_n| = 1` on the circle.
  have hstep (s : Finset (ball (0 : ℂ) 1)) :
      ‖BlaschkeProduct (ms s) 0‖ ≤ ∫ ζ, ‖boundaryValue F ζ‖ ∂circleMeasure 0 1 := by
    set G := BlaschkeProduct (ms s)
    set P : ℂ → ℂ := fun z => z ^ (m 0).toNat * ∏ a ∈ s, blaschkeProductFactor m a z with hP
    have hms : BlaschkeCondition (ms s) := hm.mono (Set.indicator_le_self _ _)
    have hGan : AnalyticOnNhd ℂ G (ball 0 1) := analyticOnNhd_blaschkeProduct hms
    have hGle : ∀ z ∈ ball (0 : ℂ) 1, ‖G z‖ ≤ 1 := fun z hz => norm_blaschkeProduct_le_one hms hz
    have hFPG : ∀ z ∈ ball (0 : ℂ) 1, F z = P z * G z := fun z hz =>
      blaschkeProduct_eq_partialProd_mul hm s hz
    have hPcont : ContinuousOn P (closedBall 0 1) := continuousOn_partialBlaschkeProduct m s
    have hPnorm : ∀ ζ ∈ sphere (0 : ℂ) 1, ‖P ζ‖ = 1 := by
      intro ζ hζ
      simp only [hP, norm_mul, norm_pow, norm_prod, mem_sphere_zero_iff_norm.1 hζ, one_pow,
        one_mul]
      refine Finset.prod_eq_one fun a _ => ?_
      by_cases ha0 : (a : ℂ) = 0
      · simp [blaschkeProductFactor, ha0]
      · simp [blaschkeProductFactor, ha0, norm_normedBlaschkeFactor_eq_one a.2 hζ]
    -- Where `F` has a nontangential limit `L`, `G = F / P` tends to `L / P ζ`, of modulus `|L|`.
    have hbv : ∀ᵐ ζ ∂circleMeasure 0 1, ‖boundaryValue G ζ‖ = ‖boundaryValue F ζ‖ := by
      filter_upwards [hFan.ae_nontangentiallyConvergentAt_of_bounded hFle,
        ae_nontangentially_neBot_circleMeasure, ae_mem_sphere_circleMeasure zero_le_one]
        with ζ hζ hne hζs
      have hPζ : P ζ ≠ 0 := by
        intro h
        have := hPnorm ζ hζs
        rw [h, norm_zero] at this
        exact zero_ne_one this
      have hPt : Tendsto P (nontangentially ζ) (𝓝 (P ζ)) := by
        refine (hPcont ζ (sphere_subset_closedBall hζs)).tendsto.comp ?_
        refine tendsto_nhdsWithin_iff.mpr ⟨hnt_le ζ, ?_⟩
        filter_upwards [eventually_mem_ball_nontangentially ζ] with z hz
        exact ball_subset_closedBall hz
      have hGt : HasNontangentialLimit G ζ (boundaryValue F ζ / P ζ) := by
        refine (Filter.Tendsto.div hζ.hasNontangentialLimit hPt hPζ).congr' ?_
        filter_upwards [eventually_mem_ball_nontangentially ζ, hPt.eventually_ne hPζ]
          with z hz hPz
        rw [Pi.div_apply, hFPG z hz]
        field_simp
      rw [hGt.boundaryValue_eq, norm_div, hPnorm ζ hζs, div_one]
    calc ‖G 0‖ ≤ ∫ ζ, ‖boundaryValue G ζ‖ ∂circleMeasure 0 1 :=
          hGan.norm_le_integral_norm_boundaryValue_of_bounded hGle
      _ = _ := integral_congr_ae hbv
  -- Garnett: `B(0) / B_n(0) → 1`.
  have htail : Tendsto (fun s => BlaschkeProduct (ms s) 0) atTop (𝓝 1) :=
    tendsto_blaschkeProduct_tail_zero hm
  -- Hence `∫ |F*| ≥ 1`; together with `|F*| ≤ 1` this forces `|F*| = 1` almost everywhere.
  have hint : 1 ≤ ∫ ζ, ‖boundaryValue F ζ‖ ∂circleMeasure 0 1 := by
    simpa using le_of_tendsto' htail.norm hstep
  have hFi : Integrable (fun ζ => ‖boundaryValue F ζ‖) (circleMeasure 0 1) :=
    ((hFan.memLp_boundaryValue_of_bounded hFle).integrable le_top).norm
  have hnonneg : 0 ≤ᵐ[circleMeasure 0 1] fun ζ => 1 - ‖boundaryValue F ζ‖ := by
    filter_upwards [hFbv_le] with ζ hζ using sub_nonneg.mpr hζ
  have hzero : ∫ ζ, (1 - ‖boundaryValue F ζ‖) ∂circleMeasure 0 1 = 0 := by
    refine le_antisymm ?_ (integral_nonneg_of_ae hnonneg)
    rw [integral_sub (integrable_const 1) hFi]
    simp
    linarith
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnonneg
    ((integrable_const 1).sub hFi)).mp hzero
  filter_upwards [hae] with ζ hζ
  simp only [Pi.zero_apply] at hζ
  linarith



/-! ## Theorem 2.4: (a) → (b) and (b) ↔ (c) -/

/-- **Theorem 2.4, (a) → (b).** The radial means of the logarithmic modulus of a
Blaschke product, multiplied by a unimodular constant, tend to zero. -/
theorem tendsto_withBotRadialMean_logNormBot_blaschkeProduct {m : ℂ → ℕ∞}
  (hm : BlaschkeCondition m) {c : ℂ} (hc : ‖c‖ = 1) :
  Tendsto (fun r => withBotRadialMean (logNormBot ∘ (fun z => c * BlaschkeProduct m z)) r)
    (𝓝[<] 1) (𝓝 0) := by
  set F := BlaschkeProduct m with hF_def
  set f : ℂ → ℂ := fun z => c * F z with hf_def
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have hFan : AnalyticOnNhd ℂ F (ball 0 1) := analyticOnNhd_blaschkeProduct hm
  have hfan : AnalyticOnNhd ℂ f (ball 0 1) := fun z hz => analyticAt_const.mul (hFan z hz)
  have hFle : ∀ z ∈ ball (0 : ℂ) 1, ‖F z‖ ≤ 1 := fun z hz => norm_blaschkeProduct_le_one hm hz
  have hnorm_f (z : ℂ) : ‖f z‖ = ‖F z‖ := by simp [f, hc]
  have hcb {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) : closedBall (0 : ℂ) |r| ⊆ ball 0 1 :=
    closedBall_subset_ball (by rw [abs_of_pos hr.1]; exact hr.2)
  -- `F` is not identically zero, since its order at the origin is finite.
  have hne : ∃ z ∈ ball (0 : ℂ) 1, f z ≠ 0 := by
    have hord : analyticOrderAt F 0 ≠ ⊤ := by
      rw [analyticOrderAt_blaschkeProduct hm h0]
      exact hm.ne_top h0
    have hfreq : ∃ᶠ z in 𝓝 (0 : ℂ), F z ≠ 0 := fun h =>
      hord (analyticOrderAt_eq_top.mpr (h.mono fun z hz => not_not.mp hz))
    obtain ⟨z, hFz, hz⟩ := (hfreq.and_eventually (isOpen_ball.mem_nhds h0)).exists
    exact ⟨z, hz, by rw [← norm_ne_zero_iff, hnorm_f, norm_ne_zero_iff]; exact hFz⟩
  -- The radial means are the real circle averages `A r`.
  set A : ℝ → ℝ := fun r => Real.circleAverage (fun z => Real.log ‖f z‖) 0 r with hA
  suffices hA0 : Tendsto A (𝓝[<] 1) (𝓝 0) by
    refine Tendsto.congr' ?_ ((WithBot.continuous_coe.tendsto 0).comp hA0)
    filter_upwards [Ioo_mem_nhdsLT (zero_lt_one' ℝ)] with r hr
    exact (withBotRadialMean_logNormBot_eq_circleAverage hfan hne hr).symm
  -- Upper bound: `log |f| ≤ 0`.
  have hupper : ∀ r ∈ Ioo (0 : ℝ) 1, A r ≤ 0 := by
    intro r hr
    have := Real.circleAverage_mono (c := 0) (R := r)
      (AnalyticOnNhd.meromorphicOn
        (hfan.mono (sphere_subset_closedBall.trans (hcb hr)))).circleIntegrable_log_norm
      (circleIntegrable_const 0 0 r) (fun z hz => by
        rw [hnorm_f]
        exact Real.log_nonpos (norm_nonneg _) (hFle z (hcb hr (sphere_subset_closedBall hz))))
    simpa [A, Real.circleAverage_const] using this
  -- Jensen: the circle averages of `log |g|` dominate `log |g(0)|`; this replaces Garnett's
  -- appeal to the subharmonicity of `log |f / B_n|`.
  have hjensen (g : ℂ → ℂ) (r : ℝ) (hr : 0 < r) (hg : AnalyticOnNhd ℂ g (closedBall 0 |r|))
      (hg0 : g 0 ≠ 0) : Real.log ‖g 0‖ ≤ Real.circleAverage (fun z => Real.log ‖g z‖) 0 r := by
    rw [hg.circleAverage_log_norm hr.ne' hg0]
    refine le_add_of_nonneg_left (finsum_nonneg fun u => ?_)
    by_cases hu : divisor g (closedBall 0 |r|) u = 0
    · simp [hu]
    · have hmem := (divisor g (closedBall 0 |r|)).supportWithinDomain hu
      rw [mem_closedBall_zero_iff, abs_of_pos hr] at hmem
      refine mul_nonneg (by exact_mod_cast hg.divisor_nonneg u) ?_
      by_cases hu0 : u = 0
      · simp [hu0]
      · apply Real.log_nonneg
        rw [zero_sub, norm_neg, ← div_eq_mul_inv]
        exact (one_le_div (norm_pos_iff.mpr hu0)).mpr hmem
  -- The finite partial products `P s` and the tails `G s = B / P s`.
  let P : Finset (ball (0 : ℂ) 1) → ℂ → ℂ := fun s z =>
    z ^ (m 0).toNat * ∏ a ∈ s, blaschkeProductFactor m a z
  let G : Finset (ball (0 : ℂ) 1) → ℂ → ℂ := fun s =>
    BlaschkeProduct ((insert 0 (Subtype.val '' (s : Set (ball (0 : ℂ) 1))))ᶜ.indicator m)
  have hPnorm (s : Finset (ball (0 : ℂ) 1)) : ∀ ζ ∈ sphere (0 : ℂ) 1, ‖P s ζ‖ = 1 := by
    intro ζ hζ
    simp only [P, norm_mul, norm_pow, norm_prod, mem_sphere_zero_iff_norm.1 hζ, one_pow, one_mul]
    refine Finset.prod_eq_one fun a _ => ?_
    by_cases ha0 : (a : ℂ) = 0
    · simp [blaschkeProductFactor, ha0]
    · simp [blaschkeProductFactor, ha0, norm_normedBlaschkeFactor_eq_one a.2 hζ]
  -- Garnett: `B_n` is continuous on the closed disc with `|B_n| = 1` on the circle, so
  -- `|B_n| ≥ e^{-ε}` near the circle.
  have hPnear (s : Finset (ball (0 : ℂ) 1)) (ε : ℝ) (hε : 0 < ε) :
      ∃ ρ < 1, 0 ≤ ρ ∧ ∀ z ∈ ball (0 : ℂ) 1, ρ < ‖z‖ → Real.exp (-ε) ≤ ‖P s z‖ := by
    have huc := Metric.uniformContinuousOn_iff.mp
      ((isCompact_closedBall (0 : ℂ) 1).uniformContinuousOn_of_continuous
        (continuousOn_partialBlaschkeProduct m s))
    obtain ⟨δ, hδ, hδP⟩ := huc (1 - Real.exp (-ε)) (by
      have := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hε)
      linarith)
    refine ⟨max (1 - δ) 0, max_lt (by linarith) one_pos, le_max_right _ _, fun z hz hρz => ?_⟩
    have hz0 : 0 < ‖z‖ := (le_max_right _ _).trans_lt hρz
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    -- Compare with the radial projection `w = z / |z|` on the circle.
    set w : ℂ := (‖z‖⁻¹ : ℝ) • z
    have hw : ‖w‖ = 1 := by
      simp [w, inv_mul_cancel₀ hz0.ne']
    have hdist : dist z w < δ := by
      have : z - w = (1 - ‖z‖⁻¹ : ℝ) • z := by simp [w, sub_smul]
      rw [dist_eq_norm, this, norm_smul, Real.norm_eq_abs,
        abs_of_nonpos (by rw [sub_nonpos]; exact one_le_inv₀ hz0 |>.mpr hz1.le)]
      have : (-(1 - ‖z‖⁻¹)) * ‖z‖ = 1 - ‖z‖ := by field_simp; ring
      rw [this]
      linarith [le_max_left (1 - δ) 0]
    have hwmem : w ∈ closedBall (0 : ℂ) 1 := by simp [hw]
    have := hδP z (ball_subset_closedBall hz) w hwmem hdist
    rw [dist_eq_norm] at this
    have htri := norm_sub_norm_le (P s w) (P s z)
    rw [norm_sub_rev] at this
    rw [hPnorm s w (mem_sphere_zero_iff_norm.mpr hw)] at htri
    linarith
  -- Garnett: near the circle, `mean of log |f| = mean of log |B_n| + mean of log |f / B_n|`,
  -- where the first term is `≥ -ε` and the second is `≥ log |(f / B_n)(0)|`.
  have hlower (s : Finset (ball (0 : ℂ) 1)) (hG0 : G s 0 ≠ 0) (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ r in 𝓝[<] (1 : ℝ), -ε + Real.log ‖G s 0‖ ≤ A r := by
    obtain ⟨ρ, hρ1, hρ0, hρ⟩ := hPnear s ε hε
    filter_upwards [Ioo_mem_nhdsLT hρ1] with r hr
    have hr' : r ∈ Ioo (0 : ℝ) 1 := ⟨hρ0.trans_lt hr.1, hr.2⟩
    have hsph : sphere (0 : ℂ) |r| ⊆ ball 0 1 := sphere_subset_closedBall.trans (hcb hr')
    have hms : BlaschkeCondition
        ((insert 0 (Subtype.val '' (s : Set (ball (0 : ℂ) 1))))ᶜ.indicator m) :=
      hm.mono (Set.indicator_le_self _ _)
    have hGan : AnalyticOnNhd ℂ (G s) (ball 0 1) := analyticOnNhd_blaschkeProduct hms
    have hPz : ∀ z ∈ sphere (0 : ℂ) |r|, Real.exp (-ε) ≤ ‖P s z‖ := fun z hz =>
      hρ z (hsph hz) (by
        rw [mem_sphere_zero_iff_norm, abs_of_pos hr'.1] at hz
        rw [hz]
        exact hr.1)
    have hPne : ∀ z ∈ sphere (0 : ℂ) |r|, P s z ≠ 0 := fun z hz h => by
      have := hPz z hz
      rw [h, norm_zero] at this
      exact (Real.exp_pos _).not_ge this
    have hPint : CircleIntegrable (fun z => Real.log ‖P s z‖) 0 r :=
      (((continuousOn_partialBlaschkeProduct m s).mono (sphere_subset_closedBall.trans
        (closedBall_subset_closedBall (by rw [abs_of_pos hr'.1]; exact hr'.2.le)))).norm.log
        (fun z hz => norm_ne_zero_iff.mpr (hPne z hz))).circleIntegrable'
    have hGint : CircleIntegrable (fun z => Real.log ‖G s z‖) 0 r :=
      (AnalyticOnNhd.meromorphicOn (hGan.mono hsph)).circleIntegrable_log_norm
    -- `log |f| = log |P s| + log |G s|` off the isolated zeros of `G s`.
    have hGcod : ∀ᶠ z in codiscreteWithin (sphere (0 : ℂ) |r|), G s z ≠ 0 :=
      codiscreteWithin_mono hsph ((hGan.eqOn_zero_or_eventually_ne_zero_of_preconnected
        (convex_ball (0 : ℂ) 1).isPreconnected).resolve_left fun h => hG0 (h h0))
    have hsplit : A r = Real.circleAverage (fun z => Real.log ‖P s z‖) 0 r +
        Real.circleAverage (fun z => Real.log ‖G s z‖) 0 r := by
      rw [← Real.circleAverage_add hPint hGint]
      apply Real.circleAverage_congr_codiscreteWithin _ hr'.1.ne'
      filter_upwards [hGcod, self_mem_codiscreteWithin (sphere (0 : ℂ) |r|)] with z hGz hz
      simp only [Pi.add_apply]
      rw [hnorm_f, show F z = P s z * G s z from blaschkeProduct_eq_partialProd_mul hm s (hsph hz),
        norm_mul, Real.log_mul (norm_ne_zero_iff.mpr (hPne z hz)) (norm_ne_zero_iff.mpr hGz)]
    have hPmean : -ε ≤ Real.circleAverage (fun z => Real.log ‖P s z‖) 0 r := by
      have := Real.circleAverage_mono (circleIntegrable_const (-ε) 0 r) hPint (fun z hz => by
        rw [Real.le_log_iff_exp_le (norm_pos_iff.mpr (hPne z hz))]
        exact hPz z hz)
      simpa [Real.circleAverage_const] using this
    rw [hsplit]
    exact add_le_add hPmean (hjensen (G s) r hr'.1 (hGan.mono (hcb hr')) hG0)
  -- Garnett: choose `B_n` with `|(f / B_n)(0)|` close to one.
  have htail := tendsto_blaschkeProduct_tail_zero hm
  have hGt : Tendsto (fun s => ‖G s 0‖) atTop (𝓝 1) := by simpa [G] using htail.norm
  have hlogG : Tendsto (fun s => Real.log ‖G s 0‖) atTop (𝓝 0) := by
    have h := (Real.continuousAt_log one_ne_zero).tendsto.comp hGt
    rw [Real.log_one] at h
    exact h
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · obtain ⟨s, hs, hs0⟩ := ((hlogG.eventually (lt_mem_nhds (by linarith : a / 2 < 0))).and
      (htail.eventually_ne one_ne_zero)).exists
    filter_upwards [hlower s hs0 (-a / 4) (by linarith)] with r hr
    linarith
  · filter_upwards [Ioo_mem_nhdsLT (zero_lt_one' ℝ)] with r hr
    exact (hupper r hr).trans_lt hb

/-- **Theorem 2.4, (b) ↔ (c).** For an analytic function bounded in modulus by one,
radial logarithmic means tend to zero if and only if zero is the least harmonic majorant
of its logarithmic modulus. -/
theorem tendsto_withBotRadialMean_logNormBot_iff_isLeastHarmonicMajorant_zero
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (ball 0 1))
    (hbound : ∀ z ∈ ball 0 1, ‖f z‖ ≤ 1) :
    Tendsto (fun r => withBotRadialMean (logNormBot ∘ f) r) (𝓝[<] 1) (𝓝 0) ↔
      IsLeastHarmonicMajorant 0 (logNormBot ∘ f) (ball 0 1) := by
  -- codex without review
  have hzero : IsHarmonicMajorant 0 (logNormBot ∘ f) (ball 0 1) := by
    refine ⟨InnerProductSpace.harmonicOnNhd_const 0, ?_⟩
    intro z hz
    by_cases hfz : f z = 0
    · simp [logNormBot, hfz]
    · simpa [Function.comp_def, logNormBot, hfz] using
        (Real.log_nonpos (norm_nonneg (f z)) (hbound z hz))
  have h0 : (0 : ℂ) ∈ ball 0 1 := by simp
  have hr_pos : ∀ᶠ r : ℝ in 𝓝[<] 1, 0 < r :=
    (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  by_cases hne : ∃ z ∈ ball (0 : ℂ) 1, (logNormBot ∘ f) z ≠ ⊥
  swap
  · -- If `log ‖f‖ ≡ ⊥` on the disc, both sides fail: the radial means are `⊥`, and the
    -- harmonic majorant `-1` lies below `0`.
    push Not at hne
    refine iff_of_false (fun hmean0 => ?_) (fun hz => ?_)
    · have hbot : ∀ᶠ r : ℝ in 𝓝[<] 1, withBotRadialMean (logNormBot ∘ f) r = ⊥ := by
        filter_upwards [hr_pos, self_mem_nhdsWithin] with r hr hr1
        unfold withBotRadialMean withBotIntegral
        rw [ite_eq_right]
        rintro ⟨hnull, -⟩
        have huniv : angularMeasure (univ : Set ℝ) = 0 :=
          MeasureTheory.measure_mono_null
            (fun θ _ => hne _ (radial_point_mem_unitDisc hr hr1)) hnull
        simp at huniv
      have := tendsto_nhds_unique (tendsto_const_nhds.congr' (hbot.mono fun r hr => hr.symm))
        hmean0
      simp at this
    · have hneg : IsHarmonicMajorant (fun _ => -1) (logNormBot ∘ f) (ball 0 1) :=
        ⟨InnerProductSpace.harmonicOnNhd_const (-1), fun z hz' => by rw [hne z hz']; exact bot_le⟩
      have := hz.2 _ hneg 0 h0
      norm_num at this
  obtain ⟨u, hu, hlim⟩ := exists_isLeastHarmonicMajorant_tendsto_poissonModification
    (logNormBot_comp_analytic_subharmonicOn_scalar isOpen_ball hf.analyticOn) hne
    ⟨0, hzero⟩
  have hmean : Tendsto (fun r => withBotRadialMean (logNormBot ∘ f) r)
      (𝓝[<] 1) (𝓝 (u 0 : WithBot ℝ)) := by
    apply (hlim 0 h0).congr'
    filter_upwards [hr_pos] with r hr
    exact poissonModification_zero_eq_withBotRadialMean _ hr
  constructor
  · intro hmean0
    have hu0 : u 0 = 0 := by
      exact_mod_cast tendsto_nhds_unique hmean hmean0
    have hle : ∀ z ∈ ball 0 1, u z ≤ 0 := hu.2 0 hzero
    obtain ⟨c, hc⟩ := harmonic_maximum_minimum_principle_general
      isOpen_ball (convex_ball (0 : ℂ) 1).isPreconnected hu.1.1
      (Or.inl ⟨0, h0, fun z hz => (hle z hz).trans_eq hu0.symm⟩)
    have hueq : ∀ z ∈ ball 0 1, u z = 0 := fun z hz =>
      (hc z hz).trans ((hc 0 h0).symm.trans hu0)
    refine ⟨hzero, fun v hv z hz => ?_⟩
    simpa only [hueq z hz, Pi.zero_apply] using hu.2 v hv z hz
  · intro hz
    have hu0 : u 0 = 0 := le_antisymm (hu.2 0 hzero 0 h0) (hz.2 u hu.1 0 h0)
    simpa only [hu0, WithBot.coe_zero] using hmean
