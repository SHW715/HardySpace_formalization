import Mathlib.Analysis.Complex.CanonicalDecomposition
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.Analysis.Complex.LocallyUniformLimit
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

/-- The multiplicity function, which counts the number of occurrences of a point in a family,
with value `∞` for infinitely many. -/
def Multiplicity {ι : Type*} (a : ι → ℂ) (z : ℂ) : ℕ∞ := (a ⁻¹' {z}).encard

/-- The Blaschke sum of a multiplicity function on the unit disc.
For an analytic function use `m := analyticOrderAt f`; for a family `a : ι → ℂ`
use `m := Multiplicity a`. -/
def blaschkeSum (m : ℂ → ℕ∞) : ℝ≥0∞ := ∑' z : ball (0 : ℂ) 1, (m z) * (1 - ‖z.1‖ₑ)

/-- A multiplicity function satisfies the Blaschke condition on the unit disc if its
Blaschke sum is finite. For a family of points, membership in the unit disc is a separate
assumption. -/
def BlaschkeCondition (m : ℂ → ℕ∞) : Prop := blaschkeSum m < ∞

/-- A sequence counted with multiplicities satisfy the Blaschke condition has only finitely many
zero terms. -/
theorem zeroIndexSet_finite {z : ℕ → ℂ} (hz : BlaschkeCondition (Multiplicity z)) :
    (z ⁻¹'{0}).Finite := by
  have hterm : (Multiplicity z 0 : ℝ≥0∞) ≤ blaschkeSum (Multiplicity z) := by
    simpa [blaschkeSum] using ENNReal.le_tsum
      (f := fun w : ball (0 : ℂ) 1 => Multiplicity z w * (1 - ‖w.1‖ₑ))
      ⟨0, by simp⟩
  apply Set.encard_ne_top_iff.mp
  intro h
  have hfinite := hterm.trans_lt hz
  simp [Multiplicity, h] at hfinite


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

#check divisor


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
    rw [Real.circleAverage_congr_codiscreteWithin heq hr.ne', ← HarmonicOnNhd.circleAverage_eq (hu.1.1.mono hsub)]
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
      rw [if_pos rfl]
      change analyticOrderAt (id ^ n : ℂ → ℂ) 0 = n
      simp [analyticOrderAt_pow analyticAt_id, nsmul_eq_mul]
    · rw [if_neg hz0, hp.analyticOrderAt_eq_zero.mpr (pow_ne_zero _ hz0)]
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

/-- The products omitting zero terms converge locally uniformly on the unit disc. -/
lemma tendstoLocallyUniformlyOn_blaschkeProductFactor {a : ℕ → ℂ}
    (ha : ∀ n, a n ∈ ball 0 1) (hsum : BlaschkeCondition (Multiplicity a)) :
    TendstoLocallyUniformlyOn
      (fun N w => ∏ n ∈ Finset.range N, blaschkeProductFactor a n w)
      (fun w => ∏' n, blaschkeProductFactor a n w) atTop (ball 0 1) := by
  sorry

/-- The finite products, including the full power accounting for zeros at the origin,
converge locally uniformly to the Blaschke product on the unit disc. -/
theorem tendstoLocallyUniformlyOn_blaschkeProduct {a : ℕ → ℂ}
    (ha : ∀ n, a n ∈ ball 0 1) (hsum : BlaschkeCondition (Multiplicity a)) :
    TendstoLocallyUniformlyOn
      (fun N w => w ^ (a ⁻¹' {0}).ncard *
        ∏ n ∈ Finset.range N, blaschkeProductFactor a n w)
      (BlaschkeProduct a) atTop (ball 0 1) := by
  -- codex with review
  have hconv := Metric.tendstoLocallyUniformlyOn_iff.mp
    (tendstoLocallyUniformlyOn_blaschkeProductFactor ha hsum)
  apply Metric.tendstoLocallyUniformlyOn_iff.mpr
  intro ε hε z hz
  obtain ⟨t, ht, hN⟩ := hconv ε hε z hz
  refine ⟨t ∩ ball 0 1, inter_mem ht self_mem_nhdsWithin, ?_⟩
  filter_upwards [hN] with N hN w hw
  have hw1 : ‖w‖ ≤ 1 := (mem_ball_zero_iff.mp hw.2).le
  simp only [BlaschkeProduct, dist_eq_norm, ← mul_sub, norm_mul, norm_pow]
  refine lt_of_le_of_lt ?_ (hN w hw.1)
  rw [dist_eq_norm]
  exact mul_le_of_le_one_left (norm_nonneg (_ : ℂ)) (pow_le_one₀ (norm_nonneg w) hw1)

/-- A Blaschke product is analytic on the unit disc. -/
theorem analyticOnNhd_blaschkeProduct {a : ℕ → ℂ}
    (ha : ∀ n, a n ∈ ball 0 1) (hsum : BlaschkeCondition (Multiplicity a)) :
    AnalyticOnNhd ℂ (BlaschkeProduct a) (ball 0 1) := by
  -- codex without review
  have hfactor (n : ℕ) : DifferentiableOn ℂ (blaschkeProductFactor a n) (ball 0 1) := by
    intro z hz
    by_cases hn : a n = 0
    · simp only [blaschkeProductFactor, hn, if_pos]
      fun_prop
    · have hnorm : ‖conj (a n) * z‖ < 1 := by
        rw [norm_mul, norm_conj]
        nlinarith [mem_ball_zero_iff.mp (ha n), mem_ball_zero_iff.mp hz,
          norm_nonneg (a n), norm_nonneg z]
      have hden : 1 - conj (a n) * z ≠ 0 := by
        intro h
        rw [← sub_eq_zero.mp h, norm_one] at hnorm
        exact (lt_irrefl _ hnorm)
      simp only [blaschkeProductFactor, normedBlaschkeFactor, if_neg hn]
      unfold BlaschkeFactor
      simp only [ofReal_one, one_pow, one_mul]
      apply DifferentiableAt.differentiableWithinAt
      fun_prop
  apply DifferentiableOn.analyticOnNhd _ isOpen_ball
  apply (tendstoLocallyUniformlyOn_blaschkeProduct ha hsum).differentiableOn _ isOpen_ball
  exact Filter.Eventually.of_forall fun N => by fun_prop

/-- A Blaschke product has modulus at most one on the unit disc. -/
theorem norm_blaschkeProduct_le_one {a : ℕ → ℂ}
    (ha : ∀ n, a n ∈ ball 0 1) (hsum : BlaschkeCondition (Multiplicity a))
    {w : ℂ} (hw : w ∈ ball 0 1) : ‖BlaschkeProduct a w‖ ≤ 1 := by
  -- codex without review
  have hfactor (n : ℕ) : ‖blaschkeProductFactor a n w‖ ≤ 1 := by
    by_cases hn : a n = 0
    · simp [blaschkeProductFactor, hn]
    · simpa [blaschkeProductFactor, normedBlaschkeFactor, hn, norm_smul, norm_div,
        norm_ne_zero_iff.mpr hn] using norm_BlaschkeFactor_one_le_one (ha n) hw
  apply le_of_tendsto ((tendstoLocallyUniformlyOn_blaschkeProduct ha hsum).tendsto_at hw).norm
  filter_upwards [] with N
  rw [norm_mul, norm_pow, norm_prod]
  exact mul_le_one₀ (pow_le_one₀ (norm_nonneg w) (mem_ball_zero_iff.mp hw).le)
    (Finset.prod_nonneg fun n _ => norm_nonneg _)
    (Finset.prod_le_one (fun n _ => norm_nonneg _) (fun n _ => hfactor n))

/-- The order at a point of the unit disc equals its number of occurrences in the sequence. -/
theorem analyticOrderAt_blaschkeProduct {a : ℕ → ℂ}
    (ha : ∀ n, a n ∈ ball 0 1) (hsum : BlaschkeCondition (Multiplicity a))
    {w : ℂ} (hw : w ∈ ball 0 1) :
    analyticOrderAt (BlaschkeProduct a) w = Multiplicity a w := by
  sorry

/-- The zeros in the unit disc are exactly the points of the defining sequence. -/
theorem blaschkeProduct_eq_zero_iff {a : ℕ → ℂ}
    (ha : ∀ n, a n ∈ ball 0 1) (hsum : BlaschkeCondition (Multiplicity a))
    {w : ℂ} (hw : w ∈ ball 0 1) :
    BlaschkeProduct a w = 0 ↔ ∃ n, a n = w := by
  have h := analyticOrderAt_ne_zero (f := BlaschkeProduct a) (z₀ := w)
  rw [analyticOrderAt_blaschkeProduct ha hsum hw, Multiplicity, Set.encard_ne_zero,
    and_iff_right (analyticOnNhd_blaschkeProduct ha hsum w hw)] at h
  exact h.symm

/-- Extended by zero outside the unit disc, a Blaschke product belongs to `H∞`. -/
theorem memHpDisc_blaschkeProduct {a : ℕ → ℂ}
    (ha : ∀ n, a n ∈ ball 0 1) (hsum : BlaschkeCondition (Multiplicity a)) :
    HardySpace.MemHpDisc ∞ ((ball 0 1).indicator (BlaschkeProduct a)) := by
  refine ⟨(analyticOnNhd_blaschkeProduct ha hsum).analyticOn.congr
    fun z hz => indicator_of_mem hz _, ?_, fun z hz => indicator_of_notMem hz _⟩
  refine lt_of_le_of_lt (iSup₂_le fun r hr => ?_) (ENNReal.ofReal_lt_top (r := 1))
  simp only [eLpNormFixed, mem_Ioo, not_top_lt, and_false, if_false,
    MeasureTheory.eLpNorm_exponent_top]
  refine MeasureTheory.eLpNormEssSup_le_of_ae_bound (MeasureTheory.ae_of_all _ fun θ => ?_)
  have hz : (r : ℂ) * exp (I * θ) ∈ ball 0 1 := radial_point_mem_unitDisc hr.1 hr.2
  rw [indicator_of_mem hz]
  exact norm_blaschkeProduct_le_one ha hsum hz

/-- A Blaschke product has nontangential boundary values of modulus one almost everywhere. -/
theorem ae_hasNontangentialLimit_blaschkeProduct {a : ℕ → ℂ}
    (ha : ∀ n, a n ∈ ball 0 1) (hsum : BlaschkeCondition (Multiplicity a)) :
    ∀ᵐ ζ ∂circleMeasure 0 1, ‖boundaryValue (BlaschkeProduct a) ζ‖ = 1 := by
  sorry
  -- can be formulated using `NontangentiallyConvergentAt`

/-! ## Theorem 2.4: (a) → (b) and (b) ↔ (c) -/

/-- **Theorem 2.4, (a) → (b).** The radial means of the logarithmic modulus of a
Blaschke product, multiplied by a unimodular constant, tend to zero. -/
theorem tendsto_withBotRadialMean_logNormBot_blaschkeProduct {a : ℕ → ℂ}
    (ha : ∀ n, a n ∈ ball 0 1) (hsum : BlaschkeCondition (Multiplicity a))
    {c : ℂ} (hc : ‖c‖ = 1) :
    Tendsto (fun r => withBotRadialMean (logNormBot ∘ (fun z => c * BlaschkeProduct a z)) r)
      (𝓝[<] 1) (𝓝 0) := by
  sorry

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
        rw [if_neg]
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
