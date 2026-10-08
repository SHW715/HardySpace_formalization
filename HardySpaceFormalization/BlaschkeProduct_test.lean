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

-- # Useless definition, hard to work on this.
/-- An effective divisor on `U` is a nonnegative integer-valued divisor with locally finite
support contained in `U`. -/
abbrev EffectiveDivisor (U : Set ℂ) := {D : Function.locallyFinsuppWithin U ℤ // 0 ≤ D}

/-- The Blaschke sum of the positive part of a divisor, restricted to the unit disc.
Negative coefficients are ignored by `Int.toNat`. -/
def blaschkeSum {U : Set ℂ} (D : Function.locallyFinsuppWithin U ℤ) : ℝ≥0∞ :=
  ∑' z : ball (0 : ℂ) 1, (D z).toNat * (1 - ‖z.1‖ₑ)

/-- A divisor satisfies the Blaschke condition if its Blaschke sum is finite.
Nonnegativity of the divisor is a separate assumption. -/
def BlaschkeCondition {U : Set ℂ} (D : Function.locallyFinsuppWithin U ℤ) : Prop :=
  blaschkeSum D < ∞


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

/-- The normalized Blaschke factor at `a` raised to the power `(D a).toNat`.
Negative coefficients are ignored. The point `0` is accounted for separately in `BlaschkeProduct`. -/
noncomputable def blaschkeProductFactor {U : Set ℂ}
  (D : Function.locallyFinsuppWithin U ℤ) (a : ℂ) : ℂ → ℂ :=
  if a = 0 then 1 else fun w ↦ normedBlaschkeFactor 1 a w ^ (D a).toNat

/-- The Blaschke product of the positive part of a divisor, restricted to the unit disc.
The origin contributes `w ^ (D 0).toNat`; other points contribute their normalized factors
raised to `(D a).toNat`. Negative coefficients and points outside the unit disc are ignored. -/
noncomputable def BlaschkeProduct {U : Set ℂ} (D : Function.locallyFinsuppWithin U ℤ) : ℂ → ℂ :=
  fun w ↦ w ^ (D 0).toNat * ∏' a : ball (0 : ℂ) 1, blaschkeProductFactor D a w

variable {f : ℂ → ℂ}
#check BlaschkeCondition (divisor f (ball 0 1)) -- But the issue is that this `BlaschkeCondition` can not rule out `f ≡ 0`.
-- But in Garnett's book, he didn't rule out `f ≡ 0` either.
#check BlaschkeProduct (divisor f (ball 0 1))


-- The proofs of the rest codes are given by codex without fully review


/-- **Theorem 2.1 (second part).** If `f` is analytic on the unit disc, not identically zero, and
`log ‖f‖` has a harmonic majorant on the disc, and moreover `f 0 ≠ 0` and `u` is the least harmonic
majorant of `log ‖f‖` on the disc, then the Blaschke sum is bounded by `u 0 - log ‖f 0‖`. -/
theorem blaschkeSum_le_of_isLeastHarmonicMajorant
    {f : ℂ → ℂ} (hf : AnalyticOn ℂ f (ball 0 1)) (hf0 : f 0 ≠ 0)
    {u : ℂ → ℝ} (hu : IsLeastHarmonicMajorant u (logNormBot ∘ f) (ball 0 1)) :
    blaschkeSum (divisor f (ball 0 1)) ≤ ENNReal.ofReal (u 0 - Real.log ‖f 0‖) := by sorry



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
    (hgB : BlaschkeCondition (divisor g (ball 0 1))) (hg : AnalyticOnNhd ℂ g (ball 0 1))
    (hfg : ∀ z ∈ ball 0 1, f z = z ^ n * g z) : BlaschkeCondition (divisor f (ball 0 1)) := by sorry

/-- **Theorem 2.1 (first part).** If `f` is analytic on the unit disc, not identically zero, and
`log ‖f‖` has a harmonic majorant on the disc, then the zeros
of `f`, counted with multiplicity, satisfy the Blaschke condition `∑ (1 - ‖zₙ‖) < ∞`.
-/
theorem blaschkeCondition_of_hasHarmonicMajorant {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (ball 0 1)) (hf_ne : ∃ z ∈ ball 0 1, f z ≠ 0)
    (hmaj : HasHarmonicMajorant (logNormBot ∘ f) (ball 0 1)) :
    BlaschkeCondition (divisor f (ball 0 1)) := by sorry


/-! ## Theorem 2.2: convergence, zeros, and boundary values of Blaschke products -/

/-- The products over finite subsets of the unit disc, omitting the origin factor,
converge locally uniformly as the finite subsets increase by inclusion. -/
lemma tendstoLocallyUniformlyOn_blaschkeProductFactor
    {D : Function.locallyFinsuppWithin (ball 0 1) ℤ}
    (hD : 0 ≤ D) (hsum : BlaschkeCondition D) :
    TendstoLocallyUniformlyOn
      (fun (s : Finset (ball (0 : ℂ) 1)) w => ∏ a ∈ s, blaschkeProductFactor D a w)
      (fun w => ∏' a : ball (0 : ℂ) 1, blaschkeProductFactor D a w)
      atTop (ball 0 1) := by
  sorry

/-- The finite products, including the full power accounting for zeros at the origin,
converge locally uniformly to the Blaschke product on the unit disc. -/
theorem tendstoLocallyUniformlyOn_blaschkeProduct
    {D : Function.locallyFinsuppWithin (ball (0 : ℂ) 1) ℤ}
    (hD : 0 ≤ D) (hsum : BlaschkeCondition D) :
    TendstoLocallyUniformlyOn
      (fun (s : Finset (ball (0 : ℂ) 1)) w => w ^ (D 0).toNat *
        ∏ a ∈ s, blaschkeProductFactor D a w)
      (BlaschkeProduct D) atTop (ball 0 1) := by
  sorry

/-- A Blaschke product is analytic on the unit disc. -/
theorem analyticOnNhd_blaschkeProduct
    {D : Function.locallyFinsuppWithin (ball (0 : ℂ) 1) ℤ}
    (hD : 0 ≤ D) (hsum : BlaschkeCondition D) :
    AnalyticOnNhd ℂ (BlaschkeProduct D) (ball 0 1) := by
  sorry

/-- A Blaschke product has modulus at most one on the unit disc. -/
theorem norm_blaschkeProduct_le_one
    {D : Function.locallyFinsuppWithin (ball (0 : ℂ) 1) ℤ}
    (hD : 0 ≤ D) (hsum : BlaschkeCondition D)
    {w : ℂ} (hw : w ∈ ball 0 1) : ‖BlaschkeProduct D w‖ ≤ 1 := by
  sorry

/-- The order at a point of the unit disc equals its coefficient in the nonnegative divisor. -/
theorem analyticOrderAt_blaschkeProduct
    {D : Function.locallyFinsuppWithin (ball (0 : ℂ) 1) ℤ}
    (hD : 0 ≤ D) (hsum : BlaschkeCondition D)
    {w : ℂ} (hw : w ∈ ball 0 1) :
    analyticOrderAt (BlaschkeProduct D) w = ((D w).toNat : ℕ∞) := by
  sorry

/-- The zeros in the unit disc are exactly the points with positive divisor coefficient. -/
theorem blaschkeProduct_eq_zero_iff
    {D : Function.locallyFinsuppWithin (ball (0 : ℂ) 1) ℤ}
    (hD : 0 ≤ D) (hsum : BlaschkeCondition D)
    {w : ℂ} (hw : w ∈ ball 0 1) :
    BlaschkeProduct D w = 0 ↔ 0 < D w := by
  sorry

/-- Extended by zero outside the unit disc, a Blaschke product belongs to `H∞`. -/
theorem memHpDisc_blaschkeProduct
    {D : Function.locallyFinsuppWithin (ball (0 : ℂ) 1) ℤ}
    (hD : 0 ≤ D) (hsum : BlaschkeCondition D) :
    HardySpace.MemHpDisc ∞ ((ball 0 1).indicator (BlaschkeProduct D)) := by
  sorry

/-- A Blaschke product has nontangential boundary values of modulus one almost everywhere. -/
theorem ae_hasNontangentialLimit_blaschkeProduct
    {D : Function.locallyFinsuppWithin (ball (0 : ℂ) 1) ℤ}
    (hD : 0 ≤ D) (hsum : BlaschkeCondition D) :
    ∀ᵐ ζ ∂circleMeasure 0 1, ‖boundaryValue (BlaschkeProduct D) ζ‖ = 1 := by
  sorry
  -- can be formulated using `NontangentiallyConvergentAt`

/-! ## Theorem 2.4: (a) → (b) and (b) ↔ (c) -/

/-- **Theorem 2.4, (a) → (b).** The radial means of the logarithmic modulus of a
Blaschke product, multiplied by a unimodular constant, tend to zero. -/
theorem tendsto_withBotRadialMean_logNormBot_blaschkeProduct
    {D : Function.locallyFinsuppWithin (ball (0 : ℂ) 1) ℤ}
    (hD : 0 ≤ D) (hsum : BlaschkeCondition D)
    {c : ℂ} (hc : ‖c‖ = 1) :
    Tendsto (fun r => withBotRadialMean (logNormBot ∘ (fun z => c * BlaschkeProduct D z)) r)
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
