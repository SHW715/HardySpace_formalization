import HardySpaceFormalization.HardySpaceDisc
import Mathlib.Analysis.Complex.LocallyUniformLimit


/-!
# Completeness of Hardy Space over unit disc in ℂ

-/

-- currently I still need results: `‖f‖ ^ p` is subharmonic for `f` analytic
-- which is still working on `Subharmonic.lean`

noncomputable section

open scoped Real ENNReal Topology
open MeasureTheory Real Complex Set Filter


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A locally uniform limit of analytic functions on an open set is analytic. -/
theorem TendstoLocallyUniformlyOn.analyticOn {ι : Type*} {φ : Filter ι}
    [φ.NeBot] [CompleteSpace E] {U : Set ℂ} {F : ι → ℂ → E} {f : ℂ → E}
    (hf : TendstoLocallyUniformlyOn F f φ U)
    (hF : ∀ᶠ n in φ, AnalyticOn ℂ (F n) U) (hU : IsOpen U) :
    AnalyticOn ℂ f U := by
  have hdiff : DifferentiableOn ℂ f U :=
    hf.differentiableOn (hF.mono fun _ hn => hn.differentiableOn) hU
  exact hdiff.analyticOn hU

namespace HardySpace
namespace HpDisc

instance instNorm (p : ℝ≥0∞) : Norm (HpDisc (E := E) p) where
  norm f := (hardyNorm (E := E) f.1 p).toReal

instance instDist (p : ℝ≥0∞) : Dist (HpDisc (E := E) p) where
  dist f g := ‖-f + g‖

instance instEDist (p : ℝ≥0∞) : EDist (HpDisc (E := E) p) where
  edist f g := hardyNorm (E := E) (f.1 - g.1) p

@[simp] lemma norm_def (p : ℝ≥0∞) (f : HpDisc (E := E) p) :
    ‖f‖ = (hardyNorm (E := E) f.1 p).toReal := by rfl

@[simp] lemma norm_zero (p : ℝ≥0∞) :
    ‖(0 : HpDisc (E := E) p)‖ = 0 := by
  by_cases hp : p ∈ Ioo (0 : ℝ≥0∞) 1
  · have hpt : 0 < p.toReal := ENNReal.toReal_pos hp.1.ne' (ne_of_lt (hp.2.trans ENNReal.one_lt_top))
    simp [hardyNorm, eLpNormFixed, hp, ENNReal.zero_rpow_of_pos hpt]
  · simp [hardyNorm, eLpNormFixed, hp]

@[simp] lemma norm_neg (p : ℝ≥0∞) (f : HpDisc (E := E) p) :
    ‖-f‖ = ‖f‖ := by
  simp [hardyNorm]
  congr; ext r; congr; ext hr
  exact eLpNormFixed_neg (fun θ : ℝ => f.1 (r * exp (I * θ))) p
    (ENNReal.ofReal (π⁻¹ * 2⁻¹) • volume.restrict (Ico 0 (2 * π)))

lemma norm_add_le (p : ℝ≥0∞) (f g : HpDisc (E := E) p) :
    ‖f + g‖ ≤ ‖f‖ + ‖g‖ := by
  rcases f.2 with ⟨hf_an, ⟨hf_norm, _⟩⟩
  rcases g.2 with ⟨hg_an, ⟨hg_norm, _⟩⟩
  simp [norm_def]; exact ENNReal.toReal_le_add (hardyNorm_add_le hf_an hg_an) hf_norm.ne hg_norm.ne


lemma norm_eq_zero_iff (p : ℝ≥0∞)
    {f : HpDisc (E := E) p} [Fact (1 ≤ p)] : ‖f‖ = 0 ↔ f = 0 := by
  constructor
  . intro h; simp [norm_def] at h
    -- This part is given by codex without review
    have hp_ne_zero : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out))
    have hpunctured : ∀ z ∈ unitDisc, z ≠ 0 → f.1 z = 0 := by
      intro z hz hz0
      rcases exists_radial_repr_of_mem_unitDisc_ne_zero hz hz0 with
        ⟨r, θ, hr0, hr1, hθ, hz_repr⟩
      let μ : Measure ℝ := ENNReal.ofReal (1 / (2 * π)) • volume.restrict (Ico 0 (2 * π))
      have hradial_zero : eLpNormFixed (fun θ : ℝ => f.1 (r * exp (I * θ))) p μ = 0 := by
        have hHardy : hardyNorm f.1 p = 0 := by
          rcases (ENNReal.toReal_eq_zero_iff (hardyNorm f.1 p)).1 h with hzero | htop
          · exact hzero
          · exfalso; exact (ne_of_lt f.2.2.1) htop
        have hle : eLpNormFixed (fun θ : ℝ => f.1 (r * exp (I * θ))) p μ ≤ hardyNorm f.1 p := by
          unfold hardyNorm
          exact (le_iSup (fun hr : 0 < r ∧ r < 1 => eLpNormFixed
          (fun θ : ℝ => f.1 (r * exp (I * θ))) p μ) ⟨hr0, hr1⟩).trans
           (le_iSup (fun r : ℝ => ⨆ (_ : 0 < r ∧ r < 1), eLpNormFixed
           (fun θ : ℝ => f.1 (r * exp (I * θ))) p μ) r)
        exact le_antisymm (by simpa [hHardy] using hle) bot_le
      have hmeas : AEStronglyMeasurable (fun θ : ℝ => f.1 (r * exp (I * θ))) μ :=
        radial_aestronglyMeasurable f.2.1.continuousOn ⟨hr0, hr1⟩ μ
      have hzero : f.1 (r * exp (I * θ)) = 0 := by
        have hc : ENNReal.ofReal (1 / (2 * π)) ≠ 0 := by
          exact ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))
        have hae : (fun θ : ℝ => f.1 (r * exp (I * θ))) =ᵐ[
              volume.restrict (Ico 0 (2 * π))] 0 := by
          exact (MeasureTheory.Measure.ae_ennreal_smul_measure_iff hc).1
            ((eLpNormFixed_eq_zero_iff hmeas hp_ne_zero).1 hradial_zero)
        have hcont : Continuous (fun θ : ℝ => f.1 (r * exp (I * θ))) :=
          radial_cont f.2.1.continuousOn ⟨hr0, hr1⟩
        have hEqOn : EqOn (fun θ : ℝ => f.1 (r * exp (I * θ))) 0 (Ico 0 (2 * π)) := by
          exact Measure.eqOn_of_ae_eq hae hcont.continuousOn continuous_const.continuousOn
             (Ico_subset_closure_interior 0 (2 * π))
        exact hEqOn hθ
      simpa [hz_repr] using hzero
    have hpunctured' : ∀ z ≠ 0, f.1 z = 0 := by
      intro z hz0
      by_cases hz : z ∈ unitDisc
      · exact hpunctured z hz hz0
      · exact f.2.2.2 z hz
    have hcont : Continuous f.1 := by
      rw [continuous_iff_continuousAt]
      intro z
      by_cases hz0 : z = 0
      · subst z
        have h0_mem : 0 ∈ unitDisc := by simp [unitDisc]
        exact f.2.1.continuousOn.continuousAt (Metric.isOpen_ball.mem_nhds h0_mem)
      · have hnear : f.1 =ᶠ[nhds z] fun _ : ℂ => (0 : E) := by
          filter_upwards [isOpen_ne.mem_nhds hz0] with y hy
          exact hpunctured' y hy
        exact continuousAt_const.congr hnear.symm
    have hf_zero_ae : f.1 =ᵐ[volume] 0 := by
      filter_upwards [Measure.ae_ne (volume : Measure ℂ) (0 : ℂ)] with z hz
      exact hpunctured' z hz
    ext z
    exact congr_fun (Measure.eq_of_ae_eq hf_zero_ae hcont continuous_const) z
  . intro h; rw [h]; exact norm_zero p

lemma dist_eq_norm (p : ℝ≥0∞) (f g : HpDisc (E := E) p) :
    dist f g = ‖-f + g‖ := by rfl

lemma dist_self (p : ℝ≥0∞) (f : HpDisc (E := E) p) :
    dist f f = 0 := by rw [dist_eq_norm, neg_add_cancel f]; simp only [norm_zero]

lemma dist_comm (p : ℝ≥0∞) (f g : HpDisc (E := E) p) :
    dist f g = dist g f := by
  simp_rw [dist_eq_norm]; simpa [add_comm] using (norm_neg p (-g + f))

lemma dist_triangle (p : ℝ≥0∞) (f g h : HpDisc (E := E) p) :
    dist f h ≤ dist f g + dist g h := by
  simp_rw [dist_eq_norm]
  have hfgh : -f + h = (-f + g) + (-g + h) := by abel
  rw [hfgh]; exact norm_add_le p (-f + g) (-g + h)

lemma eq_of_dist_eq_zero (p : ℝ≥0∞) {f g : HpDisc (E := E) p}
  (hfg : dist f g = 0) [Fact (1 ≤ p)] : f = g := by
  rw [dist_eq_norm] at hfg
  have hsub : g - f = 0 := by
    simpa [sub_eq_add_neg, add_comm] using ((norm_eq_zero_iff p).1 hfg : -f + g = 0)
  simpa [eq_comm] using (sub_eq_zero.mp hsub : g = f)

instance instMetricSpace (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    MetricSpace (HpDisc (E := E) p) where
  dist := dist
  dist_self := dist_self p
  dist_comm := dist_comm p
  dist_triangle := dist_triangle p
  eq_of_dist_eq_zero := fun {x y} h => eq_of_dist_eq_zero p h

/-The following instances are given helped by codex, in order to make the notion 'completeness' w.r.t. Hardy norm.-/
instance (priority := 1000) instUniformSpace (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    UniformSpace (HpDisc (E := E) p) :=
  PseudoMetricSpace.toUniformSpace

instance (priority := 1000) instTopologicalSpace (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    TopologicalSpace (HpDisc (E := E) p) :=
  (instUniformSpace (E := E) p).toTopologicalSpace

instance instNormedAddCommGroup (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    NormedAddCommGroup (HpDisc (E := E) p) where
  dist_eq := fun _ _ => rfl

-- Here are two properties of Hardy norm and distance:

lemma norm_eval_le_norm_top
    (f : HpDisc (E := E) ∞) {z : ℂ} (hz : z ∈ unitDisc) :
    ‖f.1 z‖ ≤ ‖f‖ := by
  rw [norm_def]
  have hle_enorm : ‖f.1 z‖ₑ ≤ hardyNorm f.1 ∞ := by
    rw [hardyNorm_top_eq_Sup_norm f.2.1.continuousOn]
    exact le_iSup (fun w : unitDisc => ‖f.1 w.1‖ₑ) ⟨z, hz⟩
  have hfin : hardyNorm f.1 ∞ ≠ ∞ := ne_of_lt f.2.2.1
  calc
    ‖f.1 z‖ = (‖f.1 z‖ₑ).toReal := by simp
    _ ≤ (hardyNorm f.1 ∞).toReal := ENNReal.toReal_mono hfin hle_enorm

lemma norm_sub_eval_le_dist_top
    (f g : HpDisc (E := E) ∞) {z : ℂ} (hz : z ∈ unitDisc) :
    ‖f.1 z - g.1 z‖ ≤ dist f g := by
  rw [dist_eq_norm]
  calc
    ‖f.1 z - g.1 z‖ = ‖(-g + f : HpDisc (E := E) ∞).1 z‖ := by
      simp [Pi.add_apply, sub_eq_add_neg, add_comm]
    _ ≤ ‖(-f + g : HpDisc (E := E) ∞)‖ := by
      have h := norm_eval_le_norm_top (-g + f) hz
      have hnorm :
          ‖(-g + f : HpDisc (E := E) ∞)‖ =
            ‖(-f + g : HpDisc (E := E) ∞)‖ := by
        simpa [neg_add, add_comm] using (norm_neg (E := E) ∞ (-f + g))
      exact h.trans_eq hnorm


-- # Now we'd like to prove the completeness of `H^p`:

-- First, we need some helper lemmas:

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
lemma dist_limit_le_of_eventually_dist_lt {α β : Type*} [PseudoMetricSpace β]
  {l : Filter α} [NeBot l] {x : α → β} {x₀ y : β} {C : ℝ}
  (hx : Tendsto x l (𝓝 x₀)) (hC : ∀ᶠ a in l, dist (x a) y < C) :
  dist x₀ y ≤ C := le_of_tendsto (hx.dist tendsto_const_nhds) (hC.mono fun _ h => le_of_lt h)

lemma dist_limit_eval_le_of_eventually_dist_top
    {f : Filter (HpDisc (E := E) ∞)} [NeBot f] {F : ℂ → E}
    (hF : map (fun g : HpDisc (E := E) ∞ => g.1) f ≤ 𝓝 F)
    {A : Set (HpDisc (E := E) ∞)} (hA : A ∈ f)
    {g : HpDisc (E := E) ∞} (hgA : g ∈ A) {C : ℝ}
    (hAdist : ∀ q ∈ A, ∀ r ∈ A, dist q r < C)
    {z : ℂ} (hz : z ∈ unitDisc) :
    dist (F z) (g.1 z) ≤ C := by
  have hlim_z : Tendsto (fun φ : ℂ → E => φ z)
    (map (fun g : HpDisc (E := E) ∞ => g.1) f) (𝓝 (F z)) :=
     ((continuous_apply z).tendsto F).mono_left hF
  refine dist_limit_le_of_eventually_dist_lt hlim_z ?_
  rw [eventually_map]
  filter_upwards [hA] with q hqA
  have hqz : dist (q.1 z) (g.1 z) ≤ dist q g := by
    rw [dist_eq_norm_sub]; exact norm_sub_eval_le_dist_top q g hz
  exact lt_of_le_of_lt hqz (hAdist q hqA g hgA)

lemma lipschitz_eval_top (z : ℂ) :
    LipschitzWith 1 (fun g : HpDisc (E := E) ∞ => g.1 z) := by
  refine LipschitzWith.mk_one ?_
  intro g h
  by_cases hz : z ∈ unitDisc
  · rw [dist_eq_norm_sub]; exact norm_sub_eval_le_dist_top g h hz
  · simp [g.2.2.2 z hz, h.2.2.2 z hz]

lemma uniformContinuous_coe_top :
    UniformContinuous (fun g : HpDisc (E := E) ∞ => g.1) := by
  rw [uniformContinuous_pi]
  intro z; exact (lipschitz_eval_top z).uniformContinuous

-- # remember to fill in the `_ne_top` case for above 4 lemmas

lemma tendstoLocallyUniformlyOn_of_cauchy_tendsto_ne_top
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp_ne_top : p ≠ ∞)
    {f : Filter (HpDisc (E := E) p)} {Ffun : ℂ → E}
    (hf : Cauchy f)
    (hFfun : map (fun g : HpDisc (E := E) p => g.1) f ≤ 𝓝 Ffun) :
    TendstoLocallyUniformlyOn
      (fun g : HpDisc (E := E) p => g.1) Ffun f unitDisc := by
  sorry


lemma tendstoLocallyUniformlyOn_of_cauchy_tendsto_top
    {f : Filter (HpDisc (E := E) ∞)} {F : ℂ → E} (hf : Cauchy f)
    (hF : map (fun g : HpDisc (E := E) ∞ => g.1) f ≤ 𝓝 F) :
    TendstoLocallyUniformlyOn
      (fun g : HpDisc (E := E) ∞ => g.1) F f unitDisc := by
  -- This is given by codex after revision
  rw [Metric.tendstoLocallyUniformlyOn_iff]
  intro ε hε x hx
  let δ : ℝ := ε / 2
  have hδpos : 0 < δ := by positivity
  have hδlt : δ < ε := by dsimp[δ]; linarith
  rcases Metric.cauchy_iff.1 hf with ⟨hf_NeBot, hf_Cauchy⟩
  rcases hf_Cauchy δ hδpos with ⟨A, hA, hAdist⟩
  refine ⟨unitDisc, self_mem_nhdsWithin, ?_⟩
  filter_upwards [hA] with g hgA
  intro y hy
  have hle : dist (F y) (g.1 y) ≤ δ := by
    haveI : NeBot f := hf_NeBot
    exact dist_limit_eval_le_of_eventually_dist_top hF hA hgA hAdist hy
  exact lt_of_le_of_lt hle hδlt


theorem tendstoLocallyUniformlyOn_of_cauchy_tendsto
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    {f : Filter (HpDisc (E := E) p)} {Ffun : ℂ → E}
    (hf : Cauchy f)
    (hFfun : map (fun g : HpDisc (E := E) p => g.1) f ≤ 𝓝 Ffun) :
    TendstoLocallyUniformlyOn
      (fun g : HpDisc (E := E) p => g.1) Ffun f unitDisc := by
  by_cases hp_top : p = ∞
  · subst p; exact tendstoLocallyUniformlyOn_of_cauchy_tendsto_top hf hFfun
  · exact tendstoLocallyUniformlyOn_of_cauchy_tendsto_ne_top p hp_top hf hFfun

variable [CompleteSpace E]

lemma hpDisc_complete_ne_top (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp_ne_top : p ≠ ∞) :
    ∀ {f : Filter (HpDisc (E := E) p)}, Cauchy f → ∃ F, f ≤ 𝓝 F := by
  sorry

lemma hpDisc_complete_top :
    ∀ {f : Filter (HpDisc (E := E) ∞)}, Cauchy f → ∃ F, f ≤ 𝓝 F := by
  intro f hf
  have hfun : Cauchy (map (fun g : HpDisc ∞ => g.1) f) :=
    hf.map uniformContinuous_coe_top
  obtain ⟨Ffun, hFfun⟩ := CompleteSpace.complete hfun
  have hloc : TendstoLocallyUniformlyOn (fun g : HpDisc ∞ => g.1)
      Ffun f unitDisc := tendstoLocallyUniformlyOn_of_cauchy_tendsto ∞ hf hFfun
  have hFanalytic : AnalyticOn ℂ Ffun unitDisc := by
    haveI : NeBot f := hf.1
    exact hloc.analyticOn (Eventually.of_forall fun g => g.2.1) Metric.isOpen_ball
  have hFmem : MemHpDisc ∞ Ffun := by
    unfold MemHpDisc
    constructor
    . exact hFanalytic
    . constructor
      . rw [hardyNorm_top_eq_Sup_norm hFanalytic.continuousOn]
        rcases Metric.cauchy_iff.1 hf with ⟨hf_NeBot, hf_Cauchy⟩
        rcases hf_Cauchy 1 zero_lt_one with ⟨A, hA, hAdist⟩
        --rcases (Metric.cauchy_iff.1 hf).2 1 zero_lt_one with ⟨A, hA, hAdist⟩
        rcases hf.1.nonempty_of_mem hA with ⟨g, hgA⟩
        rw [iSup_lt_iff]
        refine ⟨ENNReal.ofReal (‖g‖ + 1), ENNReal.ofReal_lt_top, ?_⟩
        intro z
        have hdist_le : dist (Ffun z.1) (g.1 z.1) ≤ 1 :=
           dist_limit_eval_le_of_eventually_dist_top hFfun hA hgA hAdist z.2
        have hnorm : ‖Ffun z.1‖ ≤ ‖g‖ + 1 := by
          have hF_le : ‖Ffun z.1‖ ≤ ‖g.1 z.1‖ + 1 :=
            norm_le_norm_add_const_of_dist_le hdist_le
          have hg_le : ‖g.1 z.1‖ ≤ ‖g‖ := norm_eval_le_norm_top g z.2
          linarith
        rw [← ofReal_norm_eq_enorm]
        exact ENNReal.ofReal_le_ofReal hnorm
      . intro z hz
        have hlim_z :
            Tendsto (fun φ : ℂ → E => φ z)
              (map (fun g : HpDisc (E := E) ∞ => g.1) f) (𝓝 (Ffun z)) :=
          ((continuous_apply z).tendsto Ffun).mono_left hFfun
        have hlim_zero :
            Tendsto (fun φ : ℂ → E => φ z)
              (map (fun g : HpDisc (E := E) ∞ => g.1) f) (𝓝 (0 : E)) := by
          refine Tendsto.congr' ?_ tendsto_const_nhds
          rw [EventuallyEq, eventually_map]
          exact Filter.Eventually.of_forall fun g => (g.2.2.2 z hz).symm
        haveI : NeBot (map (fun g : HpDisc (E := E) ∞ => g.1) f) := hf.1.map _
        exact tendsto_nhds_unique hlim_z hlim_zero
  let F : HpDisc ∞ := ⟨Ffun, hFmem⟩
  use F
  show Tendsto (fun g : HpDisc (E := E) ∞ => g) f (𝓝 F)
  rw [Metric.tendsto_nhds]
  intro ε hε
  let δ : ℝ := ε / 2
  have hδpos : 0 < δ := by positivity
  have hδlt : δ < ε := by dsimp [δ]; linarith
  rcases (Metric.cauchy_iff.1 hf).2 δ hδpos with ⟨A, hA, hAdist⟩
  filter_upwards [hA] with g hgA
  have hdist_le : dist g F ≤ δ := by
    have hhardy_le : hardyNorm ((-g + F : HpDisc (E := E) ∞).1) ∞ ≤
        ENNReal.ofReal δ := by
      rw [hardyNorm_top_eq_Sup_norm (-g + F).2.1.continuousOn]
      refine iSup_le ?_
      intro z
      have hpoint_dist : dist (Ffun z.1) (g.1 z.1) ≤ δ := by
        haveI : NeBot f := hf.1
        exact dist_limit_eval_le_of_eventually_dist_top hFfun hA hgA hAdist z.2
      have hpoint_norm : ‖(-g + F : HpDisc (E := E) ∞).1 z.1‖ ≤ δ := by
        have hnorm : ‖Ffun z.1 - g.1 z.1‖ ≤ δ := by
          simpa [dist_eq_norm_sub] using hpoint_dist
        simpa [F, Pi.add_apply, sub_eq_add_neg, add_comm] using hnorm
      calc
        ‖(-g + F : HpDisc (E := E) ∞).1 z.1‖ₑ =
            ENNReal.ofReal ‖(-g + F : HpDisc (E := E) ∞).1 z.1‖ := by
          rw [ofReal_norm_eq_enorm]
        _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal hpoint_norm
    have hnorm_le : ‖(-g + F : HpDisc (E := E) ∞)‖ ≤ δ := by
      rw [norm_def]
      calc
        (hardyNorm ((-g + F : HpDisc (E := E) ∞).1) ∞).toReal ≤
            (ENNReal.ofReal δ).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hhardy_le
        _ = δ := ENNReal.toReal_ofReal hδpos.le
    simpa [dist_eq_norm, dist_comm] using hnorm_le
  exact lt_of_le_of_lt hdist_le hδlt

theorem hpDisc_complete (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ∀ {f : Filter (HpDisc (E := E) p)}, Cauchy f → ∃ F, f ≤ 𝓝 F := by
  by_cases hp_top : p = ∞
  · subst p
    exact hpDisc_complete_top
  · exact hpDisc_complete_ne_top p hp_top

/-- `H^p` on unit disc is complete for `1 ≤ p`. -/
instance instCompleteSpace
  (p : ℝ≥0∞) [Fact (1 ≤ p)] : CompleteSpace (HpDisc (E := E) p) where
    complete := hpDisc_complete p


end HpDisc
end HardySpace
