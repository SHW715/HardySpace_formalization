import HardySpaceFormalization.HardySpaceDisc
import Mathlib.Analysis.Complex.LocallyUniformLimit
import HardySpaceFormalization.HardyNorm_Bounded_inequality


/-!
# Completeness of Hardy Space over unit disc in ℂ

-/


noncomputable section

open scoped Real ENNReal Topology NNReal
open MeasureTheory Real Complex Set Filter Metric
open Classical


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- `1 ≤ p` implies `0 < p`, so every `[Fact (1 ≤ p)]` context also gets the
`[Fact (0 < p)]` instance that `instNormedAddCommGroup` needs. -/
instance factPos_of_factOneLe {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] : Fact (0 < p) :=
  ⟨zero_lt_one.trans_le hp.out⟩

/-- A locally uniform limit of analytic functions on an open set is analytic. This is a copy of
`TendstoLocallyUniformlyOn.differentiableOn` in terms of `analyticOn`. -/
theorem TendstoLocallyUniformlyOn.analyticOn {ι : Type*} {φ : Filter ι}
    [φ.NeBot] [CompleteSpace E] {U : Set ℂ} {F : ι → ℂ → E} {f : ℂ → E}
    (hf : TendstoLocallyUniformlyOn F f φ U)
    (hF : ∀ᶠ n in φ, AnalyticOn ℂ (F n) U) (hU : IsOpen U) : AnalyticOn ℂ f U :=
    (hf.differentiableOn (hF.mono fun _ hn => hn.differentiableOn) hU).analyticOn hU


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
    {f : HpDisc (E := E) p} [Fact (0 < p)] : ‖f‖ = 0 ↔ f = 0 := by
  constructor
  · intro h
    simp [norm_def] at h
    have hHardy : hardyNorm f.1 p = 0 := by
      rcases (ENNReal.toReal_eq_zero_iff (hardyNorm f.1 p)).1 h with hzero | htop
      · exact hzero
      · exact False.elim ((ne_of_lt f.2.2.1) htop)
    ext z
    by_cases hz : z ∈ unitDisc
    · rcases enorm_rpow_min_le_const_mul_hardyNorm (E := E) (p := p) (z := z)
        (Fact.out : (0 : ℝ≥0∞) < p) hz with ⟨C, hC⟩
      have hpow_zero : ‖f.1 z‖ₑ ^ (min p 1).toReal = 0 := by
        exact le_antisymm (by simpa [hHardy] using hC f.1 f.2.1) bot_le
      have hmin_pos : 0 < (min p 1).toReal := by
        apply ENNReal.toReal_pos
        · exact ne_of_gt (lt_min (Fact.out : (0 : ℝ≥0∞) < p) zero_lt_one)
        · exact ne_of_lt ((min_le_right p 1).trans_lt ENNReal.one_lt_top)
      have hnorm : ‖f.1 z‖ₑ = 0 :=
        (ENNReal.rpow_eq_zero_iff_of_pos hmin_pos).1 hpow_zero
      simpa using hnorm
    · exact f.2.2.2 z hz
  . intro h; rw [h]; exact norm_zero p

lemma norm_smul (p : ℝ≥0∞) [Fact (1 ≤ p)] (c : ℂ) (f : HpDisc (E := E) p) :
    ‖c • f‖ = ‖c‖ * ‖f‖ := by simp [norm_def, hardyNorm_const_smul' c f.1]

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
  (hfg : dist f g = 0) [Fact (0 < p)] : f = g := by
  rw [dist_eq_norm] at hfg
  have hsub : g - f = 0 := by
    simpa [sub_eq_add_neg, add_comm] using ((norm_eq_zero_iff p).1 hfg : -f + g = 0)
  simpa [eq_comm] using (sub_eq_zero.mp hsub : g = f)

instance instMetricSpace (p : ℝ≥0∞) [Fact (0 < p)] :
    MetricSpace (HpDisc (E := E) p) where
  dist := dist
  dist_self := dist_self p
  dist_comm := dist_comm p
  dist_triangle := dist_triangle p
  eq_of_dist_eq_zero := fun {x y} h => eq_of_dist_eq_zero p h

/-The following instances are given helped by codex, in order to make the notion 'completeness' w.r.t. Hardy norm.-/
instance (priority := 1100) instUniformSpace (p : ℝ≥0∞) [Fact (0 < p)] :
    UniformSpace (HpDisc (E := E) p) :=
  PseudoMetricSpace.toUniformSpace

instance (priority := 1100) instTopologicalSpace (p : ℝ≥0∞) [Fact (0 < p)] :
    TopologicalSpace (HpDisc (E := E) p) :=
  (instUniformSpace (E := E) p).toTopologicalSpace

instance instNormedAddCommGroup (p : ℝ≥0∞) [Fact (0 < p)] :
    NormedAddCommGroup (HpDisc (E := E) p) where
  dist_eq := fun _ _ => rfl

instance instNormedSpace (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    NormedSpace ℂ (HpDisc (E := E) p) where
  norm_smul_le c f := (norm_smul p c f).le



-- # Proof for completeness of `H^p` for `0 < p`

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
/-- Along a nontrivial filter `l`, if points `x a` tend to `x₀` and are eventually strictly within
distance `C` of a fixed point `y`, then the limit point is within distance `C` of `y`. -/
lemma dist_limit_le_of_eventually_dist_lt {α β : Type*} [PseudoMetricSpace β]
  {l : Filter α} [NeBot l] {x : α → β} {x₀ y : β} {C : ℝ}
  (hx : Tendsto x l (𝓝 x₀)) (hC : ∀ᶠ a in l, dist (x a) y < C) :
  dist x₀ y ≤ C := le_of_tendsto (hx.dist tendsto_const_nhds) (hC.mono fun _ h => le_of_lt h)

/-- On a closed subdisc, the positive power `(min p 1).toReal` of pointwise distance is
bounded linearly by the Hardy distance. -/
lemma exists_dist_eval_rpow_le_const_mul_dist_of_mem_closedBall
    {p : ℝ≥0∞} {r : ℝ} (hp : 0 < p) (hr : r < 1) :
    ∃ C : ℝ≥0, ∀ g h : HpDisc (E := E) p, ∀ z ∈ closedBall (0 : ℂ) r,
      dist (g.1 z) (h.1 z) ^ (min p 1).toReal ≤ C * dist g h := by
  rcases enorm_rpow_min_le_const_mul_hardyNorm_of_mem_closedBall
    (E := E) (p := p) hp hr with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro g h z hz
  let u : HpDisc (E := E) p := -g + h
  have hpoint := hC u.1 z u.2.1 hz
  have hpoint' : ENNReal.ofReal ‖u.1 z‖ ^ (min p 1).toReal ≤
      (C : ℝ≥0∞) * hardyNorm u.1 p := by
    simpa only [ofReal_norm] using hpoint
  have hprod_ne_top : (C : ℝ≥0∞) * hardyNorm u.1 p ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top (ne_of_lt u.2.2.1)
  have hreal := ENNReal.toReal_mono hprod_ne_top hpoint'
  rw [← ENNReal.toReal_rpow, ENNReal.toReal_ofReal (norm_nonneg _)] at hreal
  have hnorm : ‖u.1 z‖ = dist (g.1 z) (h.1 z) := by
    rw [_root_.dist_eq_norm]
    change ‖-g.1 z + h.1 z‖ = ‖g.1 z - h.1 z‖
    rw [show -g.1 z + h.1 z = -(g.1 z - h.1 z) by abel, _root_.norm_neg]
  rw [hnorm] at hreal
  rw [dist_eq_norm p, norm_def]
  simpa [u, ENNReal.toReal_mul] using hreal

/-- A Hardy-Cauchy sequence is uniformly Cauchy after evaluation on every closed subdisc. -/
lemma cauchySeq_eval_uniformly_on_closedBall
    {p : ℝ≥0∞} [Fact (0 < p)] {f : ℕ → HpDisc (E := E) p}
    (hf : CauchySeq f) {r : ℝ} (hr : r < 1) :
    ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, ∀ z ∈ closedBall (0 : ℂ) r,
      dist ((f m).1 z) ((f n).1 z) < ε := by
  intro ε hε
  rcases exists_dist_eval_rpow_le_const_mul_dist_of_mem_closedBall
    (E := E) (p := p) (Fact.out) hr with ⟨C, hC⟩
  let q : ℝ := (min p 1).toReal
  have hq_pos : 0 < q := by
    dsimp [q]
    apply ENNReal.toReal_pos
    · exact ne_of_gt (lt_min (Fact.out : (0 : ℝ≥0∞) < p) zero_lt_one)
    · exact ne_of_lt ((min_le_right p 1).trans_lt ENNReal.one_lt_top)
  let K : ℝ := max C 1
  have hK_pos : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_right C 1)
  have heps_pow_pos : 0 < ε ^ q := Real.rpow_pos_of_pos hε q
  let δ : ℝ := ε ^ q / (2 * K)
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    positivity
  rcases (Metric.cauchySeq_iff.1 hf) δ hδ_pos with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro m hm n hn z hz
  have hdist : dist (f m) (f n) < δ := hN m hm n hn
  have hpow_le : dist ((f m).1 z) ((f n).1 z) ^ q ≤ C * dist (f m) (f n) :=
    hC (f m) (f n) z hz
  have hpow_lt : dist ((f m).1 z) ((f n).1 z) ^ q < ε ^ q := by
    grw [hpow_le, (mul_le_mul_of_nonneg_left hdist.le C.2 : _ ≤ (C : ℝ) * δ),
      (mul_le_mul_of_nonneg_right (le_max_left (C : ℝ) 1) hδ_pos.le : _ ≤ K * δ)]
    dsimp [δ]; field_simp [hK_pos.ne']; linarith
  exact (Real.rpow_lt_rpow_iff dist_nonneg hε.le hq_pos).1 hpow_lt

/-- Evaluating a Hardy-Cauchy sequence at any point gives a Cauchy sequence in the target. -/
lemma cauchySeq_eval
    {p : ℝ≥0∞} [Fact (0 < p)] {f : ℕ → HpDisc (E := E) p}
    (hf : CauchySeq f) (z : ℂ) : CauchySeq (fun n => (f n).1 z) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  by_cases hz : z ∈ unitDisc
  · have hz_norm : ‖z‖ < 1 := by
      simpa [unitDisc, Metric.mem_ball, dist_zero_right] using hz
    let r : ℝ := (‖z‖ + 1) / 2
    have hr_lt : r < 1 := by dsimp [r]; linarith
    have hz_closed : z ∈ closedBall (0 : ℂ) r := by
      rw [Metric.mem_closedBall, dist_zero_right]
      dsimp [r]
      linarith
    rcases cauchySeq_eval_uniformly_on_closedBall (E := E) hf hr_lt ε hε with ⟨N, hN⟩
    exact ⟨N, fun m hm n hn => hN m hm n hn z hz_closed⟩
  · refine ⟨0, ?_⟩
    intro m hm n hn
    simpa [((f m).2.2.2 z hz), ((f n).2.2.2 z hz)] using hε

/-- The pointwise limit of a Hardy-Cauchy sequence is locally uniform on the unit disc. -/
lemma tendstoLocallyUniformlyOn_of_cauchySeq
    {p : ℝ≥0∞} [Fact (0 < p)] {f : ℕ → HpDisc (E := E) p}
    (hf : CauchySeq f) {F : ℂ → E}
    (hF : ∀ z, Tendsto (fun n => (f n).1 z) atTop (𝓝 (F z))) :
    TendstoLocallyUniformlyOn (fun n => (f n).1) F atTop unitDisc := by
  rw [Metric.tendstoLocallyUniformlyOn_iff]
  intro ε hε x hx
  have hx_norm : ‖x‖ < 1 := by
    simpa [unitDisc, Metric.mem_ball, dist_zero_right] using hx
  let R : ℝ := (‖x‖ + 1) / 2
  have hR_lt : R < 1 := by dsimp [R]; linarith
  have hx_lt_R : ‖x‖ < R := by dsimp [R]; linarith
  let η : ℝ := (R - ‖x‖) / 2
  have hη_pos : 0 < η := by dsimp [η]; linarith
  rcases cauchySeq_eval_uniformly_on_closedBall (E := E) hf hR_lt
    (ε / 2) (by positivity) with ⟨N, hN⟩
  refine ⟨Metric.ball x η,
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x hη_pos), ?_⟩
  filter_upwards [eventually_atTop.2 ⟨N, fun n hn => hn⟩] with n hn
  intro y hy
  have hy_closed : y ∈ Metric.closedBall (0 : ℂ) R := by
    have hy_dist : dist y x ≤ η := by
      apply le_of_lt
      simpa [Metric.mem_ball] using hy
    rw [Metric.mem_closedBall]
    grw [_root_.dist_triangle y x 0, hy_dist]
    rw [dist_zero_right]
    dsimp [η]
    linarith
  have hle : dist (F y) ((f n).1 y) ≤ ε / 2 := by
    refine dist_limit_le_of_eventually_dist_lt (hF y) ?_
    exact eventually_atTop.2 ⟨N, fun m hm => hN m hm n hn y hy_closed⟩
  exact hle.trans_lt (by linarith)

/-- Fatou's lemma transfers an eventual Cauchy bound to the Hardy gauge of the pointwise limit. -/
lemma hardyNorm_sub_limit_le_of_cauchySeq
    {p : ℝ≥0∞} [Fact (0 < p)] {f : ℕ → HpDisc (E := E) p}
    {F : ℂ → E} (hF : ∀ z, Tendsto (fun n => (f n).1 z) atTop (𝓝 (F z)))
    {δ : ℝ} {N : ℕ} (hN : ∀ n ≥ N, dist (f n) (f N) < δ) :
    hardyNorm (F - (f N).1) p ≤ ENNReal.ofReal δ := by
  unfold hardyNorm
  let μ : Measure ℝ := ENNReal.ofReal (1 / (2 * π)) • volume.restrict (Ico 0 (2 * π))
  refine iSup_le ?_
  intro r
  refine iSup_le ?_
  intro hr
  let u : ℕ → ℝ → E := fun n θ => ((f n).1 - (f N).1) (r * exp (I * θ))
  let u_lim : ℝ → E := fun θ => (F - (f N).1) (r * exp (I * θ))
  have hu : ∀ n, AEStronglyMeasurable (u n) μ := by
    intro n
    exact radial_aestronglyMeasurable
      ((f n).2.1.sub (f N).2.1).continuousOn hr μ
  have hulim : ∀ᵐ θ : ℝ ∂μ, Tendsto (fun n => u n θ) atTop (𝓝 (u_lim θ)) := by
    apply Eventually.of_forall
    intro θ
    simpa [u, u_lim, Pi.sub_apply] using
      (hF (r * exp (I * θ))).sub tendsto_const_nhds
  calc
    eLpNormFixed u_lim p μ
        ≤ atTop.liminf (fun n => eLpNormFixed (u n) p μ) :=
      eLpNormFixed_lim_le_liminf_eLpNormFixed hu u_lim hulim
    _ ≤ ENNReal.ofReal δ := by
      have heventually : ∀ᶠ n in atTop, eLpNormFixed (u n) p μ ≤ ENNReal.ofReal δ := by
        filter_upwards [eventually_atTop.2 ⟨N, fun n hn => hn⟩] with n hn
        calc
          eLpNormFixed (u n) p μ
              = eLpNormFixed
                  (fun θ : ℝ => -((-f n + f N : HpDisc p).1 (r * exp (I * θ)))) p μ := by
                congr 1
                funext θ
                simp [u, Pi.sub_apply, sub_eq_add_neg, add_comm]
          _ = eLpNormFixed
                (fun θ : ℝ => (-f n + f N : HpDisc p).1 (r * exp (I * θ))) p μ :=
              eLpNormFixed_neg
                (fun θ : ℝ => (-f n + f N : HpDisc p).1 (r * exp (I * θ))) p μ
          _ ≤ hardyNorm (E := E) ((-f n + f N : HpDisc p).1) p :=
              hardyNorm_radial_le ((-f n + f N : HpDisc p).1) p hr
          _ ≤ ENNReal.ofReal δ := by
            refine le_of_lt ((ENNReal.lt_ofReal_iff_toReal_lt ?_).2 ?_)
            · exact ne_of_lt (-f n + f N : HpDisc p).2.2.1
            · simpa [dist_eq_norm, norm_def] using hN n hn
      refine Filter.liminf_le_of_le (by isBoundedDefault) ?_
      intro b hb
      rcases (hb.and heventually).exists with ⟨n, hbn, hnδ⟩
      exact hbn.trans hnδ


variable [CompleteSpace E]

/-- `H^p` on the unit disc is complete for every positive extended exponent `p`. -/
theorem hpDisc_complete (p : ℝ≥0∞) [Fact (0 < p)] :
    ∀ {f : Filter (HpDisc (E := E) p)}, Cauchy f → ∃ F, f ≤ 𝓝 F := by
  let hcomplete : CompleteSpace (HpDisc (E := E) p) := by
    apply Metric.complete_of_cauchySeq_tendsto
    intro f hf
    let F : ℂ → E := fun z => atTop.limUnder (fun n => (f n).1 z)
    have hF : ∀ z, Tendsto (fun n => (f n).1 z) atTop (𝓝 (F z)) := by
      intro z
      exact (cauchySeq_eval (E := E) hf z).tendsto_limUnder
    have hloc : TendstoLocallyUniformlyOn (fun n => (f n).1) F atTop unitDisc :=
      tendstoLocallyUniformlyOn_of_cauchySeq (E := E) hf hF
    have hFanalytic : AnalyticOn ℂ F unitDisc :=
      hloc.analyticOn (Eventually.of_forall fun n => (f n).2.1) Metric.isOpen_ball
    have hFzero : ∀ z ∉ unitDisc, F z = 0 := by
      intro z hz
      have hzero : Tendsto (fun n => (f n).1 z) atTop (𝓝 (0 : E)) := by
        rw [show (fun n => (f n).1 z) = fun _ : ℕ => (0 : E) by
          funext n
          exact (f n).2.2.2 z hz]
        exact tendsto_const_nhds
      exact tendsto_nhds_unique (hF z) hzero
    have hFfinite : hardyNorm F p < ∞ := by
      rcases (Metric.cauchySeq_iff'.1 hf) 1 zero_lt_one with ⟨N, hN⟩
      have hdiff : hardyNorm (F - (f N).1) p ≤ ENNReal.ofReal 1 :=
        hardyNorm_sub_limit_le_of_cauchySeq (E := E) hF hN
      calc
        hardyNorm F p = hardyNorm ((F - (f N).1) + (f N).1) p := by
          congr 1
          ext z
          simp [Pi.add_apply, sub_eq_add_neg, add_assoc]
        _ ≤ hardyNorm (F - (f N).1) p + hardyNorm (f N).1 p :=
          hardyNorm_add_le (hFanalytic.sub (f N).2.1) (f N).2.1
        _ < ∞ := ENNReal.add_lt_top.2
          ⟨lt_of_le_of_lt hdiff ENNReal.ofReal_lt_top, (f N).2.2.1⟩
    have hFmem : MemHpDisc (E := E) p F := ⟨hFanalytic, hFfinite, hFzero⟩
    let Fhp : HpDisc (E := E) p := ⟨F, hFmem⟩
    refine ⟨Fhp, ?_⟩
    rw [Metric.tendsto_atTop]
    intro ε hε
    let δ : ℝ := ε / 2
    have hδ_pos : 0 < δ := by dsimp [δ]; positivity
    rcases (Metric.cauchySeq_iff'.1 hf) δ hδ_pos with ⟨N, hN⟩
    have hhardy : hardyNorm (F - (f N).1) p ≤ ENNReal.ofReal δ :=
      hardyNorm_sub_limit_le_of_cauchySeq (E := E) hF hN
    have hdist_limit : dist (f N) Fhp ≤ δ := by
      rw [dist_eq_norm, norm_def]
      have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hhardy
      simpa [Fhp, F, ENNReal.toReal_ofReal hδ_pos.le, Pi.add_apply,
        sub_eq_add_neg, add_comm] using hreal
    refine ⟨N, ?_⟩
    intro n hn
    calc
      dist (f n) Fhp ≤ dist (f n) (f N) + dist (f N) Fhp :=
        _root_.dist_triangle _ _ _
      _ < δ + δ := add_lt_add_of_lt_of_le (hN n hn) hdist_limit
      _ = ε := by dsimp [δ]; ring
  intro f hf
  exact CompleteSpace.complete (self := hcomplete) hf

instance instCompleteSpace
    (p : ℝ≥0∞) [Fact (0 < p)] : CompleteSpace (HpDisc (E := E) p) where
  complete := hpDisc_complete p


end HpDisc
end HardySpace
