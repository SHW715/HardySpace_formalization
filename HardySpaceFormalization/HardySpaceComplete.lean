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
    {f : HpDisc (E := E) p} [Fact (1 ≤ p)] : ‖f‖ = 0 ↔ f = 0 := by
  constructor
  · intro h
    simp [norm_def] at h
    have hHardy : hardyNorm f.1 p = 0 := by
      rcases (ENNReal.toReal_eq_zero_iff (hardyNorm f.1 p)).1 h with hzero | htop
      · exact hzero
      · exact False.elim ((ne_of_lt f.2.2.1) htop)
    ext z
    by_cases hz : z ∈ unitDisc
    · rcases norm_eval_le_const_mul_hardyNorm (E := E) (p := p) (z := z)
        (Fact.out : (1 : ℝ≥0∞) ≤ p) hz with ⟨C, hC⟩
      have hnorm : ‖f.1 z‖ₑ = 0 := by
        exact le_antisymm (by simpa [hHardy] using hC f.1 f.2.1) bot_le
      simpa using hnorm
    · exact f.2.2.2 z hz
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



-- # Now we'd like to prove the completeness of `H^p`:



-- First, we need some helper lemmas:
omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
/-- Along a nontrivial filter `l`, if points `x a` tend to `x₀` and are eventually strictly within
distance `C` of a fixed point `y`, then the limit point is within distance `C` of `y`. -/
lemma dist_limit_le_of_eventually_dist_lt {α β : Type*} [PseudoMetricSpace β]
  {l : Filter α} [NeBot l] {x : α → β} {x₀ y : β} {C : ℝ}
  (hx : Tendsto x l (𝓝 x₀)) (hC : ∀ᶠ a in l, dist (x a) y < C) :
  dist x₀ y ≤ C := le_of_tendsto (hx.dist tendsto_const_nhds) (hC.mono fun _ h => le_of_lt h)

/-- If ambient functions from `HpDisc p` tend to `F` along a nontrivial filter,
and at a fixed point `z` their values are eventually strictly within `E`-distance
`C` of a fixed comparison function `g z`, then the limit value `F z` is within
`E`-distance `C` of `g z`. -/
lemma dist_limit_eval_le_of_eventually_bound
    {p : ℝ≥0∞} {f : Filter (HpDisc (E := E) p)} [NeBot f] {F : ℂ → E}
    (hF : map (fun q : HpDisc (E := E) p => q.1) f ≤ 𝓝 F)
    {g : HpDisc (E := E) p} {z : ℂ} {C : ℝ}
    (hqg : ∀ᶠ q in f, dist (q.1 z) (g.1 z) < C) : dist (F z) (g.1 z) ≤ C := by
  have hlim_z : Tendsto (fun φ : ℂ → E => φ z)
      (map (fun q : HpDisc (E := E) p => q.1) f) (𝓝 (F z)) :=
    ((continuous_apply z).tendsto F).mono_left hF
  refine dist_limit_le_of_eventually_dist_lt hlim_z ?_
  rw [eventually_map]; exact hqg

/-- On each closed subdisc, point evaluations are Lipschitz with respect to the Hardy distance. -/
lemma exists_dist_eval_le_const_mul_dist_of_mem_closedBall
  {p : ℝ≥0∞} {r : ℝ} (hp : 1 ≤ p) (hr : r < 1)  :
  ∃ C : ℝ≥0, ∀ g h : HpDisc (E := E) p, ∀ z ∈ closedBall (0 : ℂ) r,
    dist (g.1 z) (h.1 z) ≤ C * dist g h := by
  -- codex after review
  rcases norm_eval_le_const_mul_hardyNorm_of_mem_closedBall
    (E := E) (p := p) hp hr with ⟨C, hC⟩
  use C; intro g h z hz
  let u : HpDisc (E := E) p := -g + h
  rw [_root_.dist_comm _ _, dist_eq_norm_sub, sub_eq_add_neg, add_comm]
  rw [dist_eq_norm, norm_def]
  have hpoint : ‖u.1 z‖ₑ ≤ (C : ℝ≥0∞) * hardyNorm u.1 p := hC u.1 z u.2.1 hz
  have hprod_ne_top : (C : ℝ≥0∞) * hardyNorm u.1 p ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top (ne_of_lt u.2.2.1)
  simpa [ENNReal.toReal_mul] using ENNReal.toReal_mono hprod_ne_top hpoint

/-- At each point of the unit disc, point evaluation is Lipschitz with respect to the Hardy
distance. -/
lemma exists_dist_eval_le_const_mul_dist {p : ℝ≥0∞} (hp : 1 ≤ p)
    {z : ℂ} (hz : z ∈ unitDisc) :
    ∃ C : ℝ≥0, ∀ g h : HpDisc (E := E) p,
      dist (g.1 z) (h.1 z) ≤ C * dist g h := by
  -- after review
  rcases norm_eval_le_const_mul_hardyNorm (E := E) (p := p) (z := z)
      hp hz with ⟨C, hC⟩
  use C; intro g h
  rw [_root_.dist_comm _ _, dist_eq_norm_sub, sub_eq_add_neg, add_comm]
  rw [dist_eq_norm, norm_def]
  let u : HpDisc (E := E) p := -g + h
  have hpoint : ‖u.1 z‖ₑ ≤ (C : ℝ≥0∞) * hardyNorm u.1 p := hC u.1 u.2.1
  have hprod_ne_top : (C : ℝ≥0∞) * hardyNorm u.1 p ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top (ne_of_lt u.2.2.1)
  simpa [ENNReal.toReal_mul] using ENNReal.toReal_mono hprod_ne_top hpoint

/-- Point evaluation at a fixed point is Lipschitz for the Hardy-norm metric on `HpDisc`.-/
lemma lipschitz_eval (p : ℝ≥0∞) [Fact (1 ≤ p)] (z : ℂ) :
    ∃ C : ℝ≥0, LipschitzWith C (fun g : HpDisc (E := E) p => g.1 z) := by
  by_cases hz : z ∈ unitDisc
  · rcases exists_dist_eval_le_const_mul_dist (E := E) (p := p) (Fact.out) hz with ⟨C, hC⟩
    exact ⟨C, LipschitzWith.of_dist_le_mul hC⟩
  · refine ⟨0, LipschitzWith.of_dist_le_mul ?_⟩
    intro g h
    simp [g.2.2.2 z hz, h.2.2.2 z hz]

/-- The coercion from `HpDisc` to ambient functions is uniformly continuous when the ambient
function space carries the product uniformity. -/
lemma uniformContinuous_coe (p : ℝ≥0∞) [Fact (1 ≤ p)]  :
    UniformContinuous (fun g : HpDisc (E := E) p => g.1) := by
  rw [uniformContinuous_pi]
  intro z
  rcases lipschitz_eval (E := E) p z with ⟨C, hC⟩
  exact hC.uniformContinuous

/-- A Hardy-norm Cauchy filter whose ambient functions converge to `F` converges to `F`
locally uniformly on the unit disc. -/
lemma tendstoLocallyUniformlyOn_of_cauchy_tendsto
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    {f : Filter (HpDisc (E := E) p)} {F : ℂ → E} (hf : Cauchy f)
    (hF : map (fun g : HpDisc (E := E) p => g.1) f ≤ 𝓝 F) :
    TendstoLocallyUniformlyOn (fun g : HpDisc p => g.1) F f unitDisc := by
  -- codex after review
  rw [Metric.tendstoLocallyUniformlyOn_iff]
  intro ε hε x hx
  have hx_norm : ‖x‖ < 1 := by
    simpa [unitDisc, Metric.mem_ball, dist_zero_right] using hx
  let R : ℝ := (‖x‖ + 1) / 2
  have hR_lt : R < 1 := by dsimp [R]; linarith
  have hx_lt_R : ‖x‖ < R := by dsimp [R]; linarith
  let η : ℝ := (R - ‖x‖) / 2
  have hη_pos : 0 < η := by dsimp [η]; linarith
  rcases exists_dist_eval_le_const_mul_dist_of_mem_closedBall
      (E := E) (p := p) (Fact.out : (1 : ℝ≥0∞) ≤ p) hR_lt with ⟨C, hEval_closed⟩
  let K : ℝ := max C 1
  have hK_pos : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_right C 1)
  let δ : ℝ := ε / (4 * K)
  have hδ_pos : 0 < δ := by dsimp [δ]; positivity
  have hCδ_lt : C * δ < ε / 2 := by
    calc
      C * δ ≤ K * δ := by
        refine mul_le_mul_of_nonneg_right ?_ ?_
        . exact le_max_left C 1
        . exact le_of_lt hδ_pos
      _ = ε / 4 := by dsimp [δ]; field_simp [hK_pos.ne']
      _ < ε / 2 := by linarith
  rcases Metric.cauchy_iff.1 hf with ⟨hf_NeBot, hf_Cauchy⟩
  rcases hf_Cauchy δ hδ_pos with ⟨A, hA, hAdist⟩
  refine ⟨Metric.ball x η, mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x hη_pos), ?_⟩
  filter_upwards [hA] with g hgA
  intro y hy
  have hy_closed : y ∈ Metric.closedBall (0 : ℂ) R := by
    have hy_dist : dist y x ≤  η := by
      apply le_of_lt; simpa [Metric.mem_ball] using hy
    rw [Metric.mem_closedBall]
    grw [_root_.dist_triangle y x 0, hy_dist]
    rw [dist_zero_right]
    dsimp [η]; linarith
  have hle : dist (F y) (g.1 y) ≤ ε / 2 := by
    refine dist_limit_eval_le_of_eventually_bound hF ?_
    filter_upwards [hA] with q hqA
    grw [hEval_closed q g y hy_closed]
    have hmul : C * dist q g ≤ C * δ :=
      mul_le_mul_of_nonneg_left (le_of_lt (hAdist q hqA g hgA)) C.2
    exact lt_of_le_of_lt hmul hCδ_lt
  exact lt_of_le_of_lt hle (by linarith)

/-- If a Hardy-Cauchy filter is eventually `δ`-small around `g`, then the ambient limit is
`δ`-close to `g` in Hardy norm. -/
lemma hardyNorm_sub_limit_le_of_eventually_dist_lt
    (p : ℝ≥0∞) [Fact (1 ≤ p)] {f : Filter (HpDisc (E := E) p)} {F : ℂ → E}
    (hf : Cauchy f) (hF : map (fun g : HpDisc p => g.1) f ≤ 𝓝 F)
    (hFanalytic : AnalyticOn ℂ F unitDisc)
    {δ : ℝ} (hδ_pos : 0 < δ)
    {g : HpDisc p} (hg_eventually : ∀ᶠ h in f, dist h g < δ) :
    hardyNorm (F - g.1) p ≤ ENNReal.ofReal δ := by
  -- codex with review
  rcases Metric.cauchy_iff.1 hf with ⟨hf_NeBot, hf_Cauchy⟩
  unfold hardyNorm
  let μ : Measure ℝ := ENNReal.ofReal (1 / (2 * π)) • volume.restrict (Ico 0 (2 * π))
  haveI : IsProbabilityMeasure μ := circle_measure_isProbabilityMeasure
  refine iSup_le ?_
  intro r
  refine iSup_le ?_
  intro hr
  have hslice_le_alpha : ∀ α : ℝ, 0 < α → eLpNormFixed (fun θ : ℝ => (F - g.1) (r * exp (I * θ))) p μ
   ≤ ENNReal.ofReal (δ + α) := by
    intro α hα
    rcases exists_dist_eval_le_const_mul_dist_of_mem_closedBall
      (E := E) (p := p) (Fact.out) hr.2 with ⟨C, hEval_closed⟩
    let K : ℝ := max C 1
    have hK_pos : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_right C 1)
    let η : ℝ := α / (2 * K)
    have hη_pos : 0 < η := by dsimp [η]; positivity
    have hCη_lt : C * η < α := by
      calc
        C * η ≤ K * η := mul_le_mul_of_nonneg_right (le_max_left C 1) (le_of_lt hη_pos)
        _ = α / 2 := by dsimp [η]; field_simp [hK_pos.ne']
        _ < α := by linarith
    rcases hf_Cauchy η hη_pos with ⟨B, hB, hBdist⟩
    rcases hf_NeBot.nonempty_of_mem (inter_mem hg_eventually hB) with ⟨q, hq_close, hqB⟩
    have hFq_bound : eLpNormFixed (fun θ : ℝ => (F - q.1) (r * exp (I * θ))) p μ ≤
        ENNReal.ofReal α := by
      refine eLpNormFixed_le_of_ae_bound_of_one_le (p := p) (μ := μ) (Fact.out) ?_
      apply Eventually.of_forall
      intro θ
      let z : ℂ := r * exp (I * θ)
      have hz_closed : z ∈ Metric.closedBall (0 : ℂ) r := by
        rw [Metric.mem_closedBall, dist_zero_right, ← abs_of_pos hr.1]
        dsimp [z]; simp
      have hdist : dist (F z) (q.1 z) ≤ α := by
        refine dist_limit_eval_le_of_eventually_bound hF ?_
        filter_upwards [hB] with s hsB
        grw [hEval_closed s q z hz_closed]
        refine lt_of_le_of_lt ?_ hCη_lt
        exact mul_le_mul_of_nonneg_left (le_of_lt (hBdist s hsB q hqB)) C.2
      simpa [z, Pi.sub_apply, dist_eq_norm_sub] using hdist
    have hqg_bound : eLpNormFixed (fun θ : ℝ => (q.1 - g.1) (r * exp (I * θ))) p μ
      ≤ ENNReal.ofReal δ := by
      calc
        eLpNormFixed (fun θ : ℝ => (q.1 - g.1) (r * exp (I * θ))) p μ
          = eLpNormFixed (fun θ : ℝ => -(((-q + g : HpDisc p).1)
          (r * exp (I * θ)))) p μ := by
          congr 1; funext θ; simp [Pi.sub_apply, sub_eq_add_neg, add_comm]
        _ = eLpNormFixed (fun θ : ℝ => ((-q + g : HpDisc p).1) (r * exp (I * θ))) p μ :=
          eLpNormFixed_neg (fun θ : ℝ => ((-q + g : HpDisc p).1) (r * exp (I * θ))) p μ
        _ ≤ hardyNorm (E := E) ((-q + g : HpDisc p).1) p :=
          hardyNorm_radial_le ((-q + g : HpDisc p).1) p hr
        _ ≤ ENNReal.ofReal δ := by
          refine le_of_lt ((ENNReal.lt_ofReal_iff_toReal_lt ?_).2 ?_)
          . exact ne_of_lt (-q + g : HpDisc p).2.2.1
          . simpa [dist_eq_norm, norm_def] using hq_close
    calc
      eLpNormFixed (fun θ : ℝ => (F - g.1) (r * exp (I * θ))) p μ
        = eLpNormFixed ((fun θ : ℝ => (F - q.1) (r * exp (I * θ)))
        + (fun θ : ℝ => (q.1 - g.1) (r * exp (I * θ)))) p μ := by
        congr 1; funext θ; simp [Pi.add_apply, sub_eq_add_neg, add_assoc]
      _ ≤ eLpNormFixed (fun θ : ℝ => (F - q.1) (r * exp (I * θ))) p μ +
        eLpNormFixed (fun θ : ℝ => (q.1 - g.1) (r * exp (I * θ))) p μ := by
        refine eLpNormFixed_add_le ?_ ?_
        . exact radial_aestronglyMeasurable (hFanalytic.sub q.2.1).continuousOn hr μ
        . exact radial_aestronglyMeasurable (q.2.1.sub g.2.1).continuousOn hr μ
      _ ≤ ENNReal.ofReal α + ENNReal.ofReal δ := add_le_add hFq_bound hqg_bound
      _ = ENNReal.ofReal (δ + α) := by
        rw [← ENNReal.ofReal_add (le_of_lt hα) (le_of_lt hδ_pos)]; ring_nf
  rw [← ENNReal.ofReal_toReal (ne_top_of_le_ne_top
    ENNReal.ofReal_ne_top (hslice_le_alpha 1 zero_lt_one))]
  apply ENNReal.ofReal_le_ofReal
  apply le_of_forall_pos_le_add
  intro α hα
  have htoReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hslice_le_alpha α hα)
  have hsum_nonneg : 0 ≤ δ + α := le_of_lt (add_pos hδ_pos hα)
  simpa [ENNReal.toReal_ofReal hsum_nonneg] using htoReal

/-- An ambient-function limit of a Hardy-Cauchy filter has finite Hardy norm. -/
theorem hardyNorm_lt_top_of_tendsto_coe_cauchy
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    {f : Filter (HpDisc (E := E) p)} {F : ℂ → E}
    (hf : Cauchy f) (hF : map (fun g : HpDisc p => g.1) f ≤ 𝓝 F)
    (hFanalytic : AnalyticOn ℂ F unitDisc) : hardyNorm F p < ∞ := by
  rcases Metric.cauchy_iff.1 hf with ⟨hf_NeBot, hf_Cauchy⟩
  rcases hf_Cauchy 1 zero_lt_one with ⟨A, hA, hAdist⟩
  rcases hf_NeBot.nonempty_of_mem hA with ⟨g, hgA⟩
  have hdiff_le : hardyNorm (F - g.1) p ≤ ENNReal.ofReal 1 := by
    have hg_eventually : ∀ᶠ h in f, dist h g < 1 := by
      filter_upwards [hA] with h hhA
      exact hAdist h hhA g hgA
    simpa using hardyNorm_sub_limit_le_of_eventually_dist_lt (E := E) p
      hf hF hFanalytic (δ := 1) zero_lt_one hg_eventually
  calc
    hardyNorm F p = hardyNorm ((F - g.1) + g.1) p := by
      congr 1; ext z; simp [Pi.add_apply, sub_eq_add_neg, add_assoc]
    _ ≤ hardyNorm (F - g.1) p + hardyNorm g.1 p := hardyNorm_add_le (hFanalytic.sub g.2.1) g.2.1
    _ < ∞ := ENNReal.add_lt_top.2 ⟨lt_of_le_of_lt hdiff_le ENNReal.ofReal_lt_top, g.2.2.1⟩

/-- A limit of Hardy `p`-functions still vanishes outside the unit disc.-/
lemma zero_off_unitDisc_of_tendsto_coe {p : ℝ≥0∞}
    {f : Filter (HpDisc (E := E) p)} [NeBot f] {F : ℂ → E}
    (hF : map (fun g : HpDisc (E := E) p => g.1) f ≤ 𝓝 F) :
    ∀ z ∉ unitDisc, F z = 0 := by
  intro z hz
  have hlim_z : Tendsto (fun φ : ℂ → E => φ z)
      (map (fun g : HpDisc p => g.1) f) (𝓝 (F z)) :=
    ((continuous_apply z).tendsto F).mono_left hF
  have hlim_zero : Tendsto (fun φ : ℂ → E => φ z)
      (map (fun g : HpDisc p => g.1) f) (𝓝 (0 : E)) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    rw [EventuallyEq, eventually_map]
    exact Filter.Eventually.of_forall fun g => (g.2.2.2 z hz).symm
  exact tendsto_nhds_unique hlim_z hlim_zero

/-- Ambient-function convergence of a Hardy-Cauchy filter upgrades to convergence in the Hardy
metric, once the ambient limit has been shown to lie in `HpDisc p`. -/
theorem tendsto_hpDisc_of_tendsto_coe_cauchy
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    {f : Filter (HpDisc (E := E) p)} {F : ℂ → E}
    (hf : Cauchy f) (hF : map (fun g : HpDisc p => g.1) f ≤ 𝓝 F)
    (hFmem : MemHpDisc p F) : f ≤ 𝓝 (⟨F, hFmem⟩ : HpDisc p) := by
  let F : HpDisc (E := E) p := ⟨F, hFmem⟩
  haveI : NeBot f := hf.1
  show Tendsto (fun g : HpDisc (E := E) p => g) f (𝓝 F)
  rw [Metric.tendsto_nhds]
  intro ε hε
  let δ : ℝ := ε / 2
  have hδpos : 0 < δ := by positivity
  have hδlt : δ < ε := by dsimp [δ]; linarith
  rcases (Metric.cauchy_iff.1 hf).2 δ hδpos with ⟨A, hA, hAdist⟩
  filter_upwards [hA] with g hgA
  refine lt_of_le_of_lt ?_ hδlt
  rw [dist_eq_norm]
  rw [← ENNReal.toReal_ofReal hδpos.le]
  refine ENNReal.toReal_mono ENNReal.ofReal_ne_top ?_
  have hg_eventually : ∀ᶠ h in f, dist h g < δ := by
    filter_upwards [hA] with h hhA
    exact hAdist h hhA g hgA
  have hhardy_le : hardyNorm (E := E) (F - g.1) p ≤ ENNReal.ofReal δ :=
    hardyNorm_sub_limit_le_of_eventually_dist_lt p hf hF hFmem.1
      hδpos hg_eventually
  simpa [F, Pi.add_apply, sub_eq_add_neg, add_comm] using hhardy_le


variable [CompleteSpace E]

theorem hpDisc_complete (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ∀ {f : Filter (HpDisc (E := E) p)}, Cauchy f → ∃ F, f ≤ 𝓝 F := by
  intro f hf
  haveI : NeBot f := hf.1
  have hfun : Cauchy (map (fun g : HpDisc (E := E) p => g.1) f) :=
    hf.map (uniformContinuous_coe (E := E) p)
  obtain ⟨Ffun, hFfun⟩ := CompleteSpace.complete hfun
  have hloc : TendstoLocallyUniformlyOn (fun g : HpDisc (E := E) p => g.1)
      Ffun f unitDisc := tendstoLocallyUniformlyOn_of_cauchy_tendsto p hf hFfun
  have hFanalytic : AnalyticOn ℂ Ffun unitDisc :=
    hloc.analyticOn (Eventually.of_forall fun g => g.2.1) Metric.isOpen_ball
  have hFmem : MemHpDisc (E := E) p Ffun := by
    unfold MemHpDisc
    constructor
    · exact hFanalytic
    · constructor
      · exact hardyNorm_lt_top_of_tendsto_coe_cauchy p hf hFfun hFanalytic
      · exact zero_off_unitDisc_of_tendsto_coe hFfun
  let F : HpDisc (E := E) p := ⟨Ffun, hFmem⟩
  exact ⟨F, tendsto_hpDisc_of_tendsto_coe_cauchy p hf hFfun hFmem⟩

/-- `H^p` on unit disc is complete for `1 ≤ p`. -/
instance instCompleteSpace
  (p : ℝ≥0∞) [Fact (1 ≤ p)] : CompleteSpace (HpDisc (E := E) p) where
    complete := hpDisc_complete p


end HpDisc
end HardySpace
