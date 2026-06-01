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

-- Here are two properties of Hardy `∞`-norm and distance:


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
    ‖f.1 z - g.1 z‖ = ‖(-g + f : HpDisc ∞).1 z‖ := by
      simp [Pi.add_apply, sub_eq_add_neg, add_comm]
    _ ≤ ‖(-f + g : HpDisc ∞)‖ := by
      grw [norm_eval_le_norm_top (-g + f) hz]
      apply le_of_eq
      simpa [neg_add, add_comm] using (norm_neg ∞ (-f + g))


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


lemma dist_limit_eval_le_of_eventually_dist_ne_top
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {f : Filter (HpDisc (E := E) p)} [NeBot f] {F : ℂ → E}
    (hF : map (fun g : HpDisc (E := E) p => g.1) f ≤ 𝓝 F)
    {A : Set (HpDisc (E := E) p)} (hA : A ∈ f)
    {g : HpDisc (E := E) p} (hgA : g ∈ A)
    {C ε : ℝ} (hC_nonneg : 0 ≤ C) {δ : ℝ}
    (hδ_bound : C * δ < ε) (hAdist : ∀ q ∈ A, ∀ r ∈ A, dist q r < δ)
    {z : ℂ} (hEval : ∀ q : HpDisc (E := E) p,
    dist (q.1 z) (g.1 z) ≤ C * dist q g) : dist (F z) (g.1 z) ≤ ε := by
  refine dist_limit_eval_le_of_eventually_bound hF ?_
  filter_upwards [hA] with q hqA
  have hqz : dist (q.1 z) (g.1 z) ≤ C * dist q g := hEval q
  have hmul : C * dist q g ≤ C * δ :=
    mul_le_mul_of_nonneg_left (le_of_lt (hAdist q hqA g hgA)) hC_nonneg
  exact lt_of_le_of_lt (hqz.trans hmul) hδ_bound


/-- In `H∞`, a Hardy-distance diameter bound on an eventual set passes to pointwise distances
between the ambient limit and any member of that set. -/
lemma dist_limit_eval_le_of_eventually_dist_top
    {f : Filter (HpDisc (E := E) ∞)} [NeBot f] {F : ℂ → E}
    (hF : map (fun g : HpDisc ∞ => g.1) f ≤ 𝓝 F)
    {A : Set (HpDisc ∞)} (hA : A ∈ f)
    {g : HpDisc ∞} (hgA : g ∈ A) {C : ℝ}
    (hAdist : ∀ q ∈ A, ∀ r ∈ A, dist q r < C)
    {z : ℂ} (hz : z ∈ unitDisc) : dist (F z) (g.1 z) ≤ C := by
  refine dist_limit_eval_le_of_eventually_bound hF ?_
  filter_upwards [hA] with q hqA
  have hqz : dist (q.1 z) (g.1 z) ≤ dist q g := by
    rw [dist_eq_norm_sub]; exact norm_sub_eval_le_dist_top q g hz
  exact lt_of_le_of_lt hqz (hAdist q hqA g hgA)




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


/-- Point evaluation at a fixed point is Lipschitz for the Hardy-norm metric on `HpDisc`.
Outside the unit disc this is the zero map, since `HpDisc` functions are zero there. -/
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
    (hFfun : map (fun g : HpDisc (E := E) p => g.1) f ≤ 𝓝 F) :
    TendstoLocallyUniformlyOn
      (fun g : HpDisc (E := E) p => g.1) F f unitDisc := by
  -- codex without review
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
      (E := E) (p := p) (Fact.out : (1 : ℝ≥0∞) ≤ p) hR_lt with
    ⟨C, hEval_closed⟩
  have hC_nonneg : 0 ≤ (C : ℝ) := C.2
  let K : ℝ := max C 1
  have hK_pos : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_right C 1)
  let δ : ℝ := ε / (4 * K)
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    positivity
  have hCδ_lt : C * δ < ε / 2 := by
    have hC_le_K : C ≤ K := le_max_left C 1
    have hδ_nonneg : 0 ≤ δ := le_of_lt hδ_pos
    calc
      C * δ ≤ K * δ := mul_le_mul_of_nonneg_right hC_le_K hδ_nonneg
      _ = ε / 4 := by
        dsimp [δ]
        field_simp [hK_pos.ne']
      _ < ε / 2 := by linarith
  rcases Metric.cauchy_iff.1 hf with ⟨hf_NeBot, hf_Cauchy⟩
  rcases hf_Cauchy δ hδ_pos with ⟨A, hA, hAdist⟩
  refine ⟨Metric.ball x η, mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x hη_pos), ?_⟩
  filter_upwards [hA] with g hgA
  intro y hy
  have hy_closed : y ∈ Metric.closedBall (0 : ℂ) R := by
    have hy_dist : dist y x < η := by
      simpa [Metric.mem_ball] using hy
    have hynorm_le : ‖y‖ ≤ dist y x + ‖x‖ := by
      calc
        ‖y‖ = dist y 0 := by simp
        _ ≤ dist y x + dist x 0 := _root_.dist_triangle y x 0
        _ = dist y x + ‖x‖ := by simp [dist_zero_right]
    have hynorm_lt : ‖y‖ < R := by
      calc
        ‖y‖ ≤ dist y x + ‖x‖ := hynorm_le
        _ < η + ‖x‖ := by
          simpa [add_comm, add_left_comm, add_assoc] using add_lt_add_right hy_dist ‖x‖
        _ < R := by dsimp [η]; linarith
    simpa [Metric.mem_closedBall, dist_zero_right] using le_of_lt hynorm_lt
  have hle : dist (F y) (g.1 y) ≤ ε / 2 := by
    haveI : NeBot f := hf_NeBot
    exact dist_limit_eval_le_of_eventually_dist_ne_top
      (E := E) (p := p) hFfun hA hgA hC_nonneg hCδ_lt hAdist
      (z := y) (fun q => hEval_closed q g y hy_closed)
  exact lt_of_le_of_lt hle (by linarith)





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

/-- If a Hardy-Cauchy filter is eventually `δ`-small around `g`, then the ambient limit is
`2 * δ`-close to `g` in Hardy norm. -/
lemma hardyNorm_sub_limit_le_of_eventually_dist_lt
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (_hp_ne_top : p ≠ ∞)
    {f : Filter (HpDisc (E := E) p)} {F : ℂ → E}
    (hf : Cauchy f) (hF : map (fun g : HpDisc p => g.1) f ≤ 𝓝 F)
    (hFanalytic : AnalyticOn ℂ F unitDisc)
    {δ : ℝ} (hδ_pos : 0 < δ)
    {A : Set (HpDisc (E := E) p)} (hA : A ∈ f)
    (hAdist : ∀ q ∈ A, ∀ r ∈ A, dist q r < δ)
    {g : HpDisc (E := E) p} (hgA : g ∈ A) :
    hardyNorm (E := E) (F - g.1) p ≤ ENNReal.ofReal (2 * δ) := by
  -- codex without review
  rcases Metric.cauchy_iff.1 hf with ⟨hf_NeBot, hf_Cauchy⟩
  unfold hardyNorm
  let μ : Measure ℝ := ENNReal.ofReal (1 / (2 * π)) • volume.restrict (Ico 0 (2 * π))
  haveI : IsProbabilityMeasure μ := circle_measure_isProbabilityMeasure
  refine iSup_le ?_
  intro r
  refine iSup_le ?_
  intro hr
  rcases exists_dist_eval_le_const_mul_dist_of_mem_closedBall
      (E := E) (p := p) (Fact.out : (1 : ℝ≥0∞) ≤ p) hr.2 with
    ⟨C, hEval_closed⟩
  have hC_nonneg : 0 ≤ (C : ℝ) := C.2
  let K : ℝ := max C 1
  have hK_pos : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_right C 1)
  let η : ℝ := δ / (2 * K)
  have hη_pos : 0 < η := by
    dsimp [η]
    positivity
  have hCη_lt : C * η < δ := by
    have hC_le_K : C ≤ K := le_max_left C 1
    have hη_nonneg : 0 ≤ η := le_of_lt hη_pos
    calc
      C * η ≤ K * η := mul_le_mul_of_nonneg_right hC_le_K hη_nonneg
      _ = δ / 2 := by
        dsimp [η]
        field_simp [hK_pos.ne']
      _ < δ := by linarith
  rcases hf_Cauchy η hη_pos with ⟨B, hB, hBdist⟩
  rcases hf_NeBot.nonempty_of_mem (inter_mem hA hB) with ⟨q, hqA, hqB⟩
  have hFq_bound :
      eLpNormFixed (fun θ : ℝ => (F - q.1) (r * exp (I * θ))) p μ ≤
        ENNReal.ofReal δ := by
    refine eLpNormFixed_le_of_ae_bound_of_one_le
      (p := p) (μ := μ) (Fact.out : (1 : ℝ≥0∞) ≤ p) ?_
    exact Eventually.of_forall fun θ => by
      let z : ℂ := r * exp (I * θ)
      have hz_closed : z ∈ Metric.closedBall (0 : ℂ) r := by
        have hnorm : ‖z‖ = |r| := by
          dsimp [z]
          simp
        rw [Metric.mem_closedBall, dist_zero_right, hnorm, abs_of_pos hr.1]
      have hdist : dist (F z) (q.1 z) ≤ δ :=
        dist_limit_eval_le_of_eventually_dist_ne_top
          (E := E) (p := p) hF hB hqB hC_nonneg hCη_lt hBdist
          (z := z) (fun s => hEval_closed s q z hz_closed)
      simpa [z, Pi.sub_apply, dist_eq_norm_sub] using hdist
  have hqg_bound :
      eLpNormFixed (fun θ : ℝ => (q.1 - g.1) (r * exp (I * θ))) p μ ≤
        ENNReal.ofReal δ := by
    have hradial_le :
        eLpNormFixed (fun θ : ℝ => ((-q + g : HpDisc (E := E) p).1)
            (r * exp (I * θ))) p μ ≤
          hardyNorm (E := E) ((-q + g : HpDisc (E := E) p).1) p :=
      hardyNorm_radial_le ((-q + g : HpDisc (E := E) p).1) p hr
    have hhardy_le :
        hardyNorm (E := E) ((-q + g : HpDisc (E := E) p).1) p ≤
          ENNReal.ofReal δ := by
      have hdist_lt : dist q g < δ := hAdist q hqA g hgA
      have hfin :
          hardyNorm (E := E) ((-q + g : HpDisc (E := E) p).1) p ≠ ∞ :=
        ne_of_lt (-q + g : HpDisc (E := E) p).2.2.1
      have htoReal :
          (hardyNorm (E := E) ((-q + g : HpDisc (E := E) p).1) p).toReal < δ := by
        simpa [dist_eq_norm, norm_def] using hdist_lt
      exact le_of_lt ((ENNReal.lt_ofReal_iff_toReal_lt hfin).2 htoReal)
    calc
      eLpNormFixed (fun θ : ℝ => (q.1 - g.1) (r * exp (I * θ))) p μ
          = eLpNormFixed (fun θ : ℝ => -(((-q + g : HpDisc (E := E) p).1)
              (r * exp (I * θ)))) p μ := by
            congr 1
            funext θ
            simp [Pi.sub_apply, sub_eq_add_neg, add_comm]
      _ = eLpNormFixed (fun θ : ℝ => ((-q + g : HpDisc (E := E) p).1)
              (r * exp (I * θ))) p μ := by
            exact eLpNormFixed_neg
              (fun θ : ℝ => ((-q + g : HpDisc (E := E) p).1) (r * exp (I * θ))) p μ
      _ ≤ ENNReal.ofReal δ := hradial_le.trans hhardy_le
  have hFq_meas : AEStronglyMeasurable
      (fun θ : ℝ => (F - q.1) (r * exp (I * θ))) μ :=
    radial_aestronglyMeasurable (hFanalytic.sub q.2.1).continuousOn hr μ
  have hqg_meas : AEStronglyMeasurable
      (fun θ : ℝ => (q.1 - g.1) (r * exp (I * θ))) μ :=
    radial_aestronglyMeasurable (q.2.1.sub g.2.1).continuousOn hr μ
  calc
    eLpNormFixed (fun θ : ℝ => (F - g.1) (r * exp (I * θ))) p μ
        = eLpNormFixed
            ((fun θ : ℝ => (F - q.1) (r * exp (I * θ))) +
              (fun θ : ℝ => (q.1 - g.1) (r * exp (I * θ)))) p μ := by
          congr 1
          funext θ
          simp [Pi.add_apply, sub_eq_add_neg, add_assoc]
    _ ≤ eLpNormFixed (fun θ : ℝ => (F - q.1) (r * exp (I * θ))) p μ +
          eLpNormFixed (fun θ : ℝ => (q.1 - g.1) (r * exp (I * θ))) p μ :=
        eLpNormFixed_add_le hFq_meas hqg_meas
    _ ≤ ENNReal.ofReal δ + ENNReal.ofReal δ := add_le_add hFq_bound hqg_bound
    _ = ENNReal.ofReal (2 * δ) := by
      rw [← ENNReal.ofReal_add (le_of_lt hδ_pos) (le_of_lt hδ_pos)]
      ring_nf

/-- The ambient-function limit of a Hardy-Cauchy filter has finite Hardy `p`-norm for
`1 ≤ p < ∞`. -/
lemma hardyNorm_lt_top_of_tendsto_coe_cauchy_ne_top
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp_ne_top : p ≠ ∞)
    {f : Filter (HpDisc (E := E) p)} {F : ℂ → E}
    (hf : Cauchy f) (hF : map (fun g : HpDisc p => g.1) f ≤ 𝓝 F)
    (hFanalytic : AnalyticOn ℂ F unitDisc) : hardyNorm F p < ∞ := by
  rcases Metric.cauchy_iff.1 hf with ⟨hf_NeBot, hf_Cauchy⟩
  rcases hf_Cauchy 1 zero_lt_one with ⟨A, hA, hAdist⟩
  rcases hf_NeBot.nonempty_of_mem hA with ⟨g, hgA⟩
  have hdiff_le : hardyNorm (F - g.1) p ≤ ENNReal.ofReal 2 := by
    simpa using hardyNorm_sub_limit_le_of_eventually_dist_lt (E := E) p
     hp_ne_top hf hF hFanalytic (δ := 1) zero_lt_one hA hAdist hgA
  calc
    hardyNorm F p = hardyNorm ((F - g.1) + g.1) p := by
      congr 1; ext z; simp [Pi.add_apply, sub_eq_add_neg, add_assoc]
    _ ≤ hardyNorm (F - g.1) p + hardyNorm g.1 p := hardyNorm_add_le (hFanalytic.sub g.2.1) g.2.1
    _ < ∞ := ENNReal.add_lt_top.2 ⟨lt_of_le_of_lt hdiff_le ENNReal.ofReal_lt_top, g.2.2.1⟩

/-- In the `H∞` case, an ambient-function limit of a Hardy-Cauchy filter has finite Hardy norm. -/
lemma hardyNorm_lt_top_of_tendsto_coe_cauchy_top
    {f : Filter (HpDisc (E := E) ∞)} {F : ℂ → E}
    (hf : Cauchy f) (hF : map (fun g : HpDisc ∞ => g.1) f ≤ 𝓝 F)
    (hFanalytic : AnalyticOn ℂ F unitDisc) : hardyNorm F ∞ < ∞ := by
  -- after review
  rw [hardyNorm_top_eq_Sup_norm hFanalytic.continuousOn]
  rcases Metric.cauchy_iff.1 hf with ⟨hf_NeBot, hf_Cauchy⟩
  rcases hf_Cauchy 1 zero_lt_one with ⟨A, hA, hAdist⟩
  rcases hf.1.nonempty_of_mem hA with ⟨g, hgA⟩
  rw [iSup_lt_iff]
  refine ⟨ENNReal.ofReal (‖g‖ + 1), ENNReal.ofReal_lt_top, ?_⟩
  intro z
  rw [← ofReal_norm_eq_enorm]
  refine ENNReal.ofReal_le_ofReal ?_
  have hdist_le : dist (F z.1) (g.1 z.1) ≤ 1 :=
    dist_limit_eval_le_of_eventually_dist_top hF hA hgA hAdist z.2
  grw [norm_le_norm_add_const_of_dist_le hdist_le]
  grw [norm_eval_le_norm_top g z.2]

/-- An ambient-function limit of a Hardy-Cauchy filter has finite Hardy norm. -/
theorem hardyNorm_lt_top_of_tendsto_coe_cauchy
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    {f : Filter (HpDisc (E := E) p)} {F : ℂ → E}
    (hf : Cauchy f)
    (hF : map (fun g : HpDisc (E := E) p => g.1) f ≤ 𝓝 F)
    (hFanalytic : AnalyticOn ℂ F unitDisc) :
    hardyNorm (E := E) F p < ∞ := by
  by_cases hp_top : p = ∞
  · subst p
    exact hardyNorm_lt_top_of_tendsto_coe_cauchy_top hf hF hFanalytic
  · exact hardyNorm_lt_top_of_tendsto_coe_cauchy_ne_top p hp_top hf hF hFanalytic

/-- For `1 ≤ p < ∞`, let `f` be a Cauchy filter in `H^p`. If the underlying
functions of elements of `f` converge to a function `F`, and if `F` itself belongs
to `H^p`, then `f` converges to `F` in the `H^p` metric. -/
lemma tendsto_hpDisc_of_tendsto_coe_cauchy_ne_top
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp_ne_top : p ≠ ∞)
    {f : Filter (HpDisc (E := E) p)} {F : ℂ → E}
    (hf : Cauchy f) (hF : map (fun g : HpDisc p => g.1) f ≤ 𝓝 F)
    (hFmem : MemHpDisc p F) : f ≤ 𝓝 (⟨F, hFmem⟩ : HpDisc p) := by
  -- after review
  let F : HpDisc (E := E) p := ⟨F, hFmem⟩
  haveI : NeBot f := hf.1
  show Tendsto (fun g : HpDisc (E := E) p => g) f (𝓝 F)
  rw [Metric.tendsto_nhds]
  intro ε hε
  let δ : ℝ := ε / 3
  have hδpos : 0 < δ := by positivity
  have h2δlt : 2 * δ < ε := by dsimp [δ]; linarith
  rcases (Metric.cauchy_iff.1 hf).2 δ hδpos with ⟨A, hA, hAdist⟩
  filter_upwards [hA] with g hgA
  refine lt_of_le_of_lt ?_ h2δlt
  rw [dist_eq_norm]
  rw [← ENNReal.toReal_ofReal (mul_nonneg zero_le_two hδpos.le)]
  refine ENNReal.toReal_mono ENNReal.ofReal_ne_top ?_
  have hhardy_le : hardyNorm (E := E) (F - g.1) p ≤ ENNReal.ofReal (2 * δ) :=
    hardyNorm_sub_limit_le_of_eventually_dist_lt p hp_ne_top hf hF hFmem.1
      hδpos hA hAdist hgA
  simpa [F, Pi.add_apply, sub_eq_add_neg, add_comm] using hhardy_le

/-- In the `H∞` case, ambient-function convergence of a Hardy-Cauchy filter upgrades to
convergence in the Hardy metric. -/
lemma tendsto_hpDisc_of_tendsto_coe_cauchy_top
    {f : Filter (HpDisc (E := E) ∞)} {F : ℂ → E}
    (hf : Cauchy f) (hF : map (fun g : HpDisc ∞ => g.1) f ≤ 𝓝 F)
    (hFmem : MemHpDisc ∞ F) : f ≤ 𝓝 (⟨F, hFmem⟩ : HpDisc ∞) := by
  -- after review
  let F : HpDisc (E := E) ∞ := ⟨F, hFmem⟩
  haveI : NeBot f := hf.1
  show Tendsto (fun g : HpDisc ∞ => g) f (𝓝 F)
  rw [Metric.tendsto_nhds]
  intro ε hε
  let δ : ℝ := ε / 2
  have hδpos : 0 < δ := by positivity
  have hδlt : δ < ε := by dsimp [δ]; linarith
  rcases (Metric.cauchy_iff.1 hf).2 δ hδpos with ⟨A, hA, hAdist⟩
  filter_upwards [hA] with g hgA
  refine lt_of_le_of_lt ?_ hδlt
  rw [← ENNReal.toReal_ofReal hδpos.le]
  rw [dist_eq_norm, norm_def]
  refine ENNReal.toReal_mono ENNReal.ofReal_ne_top ?_
  rw [hardyNorm_top_eq_Sup_norm (-g + F).2.1.continuousOn]
  refine iSup_le ?_
  intro z
  rw [← ofReal_norm_eq_enorm]
  apply ENNReal.ofReal_le_ofReal
  have hpoint_dist : dist (F.1 z.1) (g.1 z.1) ≤ δ :=
    dist_limit_eval_le_of_eventually_dist_top hF hA hgA hAdist z.2
  have hnorm : ‖F.1 z.1 - g.1 z.1‖ ≤ δ := by
    simpa [dist_eq_norm_sub] using hpoint_dist
  simpa [F, Pi.add_apply, sub_eq_add_neg, add_comm] using hnorm



/-- Ambient-function convergence of a Hardy-Cauchy filter upgrades to convergence in the Hardy
metric, once the ambient limit has been shown to lie in `HpDisc p`. -/
theorem tendsto_hpDisc_of_tendsto_coe_cauchy
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    {f : Filter (HpDisc (E := E) p)} {F : ℂ → E}
    (hf : Cauchy f) (hF : map (fun g : HpDisc p => g.1) f ≤ 𝓝 F)
    (hFmem : MemHpDisc p F) : f ≤ 𝓝 (⟨F, hFmem⟩ : HpDisc p) := by
  by_cases hp_top : p = ∞
  · subst p
    exact tendsto_hpDisc_of_tendsto_coe_cauchy_top hf hF hFmem
  · exact tendsto_hpDisc_of_tendsto_coe_cauchy_ne_top p hp_top hf hF hFmem


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
