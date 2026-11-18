import HardySpaceFormalization.Harmonic_max_principle
import Mathlib.Analysis.Complex.Harmonic.MeanValue

/-!
# Mean value property and maximum principles on `ℂ`

The complex case of the ball-average mean value property and its converse, split off from
`Harmonic_max_principle.lean`, together with `ℂ` versions of that file's maximum and comparison
principles. These rest on the proved `HarmonicOnNhd.ballAverage_eq_complex` instead of the general
`HarmonicOnNhd.ballAverage_eq`.
-/

open MeasureTheory Metric Set Real Filter
open scoped ENNReal Topology

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ### The complex case

On `ℂ` the mean value property for balls follows from mathlib's circle version
`InnerProductSpace.HarmonicOnNhd.circleAverage_eq` by integrating in polar coordinates. -/

/-- In polar coordinates, the ball average on `ℂ` is a weighted radial integral of circle
averages: `ballAverage f c R = (2 / R ^ 2) • ∫ r in 0..R, r • circleAverage f c r`. -/
theorem ballAverage_eq_intervalIntegral_circleAverage [CompleteSpace F] {f : ℂ → F} {c : ℂ}
    {R : ℝ} (hR : 0 < R) (hf : ContinuousOn f (closedBall c R)) :
    ballAverage f c R = (2 / R ^ 2) • ∫ r in (0 : ℝ)..R, r • circleAverage f c r := by
  -- The integrand in polar coordinates.
  set G : ℝ × ℝ → F := fun p => p.1 • f (circleMap c p.1 p.2) with hG
  have hsymm : ∀ p : ℝ × ℝ, c + Complex.polarCoord.symm p = circleMap c p.1 p.2 := by
    intro p
    simp [circleMap, Complex.exp_mul_I]
  -- Translate to the origin and change to polar coordinates.
  have hpolar : ∫ y in ball c R, f y = ∫ p in Ioo 0 R ×ˢ Ioo (-π) π, G p := by
    have h1 : ∫ y in ball c R, f y = ∫ z, (ball c R).indicator f (c + z) := by
      rw [integral_add_left_eq_self (fun y => (ball c R).indicator f y) c,
        integral_indicator measurableSet_ball]
    rw [h1, ← Complex.integral_comp_polarCoord_symm
      (fun z => (ball c R).indicator f (c + z)), polarCoord_target]
    have hset : Ioo 0 R ×ˢ Ioo (-π) π = (Ioi (0 : ℝ) ×ˢ Ioo (-π) π) ∩ (Iio R ×ˢ univ) := by
      ext p
      simp only [mem_prod, mem_Ioo, mem_inter_iff, mem_Ioi, mem_Iio, mem_univ]
      tauto
    rw [hset, ← setIntegral_indicator (measurableSet_Iio.prod MeasurableSet.univ)]
    refine setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) fun p hp => ?_
    have hp0 : 0 < p.1 := hp.1
    have hiff : c + Complex.polarCoord.symm p ∈ ball c R ↔ p.1 < R := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_polarCoord_symm,
        abs_of_pos hp0]
    by_cases hpR : p.1 < R
    · have hmem : p ∈ Iio R ×ˢ (univ : Set ℝ) := ⟨hpR, mem_univ _⟩
      rw [indicator_of_mem (hiff.2 hpR), indicator_of_mem hmem, hsymm]
    · have hmem : p ∉ Iio R ×ˢ (univ : Set ℝ) := fun h => hpR h.1
      simp only [indicator_of_notMem (mt hiff.1 hpR), indicator_of_notMem hmem, smul_zero]
  -- Fubini on the rectangle; integrability comes from continuity on the compact closure.
  have hGcont : ContinuousOn G (Icc 0 R ×ˢ Icc (-π) π) := by
    refine continuousOn_fst.smul (hf.comp (by unfold circleMap; fun_prop) fun p hp => ?_)
    rw [← hsymm, mem_closedBall, dist_eq_norm, add_sub_cancel_left,
      Complex.norm_polarCoord_symm, abs_of_nonneg hp.1.1]
    exact hp.1.2
  have hGint : IntegrableOn G (Ioo 0 R ×ˢ Ioo (-π) π) :=
    (hGcont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  have hfub : ∫ p in Ioo 0 R ×ˢ Ioo (-π) π, G p =
      ∫ r in Ioo 0 R, ∫ θ in Ioo (-π) π, G (r, θ) := by
    rw [Measure.volume_eq_prod] at hGint ⊢
    exact setIntegral_prod _ hGint
  -- The angular integral is `2π` times the circle average.
  have hinner : ∀ r : ℝ, ∫ θ in Ioo (-π) π, G (r, θ) = (2 * π) • (r • circleAverage f c r) := by
    intro r
    have hc : circleAverage f c r = (2 * π)⁻¹ • ∫ θ in (-π)..π, f (circleMap c r θ) := by
      rw [circleAverage_eq_integral_add (-π),
        intervalIntegral.integral_comp_add_right (fun θ => f (circleMap c r θ))]
      congr 2 <;> ring
    simp only [hG]
    rw [integral_smul, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by linarith [pi_pos]), hc, smul_comm r (2 * π)⁻¹,
      smul_smul, mul_inv_cancel₀ (by positivity), one_smul]
  unfold ballAverage
  simp_rw [hpolar, hfub, hinner]
  rw [integral_smul, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hR.le,
    Complex.volume_ball, smul_smul]
  congr 1
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hR.le,
    ENNReal.coe_toReal, NNReal.coe_real_pi]
  field_simp

/-- Mean value property for ball averages on `ℂ`. -/
theorem HarmonicOnNhd.ballAverage_eq_complex [CompleteSpace F] {f : ℂ → F} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : InnerProductSpace.HarmonicOnNhd f (closedBall c R)) :
    ballAverage f c R = f c := by
  rw [ballAverage_eq_intervalIntegral_circleAverage hR hf.continuousOn]
  -- Every circle average of radius `r ∈ [0, R]` equals `f c`.
  have h : ∀ r ∈ Set.uIcc 0 R, r • circleAverage f c r = r • f c := by
    intro r hr
    rw [Set.uIcc_of_le hR.le] at hr
    rw [InnerProductSpace.HarmonicOnNhd.circleAverage_eq
      (hf.mono (closedBall_subset_closedBall (by rw [abs_of_nonneg hr.1]; exact hr.2)))]
  rw [intervalIntegral.integral_congr h, intervalIntegral.integral_smul_const, integral_id,
    smul_smul]
  have hc : 2 / R ^ 2 * ((R ^ 2 - 0 ^ 2) / 2) = 1 := by
    field_simp
    ring
  rw [hc, one_smul]

/-- A local mean-value property for ball averages implies harmonicity on `ℂ`. -/
theorem HarmonicOnNhd_of_ballAverage_eq_complex {u : ℂ → F} {s : Set ℂ}
    (hs : IsOpen s) (hcont : ContinuousOn u s)
    (hmean : ∀ x ∈ s, ∃ ε > 0, ∀ r (_ : 0 < r ∧ r < ε), ballAverage u x r = u x) :
    InnerProductSpace.HarmonicOnNhd u s := by
  sorry

/-! ### Maximum principles on `ℂ`

The strong maximum principle only uses the local ball mean value property, so it is first proved
for continuous functions having that property. For harmonic functions this property is
`HarmonicOnNhd.ballAverage_eq_complex`, so the harmonic maximum and comparison principles on `ℂ`
below do not depend on the general `HarmonicOnNhd.ballAverage_eq`. -/

/-- If a continuous real function with the local ball mean value property attains its maximum
over an open set `s` at `a`, then its maximum level set is open in the subtype topology on `s`. -/
lemma isOpen_maxLevelSet_of_ballAverage_eq_complex
    {v : ℂ → ℝ} {s : Set ℂ} {a : ℂ}
    (hs_open : IsOpen s) (hv_cont : ContinuousOn v s)
    (hv_mean : ∀ x ∈ s, ∃ ε > 0, ∀ r (_ : 0 < r ∧ r < ε), ballAverage v x r = v x)
    (hmax : ∀ y ∈ s, v y ≤ v a) :
    IsOpen ({x : s | v x = v a} : Set s) := by
  rw [Metric.isOpen_iff]
  intro x hxT
  rcases Metric.nhds_basis_closedBall.mem_iff.mp (hs_open.mem_nhds x.property) with
    ⟨r₀, hr₀_pos, hr₀_sub⟩
  rcases hv_mean x x.property with ⟨ε, hε_pos, hε⟩
  -- A radius small enough for both the inclusion in `s` and the mean value property.
  set r := min r₀ (ε / 2) with hr_def
  have hr_pos : 0 < r := lt_min hr₀_pos (half_pos hε_pos)
  have hclosed_sub : closedBall (x : ℂ) r ⊆ s :=
    (closedBall_subset_closedBall (min_le_left _ _)).trans hr₀_sub
  have hmean : ballAverage v (x : ℂ) r = v (x : ℂ) :=
    hε r ⟨hr_pos, (min_le_right _ _).trans_lt (half_lt_self hε_pos)⟩
  refine ⟨r, hr_pos, fun y hy => ?_⟩
  have hy_ball : (y : ℂ) ∈ ball (x : ℂ) r := by
    simpa only [Metric.mem_ball, Subtype.dist_eq] using hy
  have hv_le : ∀ z ∈ closedBall (x : ℂ) r, v z ≤ v (x : ℂ) := fun z hz =>
    (hmax z (hclosed_sub hz)).trans_eq hxT.symm
  by_contra hy_not
  have hy_lt : v (y : ℂ) < v (x : ℂ) :=
    lt_of_le_of_ne (hv_le y (ball_subset_closedBall hy_ball))
      fun hy_eq => hy_not (hy_eq.trans hxT)
  have havg_lt : ballAverage v (x : ℂ) r < v (x : ℂ) :=
    ballAverage_lt_of_forall_le_of_exists_lt hr_pos (hv_cont.mono hclosed_sub) hv_le
      ⟨y, hy_ball, hy_lt⟩
  rw [hmean] at havg_lt
  exact lt_irrefl _ havg_lt

/-- Strong maximum/minimum principle on `ℂ` for continuous real functions with the local ball mean
value property: if such a function on a connected open set attains an interior maximum or
minimum, then it is constant there. -/
theorem maximum_minimum_principle_of_ballAverage_eq_complex
    {u : ℂ → ℝ} {s : Set ℂ}
    (hs_open : IsOpen s) (hs_conn : IsPreconnected s) (hu_cont : ContinuousOn u s)
    (hu_mean : ∀ x ∈ s, ∃ ε > 0, ∀ r (_ : 0 < r ∧ r < ε), ballAverage u x r = u x)
    (h_extreme : (∃ x ∈ s, ∀ y ∈ s, u y ≤ u x) ∨ (∃ x ∈ s, ∀ y ∈ s, u x ≤ u y)) :
    ∃ c : ℝ, ∀ x ∈ s, u x = c := by
  have max_case : ∀ {v : ℂ → ℝ}, ContinuousOn v s →
      (∀ x ∈ s, ∃ ε > 0, ∀ r (_ : 0 < r ∧ r < ε), ballAverage v x r = v x) →
      (∃ a ∈ s, ∀ y ∈ s, v y ≤ v a) → ∃ c : ℝ, ∀ x ∈ s, v x = c := by
    intro v hv_cont hv_mean hmax
    rcases hmax with ⟨a, ha, hmax⟩
    let T : Set s := {x | v x = v a}
    have : PreconnectedSpace s := Subtype.preconnectedSpace hs_conn
    have hT_nonempty : T.Nonempty := ⟨⟨a, ha⟩, rfl⟩
    have hT_closed : IsClosed T := by
      have hv_cont_s : Continuous (s.domRestrict v) := hv_cont.domRestrict
      simpa [T, Set.domRestrict_apply] using isClosed_eq hv_cont_s continuous_const
    have hT_open : IsOpen T :=
      isOpen_maxLevelSet_of_ballAverage_eq_complex hs_open hv_cont hv_mean hmax
    have hT_univ : T = Set.univ := IsClopen.eq_univ ⟨hT_closed, hT_open⟩ hT_nonempty
    refine ⟨v a, fun x hx => ?_⟩
    have : (⟨x, hx⟩ : s) ∈ T := by
      rw [hT_univ]
      exact mem_univ _
    simpa [T] using this
  rcases h_extreme with hmax | hmin
  · exact max_case hu_cont hu_mean hmax
  · rcases hmin with ⟨a, ha, hmin⟩
    -- The minimum case is the maximum case for `-u`, which inherits the mean value property.
    have hneg_mean :
        ∀ x ∈ s, ∃ ε > 0, ∀ r (_ : 0 < r ∧ r < ε), ballAverage (-u) x r = (-u) x := by
      intro x hx
      rcases hu_mean x hx with ⟨ε, hε, hε_mean⟩
      refine ⟨ε, hε, fun r hr => ?_⟩
      have h := hε_mean r hr
      simp only [ballAverage, Pi.neg_apply, integral_neg, smul_neg] at h ⊢
      rw [h]
    have hmax_neg : ∃ x ∈ s, ∀ y ∈ s, (-u) y ≤ (-u) x :=
      ⟨a, ha, fun y hy => neg_le_neg (hmin y hy)⟩
    rcases max_case hu_cont.neg hneg_mean hmax_neg with ⟨c, hc⟩
    refine ⟨-c, fun x hx => ?_⟩
    have hcx := hc x hx
    change -u x = c at hcx
    linarith

/-- Strong maximum/minimum principle for real-valued harmonic functions on `ℂ`: if a harmonic
function on a connected domain attains an interior maximum or minimum, then it is constant on the
domain. -/
theorem harmonic_maximum_minimum_principle_complex
    {u : ℂ → ℝ} {s : Set ℂ}
    (hs_open : IsOpen s) (hs_conn : IsPreconnected s)
    (hu : InnerProductSpace.HarmonicOnNhd u s)
    (h_extreme : (∃ x ∈ s, ∀ y ∈ s, u y ≤ u x) ∨ (∃ x ∈ s, ∀ y ∈ s, u x ≤ u y)) :
    ∃ c : ℝ, ∀ x ∈ s, u x = c := by
  refine maximum_minimum_principle_of_ballAverage_eq_complex hs_open hs_conn hu.continuousOn
    (fun x hx => ?_) h_extreme
  rcases Metric.nhds_basis_closedBall.mem_iff.mp (hs_open.mem_nhds hx) with ⟨ε, hε, hε_sub⟩
  exact ⟨ε, hε, fun r hr => HarmonicOnNhd.ballAverage_eq_complex hr.1
    (hu.mono ((closedBall_subset_closedBall hr.2.le).trans hε_sub))⟩

/-- A harmonic function on a bounded connected domain in `ℂ` achieves its maximum on the
boundary. -/
lemma harmonic_exists_isMaxOn_frontier_of_bounded_domain_complex
    {u : ℂ → ℝ} {s : Set ℂ}
    (hs_open : IsOpen s) (hs_conn : IsPreconnected s)
    (hs_nonempty : s.Nonempty)
    (hs_bdd : Bornology.IsBounded s)
    (hu_cont : ContinuousOn u (closure s))
    (hu_harm : InnerProductSpace.HarmonicOnNhd u s) :
    ∃ z ∈ frontier s, IsMaxOn u (closure s) z := by
  have hcompact : IsCompact (closure s) := hs_bdd.isCompact_closure
  rcases hcompact.exists_isMaxOn hs_nonempty.closure hu_cont with
    ⟨a, ha_closure, ha_max⟩
  by_cases ha_frontier : a ∈ frontier s
  · exact ⟨a, ha_frontier, ha_max⟩
  · have ha_s : a ∈ s :=
      mem_of_mem_closure_not_mem_frontier_of_isOpen hs_open ha_closure ha_frontier
    have h_extreme :
        (∃ x ∈ s, ∀ y ∈ s, u y ≤ u x) ∨
          (∃ x ∈ s, ∀ y ∈ s, u x ≤ u y) := by
      left
      refine ⟨a, ha_s, ?_⟩
      intro y hy
      exact ha_max (subset_closure hy)
    rcases harmonic_maximum_minimum_principle_complex
        hs_open hs_conn hu_harm h_extreme with ⟨C, hC⟩
    have hC_closure : ∀ y ∈ closure s, u y = C :=
      eqOn_closure_of_eqOn_of_continuousOn hu_cont hC
    have hs_ne_univ : s ≠ Set.univ := by
      intro hs_eq
      have hbdd_univ : Bornology.IsBounded (Set.univ : Set ℂ) := by
        simpa [hs_eq] using hs_bdd
      exact NormedSpace.unbounded_univ ℝ ℂ hbdd_univ
    have hfrontier_nonempty : (frontier s).Nonempty :=
      (nonempty_frontier_iff).2 ⟨hs_nonempty, hs_ne_univ⟩
    rcases hfrontier_nonempty with ⟨z, hz_frontier⟩
    refine ⟨z, hz_frontier, ?_⟩
    intro y hy
    change u y ≤ u z
    rw [hC_closure y hy, hC_closure z (frontier_subset_closure hz_frontier)]

/-- A harmonic function on a bounded connected domain in `ℂ` achieves its minimum on the
boundary. -/
lemma harmonic_exists_isMinOn_frontier_of_bounded_domain_complex
    {u : ℂ → ℝ} {s : Set ℂ}
    (hs_open : IsOpen s) (hs_conn : IsPreconnected s)
    (hs_nonempty : s.Nonempty)
    (hs_bdd : Bornology.IsBounded s)
    (hu_cont : ContinuousOn u (closure s))
    (hu_harm : InnerProductSpace.HarmonicOnNhd u s) :
    ∃ w ∈ frontier s, IsMinOn u (closure s) w := by
  rcases harmonic_exists_isMaxOn_frontier_of_bounded_domain_complex (u := -u) (s := s)
      hs_open hs_conn hs_nonempty hs_bdd hu_cont.neg hu_harm.neg with
    ⟨w, hw_frontier, hw_max_neg⟩
  refine ⟨w, hw_frontier, ?_⟩
  intro y hy
  simpa using hw_max_neg hy

/-- A harmonic function on a bounded connected domain in `ℂ` achieves its maximum and minimum on
the boundary. -/
theorem harmonic_exists_isMaxOn_isMinOn_frontier_of_bounded_domain_complex
    {u : ℂ → ℝ} {s : Set ℂ}
    (hs_open : IsOpen s) (hs_conn : IsPreconnected s)
    (hs_nonempty : s.Nonempty)
    (hs_bdd : Bornology.IsBounded s)
    (hu_cont : ContinuousOn u (closure s))
    (hu_harm : InnerProductSpace.HarmonicOnNhd u s) :
    (∃ z ∈ frontier s, IsMaxOn u (closure s) z)
      ∧ (∃ w ∈ frontier s, IsMinOn u (closure s) w) :=
  ⟨harmonic_exists_isMaxOn_frontier_of_bounded_domain_complex
      hs_open hs_conn hs_nonempty hs_bdd hu_cont hu_harm,
    harmonic_exists_isMinOn_frontier_of_bounded_domain_complex
      hs_open hs_conn hs_nonempty hs_bdd hu_cont hu_harm⟩

/-- Maximum principle on a bounded connected domain in `ℂ`: if a harmonic function is continuous on
the closure of the domain and is bounded above by `M` on the frontier, then it is bounded above by
`M` throughout the domain. -/
theorem harmonic_maximum_principle_on_domain_complex
    {u : ℂ → ℝ} {s : Set ℂ} {M : ℝ}
    (hs_open : IsOpen s) (hs_conn : IsPreconnected s)
    (hs_nonempty : s.Nonempty)
    (hs_bdd : Bornology.IsBounded s)
    (hu : InnerProductSpace.HarmonicOnNhd u s)
    (huc : ContinuousOn u (closure s)) :
    (∀ y ∈ frontier s, u y ≤ M) → ∀ y ∈ s, u y ≤ M := by
  intro hbd y hy
  rcases harmonic_exists_isMaxOn_frontier_of_bounded_domain_complex
      hs_open hs_conn hs_nonempty hs_bdd huc hu with
    ⟨z, hz_frontier, hz_max⟩
  exact (hz_max (subset_closure hy)).trans (hbd z hz_frontier)

/-- Comparison principle on a bounded connected domain in `ℂ`: if two harmonic functions are
continuous on the closure of the domain and `u ≤ v` on the frontier, then `u ≤ v` throughout the
domain. -/
theorem harmonic_comparison_principle_on_domain_complex
    {u v : ℂ → ℝ} {s : Set ℂ}
    (hs_open : IsOpen s) (hs_conn : IsPreconnected s)
    (hs_nonempty : s.Nonempty)
    (hs_bdd : Bornology.IsBounded s)
    (hu : InnerProductSpace.HarmonicOnNhd u s)
    (hv : InnerProductSpace.HarmonicOnNhd v s)
    (huc : ContinuousOn u (closure s))
    (hvc : ContinuousOn v (closure s)) :
    (∀ y ∈ frontier s, u y ≤ v y) → ∀ y ∈ s, u y ≤ v y := by
  intro hbd y hy
  have hdiff_harm : InnerProductSpace.HarmonicOnNhd (u - v) s := hu.sub hv
  have hdiff_cont : ContinuousOn (u - v) (closure s) := huc.sub hvc
  have hdiff_bd : ∀ y ∈ frontier s, (u - v) y ≤ 0 := by
    intro y hy
    exact sub_nonpos.mpr (hbd y hy)
  have hdiff_dom : ∀ y ∈ s, (u - v) y ≤ 0 :=
    harmonic_maximum_principle_on_domain_complex
      hs_open hs_conn hs_nonempty hs_bdd hdiff_harm hdiff_cont hdiff_bd
  exact sub_nonpos.mp (hdiff_dom y hy)

/-- Maximum principle on a ball in `ℂ`: if a harmonic function is continuous on the closed ball
and is bounded above by `M` on the sphere, then it is bounded above by `M` inside the ball. -/
theorem harmonic_maximum_principle_on_ball_complex
    {u : ℂ → ℝ} {x : ℂ} {r M : ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u (ball x r))
    (huc : ContinuousOn u (closedBall x r)) :
    (∀ y ∈ sphere x r, u y ≤ M) → ∀ y ∈ ball x r, u y ≤ M := by
  intro hbd y hy
  have hr : 0 < r := pos_of_mem_ball hy
  have huc_closure : ContinuousOn u (closure (ball x r)) := by
    simpa [closure_ball x hr.ne'] using huc
  have hbd_frontier : ∀ z ∈ frontier (ball x r), u z ≤ M := by
    intro z hz
    exact hbd z (by simpa [frontier_ball x hr.ne'] using hz)
  exact harmonic_maximum_principle_on_domain_complex
    (s := ball x r) (u := u) (M := M)
    isOpen_ball isPreconnected_ball ⟨x, mem_ball_self hr⟩ isBounded_ball
    hu huc_closure hbd_frontier y hy

/-- Comparison principle on a ball in `ℂ`: if two harmonic functions are continuous on the closed
ball and `u ≤ v` on the sphere, then `u ≤ v` inside the ball. -/
theorem harmonic_comparison_principle_on_ball_complex
    {u v : ℂ → ℝ} {x : ℂ} {r : ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u (ball x r))
    (hv : InnerProductSpace.HarmonicOnNhd v (ball x r))
    (huc : ContinuousOn u (closedBall x r))
    (hvc : ContinuousOn v (closedBall x r)) :
    (∀ y ∈ sphere x r, u y ≤ v y) → ∀ y ∈ ball x r, u y ≤ v y := by
  intro hbd y hy
  have hr : 0 < r := pos_of_mem_ball hy
  have huc_closure : ContinuousOn u (closure (ball x r)) := by
    simpa [closure_ball x hr.ne'] using huc
  have hvc_closure : ContinuousOn v (closure (ball x r)) := by
    simpa [closure_ball x hr.ne'] using hvc
  have hbd_frontier : ∀ z ∈ frontier (ball x r), u z ≤ v z := by
    intro z hz
    exact hbd z (by simpa [frontier_ball x hr.ne'] using hz)
  exact harmonic_comparison_principle_on_domain_complex
    (s := ball x r) (u := u) (v := v)
    isOpen_ball isPreconnected_ball ⟨x, mem_ball_self hr⟩ isBounded_ball
    hu hv huc_closure hvc_closure hbd_frontier y hy
