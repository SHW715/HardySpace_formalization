import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

/-!
# Harmonic functions composed with holomorphic maps

A real harmonic function on an open subset of `ℂ` composed with a holomorphic map is harmonic.
mathlib only records post-composition with continuous linear maps (`HarmonicAt.comp_CLM`).

The proof is local: near `φ x` the function `u` is the real part of a holomorphic `F`
(`HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq`), so near `x` the composition `u ∘ φ` is the
real part of the holomorphic `F ∘ φ`.
-/

open Metric Set
open scoped Topology

namespace InnerProductSpace

variable {u : ℂ → ℝ} {φ : ℂ → ℂ} {x : ℂ} {s t : Set ℂ}

/-- A real harmonic function composed with a holomorphic map is harmonic. -/
theorem HarmonicAt.comp_analyticAt (hu : HarmonicAt u (φ x)) (hφ : AnalyticAt ℂ φ x) :
    HarmonicAt (u ∘ φ) x := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (isOpen_setOf_harmonicAt u) (φ x) hu
  obtain ⟨F, hF, hFu⟩ :=
    HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq (f := u) fun y hy => hball hy
  have hFφ : AnalyticAt ℂ (F ∘ φ) x := (hF (φ x) (mem_ball_self hε)).comp hφ
  refine (harmonicAt_congr_nhds ?_).1 hFφ.harmonicAt_re
  filter_upwards [hφ.continuousAt.preimage_mem_nhds (ball_mem_nhds _ hε)] with y hy
  exact hFu hy

/-- A real harmonic function composed with a holomorphic map is harmonic. -/
theorem HarmonicOnNhd.comp_analyticOnNhd (hu : HarmonicOnNhd u t) (hφ : AnalyticOnNhd ℂ φ s)
    (hst : MapsTo φ s t) : HarmonicOnNhd (u ∘ φ) s :=
  fun x hx => (hu (φ x) (hst hx)).comp_analyticAt (hφ x hx)

end InnerProductSpace
