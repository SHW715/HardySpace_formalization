# Remaining work

## Lebesgue point API

Recorded: 2026-10-12. Status: deferred; design proposal, not implemented.

Consider a small API refactor that names the Lebesgue point condition already used
in the Poisson--Fatou development. Reuse mathlib's differentiation theory rather
than rebuilding a differentiation basis or reproving its covering theorems.

### Proposed scope

- Define the condition relative to an averaging filter on sets, using the limit
  of the average of `‖f y - f x‖` as the defining property. A possible interface is
  `IsLebesguePoint μ l f x`, with `l : Filter (Set α)`; this is a design sketch,
  not a checked declaration. Passing a single filter suffices at a given point.
- Keep the definition independent of the Vitali covering property. That property
  belongs to the theorem proving that almost every point is a Lebesgue point.
- Wrap `VitaliFamily.ae_tendsto_average_norm_sub` to obtain the a.e. theorem with
  averaging filter `v.filterAt x`. Preserve its general normed-group codomain.
- Add only the filter-transport lemmas needed to specialize to shrinking closed
  balls and circle averages. A suitable `Tendsto` relation suffices to transport
  convergence; equality of the filters is not needed for the current application.
- Express the existing circle-specific hypotheses through this interface while
  retaining the current proofs and compatibility with existing consumers.

### Extend the circle differentiation theorem's codomain

Recorded: 2026-10-13. Status: deferred.

- `ae_tendsto_average_abs_sub_circleMeasure` currently accepts real-valued
  functions. Its mathematical conclusion also holds for complex-valued functions.
  More generally, mathlib's `VitaliFamily.ae_tendsto_average_norm_sub` only requires
  a `NormedAddCommGroup` codomain, so the circle specialization can retain that
  generality by using `‖f y - f x‖` in place of the real absolute value.
- During the API refactor, provide the general norm-valued average statement and
  preserve the existing real-valued result as a specialization for current users.
  This reuses the existing differentiation theorem rather than needing a new proof
  through real and imaginary parts.
- The thesis Lebesgue point definition and differentiation theorem temporarily
  use `f : T → ℝ` to match the current circle interface. Revisit their stated
  codomain when the extension is implemented.
- Extending the circle differentiation theorem does not by itself generalize the
  real-density Poisson--Fatou theorems. Assess their integral and codomain
  requirements separately if complex- or vector-valued boundary data are needed.

### Design questions to resolve before implementation

- An arbitrary filter does not guarantee that its sets shrink to the specified
  point or have positive finite measure. The filter constantly selecting the
  empty set makes the average condition hold for every function; `NeBot` alone
  does not rule this out.
- mathlib's Bochner averages are totalized: nonintegrability and infinite measure
  can yield zero. Decide explicitly whether the predicate records only average
  convergence, with validity assumptions supplied by its theorems. The current
  preference is this lightweight approach, with documented hypotheses ensuring
  shrinking sets, eventually positive finite measure, and the integrability
  needed for mathematical applications.
- Keep the distinction between a pointwise Lebesgue point hypothesis and an a.e.
  existence theorem. A.e. differentiation cannot replace a hypothesis at a
  specified point in the pointwise Poisson convergence theorem.
- Do not assume `IsUnifLocDoublingMeasure` for `circleMeasure 0 1` viewed as a
  measure on ambient `ℂ`. Continue using the Besicovitch Vitali family; a measure
  on the circle subtype would be a separate setup.

### Existing code and references

In [NontangentialLimit.lean](HardySpaceFormalization/NontangentialLimit.lean):

- `ae_tendsto_average_abs_sub_circleMeasure`: the a.e. circle statement, already
  obtained from `VitaliFamily.ae_tendsto_average_norm_sub`.
- `hasNontangentialLimit_poissonIntegral_of_lebesguePoint`: pointwise Poisson
  convergence, currently taking the average-limit condition explicitly.
- `isAEBoundaryValue_poissonIntegral`: combines the two preceding results.

Relevant mathlib modules:

- `MeasureTheory/Covering/VitaliFamily.lean`: `filterAt`, its nontriviality,
  `filterAt_basis_closedBall`, and `tendsto_filterAt_iff`.
- `MeasureTheory/Covering/Differentiation.lean`: a.e. average-norm convergence,
  measure differentiation, and the singular-measure zero-density theorem.
- `MeasureTheory/Covering/Besicovitch.lean`: `vitaliFamily` and `tendsto_filterAt`.
- `MeasureTheory/Integral/Average.lean`: average definitions and totalization.

### Limits of this task

Do not generalize Poisson convergence to arbitrary averaging filters merely by
changing the Lebesgue point definition. The proof still needs the relation
between the Poisson kernel, ball-density bounds, and circle geometry. Revisit
that larger abstraction when a second substantive application, such as another
approximate identity or domain, supplies concrete requirements.

When implementing, run `lake build`, preserve the Fatou chain's freedom from
`sorryAx`, and update the blueprint for any new roadmap-level definition or
changed statements. Update the module map if a general-purpose module is added.
