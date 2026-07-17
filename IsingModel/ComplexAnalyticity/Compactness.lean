import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.UniformSpace.CompactConvergence

/-!
# Complex Compactness Handoffs

This module is part of the split `IsingModel.ComplexAnalyticity` development.
-/

namespace IsingModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped Complex

/-- **Compact-open Arzelà-Ascoli handoff**: if a set of continuous maps has
compact image in the pointwise function space and is equicontinuous, then it is
compact for the compact-open topology on continuous maps. This is a thin
project-local wrapper around mathlib's general `ArzelaAscoli` theorem, used as
the topological target for later Montel-style compactness inputs. -/
theorem isCompact_compactOpen_complex_of_isCompact_toFun_image_equicontinuous
    {X : Type*} [TopologicalSpace X]
    {S : Set C(X, ℂ)}
    (hSfun : IsCompact (ContinuousMap.toFun '' S))
    (hSeq : Equicontinuous ((↑) : S → X → ℂ)) :
    IsCompact S :=
  ArzelaAscoli.isCompact_of_equicontinuous S hSfun hSeq

/-- **Closed-product pointwise compactness handoff**: if the image of a family
of continuous maps in the pointwise function space is closed and every point
evaluation lands in a compact target set, then the pointwise image is compact.
This is a Tychonoff-style bridge used before the compact-open Arzelà-Ascoli
handoff. -/
theorem isCompact_toFun_image_complex_of_isClosed_subset_pi_compacts
    {X : Type*} [TopologicalSpace X]
    {S : Set C(X, ℂ)}
    (K : X → Set ℂ)
    (hK : ∀ x, IsCompact (K x))
    (hclosed : IsClosed (ContinuousMap.toFun '' S))
    (hmem : ∀ f ∈ S, ∀ x, f x ∈ K x) :
    IsCompact (ContinuousMap.toFun '' S) := by
  refine IsCompact.of_isClosed_subset (isCompact_univ_pi hK) hclosed ?_
  rintro _ ⟨f, hf, rfl⟩
  exact Set.mem_pi.mpr (fun x _ => hmem f hf x)

/-- **Closed-product Arzelà-Ascoli handoff**: closedness of the pointwise
function-space image, compact pointwise target sets, and equicontinuity imply
compactness in the compact-open topology. -/
theorem isCompact_compactOpen_complex_of_isClosed_subset_pi_compacts_equicontinuous
    {X : Type*} [TopologicalSpace X]
    {S : Set C(X, ℂ)}
    (K : X → Set ℂ)
    (hK : ∀ x, IsCompact (K x))
    (hclosed : IsClosed (ContinuousMap.toFun '' S))
    (hmem : ∀ f ∈ S, ∀ x, f x ∈ K x)
    (hSeq : Equicontinuous ((↑) : S → X → ℂ)) :
    IsCompact S :=
  isCompact_compactOpen_complex_of_isCompact_toFun_image_equicontinuous
    (isCompact_toFun_image_complex_of_isClosed_subset_pi_compacts
      K hK hclosed hmem)
    hSeq

/-- **Norm-bounded pointwise compactness handoff**: if the pointwise
function-space image is closed and every point evaluation is bounded by a
chosen real radius, then the pointwise image is compact.  The compact
pointwise targets are the closed complex balls `Metric.closedBall 0 (R x)`. -/
theorem isCompact_toFun_image_complex_of_isClosed_norm_le
    {X : Type*} [TopologicalSpace X]
    {S : Set C(X, ℂ)}
    (R : X → ℝ)
    (hclosed : IsClosed (ContinuousMap.toFun '' S))
    (hnorm : ∀ f ∈ S, ∀ x, ‖f x‖ ≤ R x) :
    IsCompact (ContinuousMap.toFun '' S) :=
  isCompact_toFun_image_complex_of_isClosed_subset_pi_compacts
    (fun x => Metric.closedBall (0 : ℂ) (R x))
    (fun x => isCompact_closedBall (0 : ℂ) (R x))
    hclosed
    (fun f hf x => by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hnorm f hf x)

/-- **Norm-bounded closed-product Arzelà-Ascoli handoff**: closedness of the
pointwise image, pointwise norm bounds, and equicontinuity imply compactness
in the compact-open topology. -/
theorem isCompact_compactOpen_complex_of_isClosed_norm_le_equicontinuous
    {X : Type*} [TopologicalSpace X]
    {S : Set C(X, ℂ)}
    (R : X → ℝ)
    (hclosed : IsClosed (ContinuousMap.toFun '' S))
    (hnorm : ∀ f ∈ S, ∀ x, ‖f x‖ ≤ R x)
    (hSeq : Equicontinuous ((↑) : S → X → ℂ)) :
    IsCompact S :=
  isCompact_compactOpen_complex_of_isCompact_toFun_image_equicontinuous
    (isCompact_toFun_image_complex_of_isClosed_norm_le R hclosed hnorm)
    hSeq

/-- **Range norm-bounded pointwise compactness handoff**: if the selected
carrier is the range of a sequence of continuous maps, then stagewise
pointwise norm bounds give the carrier-wide norm bounds needed for the
closed-ball pointwise compactness criterion. -/
theorem isCompact_toFun_range_complex_of_isClosed_norm_le
    {X : Type*} [TopologicalSpace X] {α : Type*}
    (F : α → C(X, ℂ))
    (R : X → ℝ)
    (hclosed : IsClosed (ContinuousMap.toFun '' Set.range F))
    (hnorm : ∀ a, ∀ x, ‖F a x‖ ≤ R x) :
    IsCompact (ContinuousMap.toFun '' Set.range F) :=
  isCompact_toFun_image_complex_of_isClosed_norm_le R hclosed
    (fun f hf x => by
      rcases hf with ⟨a, rfl⟩
      exact hnorm a x)

/-- **Range norm-bounded closed-product Arzelà-Ascoli handoff**: closedness of
the pointwise image of the range, stagewise pointwise norm bounds, and
equicontinuity of the range imply compactness of the range in the compact-open
topology. -/
theorem isCompact_compactOpen_range_complex_of_isClosed_norm_le_equicontinuous
    {X : Type*} [TopologicalSpace X] {α : Type*}
    (F : α → C(X, ℂ))
    (R : X → ℝ)
    (hclosed : IsClosed (ContinuousMap.toFun '' Set.range F))
    (hnorm : ∀ a, ∀ x, ‖F a x‖ ≤ R x)
    (hSeq : Equicontinuous ((↑) : Set.range F → X → ℂ)) :
    IsCompact (Set.range F) :=
  isCompact_compactOpen_complex_of_isClosed_norm_le_equicontinuous
    R hclosed
    (fun f hf x => by
      rcases hf with ⟨a, rfl⟩
      exact hnorm a x)
    hSeq

end IsingModel
