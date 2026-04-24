import IsingModel.TestGenerators

set_option linter.style.nativeDecide false

/-!
# Test generators for Ising model property tests (Issue #888 Step P1)

Thin wrapper that re-exports `IsingModel.TestGenerators` and provides
`native_decide` sanity checks for the small-graph definitions.

New code should import `IsingModel.TestGenerators` directly.
-/

namespace IsingModel.Test.Generators

open IsingModel.TestGenerators

/-! ## Sanity checks (native_decide) -/

/-- chainGraph2 has exactly 1 edge. -/
example : Fintype.card chainGraph2.edgeSet = 1 := by native_decide

/-- chainGraph3 has exactly 2 edges. -/
example : Fintype.card chainGraph3.edgeSet = 2 := by native_decide

/-- triangleGraph (K₃) has exactly 3 edges. -/
example : Fintype.card triangleGraph.edgeSet = 3 := by native_decide

/-- squareGraph has exactly 4 edges. -/
example : Fintype.card squareGraph.edgeSet = 4 := by native_decide

/-- k4Graph has exactly 6 edges. -/
example : Fintype.card k4Graph.edgeSet = 6 := by native_decide

/-- allConfigsFinset 2 has 4 elements. -/
example : (allConfigsFinset 2).card = 4 := by native_decide

/-- allConfigsFinset 3 has 8 elements. -/
example : (allConfigsFinset 3).card = 8 := by native_decide

/-- chainGraph2: formalCouplingSum = 0. -/
example : formalCouplingSum chainGraph2 = 0 := by native_decide

/-- chainGraph3: formalCouplingSum = 0. -/
example : formalCouplingSum chainGraph3 = 0 := by native_decide

/-- triangleGraph: formalCouplingSum = 0. -/
example : formalCouplingSum triangleGraph = 0 := by native_decide

end IsingModel.Test.Generators
