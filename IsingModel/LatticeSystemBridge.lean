import IsingModel.LatticeSystemBridge.Coupling
import IsingModel.LatticeSystemBridge.Abstraction
import IsingModel.LatticeSystemBridge.GibbsCompat
import IsingModel.LatticeSystemBridge.CorrelationCompat

/-!
# Lattice-system integration bridge umbrella

Bridge layer for future merger of `ising-model` into
[`lattice-system`](https://github.com/phasetr/lattice-system). All content is purely
additive — no existing `IsingModel.*` definition is modified.

* `Coupling.lean` — real-valued analog of `LatticeSystem.Lattice.couplingOf`.
* `Abstraction.lean` — abstract `ClassicalSpinSystem` structure and the canonical
  Ising instance.

For the integration plan, see `.self-local/docs/9-lattice-system-integration-plan.md`.
-/
