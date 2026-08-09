import IsingModel.Concrete.LatticeGraphBED
import IsingModel.PhaseTransition
import IsingModel.Inequalities.FKG

/-!
# ℤ^d magnetization surface, assembled

Gathers behind a single import the ℤ^d material supplied by the modules it imports: the
lattice graph together with its boundary and energy-distribution layer, the phase-transition
layer in which the finite-volume magnetization and susceptibility are defined and their
behaviour in the parameters is established, and the FKG correlation inequality.

Reference: Glimm--Jaffe, *Quantum Physics* (2nd ed.), §4.4 for the FKG inequality and §5.3
for the magnetization as the one-point expectation.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

end Ambient
end IsingModel
