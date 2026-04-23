import IsingModel.AmbientLattice

/-!
# Random current foundation (GJ §5.1 Simon-Lieb attempt, step 1)

A current on a finite induced subgraph is an `ℕ`-valued function
on its (finite) edge set. This file fixes the type and the basic
algebraic operations (`Zero`, `Add`); subsequent PRs will add the
parity, the source/sink characterisation, and ultimately the
Aizenman switching lemma feeding the random-current expression of
`⟨σ^A⟩^Λ` and Simon-Lieb (FV Prop 9.31).

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.1 pp. 76–79;
Friedli–Velenik §3.7, Prop 9.31. -/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Current on a finite induced subgraph**: an `ℕ`-valued
function on the (finite) edge set of `inducedGraph G Λ`. The
underlying type used for the random-current representation of the
Ising 2-point function in GJ §5.1 / FV Prop 9.31. -/
abbrev Current (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :=
  (inducedGraph G Λ).edgeSet → ℕ

/-- **Zero current**: the constant zero function. -/
instance Current.instZero (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] : Zero (Current G Λ) :=
  ⟨fun _ => 0⟩

/-- **Pointwise addition** of currents. -/
instance Current.instAdd (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] : Add (Current G Λ) :=
  ⟨fun n m => fun e => n e + m e⟩

end Ambient

end IsingModel
