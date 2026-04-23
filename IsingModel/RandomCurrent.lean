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

/-- **Parity at a vertex**: for a current `n` and a vertex
`v : ↑Λ`, the parity (mod 2) of the sum of `n e` over edges `e`
incident to `v`. The source set of `n` is the set of vertices
where the parity is non-zero; the parity drives the source/sink
characterisation and the Aizenman switching lemma in subsequent
PRs (FV §3.7). -/
def Current.parity (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (v : ↑Λ) : ZMod 2 :=
  ∑ e : (inducedGraph G Λ).edgeSet,
    if v ∈ (e : Sym2 ↑Λ) then ((n e : ℕ) : ZMod 2) else 0

omit [DecidableEq V] in
/-- **Zero parity**: the zero current has parity `0` at every
vertex (each summand vanishes). -/
@[simp]
theorem Current.zero_parity (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (v : ↑Λ) :
    (0 : Current G Λ).parity G Λ v = 0 := by
  unfold Current.parity
  simp only [show ((0 : Current G Λ) : (inducedGraph G Λ).edgeSet → ℕ) = fun _ => 0
    from rfl]
  simp

omit [DecidableEq V] in
/-- **Additive parity**: parity distributes over addition of
currents (sum of parities equals parity of the sum). -/
theorem Current.add_parity (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n m : Current G Λ) (v : ↑Λ) :
    (n + m).parity G Λ v = n.parity G Λ v + m.parity G Λ v := by
  unfold Current.parity
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  by_cases hv : v ∈ (e : Sym2 ↑Λ)
  · simp [hv, show ((n + m) e : ℕ) = n e + m e from rfl, Nat.cast_add]
  · simp [hv]

end Ambient

end IsingModel
