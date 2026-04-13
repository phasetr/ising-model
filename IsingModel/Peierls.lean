import IsingModel.Lattice

/-!
# Peierls argument for the existence of phase transitions

The Peierls argument shows that the d-dimensional Ising model (d ≥ 2)
has spontaneous magnetization at sufficiently low temperature (large β).

## Main results

* `peierls_bound` — `Pr(γ ⊂ ∂X) ≤ exp(-2β|γ|)` (Proposition 5.4.1)
* `spontaneous_magnetization` — `0 ≤ 1 - ⟨σ_i⟩₊ ≤ exp(-cβ)` (Proposition 5.4.2)

## Proof outline

The Peierls argument works on `ℤ^d` with `d ≥ 2` and + boundary conditions.
For any configuration σ with σ_i = -1, there exists a contour γ enclosing i.
Flipping all spins inside γ removes γ from the phase boundary, decreasing
the energy by `2β|γ|`. This gives the Peierls bound on the probability of γ.
Summing over all contours enclosing i (their number grows at most
exponentially in |γ|) gives the spontaneous magnetization bound for large β.

## References

* Glimm–Jaffe, *Quantum Physics*, §5.4, pp. 80–84.
* Friedli–Velenik, *Statistical Mechanics of Lattice Systems*, §3.7.
-/

namespace IsingModel

open Finset Real

/-! ## Phase boundary (contour) on a finite graph

For any graph G and configuration σ, the phase boundary is the set of
edges where neighboring spins disagree. In the Peierls argument, this
is used with + boundary conditions on a finite box in ℤ^d. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Whether an edge has disagreeing spins (-1 edge spin). -/
private def edgeDisagrees (σ : Config ι) (e : Sym2 ι) : Bool :=
  Sym2.lift ⟨fun i j => decide (σ i ≠ σ j), fun i j => by
    simp only [ne_comm]⟩ e

def phaseBoundary (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet]
    (σ : Config ι) : Finset (Sym2 ι) :=
  G.edgeFinset.filter (fun e => edgeDisagrees σ e)

/-- The number of disagreeing edges (length of the phase boundary). -/
def phaseBoundarySize (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet]
    (σ : Config ι) : ℕ :=
  (phaseBoundary G σ).card

/-- An edge is in the phase boundary iff the spins at its endpoints disagree. -/
theorem mem_phaseBoundary (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet]
    (σ : Config ι) (e : Sym2 ι) :
    e ∈ phaseBoundary G σ ↔
      e ∈ G.edgeFinset ∧ edgeDisagrees σ e = true := by
  simp [phaseBoundary, Finset.mem_filter]

/-! ## Energy in terms of phase boundary

For the Ising model with h = 0 and uniform coupling J, the Hamiltonian
can be expressed in terms of the phase boundary size:
  H(σ) = -J · (|E| - 2|∂σ|)
where |E| is the total number of edges and |∂σ| is the phase boundary size. -/

/-- The edge spin is +1 for agreeing spins and -1 for disagreeing spins. -/
private theorem edgeSpin_eq_one_or_neg_one (σ : Config ι) (e : Sym2 ι) :
    edgeSpin (K := ℝ) σ e = 1 ∨ edgeSpin (K := ℝ) σ e = -1 := by
  refine Sym2.ind (fun i j => ?_) e
  simp only [edgeSpin, Sym2.lift_mk]
  cases σ i <;> cases σ j <;> simp [Spin.sign, Spin.toSign]

/-- For h = 0, the Hamiltonian equals `-J * (|E| - 2|∂σ|)` where |∂σ| is
the phase boundary size. Each agreeing edge contributes +1 to the edge sum
and each disagreeing edge contributes -1, so the sum = |E| - 2|∂σ|. -/
theorem hamiltonian_boundary (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet]
    (J β : ℝ) (σ : Config ι) :
    hamiltonian G ⟨J, 0, β⟩ σ =
      -J * (↑G.edgeFinset.card - 2 * ↑(phaseBoundarySize G σ)) := by
  sorry

/-! ## Peierls bound (Proposition 5.4.1)

For the Ising model with + boundary conditions, the probability that
a given contour γ is part of the phase boundary is bounded by `exp(-2β|γ|)`.

The proof uses the "spin-flip inside γ" argument: for any configuration σ
with γ ⊂ ∂σ, flipping all spins inside γ gives a configuration σ* with
∂(σ*) = ∂σ \ γ, decreasing energy by 2βJ|γ|.

The mapping σ → σ* is injective from {σ : γ ⊂ ∂σ} to {σ : γ ∩ ∂σ = ∅},
which gives:
  Pr(γ ⊂ ∂σ) = Σ_{γ⊂∂σ} w(σ) / Z ≤ Σ_{γ⊂∂σ} w(σ*) exp(-2βJ|γ|) / Z
              ≤ exp(-2βJ|γ|). -/

-- The full Peierls bound requires:
-- 1. Definition of + boundary conditions (fixing boundary spins to +1)
-- 2. The spin-flip map σ → σ* (flip spins inside a contour)
-- 3. The energy decrease: H(σ) - H(σ*) = 2J|γ| for h=0
-- 4. Injectivity of the flip map
-- 5. Summing the ratio w(σ)/w(σ*) = exp(-2βJ|γ|)
--
-- This will be developed in subsequent commits.

end IsingModel
