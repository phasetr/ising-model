import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic
import IsingModel.GibbsMeasure
import IsingModel.Hamiltonian

/-!
# Edge enumeration of the cycle graph (GJ §17.1 transfer-matrix bridge)

To identify the transfer-matrix partition function `Tr(Tᴺ)` with the project's
graph-based Ising partition function on the cyclic chain, one needs the edge set
of `SimpleGraph.cycleGraph N` enumerated as the `N` cyclic nearest-neighbour
pairs.  Mathlib provides the adjacency (`cycleGraph_adj`: `u ~ v ↔ u-v=±1`) but
not the edge-finset enumeration, supplied here:

  `(cycleGraph (n+2)).edgeFinset = image (fun i => s(i, i+1)) univ`.

This is the combinatorial input for rewriting a product over cycle-graph edges as
a linear product over `Fin N` (the transfer-matrix form).

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §17.1.
-/

namespace IsingModel

namespace TransferMatrix

open Finset SimpleGraph

/-- **Edge enumeration of the cycle graph**: the edge set of `cycleGraph (n+2)` is
the image of the cyclic nearest-neighbour pairing `i ↦ s(i, i+1)` over
`Fin (n+2)`.  (The pairing is injective — hence the edges are `n+2` *distinct*
cyclic pairs — only for `n+2 ≥ 3`; at `n = 0` i.e. `N = 2` the two pairs collapse
to the single edge `s(0,1)`, and the image is still correct.) -/
theorem cycleGraph_edgeFinset_eq_image (n : ℕ) :
    (cycleGraph (n + 2)).edgeFinset
      = Finset.image (fun i : Fin (n + 2) => s(i, i + 1)) Finset.univ := by
  ext e
  refine Sym2.ind (fun a b => ?_) e
  rw [mem_edgeFinset, mem_edgeSet, cycleGraph_adj, Finset.mem_image]
  constructor
  · rintro (h | h)
    · refine ⟨b, Finset.mem_univ _, ?_⟩
      have hab : a = b + 1 := sub_eq_iff_eq_add'.mp h
      rw [hab]; exact Sym2.eq_swap
    · refine ⟨a, Finset.mem_univ _, ?_⟩
      have hba : b = a + 1 := sub_eq_iff_eq_add'.mp h
      rw [hba]
  · rintro ⟨i, _, hi⟩
    rw [Sym2.eq_iff] at hi
    rcases hi with ⟨rfl, hb⟩ | ⟨rfl, ha⟩
    · right; exact sub_eq_iff_eq_add'.mpr hb.symm
    · left; exact sub_eq_iff_eq_add'.mpr ha.symm

/-- The cyclic nearest-neighbour pairing `i ↦ s(i, i+1)` is injective on
`Fin (n+3)` (a cycle on `≥ 3` vertices has no repeated edges). -/
theorem cyclePair_injective (n : ℕ) :
    Function.Injective (fun i : Fin (n + 3) => s(i, i + 1)) := by
  intro i j hij
  rw [Sym2.eq_iff] at hij
  rcases hij with ⟨h1, _⟩ | ⟨h1, h2⟩
  · exact h1
  · exfalso
    have hc : (1 + 1 : Fin (n + 3)) = 0 := by
      have hcc : (j : Fin (n + 3)) + (1 + 1) = j + 0 := by
        rw [add_zero, ← add_assoc, ← h1]; exact h2
      exact add_left_cancel hcc
    have hval : ((1 + 1 : Fin (n + 3)) : ℕ) = 0 := by rw [hc]; rfl
    rw [Fin.val_add, Fin.val_one, Nat.mod_eq_of_lt (by omega : 1 + 1 < n + 3)] at hval
    omega

/-- **Product over cycle-graph edges as a linear cyclic product**: for any
commutative monoid, `∏_{e ∈ (cycleGraph (n+3)).edgeFinset} f e = ∏_{i} f s(i, i+1)`.
The combinatorial bridge turning a product over the cyclic chain's edges into the
transfer-matrix's linear product over sites. -/
theorem prod_cycleGraph_edgeFinset {M : Type*} [CommMonoid M] (n : ℕ)
    (f : Sym2 (Fin (n + 3)) → M) :
    ∏ e ∈ (cycleGraph (n + 3)).edgeFinset, f e
      = ∏ i : Fin (n + 3), f s(i, i + 1) := by
  rw [cycleGraph_edgeFinset_eq_image (n + 1),
    Finset.prod_image (fun i _ j _ h => cyclePair_injective n h)]

/-- The cycle graph on `n+3` vertices has `n+3` edges. -/
theorem card_cycleGraph_edgeFinset (n : ℕ) :
    (cycleGraph (n + 3)).edgeFinset.card = n + 3 := by
  rw [cycleGraph_edgeFinset_eq_image (n + 1),
    Finset.card_image_of_injective _ (cyclePair_injective n), Finset.card_univ,
    Fintype.card_fin]

/-- **Boltzmann weight as an edge product at `h = 0`** (general graph):
`boltzmannWeight G ⟨J,0,β⟩ σ = ∏_{e ∈ G.edgeFinset} exp(β·J·edgeSpin σ e)`. -/
theorem boltzmannWeight_eq_prod_exp_of_h_zero {ι : Type*} [Fintype ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] {J β : ℝ} (σ : Config ι) :
    boltzmannWeight G (⟨J, 0, β⟩ : IsingParams ℝ) σ
      = ∏ e ∈ G.edgeFinset, Real.exp (β * J * edgeSpin (K := ℝ) σ e) := by
  unfold boltzmannWeight hamiltonian interactionEnergy externalFieldEnergy
  simp only [neg_zero, zero_mul, add_zero]
  rw [show -β * (-J * ∑ e ∈ G.edgeFinset, edgeSpin (K := ℝ) σ e)
      = β * J * ∑ e ∈ G.edgeFinset, edgeSpin (K := ℝ) σ e from by ring,
    Finset.mul_sum, Real.exp_sum]

/-- **Cyclic-chain partition function as a site product** (Glimm–Jaffe §17.1):
`Z_N = ∑_σ ∏_{i : Fin N} exp(β·J·σᵢσᵢ₊₁)` for the cyclic chain `N = n+3`.  Combines
the `h = 0` edge-product form of the Boltzmann weight with the cycle-graph edge
enumeration; the linear product over sites is the transfer-matrix shape (the final
identification with `λ₊ᴺ + λ₋ᴺ` via the spin↔`Fin 2` encoding is a subsequent step). -/
theorem partitionFunction_cycleGraph_eq_sum_prod (n : ℕ) {J β : ℝ} :
    partitionFunction (cycleGraph (n + 3)) (⟨J, 0, β⟩ : IsingParams ℝ)
      = ∑ σ : Config (Fin (n + 3)),
          ∏ i : Fin (n + 3), Real.exp (β * J * edgeSpin (K := ℝ) σ s(i, i + 1)) := by
  unfold partitionFunction
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [boltzmannWeight_eq_prod_exp_of_h_zero, prod_cycleGraph_edgeFinset]

end TransferMatrix

end IsingModel
