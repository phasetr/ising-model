import IsingModel.GibbsMeasure
import IsingModel.Hamiltonian
import IsingModel.SumGraph
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Prod

/-!
# Hamiltonian additivity on the disjoint sum graph

This file lifts the combinatorial edge-set decomposition from
`IsingModel.SumGraph` to the Ising Hamiltonian: on the disjoint sum
`G ⊕g H`, with a configuration of the form `Sum.elim σ₁ σ₂`, the
Hamiltonian splits additively,
`hamiltonian (G ⊕g H) p (Sum.elim σ₁ σ₂)
  = hamiltonian G p σ₁ + hamiltonian H p σ₂`.

This file now covers Steps 2–4 of the Glimm–Jaffe §4.6 (pp. 70ff)
super-additivity route toward convergence of the thermodynamic-limit
free-energy density (Prop 4.6.1):

* Step 2 — `Config.sumEquiv` (configuration product equivalence).
* Step 3 — `hamiltonian_sum` (Hamiltonian additivity).
* Step 4 — `partitionFunction_sum` / `log_partitionFunction_sum`
  (partition function multiplicativity, hence `log Z` additivity).

Step 5 (Fekete-style convergence from `log Z` super-additivity and
the uniform upper bound of PRs #122, #123) follows in a subsequent PR.

## Main declarations

* `IsingModel.Config.sumEquiv` — `Config (ι ⊕ ι') ≃ Config ι × Config ι'`.
* `IsingModel.edgeSpin_sumInl_sym2Map` /
  `IsingModel.edgeSpin_sumInr_sym2Map` — per-edge spin pullback through
  `Sum.inl` / `Sum.inr`.
* `IsingModel.externalFieldEnergy_sum` — additivity of the field term.
* `IsingModel.interactionEnergy_sum` — additivity of the interaction term.
* `IsingModel.hamiltonian_sum` — Hamiltonian additivity on `G ⊕g H`.
* `IsingModel.partitionFunction_sum` —
  `Z_{G ⊕g H}(p) = Z_G(p) · Z_H(p)` on the disjoint sum graph
  (Glimm–Jaffe §4.6 super-additivity Step 4).
* `IsingModel.log_partitionFunction_sum` — the logarithmic form
  `log Z_{G ⊕g H} = log Z_G + log Z_H`.
-/

namespace IsingModel

variable {ι ι' : Type*}
variable {K : Type*} [Field K]

/-- The configuration space of a disjoint sum of vertex types is the
product of the component configuration spaces, via the standard
`Equiv.sumArrowEquivProdArrow`. -/
def Config.sumEquiv : Config (ι ⊕ ι') ≃ Config ι × Config ι' :=
  Equiv.sumArrowEquivProdArrow ι ι' Spin

/-- The first component of `Config.sumEquiv σ` is the restriction of
`σ` along `Sum.inl`. -/
@[simp]
theorem Config.sumEquiv_apply_fst (σ : Config (ι ⊕ ι')) (i : ι) :
    ((Config.sumEquiv σ).1 : Config ι) i = σ (Sum.inl i) := rfl

/-- The second component of `Config.sumEquiv σ` is the restriction of
`σ` along `Sum.inr`. -/
@[simp]
theorem Config.sumEquiv_apply_snd (σ : Config (ι ⊕ ι')) (i : ι') :
    ((Config.sumEquiv σ).2 : Config ι') i = σ (Sum.inr i) := rfl

/-- The inverse of `Config.sumEquiv` assembles a pair of
configurations back into a configuration on the disjoint sum type
via `Sum.elim`. -/
@[simp]
theorem Config.sumEquiv_symm (σ₁ : Config ι) (σ₂ : Config ι') :
    Config.sumEquiv.symm (σ₁, σ₂) = Sum.elim σ₁ σ₂ := rfl

/-- Per-edge spin pullback through `Sum.inl`: the edge product on a
`Sum.inl`-image edge in the sum graph equals the edge product on the
corresponding edge of the first component. -/
theorem edgeSpin_sumInl_sym2Map (σ₁ : Config ι) (σ₂ : Config ι')
    (e : Sym2 ι) :
    edgeSpin (K := K) (Sum.elim σ₁ σ₂)
        ((Function.Embedding.inl : ι ↪ ι ⊕ ι').sym2Map e)
      = edgeSpin σ₁ e := by
  refine e.ind (fun i j => ?_)
  simp [edgeSpin, Function.Embedding.sym2Map_apply, Sym2.map_mk,
        Function.Embedding.inl_apply]

/-- Per-edge spin pullback through `Sum.inr`. -/
theorem edgeSpin_sumInr_sym2Map (σ₁ : Config ι) (σ₂ : Config ι')
    (e : Sym2 ι') :
    edgeSpin (K := K) (Sum.elim σ₁ σ₂)
        ((Function.Embedding.inr : ι' ↪ ι ⊕ ι').sym2Map e)
      = edgeSpin σ₂ e := by
  refine e.ind (fun i j => ?_)
  simp [edgeSpin, Function.Embedding.sym2Map_apply, Sym2.map_mk,
        Function.Embedding.inr_apply]

/-- Additivity of the external field energy on disjoint-sum
configurations: the energy of a `Sum.elim` splits additively by
`Fintype.sum_sum_type`. -/
theorem externalFieldEnergy_sum [Fintype ι] [Fintype ι']
    (h : K) (σ₁ : Config ι) (σ₂ : Config ι') :
    externalFieldEnergy (ι := ι ⊕ ι') h (Sum.elim σ₁ σ₂)
      = externalFieldEnergy h σ₁ + externalFieldEnergy h σ₂ := by
  unfold externalFieldEnergy
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  ring

/-- Additivity of the interaction energy on disjoint-sum
configurations: via the edge-set decomposition (PR #134) and
`edgeSpin` pullback, the sum over `(G ⊕g H).edgeFinset` splits
additively. -/
theorem interactionEnergy_sum
    (G : SimpleGraph ι) (H : SimpleGraph ι')
    [Fintype G.edgeSet] [Fintype H.edgeSet]
    (J : K) (σ₁ : Config ι) (σ₂ : Config ι') :
    interactionEnergy (G.sum H) J (Sum.elim σ₁ σ₂)
      = interactionEnergy G J σ₁ + interactionEnergy H J σ₂ := by
  classical
  unfold interactionEnergy
  rw [SimpleGraph.edgeFinset_sum,
      Finset.sum_union (SimpleGraph.disjoint_inl_inr_edgeFinset G H),
      Finset.sum_map, Finset.sum_map]
  simp only [edgeSpin_sumInl_sym2Map, edgeSpin_sumInr_sym2Map]
  ring

/-- **Hamiltonian additivity on the disjoint sum graph**
(Glimm–Jaffe §4.6 super-additivity Step 2-3, pp. 70ff):
`H_{G ⊕g H}(Sum.elim σ₁ σ₂) = H_G(σ₁) + H_H(σ₂)`.

Summing the interaction and external-field contributions, each of
which decomposes additively by `interactionEnergy_sum` and
`externalFieldEnergy_sum`. -/
theorem hamiltonian_sum [LinearOrder K] [IsStrictOrderedRing K]
    [Fintype ι] [Fintype ι']
    (G : SimpleGraph ι) (H : SimpleGraph ι')
    [Fintype G.edgeSet] [Fintype H.edgeSet]
    (p : IsingParams K) (σ₁ : Config ι) (σ₂ : Config ι') :
    hamiltonian (G.sum H) p (Sum.elim σ₁ σ₂)
      = hamiltonian G p σ₁ + hamiltonian H p σ₂ := by
  unfold hamiltonian
  rw [interactionEnergy_sum, externalFieldEnergy_sum]
  ring

/-- **Partition function multiplicativity on the disjoint sum graph**
(Glimm–Jaffe §4.6 super-additivity Step 4, pp. 70ff):
`Z_{G ⊕g H}(p) = Z_G(p) · Z_H(p)`.

Proof sketch. By `Equiv.sum_comp` applied to `Config.sumEquiv.symm`,
the sum over `Config (ι ⊕ ι')` becomes a sum over
`Config ι × Config ι'` (`Sum.elim`-assembled). `Fintype.sum_prod_type`
splits it into a double sum. The Hamiltonian additivity of the
previous theorem (`hamiltonian_sum`) and `Real.exp_add` turn
`exp(-β (H_G + H_H))` into the product `exp(-β H_G) · exp(-β H_H)`.
Finally `Finset.sum_mul_sum` collapses the double sum back into the
product of two partition functions. -/
theorem partitionFunction_sum
    [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι']
    (G : SimpleGraph ι) (H : SimpleGraph ι')
    [Fintype G.edgeSet] [Fintype H.edgeSet]
    (p : IsingParams ℝ) :
    partitionFunction (G.sum H) p
      = partitionFunction G p * partitionFunction H p := by
  unfold partitionFunction boltzmannWeight
  rw [← Equiv.sum_comp Config.sumEquiv.symm
        (fun σ => Real.exp (-p.β * hamiltonian (G.sum H) p σ))]
  rw [Fintype.sum_prod_type]
  simp only [Config.sumEquiv_symm, hamiltonian_sum, mul_add, Real.exp_add]
  rw [← Finset.sum_mul_sum]

/-- **Log-partition additivity on the disjoint sum graph**:
`log Z_{G ⊕g H}(p) = log Z_G(p) + log Z_H(p)`.

Immediate consequence of `partitionFunction_sum` combined with
`Real.log_mul`, whose side conditions are discharged by
nonvanishing (`partitionFunction_ne_zero`). -/
theorem log_partitionFunction_sum
    [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι']
    (G : SimpleGraph ι) (H : SimpleGraph ι')
    [Fintype G.edgeSet] [Fintype H.edgeSet]
    (p : IsingParams ℝ) :
    Real.log (partitionFunction (G.sum H) p)
      = Real.log (partitionFunction G p)
        + Real.log (partitionFunction H p) := by
  rw [partitionFunction_sum,
      Real.log_mul (partitionFunction_ne_zero G p) (partitionFunction_ne_zero H p)]

end IsingModel
