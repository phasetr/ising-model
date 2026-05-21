import IsingModel.Conditioning.Reflection

/-!
# High-Temperature Expansion

This module is part of the split `IsingModel.Conditioning` development.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## High-temperature / cluster expansion (§18.1–18.3)

Glimm–Jaffe Chapter 18 develops the cluster expansion for P(φ)₂ fields.
The lattice Ising analogue is the **high-temperature expansion**, which
decomposes each Boltzmann factor using

`exp(βJ · σ_iσ_j) = cosh(βJ) + sinh(βJ) · σ_iσ_j`

(already proved as `exp_edgeSpin_decomp` in `NonnegCorrelations.lean`).

The high-temperature expansion gives:
`Z = (cosh βJ)^|E| · Σ_σ ∏_e (1 + tanh(βJ) · σ_iσ_j) · exp(βh Σ σ_i)`

For `h = 0`, the sum over σ selects only even subgraphs (those where
every vertex has even degree), giving the well-known formula:
`Z(h=0) = 2^|ι| · (cosh βJ)^|E| · Σ_{X ⊆ E, even} (tanh βJ)^|X|`

The convergence of this expansion for small `tanh(βJ)` (high temperature)
establishes exponential decay of correlations and uniqueness of the
Gibbs state — the lattice analogue of Theorem 18.1.1.

The key algebraic ingredient `exp_edgeSpin_decomp` is already formalized. -/

/-- **Partition function high-temperature expansion** (lattice analogue of GJ §18.3).

For any Ising parameter `p = (J, h, β)` and any finite simple graph `G`,
\[
Z(G; p) = (\cosh(\beta J))^{|E|} \sum_\sigma
  \Bigl(\prod_{e \in E} (1 + \tanh(\beta J)\,\sigma_i\sigma_j)\Bigr)
  \exp\!\bigl(\beta h \sum_i \sigma_i\bigr).
\]

Reference: Glimm–Jaffe, *Quantum Physics*, §18.1–18.3, pp. 378–386
("Clustering and analyticity"); see also Friedli–Velenik §3.7.3
("Uniqueness at high temperature"), eqs. (3.41)–(3.42), pp. 116–117
(2017 ed.). The proof rewrites each edge factor via
`exp_edgeSpin_decomp` (which gives `exp(α·s) = cosh α + sinh α · s`
for `s ∈ {±1}`) and pulls out the common factor `cosh(βJ)`. -/
theorem partitionFunction_high_temp_expansion
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) :
    partitionFunction G p =
      Real.cosh (p.β * p.J) ^ G.edgeFinset.card *
      ∑ σ : Config ι,
        (∏ e ∈ G.edgeFinset, (1 + Real.tanh (p.β * p.J) * edgeSpin σ e)) *
        Real.exp (p.β * p.h * ∑ i : ι, Spin.sign ℝ (σ i)) := by
  unfold partitionFunction boltzmannWeight hamiltonian
    interactionEnergy externalFieldEnergy
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  have hexp_split :
      Real.exp (-p.β *
          (-p.J * ∑ e ∈ G.edgeFinset, edgeSpin σ e
            + -p.h * ∑ i : ι, Spin.sign ℝ (σ i))) =
        (∏ e ∈ G.edgeFinset, Real.exp (p.β * p.J * edgeSpin σ e)) *
          Real.exp (p.β * p.h * ∑ i : ι, Spin.sign ℝ (σ i)) := by
    have hrewrite :
        -p.β *
            (-p.J * ∑ e ∈ G.edgeFinset, edgeSpin σ e
              + -p.h * ∑ i : ι, Spin.sign ℝ (σ i))
          = (∑ e ∈ G.edgeFinset, p.β * p.J * edgeSpin σ e)
            + p.β * p.h * ∑ i : ι, Spin.sign ℝ (σ i) := by
      rw [show
          -p.β *
              (-p.J * ∑ e ∈ G.edgeFinset, edgeSpin σ e
                + -p.h * ∑ i : ι, Spin.sign ℝ (σ i))
            = (p.β * p.J) * (∑ e ∈ G.edgeFinset, edgeSpin σ e)
              + p.β * p.h * (∑ i : ι, Spin.sign ℝ (σ i)) from by ring,
          Finset.mul_sum]
    rw [hrewrite, Real.exp_add, Real.exp_sum]
  rw [hexp_split]
  have hedge_decomp : ∀ e ∈ G.edgeFinset,
      Real.exp (p.β * p.J * edgeSpin σ e) =
        Real.cosh (p.β * p.J) * (1 + Real.tanh (p.β * p.J) * edgeSpin σ e) := by
    intro e _
    rw [exp_edgeSpin_decomp, Real.tanh_eq_sinh_div_cosh]
    have hcosh_ne : Real.cosh (p.β * p.J) ≠ 0 := (Real.cosh_pos _).ne'
    field_simp
  rw [Finset.prod_congr rfl hedge_decomp, Finset.prod_mul_distrib,
      Finset.prod_const]
  ring

/-- **Partition function high-temperature expansion at zero field**
(GJ §18.3 / FV §3.7.3 eq. (3.42)):
\[
Z(G; J, 0, \beta) = (\cosh(\beta J))^{|E|}
\sum_\sigma \prod_{\{i,j\} \in E}
  (1 + \tanh(\beta J)\,\sigma_i\sigma_j).
\]

Direct corollary of `partitionFunction_high_temp_expansion` at `h = 0`,
where the field factor `exp(βh · Σ sign(σ_i))` collapses to `1`. -/
theorem partitionFunction_high_temp_expansion_h_zero
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) :
    partitionFunction G ⟨J, 0, β⟩ =
      Real.cosh (β * J) ^ G.edgeFinset.card *
      ∑ σ : Config ι,
        ∏ e ∈ G.edgeFinset, (1 + Real.tanh (β * J) * edgeSpin σ e) := by
  rw [partitionFunction_high_temp_expansion G ⟨J, 0, β⟩]
  simp

/-- **Partition function general-`h` subset expansion**: for any
Ising parameter `p = (J, h, β)`,
\[
Z(G; p) = (\cosh(\beta J))^{|E|}
\sum_{X \subseteq E} \tanh(\beta J)^{|X|}
\sum_\sigma \Bigl(\prod_{e \in X} \sigma_i\sigma_j\Bigr)
\exp\!\bigl(\beta h \sum_i \sigma_i\bigr).
\]

Intermediate form between `partitionFunction_high_temp_expansion`
(Step 281, full product form) and `partitionFunction_high_temp_expansion_h_zero_closed`
(Step 283, h = 0 closed form). At `h = 0` the inner σ-sum collapses
by parity to give the FV (3.45) even-subgraph form; at general `h`
the σ-sum carries the residual external-field dependence.

Proof: apply Step 281 (general-`h` expansion), then expand each edge
product via `Finset.prod_one_add` and pull `tanh(βJ)^|X|` out of the
inner product, swapping the σ- and `X`-sums via `Finset.sum_comm`. -/
theorem partitionFunction_high_temp_expansion_subset_form
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) :
    partitionFunction G p =
      Real.cosh (p.β * p.J) ^ G.edgeFinset.card *
      ∑ X ∈ G.edgeFinset.powerset,
        Real.tanh (p.β * p.J) ^ X.card *
          ∑ σ : Config ι,
            (∏ e ∈ X, edgeSpin (K := ℝ) σ e) *
            Real.exp (p.β * p.h * ∑ i : ι, Spin.sign ℝ (σ i)) := by
  rw [partitionFunction_high_temp_expansion G p]
  -- Step 1: subset expansion via Finset.prod_one_add
  have hexpand : ∀ σ : Config ι,
      (∏ e ∈ G.edgeFinset, (1 + Real.tanh (p.β * p.J) * edgeSpin σ e))
        = ∑ X ∈ G.edgeFinset.powerset,
            ∏ e ∈ X, (Real.tanh (p.β * p.J) * edgeSpin σ e) := fun σ =>
    Finset.prod_one_add G.edgeFinset
  simp_rw [hexpand]
  -- Step 2: pull tanh^|X| out of inner product
  have hpull : ∀ σ : Config ι, ∀ X : Finset (Sym2 ι),
      (∏ e ∈ X, (Real.tanh (p.β * p.J) * edgeSpin σ e))
        = Real.tanh (p.β * p.J) ^ X.card *
            (∏ e ∈ X, edgeSpin (K := ℝ) σ e) := by
    intros σ X
    rw [Finset.prod_mul_distrib, Finset.prod_const]
  simp_rw [hpull]
  -- Step 3: distribute the field exponential factor
  rw [show
      cosh (p.β * p.J) ^ G.edgeFinset.card *
          ∑ σ : Config ι,
            (∑ X ∈ G.edgeFinset.powerset,
              tanh (p.β * p.J) ^ X.card *
                ∏ e ∈ X, edgeSpin σ e) *
            Real.exp (p.β * p.h * ∑ i : ι, Spin.sign ℝ (σ i))
        = cosh (p.β * p.J) ^ G.edgeFinset.card *
          ∑ σ : Config ι,
            ∑ X ∈ G.edgeFinset.powerset,
              tanh (p.β * p.J) ^ X.card *
                (∏ e ∈ X, edgeSpin σ e) *
                Real.exp (p.β * p.h * ∑ i : ι, Spin.sign ℝ (σ i)) by
    congr 1
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [Finset.sum_mul]]
  -- Step 4: swap σ ↔ X and pull tanh^|X| out of σ-sum
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun X _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  ring


end IsingModel
