import IsingModel.AmbientLattice.Monotonicity.InducedEnergySplit

/-!
# Boltzmann-weight factoring of an induced graph over the restricted configuration

The Boltzmann-weight counterpart of the Hamiltonian split
`hamiltonian_inducedGraph_restrict_add` (`InducedEnergySplit.lean`): exponentiating
the energy split factors the Boltzmann weight on `inducedGraph G Λ₂` as the
Boltzmann weight on `inducedGraph G Λ₁` (restricted configuration) times an
exponential factor collecting the complement-site field and the extra-edge
interaction.

When the complement sites and the extra edges all carry frozen spins (as on the
cubic box with `+` boundary, where the extra edges touch the frozen `+` shell —
`cubicBox_shell_adj_not_mem_inner`), that exponential factor is a **constant**
(independent of the free configuration) and cancels in the normalised
boundary-condition expectation — the nearest-neighbour screening of the `+` state
(Issue #3565).

Reference: Friedli–Velenik, *Statistical Mechanics of Lattice Systems* (2017),
Lemma 3.22, §6.
-/

namespace IsingModel

namespace Ambient

open Finset

variable {V : Type*} [DecidableEq V]

/-- **Boltzmann-weight factoring of an induced graph over the restricted
configuration**: the Boltzmann weight on `inducedGraph G Λ₂` equals the Boltzmann
weight on `inducedGraph G Λ₁` (restricted configuration) times the exponential of
`-β` times the complement-site field plus the extra-edge interaction.  Obtained by
exponentiating `hamiltonian_inducedGraph_restrict_add`. -/
theorem boltzmannWeight_inducedGraph_restrict_factor (G : SimpleGraph V)
    {Λ₁ Λ₂ : Finset V} (h12 : Λ₁ ⊆ Λ₂)
    [Fintype (inducedGraph G Λ₁).edgeSet]
    [Fintype (inducedGraph G Λ₂).edgeSet]
    [Fintype (extendGraphFromΛ₁ G Λ₁ Λ₂).edgeSet]
    (p : IsingParams ℝ) (σ : (↑Λ₂ : Type _) → Spin) :
    boltzmannWeight (inducedGraph G Λ₂) p σ
      = boltzmannWeight (inducedGraph G Λ₁) p (restrictConfig h12 σ)
        * Real.exp (-p.β *
            ((-p.h * ∑ v : {x : (↑Λ₂ : Type _) // ¬ (x.val ∈ Λ₁)},
                Spin.sign ℝ (σ v.val))
              + (-p.J) * ∑ e ∈ (inducedGraph G Λ₂).edgeFinset \
                  (extendGraphFromΛ₁ G Λ₁ Λ₂).edgeFinset, edgeSpin (K := ℝ) σ e)) := by
  simp only [boltzmannWeight]
  rw [hamiltonian_inducedGraph_restrict_add G h12 p σ, ← Real.exp_add]
  congr 1
  ring

/-- **Constant Boltzmann-weight factor under frozen complement and extra edges**:
if every complement site of `σ` is `up` and every extra edge has `edgeSpin = 1`
(as on the cubic box with `+` boundary, where the extra edges touch the frozen `+`
shell), then the exponential factor of
`boltzmannWeight_inducedGraph_restrict_factor` collapses to a **constant**
depending only on the number of complement sites and extra edges — independent of
the free configuration.  This is the constant that cancels in the normalised `+`
boundary-condition expectation (the screening). -/
theorem boltzmannWeight_inducedGraph_restrict_factor_const (G : SimpleGraph V)
    {Λ₁ Λ₂ : Finset V} (h12 : Λ₁ ⊆ Λ₂)
    [Fintype (inducedGraph G Λ₁).edgeSet]
    [Fintype (inducedGraph G Λ₂).edgeSet]
    [Fintype (extendGraphFromΛ₁ G Λ₁ Λ₂).edgeSet]
    (p : IsingParams ℝ) (σ : (↑Λ₂ : Type _) → Spin)
    (hcompl : ∀ v : {x : (↑Λ₂ : Type _) // ¬ (x.val ∈ Λ₁)}, σ v.val = Spin.up)
    (hextra : ∀ e ∈ (inducedGraph G Λ₂).edgeFinset \
        (extendGraphFromΛ₁ G Λ₁ Λ₂).edgeFinset, edgeSpin (K := ℝ) σ e = 1) :
    boltzmannWeight (inducedGraph G Λ₂) p σ
      = boltzmannWeight (inducedGraph G Λ₁) p (restrictConfig h12 σ)
        * Real.exp (-p.β *
            ((-p.h) * (Fintype.card {x : (↑Λ₂ : Type _) // ¬ (x.val ∈ Λ₁)} : ℝ)
              + (-p.J) * (((inducedGraph G Λ₂).edgeFinset \
                  (extendGraphFromΛ₁ G Λ₁ Λ₂).edgeFinset).card : ℝ))) := by
  have hval : ∀ v : {x : (↑Λ₂ : Type _) // ¬ (x.val ∈ Λ₁)},
      Spin.sign ℝ (σ v.val) = 1 := fun v => by rw [hcompl v]; simp [Spin.sign, Spin.toSign]
  have hc : (∑ v : {x : (↑Λ₂ : Type _) // ¬ (x.val ∈ Λ₁)}, Spin.sign ℝ (σ v.val))
      = (Fintype.card {x : (↑Λ₂ : Type _) // ¬ (x.val ∈ Λ₁)} : ℝ) := by
    simp only [hval, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have he : (∑ e ∈ (inducedGraph G Λ₂).edgeFinset \
        (extendGraphFromΛ₁ G Λ₁ Λ₂).edgeFinset, edgeSpin (K := ℝ) σ e)
      = (((inducedGraph G Λ₂).edgeFinset \
          (extendGraphFromΛ₁ G Λ₁ Λ₂).edgeFinset).card : ℝ) := by
    rw [Finset.sum_congr rfl hextra, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [boltzmannWeight_inducedGraph_restrict_factor G h12 p σ, hc, he]

end Ambient

end IsingModel
