import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSBridgeFromSimonLieb

/-!
# Correlation pair symmetry + cluster property ferromagnetic aliases bundle

GJ-proposition-unit bundle of pair-symmetry properties of `correlationInfinite`
and ferromagnetic-form aliases for nearby infrastructure.

Built on the existing `Finset.pair_comm` and pair-correlation Λ-layer
infrastructure.

**Reference:** Glimm--Jaffe §17.5; Friedli--Velenik §3.7.
-/

namespace IsingModel
namespace Ambient

/-! ## Correlation pair-symmetry properties -/

/-- **Pair correlation symmetry: `corr {i, j} = corr {j, i}`** for any
exhaustion. Direct consequence of `Finset.pair_comm`. -/
theorem correlationInfinite_pair_comm
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i j : Fin d → ℤ) :
    correlationInfinite (latticeGraph d) Λ p {i, j}
      = correlationInfinite (latticeGraph d) Λ p {j, i} := by
  simp [Finset.pair_comm i j]

/-- **Pair correlationAlongExhaustion symmetry**. -/
theorem correlationAlongExhaustion_pair_comm
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (i j : Fin d → ℤ) (n : ℕ) :
    correlationAlongExhaustion (latticeGraph d) Λ p {i, j} n
      = correlationAlongExhaustion (latticeGraph d) Λ p {j, i} n := by
  simp [Finset.pair_comm i j]

/-! ## HLS sum symmetry under z ↔ z' relabeling helpers -/

/-- **HLS pair-product summand symmetry under `(x₀, y₀) ↔ (y₀, x₀)`**. -/
theorem correlationInfinite_pair_product_anchor_comm
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (x₀ y₀ z : Fin d → ℤ) :
    correlationInfinite (latticeGraph d) Λ p {x₀, z} *
        correlationInfinite (latticeGraph d) Λ p {y₀, z}
      = correlationInfinite (latticeGraph d) Λ p {y₀, z} *
          correlationInfinite (latticeGraph d) Λ p {x₀, z} :=
  mul_comm _ _

/-- **HLS pair-product summand symmetry under `z ↔ z`** (trivial, but useful
for unifying access patterns). -/
theorem correlationInfinite_pair_product_inner_comm
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (x₀ y₀ z : Fin d → ℤ) :
    correlationInfinite (latticeGraph d) Λ p {x₀, z} *
        correlationInfinite (latticeGraph d) Λ p {y₀, z}
      = correlationInfinite (latticeGraph d) Λ p {z, x₀} *
          correlationInfinite (latticeGraph d) Λ p {z, y₀} := by
  rw [correlationInfinite_pair_comm Λ p x₀ z,
      correlationInfinite_pair_comm Λ p y₀ z]

/-! ## Symmetric ferromagnetic alias for active range -/

/-- **Active range at swapped pair `{z, x}` from active range at `{x, z}`**. -/
theorem correlationInfinite_pair_active_swap
    {d : ℕ} {J β : ℝ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (x z : Fin d → ℤ)
    (h_active : correlationInfinite (latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        {x, z} ∈ Set.Ioo (0 : ℝ) 2) :
    correlationInfinite (latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ) {z, x}
      ∈ Set.Ioo (0 : ℝ) 2 := by
  rw [correlationInfinite_pair_comm Λ _ z x]
  exact h_active

/-- **Active range is symmetric in `(x, z)`**. -/
theorem correlationInfinite_pair_active_comm_iff
    {d : ℕ} {J β : ℝ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (x z : Fin d → ℤ) :
    (correlationInfinite (latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}
      ∈ Set.Ioo (0 : ℝ) 2)
    ↔ correlationInfinite (latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ) {z, x}
      ∈ Set.Ioo (0 : ℝ) 2 := by
  rw [correlationInfinite_pair_comm Λ _ x z]

/-- **Cluster property is symmetric in its pair argument** (trivial, but
exposed as an API). -/
theorem correlationInfinite_pair_le_iff_swap
    {d : ℕ} {J β : ℝ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (x z : Fin d → ℤ) (c : ℝ) :
    correlationInfinite (latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}
      ≤ c
    ↔ correlationInfinite (latticeGraph d) Λ (⟨J, 0, β⟩ : IsingParams ℝ) {z, x}
      ≤ c := by
  rw [correlationInfinite_pair_comm Λ _ x z]

/-- **Distance is symmetric: `latticeDistance d i j = latticeDistance d j i`**. -/
theorem latticeDistance_pair_comm
    (d : ℕ) (i j : Fin d → ℤ) :
    latticeDistance d i j = latticeDistance d j i :=
  IsingModel.latticeDistance_comm d i j

end Ambient
end IsingModel
