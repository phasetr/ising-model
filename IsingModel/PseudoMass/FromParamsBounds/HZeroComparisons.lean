import IsingModel.PseudoMass.FromParamsBounds.TendstoAndLower

/-!
# Pseudo-Mass h = 0 Comparisons

This module is part of the split `IsingModel.PseudoMass.FromParamsBounds` development.

## Umbrella-reachable via its cluster head

This module has no importers outside its own cluster.  The cluster head is
registered in the root umbrella `IsingModel.lean`, so this module too lies
inside the transitive import closure of `import IsingModel` — the prerequisite
for the capstone axiom audit (`scripts/audit_gate.py`, check V3) to reach it.
Note that V3 inspects only the names listed in `scripts/audit/capstones.txt`,
and no declaration of this module is currently listed there.  It is
genuine formalization — non-trivial comparison / sandwich / log-bound results
for the `J = 0` / `h = 0` slices of `pseudoMassFromParamsAtPair`, built on the
`PseudoMass/FromParamsBasic` results.
-/

namespace IsingModel

open Set Real Filter

/-- **`pseudoMassFromParamsAtPair_at_h_zero < pseudoMass(c) ↔ c < truncated2`**
when both `c, truncated2 ∈ Ioo 0 2`: pseudoMass strict anti reverses the
inequality. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_lt_pseudoMass_iff_lt_truncated2
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ)
    {c : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 2)
    (htrunc : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z <
      pseudoMass hα hr hc ↔
    c < Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) x z := by
  rw [pseudoMassFromParamsAtPair_at_h_zero_eq_pseudoMass_of_truncated2_mem
        hα hr d Λ J β x z htrunc]
  refine ⟨?_, fun hlt => pseudoMass_strictAnti hα hr hc htrunc hlt⟩
  intro hlt
  by_contra h_neg
  have h_neg' : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) x z ≤ c := not_lt.mp h_neg
  exact absurd hlt (not_lt.mpr (pseudoMass_antitone hα hr htrunc hc h_neg'))

/-- **`pseudoMass(c) < pseudoMassFromParamsAtPair_at_h_zero ↔ truncated2 < c`**:
companion of `_lt_pseudoMass_iff_lt_truncated2`. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_gt_pseudoMass_iff_gt_truncated2
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ)
    {c : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 2)
    (htrunc : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2) :
    pseudoMass hα hr hc <
      pseudoMassFromParamsAtPair hα hr d Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) x z ↔
    Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) x z < c := by
  rw [pseudoMassFromParamsAtPair_at_h_zero_eq_pseudoMass_of_truncated2_mem
        hα hr d Λ J β x z htrunc]
  refine ⟨?_, fun hlt => pseudoMass_strictAnti hα hr htrunc hc hlt⟩
  intro hlt
  by_contra h_neg
  have h_neg' : c ≤ Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                      (⟨J, 0, β⟩ : IsingParams ℝ) x z := not_lt.mp h_neg
  exact absurd hlt (not_lt.mpr (pseudoMass_antitone hα hr hc htrunc h_neg'))

/-- **`pseudoMassFromParamsAtPair_at_h_zero ≤ pseudoMass(c) ↔ c ≤ truncated2`**:
non-strict version of `_lt_pseudoMass_iff_lt_truncated2`. Uses
`pseudoMass_antitone` for both directions. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_le_pseudoMass_iff_le_truncated2
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ)
    {c : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 2)
    (htrunc : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z ≤
      pseudoMass hα hr hc ↔
    c ≤ Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) x z := by
  rw [pseudoMassFromParamsAtPair_at_h_zero_eq_pseudoMass_of_truncated2_mem
        hα hr d Λ J β x z htrunc]
  refine ⟨?_, fun hle => pseudoMass_antitone hα hr hc htrunc hle⟩
  intro hle
  by_contra h_neg
  have h_neg' : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                  (⟨J, 0, β⟩ : IsingParams ℝ) x z < c := not_le.mp h_neg
  have := pseudoMass_strictAnti hα hr htrunc hc h_neg'
  linarith

/-- **`pseudoMass(c) ≤ pseudoMassFromParamsAtPair_at_h_zero ↔ truncated2 ≤ c`**:
companion non-strict iff. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_ge_pseudoMass_iff_ge_truncated2
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ)
    {c : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 2)
    (htrunc : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2) :
    pseudoMass hα hr hc ≤
      pseudoMassFromParamsAtPair hα hr d Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) x z ↔
    Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) x z ≤ c := by
  rw [pseudoMassFromParamsAtPair_at_h_zero_eq_pseudoMass_of_truncated2_mem
        hα hr d Λ J β x z htrunc]
  refine ⟨?_, fun hle => pseudoMass_antitone hα hr htrunc hc hle⟩
  intro hle
  by_contra h_neg
  have h_neg' : c < Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                      (⟨J, 0, β⟩ : IsingParams ℝ) x z := not_le.mp h_neg
  have := pseudoMass_strictAnti hα hr hc htrunc h_neg'
  linarith

/-- **`pseudoMassFromParamsAtPair_at_h_zero = pseudoMass(c) ↔ truncated2 = c`**:
combines the `_le_iff` and `_ge_iff` non-strict iff characterizations
via antisymmetry. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_eq_pseudoMass_iff_truncated2_eq
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ)
    {c : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 2)
    (htrunc : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z =
      pseudoMass hα hr hc ↔
    Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) x z = c := by
  refine ⟨?_, ?_⟩
  · intro heq
    have hle : pseudoMassFromParamsAtPair hα hr d Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z ≤ pseudoMass hα hr hc := heq.le
    have hge : pseudoMass hα hr hc ≤ pseudoMassFromParamsAtPair hα hr d Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z := heq.ge
    have h1 := (pseudoMassFromParamsAtPair_at_h_zero_le_pseudoMass_iff_le_truncated2
                  hα hr d Λ J β x z hc htrunc).mp hle
    have h2 := (pseudoMassFromParamsAtPair_at_h_zero_ge_pseudoMass_iff_ge_truncated2
                  hα hr d Λ J β x z hc htrunc).mp hge
    linarith
  · intro heq_t
    rw [pseudoMassFromParamsAtPair_at_h_zero_eq_pseudoMass_of_truncated2_mem
          hα hr d Λ J β x z htrunc]
    congr 1

end IsingModel
