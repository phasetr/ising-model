import IsingModel.PseudoMass.FromParamsBasic

/-!
# Pseudo-mass h-zero truncated2 bounds

H-zero specialisations of `pseudoMassFromParamsAtPair` bounds in terms of
`truncated2Infinite`.

## Umbrella-reachable via its cluster head

This module has no importers outside its own cluster.  The cluster head is
registered in the root umbrella `IsingModel.lean`, so this module too lies
inside the transitive import closure of `import IsingModel` — the prerequisite
for the capstone axiom audit (`scripts/audit_gate.py`, check V3) to reach it.
Note that V3 inspects only the names listed in `scripts/audit/capstones.txt`,
and no declaration of this module is currently listed there.  It is
genuine formalization — non-trivial sandwich / bound results for the `J = 0` /
`h = 0` slices of `pseudoMassFromParamsAtPair`, built on the
`PseudoMass/FromParamsBasic` results.
-/

namespace IsingModel

open Set Real Filter

/-! ### `h = 0` specialisations using `truncated2Infinite`

At zero external field, `correlationInfinite ⟨J, 0, β⟩ {x, z} = truncated2Infinite ⟨J, 0, β⟩ x z`
(spin-flip Z₂ symmetry forces the singleton magnetisations to vanish), so the
`*_of_corr_*` family of bounds for `pseudoMassFromParamsAtPair` translates to
the corresponding `*_of_truncated2_*` form in terms of the function
`latticeMass` is actually defined against.
-/

/-- **At `h = 0`, `pseudoMassFromParamsAtPair ≤ pseudoMassExt(c_min)` from
`c_min ≤ truncated2`**: h = 0 specialisation of `_le_of_corr_ge` using the
identity `correlationInfinite ⟨J, 0, β⟩ {x,z} = truncated2Infinite ⟨J,0,β⟩ x z`. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_le_of_truncated2_ge {α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ)
    {c_min : ℝ} (hc_min : c_min ∈ Set.Ioo (0 : ℝ) 2)
    (htrunc : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2)
    (hge : c_min ≤ Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β⟩ : IsingParams ℝ) x z) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z ≤
      pseudoMassExt hα hr c_min := by
  have hbridge := Ambient.truncated2Infinite_h_zero
    (IsingModel.latticeGraph d) Λ J β x z
  rw [hbridge] at htrunc hge
  exact pseudoMassFromParamsAtPair_le_of_corr_ge hα hr d Λ
    (⟨J, 0, β⟩ : IsingParams ℝ) x z hc_min htrunc hge

/-- **At `h = 0`, `pseudoMassExt(c_max) ≤ pseudoMassFromParamsAtPair` from
`truncated2 ≤ c_max`**: h = 0 specialisation of `_ge_of_corr_le`. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_ge_of_truncated2_le {α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ)
    {c_max : ℝ} (hc_max : c_max ∈ Set.Ioo (0 : ℝ) 2)
    (htrunc : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2)
    (hle : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) x z ≤ c_max) :
    pseudoMassExt hα hr c_max ≤
      pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z := by
  have hbridge := Ambient.truncated2Infinite_h_zero
    (IsingModel.latticeGraph d) Λ J β x z
  rw [hbridge] at htrunc hle
  exact pseudoMassFromParamsAtPair_ge_of_corr_le hα hr d Λ
    (⟨J, 0, β⟩ : IsingParams ℝ) x z hc_max htrunc hle

/-- **At `h = 0`, `pseudoMassFromParamsAtPair` sandwich** combining
`_le_of_truncated2_ge` and `_ge_of_truncated2_le`: if
`c_min ≤ truncated2 ≤ c_max` with all values in `Ioo 0 2`, then
`pseudoMassExt(c_max) ≤ pseudoMassFromParamsAtPair ≤ pseudoMassExt(c_min)`. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_sandwich_of_truncated2_mem
    {α : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ)
    {c_min c_max : ℝ}
    (hc_min : c_min ∈ Set.Ioo (0 : ℝ) 2)
    (hc_max : c_max ∈ Set.Ioo (0 : ℝ) 2)
    (htrunc : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2)
    (hge : c_min ≤ Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β⟩ : IsingParams ℝ) x z)
    (hle : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) x z ≤ c_max) :
    pseudoMassExt hα hr c_max ≤
      pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z ∧
    pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z ≤
      pseudoMassExt hα hr c_min :=
  ⟨pseudoMassFromParamsAtPair_at_h_zero_ge_of_truncated2_le
      hα hr d Λ J β x z hc_max htrunc hle,
   pseudoMassFromParamsAtPair_at_h_zero_le_of_truncated2_ge
      hα hr d Λ J β x z hc_min htrunc hge⟩

/-- **At `h = 0`, when `truncated2Infinite ∈ Ioo 0 2`, the bridge equals
the underlying `pseudoMass`** (not the totalised `pseudoMassExt`):
combining `pseudoMassFromParamsAtPair_at_h_zero_eq` (PR #1669) with
`pseudoMassExt_of_mem`. This gives access to the implicit-function-theorem
derivative API of `pseudoMass` (`HasStrictDerivAt`, etc.) when reasoning
about the bridge in the high-temperature ferromagnetic regime where
truncated2 is positive but bounded by 1. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_eq_pseudoMass_of_truncated2_mem
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ)
    (htrunc : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z =
      pseudoMass hα hr htrunc := by
  rw [pseudoMassFromParamsAtPair_at_h_zero_eq hα hr d Λ J β x z]
  exact pseudoMassExt_of_mem hα hr htrunc

/-- **At `h = 0`, the bridge as a `pseudoMass` upper bound from a
`truncated2` lower bound**: combining `_at_h_zero_le_of_truncated2_ge`
(PR #1671, gives `≤ pseudoMassExt(c_min)`) with `pseudoMassExt_of_mem`
(reduces to `pseudoMass(c_min)` when `c_min ∈ Ioo 0 2`). Useful for
deriving the §17.5 lower-bound `pseudoMass(...) ≤ latticeMass(...)`
direction. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_le_pseudoMass_of_truncated2_ge
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ)
    {c_min : ℝ} (hc_min : c_min ∈ Set.Ioo (0 : ℝ) 2)
    (htrunc : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2)
    (hge : c_min ≤ Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β⟩ : IsingParams ℝ) x z) :
    pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z ≤
      pseudoMass hα hr hc_min := by
  have hbound := pseudoMassFromParamsAtPair_at_h_zero_le_of_truncated2_ge
                    hα hr d Λ J β x z hc_min htrunc hge
  rwa [pseudoMassExt_of_mem hα hr hc_min] at hbound

/-- **At `h = 0`, the bridge as a `pseudoMass` lower bound from a
`truncated2` upper bound**: combining `_at_h_zero_ge_of_truncated2_le`
with `pseudoMassExt_of_mem`. Companion to
`_at_h_zero_le_pseudoMass_of_truncated2_ge`. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_ge_pseudoMass_of_truncated2_le
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ)
    {c_max : ℝ} (hc_max : c_max ∈ Set.Ioo (0 : ℝ) 2)
    (htrunc : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2)
    (hle : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) x z ≤ c_max) :
    pseudoMass hα hr hc_max ≤
      pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z := by
  have hbound := pseudoMassFromParamsAtPair_at_h_zero_ge_of_truncated2_le
                    hα hr d Λ J β x z hc_max htrunc hle
  rwa [pseudoMassExt_of_mem hα hr hc_max] at hbound

/-- **At `h = 0`, `pseudoMassFromParamsAtPair > 0` from `truncated2 ∈ Ioo 0 2`**:
direct corollary of `_at_h_zero_eq_pseudoMass_of_truncated2_mem` (PR #1672)
+ `pseudoMass_pos` (PR #928 Step 117g). When the truncated 2-point function
falls in the regime `(0, 2)`, the bridge is strictly positive — the
canonical "non-vanishing" condition for `pseudoMassFromParamsAtPair`
expressed in terms of the function `latticeMass` is defined against. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_pos_of_truncated2_mem
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ)
    (htrunc : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2) :
    0 < pseudoMassFromParamsAtPair hα hr d Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) x z := by
  rw [pseudoMassFromParamsAtPair_at_h_zero_eq_pseudoMass_of_truncated2_mem
        hα hr d Λ J β x z htrunc]
  exact pseudoMass_pos hα hr htrunc

/-- **At `h = 0`, full sandwich `pseudoMass(c_max) ≤
pseudoMassFromParamsAtPair ≤ pseudoMass(c_min)`** under
`c_min ≤ truncated2 ≤ c_max` with all values in `Ioo 0 2`. Combines
`_at_h_zero_le_pseudoMass_of_truncated2_ge` and
`_at_h_zero_ge_pseudoMass_of_truncated2_le` (PR #1677) into a single
sandwich in terms of the typed `pseudoMass`. This is the canonical
sandwich form for §17.5 Lemma 17.5.2: a uniform-in-Λ exponential
decay bound on `truncated2Infinite` plus the Lipschitz capstone
(`pseudoMass_pow_succ_lipschitz`) on the typed `pseudoMass` would
combine into the sandwich `m⁻ ≤ m ≤ const · m⁻`. -/
theorem pseudoMassFromParamsAtPair_at_h_zero_sandwich_pseudoMass
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (d : ℕ)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (x z : Fin d → ℤ)
    {c_min c_max : ℝ}
    (hc_min : c_min ∈ Set.Ioo (0 : ℝ) 2)
    (hc_max : c_max ∈ Set.Ioo (0 : ℝ) 2)
    (htrunc : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z ∈ Set.Ioo (0 : ℝ) 2)
    (hge : c_min ≤ Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
                    (⟨J, 0, β⟩ : IsingParams ℝ) x z)
    (hle : Ambient.truncated2Infinite (IsingModel.latticeGraph d) Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) x z ≤ c_max) :
    pseudoMass hα hr hc_max ≤
      pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z ∧
    pseudoMassFromParamsAtPair hα hr d Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z ≤
      pseudoMass hα hr hc_min :=
  ⟨pseudoMassFromParamsAtPair_at_h_zero_ge_pseudoMass_of_truncated2_le
      hα hr d Λ J β x z hc_max htrunc hle,
   pseudoMassFromParamsAtPair_at_h_zero_le_pseudoMass_of_truncated2_ge
      hα hr d Λ J β x z hc_min htrunc hge⟩

end IsingModel
