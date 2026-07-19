import IsingModel.PseudoMass.Ext

/-!
# Pseudo-Mass Correlation Composition

This module is part of the split `IsingModel.PseudoMass` development.

## Standalone module (intentional)

This file is not imported by the root umbrella `IsingModel.lean` and has no
downstream consumers in the import graph.  It is retained deliberately: it backs
the §17.5 Step 120/123 "Done" entries in `docs/index.md` (the Step 120
continuity result `pseudoMass_comp_corr_continuousAt` and the Step 123
β-antitonicity result for the pseudoMass ∘ correlation composition).  It is
genuine formalization, not dead code, and must NOT be removed; it is simply not
wired into the umbrella.
-/

namespace IsingModel

open Set Real Filter

/-! ## Continuity of pseudoMass composition with correlation (Step 120) -/

/-- **pseudoMass∘correlation is continuous in β** (Step 120).

When the correlation `c(β) = ⟨σ^A⟩_β` lies in `(0, 2)`, the totalized function
`β ↦ if c(β) ∈ Ioo 0 2 then pseudoMass(c(β)) else 0` is continuous at `β`.

Proof: manual ContinuousAt composition via Filter.Tendsto.

This is a partial result toward GJ §17.5 Thm 17.5.1: the full theorem requires
connecting the abstract pseudoMass to the concrete lattice mass via Lemma 17.5.2 bounds.

**References**: Glimm–Jaffe §17.5 pp.310–312.
-/
theorem pseudoMass_comp_corr_continuousAt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (A : Finset ι)
    (hcorr : correlation G (⟨J, 0, β⟩ : IsingParams ℝ) A ∈ Set.Ioo 0 2) :
    ContinuousAt (fun β' =>
        if hc : correlation G (⟨J, 0, β'⟩ : IsingParams ℝ) A ∈ Set.Ioo 0 2
        then pseudoMass hα hr hc else 0) β := by
  -- Proof via continuousAt_def + manual composition (Filter.Tendsto)
  set c₀ := correlation G (⟨J, 0, β⟩ : IsingParams ℝ) A
  have h_g := (IsingModel.correlation_continuousAt_beta G J β A).tendsto
  have h_f := (pseudoMass_continuousAt hα hr hcorr).tendsto
  rw [continuousAt_def]
  intro s hs
  exact h_g (h_f hs)

/-! ## Antitonicity of pseudoMass ∘ correlation in β (Step 123) -/

/-- **Step 123**: `β ↦ pseudoMass(c(β))` is antitone in β.

When the correlation `c(β) = ⟨σ^A⟩_β` lies in `(0, 2)` for all `β > 0`,
the pseudo-mass `β ↦ pseudoMass(c(β))` is antitone (decreasing) on `Ioi 0`.

Proof: compose `correlation_monotoneOn_beta` (β ↑ → c(β) ↑) with `pseudoMass_strictAnti`
(c ↑ → pseudoMass(c) ↓).

This completes the §17.5 accessible content: higher β → larger correlation →
smaller pseudo-mass (approaching zero at β_c).

Reference: derived from `pseudoMass_strictAnti` (Step 117g) and
`correlation_monotoneOn_beta` (Step 122); implicit in the §17.5 pseudo-mass analysis
(Glimm–Jaffe §17.5, 2nd ed., pp. 311–312). -/
theorem pseudoMass_comp_corr_antitoneOn_beta
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J : ℝ) (hJ : 0 ≤ J) (A : Finset ι)
    (hc_mem : ∀ β : ℝ, 0 < β →
        correlation G (⟨J, 0, β⟩ : IsingParams ℝ) A ∈ Set.Ioo 0 2) :
    AntitoneOn
      (fun β => if h : 0 < β then pseudoMass hα hr (hc_mem β h) else 0)
      (Set.Ioi 0) := by
  intro β₁ hβ₁ β₂ hβ₂ hle
  simp only [Set.mem_Ioi] at hβ₁ hβ₂
  simp only [dif_pos hβ₁, dif_pos hβ₂]
  have hcle : correlation G (⟨J, 0, β₁⟩ : IsingParams ℝ) A ≤
              correlation G (⟨J, 0, β₂⟩ : IsingParams ℝ) A :=
    correlation_monotoneOn_beta G J hJ A
      (Set.mem_Ici.mpr hβ₁.le) (Set.mem_Ici.mpr hβ₂.le) hle
  by_cases heq : correlation G (⟨J, 0, β₁⟩ : IsingParams ℝ) A =
                 correlation G (⟨J, 0, β₂⟩ : IsingParams ℝ) A
  · simp [heq]
  · exact le_of_lt
      (pseudoMass_strictAnti hα hr (hc_mem β₁ hβ₁) (hc_mem β₂ hβ₂)
        (lt_of_le_of_ne hcle heq))


end IsingModel
