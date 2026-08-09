import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransferSummability
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassFoundationTrivialSliceAndIndep

/-!
# ℤ^d characterisation of the critical inverse temperature (§17.1)

Instantiates at `IsingModel.latticeGraph d`, along `Ambient.cubicExhaustion d` and at zero
external field, the relation between the lattice mass and `criticalInverseTemp d J`. A
strictly positive lattice mass puts `ENNReal.ofReal β` at or below the critical value, and an
inverse temperature strictly above the critical value forces the lattice mass to vanish; each
of those assumes only `0 ≤ β`. Conversely an inverse temperature strictly below the critical
value forces the lattice mass to be strictly positive, and that direction assumes `0 ≤ J` as
well as `0 ≤ β`.
-/

namespace IsingModel
namespace Ambient

/-- **Lower bound on `criticalInverseTemp` from positive mass** (GJ §17.1):
if `latticeMass d (cubicExhaustion d) ⟨J, 0, β⟩ > 0` for some `β ≥ 0`, then
`ENNReal.ofReal β ≤ criticalInverseTemp d J`.

Proof: `β` is in the defining set of `criticalInverseTemp`, so `ENNReal.ofReal β` is
in the image set, and `le_sSup` gives the bound. -/
theorem criticalInverseTemp_ge_ofReal_of_latticeMass_pos
    {d : ℕ} {J β : ℝ} (hβ : 0 ≤ β)
    (h : 0 < latticeMass d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)) :
    ENNReal.ofReal β ≤ criticalInverseTemp d J :=
  le_sSup ⟨β, ⟨hβ, h⟩, rfl⟩

/-- **Mass vanishes above the critical inverse temperature** (GJ §17.1):
if `criticalInverseTemp d J < ENNReal.ofReal β` (and `β ≥ 0`), then
`latticeMass d (cubicExhaustion d) ⟨J, 0, β⟩ = 0`.

This is the characterization: for β strictly above the critical threshold, the
high-temperature exponential-decay regime ends and mass vanishes (within the ENNReal lattice).
Proof: contrapositive of `criticalInverseTemp_ge_ofReal_of_latticeMass_pos`. -/
theorem latticeMass_eq_zero_of_criticalInverseTemp_lt
    {d : ℕ} {J β : ℝ} (hβ : 0 ≤ β)
    (h : criticalInverseTemp d J < ENNReal.ofReal β) :
    latticeMass d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) = 0 := by
  by_contra hm
  exact absurd h (not_lt.mpr
    (criticalInverseTemp_ge_ofReal_of_latticeMass_pos hβ (lt_of_le_of_ne (zero_le _) (Ne.symm hm))))

/-- **Positive mass below the critical inverse temperature** (GJ §17.1):
for ferromagnetic `J ≥ 0`, `β ≥ 0`, and `ENNReal.ofReal β < criticalInverseTemp d J`,
the lattice mass is strictly positive.

Together with `latticeMass_eq_zero_of_criticalInverseTemp_lt` and
`criticalInverseTemp_ge_ofReal_of_latticeMass_pos`, this gives a near-complete picture:
`ENNReal.ofReal β < β_c → mass > 0 → ENNReal.ofReal β ≤ β_c`
(where `β_c = criticalInverseTemp d J`).
The boundary case `ENNReal.ofReal β = criticalInverseTemp d J` remains undetermined.

**GJ §17.1 context**: for σ < σ_c (= β < β_c in the Ising analog), the theory has
exponential decay of correlations; this is the defining property of the critical coupling.

Proof: by contradiction — if mass(J, β) = 0, then for all β' ≥ β (and β > 0), the
antitonicity `latticeMass_antitone_beta` gives mass(J, β') ≤ mass(J, β) = 0. Hence the
defining set ⊆ `[0, β)`, so `criticalInverseTemp ≤ ENNReal.ofReal β`, contradicting
`ENNReal.ofReal β < criticalInverseTemp`. The β = 0 case is vacuous since mass(J, 0) = ⊤. -/
theorem latticeMass_pos_of_lt_criticalInverseTemp
    {d : ℕ} {J β : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    (h : ENNReal.ofReal β < criticalInverseTemp d J) :
    0 < latticeMass d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) := by
  by_contra hm
  rw [not_lt] at hm
  have hm_zero : latticeMass d (cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) = 0 :=
    le_antisymm hm (latticeMass_nonneg _ _ _)
  rcases eq_or_lt_of_le hβ with rfl | hβ_pos
  · simp [latticeMass_top_of_beta_zero] at hm_zero
  · have h_bound : criticalInverseTemp d J ≤ ENNReal.ofReal β := by
      unfold criticalInverseTemp
      apply sSup_le
      intro b hb
      rw [Set.mem_image] at hb
      obtain ⟨γ, ⟨hγ_nn, hmass_γ⟩, hγ_eq⟩ := hb
      rw [← hγ_eq]
      apply ENNReal.ofReal_le_ofReal
      by_cases h_le : γ ≤ β
      · exact h_le
      · rw [not_le] at h_le
        have hmono := latticeMass_antitone_beta (cubicExhaustion d) hJ hβ_pos h_le.le
        rw [hm_zero] at hmono
        exact absurd hmass_γ (not_lt.mpr hmono)
    exact absurd h (not_lt.mpr h_bound)

end Ambient
end IsingModel
