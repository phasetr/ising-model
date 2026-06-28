import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.FiniteVolumePairActive
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.FiniteRegionPseudoMassDistContinuity

/-!
# GJ §17.5 Theorem 17.5.1 — PR-FV1: finite-volume per-pair pseudo-mass and finite-region mass

The finite-volume per-pair pseudo-mass `m⁻_FV(x,z,σ,n)` and the finite-region system pseudo-mass
`m⁻_FV(σ, A=volume n)`, built on the **finite-volume** two-point function
`correlationAlongExhaustion (latticeGraph d) (cubicExhaustion d) σ {x,z} n` (GJ's `⟨·⟩_{σ,A}`), in
contrast to the existing `pseudoMassFromParamsAtPairDist` / `finiteRegionPseudoMassDist` which use
the infinite-volume `correlationInfinite`.

This is the object GJ's p.312 estimate is genuinely about: at the in-box binding pair the FV mass
equals `m⁻_FV(σ,A)` *exactly* (finite attained inf ⟹ `hbind` free), and the cross-sum `∑_{z∈A}` is
local so the scale `m⁻_FV(σ,A)` is consistent with every term (no `exp` blow-up; cf. #4320).

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof, pp.~311--312.
-/

namespace IsingModel
namespace Ambient

open Real

/-- **Finite-volume per-pair pseudo-mass** at the cubic stage `n`: the totalized `pseudoMassExt` of
the finite-volume two-point function `⟨φ(x)φ(z)⟩_{σ,volume n}` at radius `latticeDistance d x z`,
with the diagonal fallback `0`.  The finite-volume analogue of `pseudoMassFromParamsAtPairDist`. -/
noncomputable def pseudoMassFromParamsAtPairFV {α d : ℕ} (hα : 1 ≤ α)
    (p : IsingParams ℝ) (n : ℕ) (x z : Fin d → ℤ) : ℝ :=
  if hxz : x ≠ z then
    pseudoMassExt hα
      (show (0 : ℝ) < (IsingModel.latticeDistance d x z : ℝ) from by
        exact_mod_cast Nat.pos_of_ne_zero
          (fun h => hxz ((IsingModel.latticeDistance_eq_zero_iff d x z).mp h)))
      (Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d) p
        {x, z} n)
  else 0

/-- **`pseudoMassFromParamsAtPairFV` is non-negative** (both branches). -/
theorem pseudoMassFromParamsAtPairFV_nonneg {α d : ℕ} (hα : 1 ≤ α)
    (p : IsingParams ℝ) (n : ℕ) (x z : Fin d → ℤ) :
    0 ≤ pseudoMassFromParamsAtPairFV hα p n x z := by
  unfold pseudoMassFromParamsAtPairFV
  by_cases hxz : x ≠ z
  · rw [dif_pos hxz]; exact pseudoMassExt_nonneg hα _ _
  · rw [dif_neg hxz]

/-- **Defining equation of `pseudoMassFromParamsAtPairFV` on a distinct pair**. -/
theorem pseudoMassFromParamsAtPairFV_of_ne {α d : ℕ} (hα : 1 ≤ α)
    (p : IsingParams ℝ) (n : ℕ) {x z : Fin d → ℤ} (hxz : x ≠ z)
    (hpos : (0 : ℝ) < (IsingModel.latticeDistance d x z : ℝ)) :
    pseudoMassFromParamsAtPairFV hα p n x z
      = pseudoMassExt hα hpos
          (Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d) p
            {x, z} n) := by
  unfold pseudoMassFromParamsAtPairFV
  rw [dif_pos hxz]

/-- **Finite-volume per-pair pseudo-mass is strictly positive** for a distinct in-box pair at
positive temperature: `0 < pseudoMassFromParamsAtPairFV` when `{x,z} ⊆ volume n`, `0<J`, `0<β`.
Active range from PR-FV0 (`correlationAlongExhaustion_cubicExhaustion_pair_active`) +
`pseudoMassExt_pos_of_mem`. -/
theorem pseudoMassFromParamsAtPairFV_pos {α d : ℕ} (hα : 1 ≤ α) {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β)
    {n : ℕ} {x z : Fin d → ℤ} (hxz : x ≠ z)
    (hsub : ({x, z} : Finset (Fin d → ℤ)) ⊆ (cubicExhaustion d).volume n) :
    0 < pseudoMassFromParamsAtPairFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n x z := by
  have hpos : (0 : ℝ) < (IsingModel.latticeDistance d x z : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero
      (fun h => hxz ((IsingModel.latticeDistance_eq_zero_iff d x z).mp h))
  rw [pseudoMassFromParamsAtPairFV_of_ne hα (⟨J, 0, β⟩ : IsingParams ℝ) n hxz hpos]
  exact pseudoMassExt_pos_of_mem hα hpos
    (correlationAlongExhaustion_cubicExhaustion_pair_active hJ hβ hxz hsub)

/-- **Finite-volume finite-region system pseudo-mass** `m⁻_FV(σ, A=volume n)`: the infimum over the
finitely many distinct pairs of the box `volume n` of the finite-volume per-pair pseudo-mass.  The
finite-volume analogue of `finiteRegionPseudoMassDist`. -/
noncomputable def finiteRegionPseudoMassDistFV {α d : ℕ} (hα : 1 ≤ α)
    (p : IsingParams ℝ) (n : ℕ)
    (hA : (finiteRegionDistinctPairs ((cubicExhaustion d).volume n)).Nonempty) : ℝ :=
  (finiteRegionDistinctPairs ((cubicExhaustion d).volume n)).inf' hA
    (fun q => pseudoMassFromParamsAtPairFV hα p n q.1 q.2)

/-- **Finite-volume finite-region pseudo-mass is strictly positive** at positive temperature: each
contributing in-box distinct pair has positive FV pseudo-mass (`pseudoMassFromParamsAtPairFV_pos`),
so the finite infimum is positive (`Finset.lt_inf'_iff`). -/
theorem finiteRegionPseudoMassDistFV_pos {α d : ℕ} (hα : 1 ≤ α) {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β)
    {n : ℕ} (hA : (finiteRegionDistinctPairs ((cubicExhaustion d).volume n)).Nonempty) :
    0 < finiteRegionPseudoMassDistFV hα (⟨J, 0, β⟩ : IsingParams ℝ) n hA := by
  unfold finiteRegionPseudoMassDistFV
  rw [Finset.lt_inf'_iff]
  intro q hq
  obtain ⟨hq1, hq2, hq_ne⟩ := mem_finiteRegionDistinctPairs.mp hq
  have hsub : ({q.1, q.2} : Finset (Fin d → ℤ)) ⊆ (cubicExhaustion d).volume n := by
    intro w hw
    rw [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact hq1
    · exact hq2
  exact pseudoMassFromParamsAtPairFV_pos hα hJ hβ hq_ne hsub

/-- **Finite-volume finite-region pseudo-mass is `≤` any contributing in-box pair's FV pseudo-mass**
(`Finset.inf'_le`): for `(x, z) ∈ finiteRegionDistinctPairs (volume n)`,
`finiteRegionPseudoMassDistFV hα p n hA ≤ pseudoMassFromParamsAtPairFV hα p n x z`. -/
theorem finiteRegionPseudoMassDistFV_le_of_mem {α d : ℕ} (hα : 1 ≤ α) (p : IsingParams ℝ)
    (n : ℕ) (hA : (finiteRegionDistinctPairs ((cubicExhaustion d).volume n)).Nonempty)
    {x z : Fin d → ℤ}
    (hmem : (x, z) ∈ finiteRegionDistinctPairs ((cubicExhaustion d).volume n)) :
    finiteRegionPseudoMassDistFV hα p n hA ≤ pseudoMassFromParamsAtPairFV hα p n x z := by
  unfold finiteRegionPseudoMassDistFV
  exact Finset.inf'_le (fun q => pseudoMassFromParamsAtPairFV hα p n q.1 q.2) hmem

end Ambient
end IsingModel
