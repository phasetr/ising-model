import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.GlobalPseudoMassDistUpperFull
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassFoundationTrivialSliceAndIndep

/-!
# GJ §17.5 Lemma 17.5.2 — arbitrary-exhaustion full-window sandwich

The full-window faithful sandwich `m⁻(σ) ≤ m(σ) ≤ C·m⁻(σ)`
(`globalPseudoMassDist_fullSandwich`, `GlobalPseudoMassDistUpperFull.lean`) is
stated for the cubic exhaustion.  The book's Lemma 17.5.2 is about the
exhaustion-**independent** infinite-volume system, so this module lifts the
sandwich to an **arbitrary** exhaustion `Λ`.

The lift is purely the exhaustion-independence of the underlying quantities:

* `correlationInfinite (latticeGraph d) Λ ⟨J,0,β⟩ {x,z}` is independent of `Λ`
  (`correlationInfinite_indep_exhaustion`, ferromagnetic), so both the faithful
  per-pair pseudo-mass `pseudoMassFromParamsAtPairDist` and the active-pair
  predicate `ActivePseudoMassPair` agree across exhaustions, hence so does their
  lower envelope `globalPseudoMassDist`;
* `latticeMass d Λ ⟨J,0,β⟩` is independent of `Λ`
  (`latticeMass_indep_cubicExhaustion`, ferromagnetic).

No new spectral input is required: the constant `C =
globalPseudoMassDistFullUpperConst α d J β` depends only on `α, d, J, β`, not on
`Λ`.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Lemma 17.5.2, pp.~311--312.
-/

namespace IsingModel
namespace Ambient

open Set Real

/-- **Exhaustion-independence of the distance-parametrized per-pair pseudo-mass**:
for ferromagnetic `p`, `pseudoMassFromParamsAtPairDist hα Λ p x z` does not depend
on the exhaustion `Λ`.

On the diagonal both sides are `0`; off the diagonal both are
`pseudoMassExt hα (dist-pos) (correlationInfinite … Λ … {x,z})`, and the
correlation is exhaustion-independent (`correlationInfinite_indep_exhaustion`). -/
theorem pseudoMassFromParamsAtPairDist_indep_exhaustion {α d : ℕ} (hα : 1 ≤ α)
    (Λ Λ' : Ambient.Exhaustion (Fin d → ℤ))
    {p : IsingParams ℝ} (hf : Ferromagnetic p) (x z : Fin d → ℤ) :
    pseudoMassFromParamsAtPairDist hα Λ p x z
      = pseudoMassFromParamsAtPairDist hα Λ' p x z := by
  by_cases hxz : x ≠ z
  · have hpos : (0 : ℝ) < (IsingModel.latticeDistance d x z : ℝ) := by
      have hne : IsingModel.latticeDistance d x z ≠ 0 :=
        fun h => hxz ((IsingModel.latticeDistance_eq_zero_iff d x z).mp h)
      exact_mod_cast Nat.pos_of_ne_zero hne
    rw [pseudoMassFromParamsAtPairDist_of_ne hα Λ p hxz hpos,
      pseudoMassFromParamsAtPairDist_of_ne hα Λ' p hxz hpos,
      correlationInfinite_indep_exhaustion (IsingModel.latticeGraph d) Λ Λ' p hf
        {x, z}]
  · have hxz' : x = z := not_not.mp hxz
    subst hxz'
    unfold pseudoMassFromParamsAtPairDist
    simp

/-- **Exhaustion-independence of the active-pair predicate**: for ferromagnetic
`p`, `ActivePseudoMassPair Λ p x z ↔ ActivePseudoMassPair Λ' p x z`, since the
underlying correlation is exhaustion-independent. -/
theorem activePseudoMassPair_indep_exhaustion {d : ℕ}
    (Λ Λ' : Ambient.Exhaustion (Fin d → ℤ))
    {p : IsingParams ℝ} (hf : Ferromagnetic p) (x z : Fin d → ℤ) :
    ActivePseudoMassPair Λ p x z ↔ ActivePseudoMassPair Λ' p x z := by
  unfold ActivePseudoMassPair
  rw [correlationInfinite_indep_exhaustion (IsingModel.latticeGraph d) Λ Λ' p hf
    {x, z}]

/-- **Exhaustion-independence of the distance-parametrized system pseudo-mass**:
for ferromagnetic `p`, `globalPseudoMassDist hα Λ p = globalPseudoMassDist hα Λ' p`.

The defining value sets `globalPseudoMassDistSet` coincide
(`activePseudoMassPair_indep_exhaustion`,
`pseudoMassFromParamsAtPairDist_indep_exhaustion`), so the infima agree. -/
theorem globalPseudoMassDist_indep_exhaustion {α d : ℕ} (hα : 1 ≤ α)
    (Λ Λ' : Ambient.Exhaustion (Fin d → ℤ))
    {p : IsingParams ℝ} (hf : Ferromagnetic p) :
    globalPseudoMassDist hα Λ p = globalPseudoMassDist hα Λ' p := by
  unfold globalPseudoMassDist
  congr 1
  unfold globalPseudoMassDistSet
  ext m
  constructor
  · rintro ⟨x, z, hact, rfl⟩
    exact ⟨x, z, (activePseudoMassPair_indep_exhaustion Λ Λ' hf x z).mp hact,
      pseudoMassFromParamsAtPairDist_indep_exhaustion hα Λ Λ' hf x z⟩
  · rintro ⟨x, z, hact, rfl⟩
    exact ⟨x, z, (activePseudoMassPair_indep_exhaustion Λ Λ' hf x z).mpr hact,
      pseudoMassFromParamsAtPairDist_indep_exhaustion hα Λ' Λ hf x z⟩

/-- **GJ §17.5 Lemma 17.5.2 full-window upper bound, arbitrary exhaustion**
`m(σ) ≤ C·m⁻(σ)` on `βJ·2d < 1`.

The cubic full-window upper bound `latticeMass_le_globalPseudoMassDist_fullUpper`
is transported to any exhaustion `Λ` by rewriting both the lattice mass
(`latticeMass_indep_cubicExhaustion`) and the system pseudo-mass
(`globalPseudoMassDist_indep_exhaustion`) to the cubic exhaustion; the upper
constant is exhaustion-independent. -/
theorem latticeMass_le_globalPseudoMassDist_fullUpper_exhaustion
    {α d : ℕ} (hα : 1 ≤ α) (hd : 0 < d)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β)
    (hβJd_lt1 : β * J * (2 * d) < 1) :
    latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ≤
      ENNReal.ofReal (globalPseudoMassDistFullUpperConst α d J β) *
        ENNReal.ofReal
          (globalPseudoMassDist hα Λ (⟨J, 0, β⟩ : IsingParams ℝ)) := by
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ.le, le_refl 0, hβ⟩
  rw [latticeMass_indep_cubicExhaustion Λ hf,
    globalPseudoMassDist_indep_exhaustion hα Λ (Ambient.cubicExhaustion d) hf]
  exact latticeMass_le_globalPseudoMassDist_fullUpper hα hd hJ hβ hβJd_lt1

/-- **GJ §17.5 Lemma 17.5.2 faithful FULL-window sandwich, arbitrary exhaustion**
`m⁻(σ) ≤ m(σ) ≤ C·m⁻(σ)` on the full high-temperature window `βJ·2d < 1`, for an
arbitrary exhaustion `Λ`.

This is the exhaustion-independent (book) form of `globalPseudoMassDist_fullSandwich`:
the lower bound `globalPseudoMassDist_le_latticeMass` already holds for any
exhaustion, and the upper bound is the arbitrary-exhaustion lift above. -/
theorem globalPseudoMassDist_fullSandwich_exhaustion
    {α d : ℕ} (hα : 1 ≤ α) (hd : 0 < d)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β)
    (hβJd_lt1 : β * J * (2 * d) < 1) :
    ENNReal.ofReal
        (globalPseudoMassDist hα Λ (⟨J, 0, β⟩ : IsingParams ℝ)) ≤
      latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ∧
    latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ≤
      ENNReal.ofReal (globalPseudoMassDistFullUpperConst α d J β) *
        ENNReal.ofReal
          (globalPseudoMassDist hα Λ (⟨J, 0, β⟩ : IsingParams ℝ)) :=
  ⟨globalPseudoMassDist_le_latticeMass hα Λ hJ.le hβ,
   latticeMass_le_globalPseudoMassDist_fullUpper_exhaustion hα hd Λ hJ hβ hβJd_lt1⟩

end Ambient
end IsingModel
