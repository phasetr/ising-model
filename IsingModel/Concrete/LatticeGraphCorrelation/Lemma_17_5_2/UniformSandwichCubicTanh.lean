import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.UniformSandwich
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSBridgeFromCubicTanh

/-!
# GJ §17.5 Lemma 17.5.2 — uniform sandwich from cubic tanh profiles

This module is part of the split
`IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2` development.  It
composes the uniform-sandwich theorem from `UniformSandwich.lean` with the
existing cubic tanh-profile infrastructure.

The new wrappers replace the raw profile input

```text
pseudoMassG α r (-log(βJ·2d)) ≤ correlationInfinite Λ {x,z}
```

by the named displacement condition
`cubicTanhProfileBound α d r β J (z - x)`.  Translation invariance changes the
anchored cubic pair `{0, z - x}` to the pair `{x,z}`, and
exhaustion-independence transfers the cubic-exhaustion correlation to the target
exhaustion.

Tracking issue: <https://github.com/phasetr/ising-model/issues/1645>.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Lemma 17.5.2, pp.~311--312.
* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §5.1, pp.~74--75.
-/

namespace IsingModel
namespace Ambient

set_option maxHeartbeats 2000000 in
-- The target-exhaustion `correlationInfinite` statement crosses the same
-- local/canonical edge-set `Fintype` boundary as the uniform-transfer modules.
/-- **Displacement tanh profile supplies the target profile lower bound**: if
`cubicTanhProfileBound` holds at the displacement `z - x`, then the raw profile
lower bound required by the uniform-sandwich theorem holds for the same pair on
any ferromagnetic target exhaustion.

The proof uses the existing anchored cubic tanh-profile bridge, translation
invariance on the cubic exhaustion, and exhaustion-independence.

References: Glimm--Jaffe §17.5, Lemma 17.5.2, pp.~311--312. -/
theorem pseudoMassG_le_correlationInfinite_of_cubicTanhProfileBound_displacement
    {α d : ℕ} {r β J : ℝ}
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (hJ : 0 ≤ J) (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z)
    (hprofile_tanh : cubicTanhProfileBound α d r β J (z - x)) :
    pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} := by
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) :=
    ⟨hJ, le_refl 0, hβ⟩
  have hzx_ne : z - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxz)
  have hprofile_cubic :
      pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
            {x, z} := by
    rw [correlationInfinite_pair_eq_displacement d hJ hβ x z]
    exact cubicTanhProfileBound_le_cubic_correlation hJ hβ hzx_ne
      hprofile_tanh
  have hind :
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} =
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
            {x, z} :=
    correlationInfinite_indep_exhaustion (IsingModel.latticeGraph d) Λ
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) hf {x, z}
  simpa [hind] using hprofile_cubic

set_option maxHeartbeats 2000000 in
-- The active-pair statement unfolds through `correlationInfinite` with a local
-- exhaustion instance and needs the same head-normalization budget.
/-- **Active pair from a displacement tanh profile**: the same
`cubicTanhProfileBound` input supplies the active-range membership required by
the system pseudo-mass on any ferromagnetic target exhaustion.

References: Glimm--Jaffe §17.5, Lemma 17.5.2, pp.~311--312. -/
theorem activePseudoMassPair_of_cubicTanhProfileBound_displacement
    {α d : ℕ} {r β J : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (hJ : 0 ≤ J) (hβ : 0 < β) (hlt : β * J * ↑(2 * d) < 1)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    (hprofile_tanh : cubicTanhProfileBound α d r β J (z - x)) :
    ActivePseudoMassPair Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z := by
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) :=
    ⟨hJ, le_refl 0, hβ⟩
  have hcorr_cubic :
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}
        ∈ Set.Ioo (0 : ℝ) 2 :=
    correlationInfinite_pair_mem_Ioo_zero_two_of_cubicTanhProfileBound_displacement
      hr hJ hβ hlt hxz hprofile_tanh
  have hind :
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} =
        Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ)
            {x, z} :=
    correlationInfinite_indep_exhaustion (IsingModel.latticeGraph d) Λ
      (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) hf {x, z}
  exact ⟨hxz, by simpa [hind] using hcorr_cubic⟩

/-- **GJ §17.5 Lemma 17.5.2 uniform sandwich from a displacement
cubic tanh-profile input (single pair)**: for any target exhaustion, the named
profile condition at `z - x` supplies the active-range and profile inputs, and
the PR #3383 uniform-sandwich theorem gives
`ofReal m⁻(x,z) ≤ latticeMass ≤ ofReal K · ofReal m⁻(x,z)`.

The constant is uniform in the pair in the same non-sharp sense as
`lemma_17_5_2_high_temp_sandwich_uniform_transfer`.

References: Glimm--Jaffe §17.5, Lemma 17.5.2, pp.~311--312. -/
theorem lemma_17_5_2_high_temp_sandwich_uniform_transfer_of_cubicTanhProfileBound
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (hd : 0 < d)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 < J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {x z : Fin d → ℤ} (hxz : x ≠ z)
    (hprofile_tanh : cubicTanhProfileBound α d r β J (z - x)) :
    ∃ K : ℝ,
      ENNReal.ofReal
          (pseudoMassFromParamsAtPair hα hr d Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) x z)
        ≤ latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ∧
      latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ≤
        ENNReal.ofReal K *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hr d Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) x z) := by
  have hxz_active :
      ActivePseudoMassPair Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z :=
    activePseudoMassPair_of_cubicTanhProfileBound_displacement
      hr Λ hJ.le hβ hlt hxz hprofile_tanh
  have hprofile :
      pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} :=
    pseudoMassG_le_correlationInfinite_of_cubicTanhProfileBound_displacement
      Λ hJ.le hβ hxz hprofile_tanh
  exact
    lemma_17_5_2_high_temp_sandwich_uniform_transfer
      hα hr hd Λ hJ hβ hlt hxz_active hprofile

/-- **GJ §17.5 Lemma 17.5.2 uniform sandwich from a family of cubic
tanh-profile inputs (all pairs)**: if `cubicTanhProfileBound` holds at every
nonzero displacement, then one constant `K` works for every distinct pair on any
target exhaustion.

This is the all-pairs version of
`lemma_17_5_2_high_temp_sandwich_uniform_transfer_of_cubicTanhProfileBound`.

References: Glimm--Jaffe §17.5, Lemma 17.5.2, pp.~311--312. -/
theorem lemma_17_5_2_high_temp_sandwich_uniform_transfer_forall_of_cubicTanhProfileBound
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (hd : 0 < d)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 < J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1)
    (hprofile_family : ∀ w : Fin d → ℤ, w ≠ 0 →
      cubicTanhProfileBound α d r β J w) :
    ∃ K : ℝ, ∀ x z : Fin d → ℤ, x ≠ z →
      ENNReal.ofReal
          (pseudoMassFromParamsAtPair hα hr d Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) x z)
        ≤ latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ∧
      latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ≤
        ENNReal.ofReal K *
          ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hr d Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) x z) := by
  obtain ⟨K, hK⟩ :=
    lemma_17_5_2_high_temp_sandwich_uniform_transfer_forall
      hα hr hd Λ hJ hβ hlt
  refine ⟨K, fun x z hxz => ?_⟩
  have hzx_ne : z - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxz)
  have hprofile_tanh : cubicTanhProfileBound α d r β J (z - x) :=
    hprofile_family (z - x) hzx_ne
  have hxz_active :
      ActivePseudoMassPair Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z :=
    activePseudoMassPair_of_cubicTanhProfileBound_displacement
      hr Λ hJ.le hβ hlt hxz hprofile_tanh
  have hprofile :
      pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
        Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} :=
    pseudoMassG_le_correlationInfinite_of_cubicTanhProfileBound_displacement
      Λ hJ.le hβ hxz hprofile_tanh
  exact hK x z hxz_active hprofile

end Ambient
end IsingModel
