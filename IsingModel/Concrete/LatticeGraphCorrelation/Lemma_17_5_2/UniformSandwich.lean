import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.UniformTransferLargeK
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassPseudoMassTransferBasic

/-!
# GJ §17.5 Lemma 17.5.2 — full sandwich with a uniform upper constant

This module is part of the split
`IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2` development.  It closes
the full Glimm--Jaffe Lemma 17.5.2 sandwich

```text
ofReal m⁻(x,z) ≤ latticeMass ≤ ofReal K · ofReal m⁻(x,z)
```

for ferromagnetic high-temperature active pairs, with a **uniform** upper
constant `K` (depending only on `α, r, d, J, β`, not on the pair).

The lower side `ofReal m⁻ ≤ latticeMass` is supplied by
`HasExponentialDecay_pseudoMassFromParamsAtPair_of_pseudoMassG_le_corr`
(the pseudo-mass rate validates exponential decay) composed with
`lemma_17_5_2_lower_bound_of_decay`; the upper side is the uniform-`K` closure
`lemma_17_5_2_upper_bound_uniform_transfer` (resp.
`lemma_17_5_2_upper_bound_of_uniform_transfer_pseudoMassG` for the
single-`K`-for-all-pairs form), and `lemma_17_5_2_sandwich_of_decay_and_upper`
assembles the two.

Unlike `lemma_17_5_2_cubic_high_temp_sandwich_capstone`, whose constant
`-log(tanh(βJ))/m⁻` is pair-dependent (and cancels `m⁻`), the constant here is
uniform in the pair — the genuine `m ≤ const·m⁻` of the book — though still
**not sharp** (it is not the transfer-matrix correlation length; see
`UniformTransferLargeK.lean`).

Tracking issue: <https://github.com/phasetr/ising-model/issues/1645>.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Lemma 17.5.2, pp.~311--312.
-/

namespace IsingModel
namespace Ambient

/-- **GJ §17.5 Lemma 17.5.2 full sandwich with a uniform upper constant
(single pair)**: for a ferromagnetic high-temperature active pair `(x, z)` whose
correlation dominates the pseudo-mass profile at the high-temperature rate, there
is a uniform constant `K` with
`ofReal m⁻(x,z) ≤ latticeMass ≤ ofReal K · ofReal m⁻(x,z)`.

The lower side comes from
`HasExponentialDecay_pseudoMassFromParamsAtPair_of_pseudoMassG_le_corr` and the
upper side from the uniform-`K` closure `lemma_17_5_2_upper_bound_uniform_transfer`.

References: Glimm--Jaffe §17.5, Lemma 17.5.2, pp.~311--312. -/
theorem lemma_17_5_2_high_temp_sandwich_uniform_transfer
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (hd : 0 < d)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 < J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) {x z : Fin d → ℤ}
    (hxz : ActivePseudoMassPair Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z)
    (hprofile : pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
      Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) {x, z}) :
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
  have hdecay :=
    HasExponentialDecay_pseudoMassFromParamsAtPair_of_pseudoMassG_le_corr
      hα hr Λ hJ.le hβ hlt hxz.2 hprofile
  obtain ⟨K, hupper⟩ :=
    lemma_17_5_2_upper_bound_uniform_transfer hα hr hd Λ hJ hβ hxz
  exact ⟨K, lemma_17_5_2_sandwich_of_decay_and_upper hα hr hdecay hupper⟩

/-- **GJ §17.5 Lemma 17.5.2 full sandwich with a single uniform constant for all
active pairs**: there is one constant `K` (depending only on `α, r, d, J, β`)
such that *every* ferromagnetic high-temperature active pair `(x, z)` whose
correlation dominates the pseudo-mass profile satisfies
`ofReal m⁻(x,z) ≤ latticeMass ≤ ofReal K · ofReal m⁻(x,z)`.

This exposes the uniformity of the constant on the statement level: the same `K`
works for all pairs, matching the book's `m ≤ const·m⁻`.

References: Glimm--Jaffe §17.5, Lemma 17.5.2, pp.~311--312. -/
theorem lemma_17_5_2_high_temp_sandwich_uniform_transfer_forall
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r) (hd : 0 < d)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 < J) (hβ : 0 < β)
    (hlt : β * J * ↑(2 * d) < 1) :
    ∃ K : ℝ, ∀ x z : Fin d → ℤ,
      ActivePseudoMassPair Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z →
      pseudoMassG α r (-Real.log (β * J * ↑(2 * d))) ≤
          Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) {x, z} →
        ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hr d Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) x z)
          ≤ latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ∧
        latticeMass d Λ (⟨J, 0, β⟩ : IsingParams ℝ) ≤
          ENNReal.ofReal K *
            ENNReal.ofReal
              (pseudoMassFromParamsAtPair hα hr d Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z) := by
  obtain ⟨K, hU⟩ := exists_uniform_transfer_pseudoMassG hα hr hd Λ hJ hβ
  refine ⟨K, fun x z hxz hprofile => ?_⟩
  have hdecay :=
    HasExponentialDecay_pseudoMassFromParamsAtPair_of_pseudoMassG_le_corr
      hα hr Λ hJ.le hβ hlt hxz.2 hprofile
  have hupper :=
    lemma_17_5_2_upper_bound_of_uniform_transfer_pseudoMassG hα hr Λ J β hxz hU
  exact lemma_17_5_2_sandwich_of_decay_and_upper hα hr hdecay hupper

end Ambient
end IsingModel
