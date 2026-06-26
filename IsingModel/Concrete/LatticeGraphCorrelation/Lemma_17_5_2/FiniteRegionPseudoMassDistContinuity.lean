import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.GlobalPseudoMassDist
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassHighTempContinuousAt
import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.HLSBridgeFromCubicTanh

/-!
# GJ §17.5 Lemma 17.5.2 — continuity of the finite-region pseudo-mass `m⁻(σ, A)`

This module formalizes parts (a) and (b) of Glimm--Jaffe §17.5 Lemma 17.5.2: for
a **bounded** region `A` (with at least one distinct pair), the system
pseudo-mass `m⁻(σ, A)` is (a) **continuous** in the inverse temperature and
(b) **strictly positive**.

The book's continuous object is `m⁻(σ, A)` for a *fixed bounded* region `A`,
namely the infimum over the **finitely many** distinct pairs `(x, z)` drawn from
`A` of the distance-parametrized per-pair pseudo-mass
`pseudoMassFromParamsAtPairDist` (introduced in `GlobalPseudoMassDist.lean`).  A
finite `Finset.inf'` of continuous functions is continuous
(`ContinuousAt.finset_inf'`), so this faithful piece is tractable — unlike the
infinite lower envelope `globalPseudoMassDist`, whose continuity is *not*
automatic (an infinite infimum of continuous functions is only upper
semicontinuous in general).

The single-pair continuity input is the high-temperature regularity of the
infinite-volume two-point correlation
(`correlationInfinite_continuousAt_beta_of_high_temp`) transported through the
pseudo-mass inversion (`pseudoMassExt_continuousAt`), valid on the standard
high-temperature window `β ∈ Ioo 0 (1 / (J · 2d))`.  Strict positivity of the
finite-region pseudo-mass is the finite-infimum version of `pseudoMass_pos`.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Lemma 17.5.2, pp.~311--312.
-/

namespace IsingModel
namespace Ambient

open Set Real

/-- **Distinct ordered pairs of a finite region** `A`: the `Finset` of ordered
pairs `(x, z) ∈ A × A` with `x ≠ z`.  The finite-region pseudo-mass `m⁻(σ, A)`
is the infimum of the per-pair pseudo-masses ranging over this set.

References: Glimm--Jaffe §17.5, p.~311. -/
def finiteRegionDistinctPairs {d : ℕ} (A : Finset (Fin d → ℤ)) :
    Finset ((Fin d → ℤ) × (Fin d → ℤ)) :=
  (A ×ˢ A).filter (fun q => q.1 ≠ q.2)

/-- **Membership in `finiteRegionDistinctPairs`**: a pair `q` lies in
`finiteRegionDistinctPairs A` iff both coordinates lie in `A` and they are
distinct. -/
theorem mem_finiteRegionDistinctPairs {d : ℕ} {A : Finset (Fin d → ℤ)}
    {q : (Fin d → ℤ) × (Fin d → ℤ)} :
    q ∈ finiteRegionDistinctPairs A ↔ q.1 ∈ A ∧ q.2 ∈ A ∧ q.1 ≠ q.2 := by
  unfold finiteRegionDistinctPairs
  rw [Finset.mem_filter, Finset.mem_product]
  tauto

/-- **Finite-region system pseudo-mass** `m⁻(σ, A)` of Glimm--Jaffe §17.5: the
infimum over the finitely many distinct pairs of the bounded region `A` of the
distance-parametrized per-pair pseudo-mass `pseudoMassFromParamsAtPairDist`.

Each contributing pair uses its own ℓ¹ lattice distance as the profile radius,
so this finite infimum is the genuine inverse correlation length restricted to
the region `A`.  It is the book's continuous object (a *finite* infimum, hence
continuous), in contrast to the infinite lower envelope `globalPseudoMassDist`.

References: Glimm--Jaffe §17.5, Lemma 17.5.2, pp.~311--312. -/
noncomputable def finiteRegionPseudoMassDist {α d : ℕ} (hα : 1 ≤ α)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (A : Finset (Fin d → ℤ))
    (hA : (finiteRegionDistinctPairs A).Nonempty) : ℝ :=
  (finiteRegionDistinctPairs A).inf' hA
    (fun q => pseudoMassFromParamsAtPairDist hα Λ p q.1 q.2)

/-- **Single-pair distance pseudo-mass is continuous in `β` at high temperature**:
for a distinct cubic-lattice pair `(x, z)` and a high-temperature inverse
temperature `β₀ ∈ Ioo 0 (1 / (J · 2d))`, the map
`β ↦ pseudoMassFromParamsAtPairDist hα (cubicExhaustion d) ⟨J, 0, β⟩ x z` is
continuous at `β₀`.

Proof: the per-pair distance pseudo-mass is `pseudoMassExt` at the constant
profile radius `r = latticeDistance d x z` composed with the correlation profile
`β ↦ ⟨σ_x σ_z⟩^∞`.  The correlation is continuous at `β₀`
(`correlationInfinite_continuousAt_beta_of_high_temp`) and lands in the active
range `Ioo 0 2` for any `0 < β` at the cubic exhaustion
(`correlationInfinite_pair_active_of_betaJ_pos`), where `pseudoMassExt` is
continuous (`pseudoMassExt_continuousAt`); composition closes the goal.

References: Glimm--Jaffe §17.5, Lemma 17.5.2, p.~311. -/
theorem pseudoMassFromParamsAtPairDist_beta_continuousAt_of_high_temp
    {α d : ℕ} (hα : 1 ≤ α) (hd : 1 ≤ d)
    {x z : Fin d → ℤ} (hxz : x ≠ z)
    {J β₀ : ℝ} (hJ : 0 < J)
    (hβ₀ : β₀ ∈ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))) :
    ContinuousAt
      (fun β => pseudoMassFromParamsAtPairDist hα (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) x z)
      β₀ := by
  -- Constant profile radius `r = latticeDistance d x z > 0`.
  have hdist_pos : (0 : ℝ) < (IsingModel.latticeDistance d x z : ℝ) := by
    have hne : IsingModel.latticeDistance d x z ≠ 0 :=
      fun h => hxz ((IsingModel.latticeDistance_eq_zero_iff d x z).mp h)
    exact_mod_cast Nat.pos_of_ne_zero hne
  -- Active-range membership at `β₀` (any `0 < β` works at the cubic exhaustion).
  have hβ₀_pos : 0 < β₀ := hβ₀.1
  have hβJ_pos : 0 < β₀ * J := mul_pos hβ₀_pos hJ
  have hmem₀ :
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β₀⟩ : IsingParams ℝ) {x, z}
        ∈ Set.Ioo (0 : ℝ) 2 :=
    correlationInfinite_pair_active_of_betaJ_pos hβ₀_pos hβJ_pos x z hxz
  -- Rewrite the per-pair distance pseudo-mass as `pseudoMassExt ∘ correlation`.
  have hfun :
      (fun β => pseudoMassFromParamsAtPairDist hα (Ambient.cubicExhaustion d)
          (⟨J, 0, β⟩ : IsingParams ℝ) x z)
        = (fun β => pseudoMassExt hα hdist_pos
            (Ambient.correlationInfinite (IsingModel.latticeGraph d)
              (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z})) := by
    funext β
    exact pseudoMassFromParamsAtPairDist_of_ne hα (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) hxz hdist_pos
  rw [hfun]
  -- Compose continuity of `pseudoMassExt` with continuity of the correlation.
  change ContinuousAt
    ((pseudoMassExt hα hdist_pos) ∘
      (fun β => Ambient.correlationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {x, z})) β₀
  exact ContinuousAt.comp
    (pseudoMassExt_continuousAt hα hdist_pos hmem₀)
    (correlationInfinite_continuousAt_beta_of_high_temp hd
      (Ambient.cubicExhaustion d) x z hxz J hJ β₀ hβ₀)

/-- **GJ §17.5 Lemma 17.5.2 (a): finite-region pseudo-mass `m⁻(σ, A)` is
continuous in `β` at high temperature** (`ContinuousAt` form).

For a bounded cubic-lattice region `A` with at least one distinct pair, the
finite-region pseudo-mass `β ↦ finiteRegionPseudoMassDist hα (cubicExhaustion d)
⟨J, 0, β⟩ A hA` is continuous at every high-temperature point
`β₀ ∈ Ioo 0 (1 / (J · 2d))`.

Proof: a finite infimum of functions continuous at `β₀` is continuous at `β₀`
(`ContinuousAt.finset_inf'`); each summand is the single-pair continuity
`pseudoMassFromParamsAtPairDist_beta_continuousAt_of_high_temp`, whose distinctness
hypothesis comes from membership in `finiteRegionDistinctPairs`.

References: Glimm--Jaffe §17.5, Lemma 17.5.2, p.~311. -/
theorem finiteRegionPseudoMassDist_beta_continuousAt_of_high_temp
    {α d : ℕ} (hα : 1 ≤ α) (hd : 1 ≤ d)
    (A : Finset (Fin d → ℤ))
    (hA : (finiteRegionDistinctPairs A).Nonempty)
    {J β₀ : ℝ} (hJ : 0 < J)
    (hβ₀ : β₀ ∈ Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))) :
    ContinuousAt
      (fun β => finiteRegionPseudoMassDist hα (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) A hA)
      β₀ := by
  unfold finiteRegionPseudoMassDist
  refine ContinuousAt.finset_inf'_apply hA ?_
  intro q hq
  have hq_ne : q.1 ≠ q.2 := (mem_finiteRegionDistinctPairs.mp hq).2.2
  exact pseudoMassFromParamsAtPairDist_beta_continuousAt_of_high_temp
    hα hd hq_ne hJ hβ₀

/-- **GJ §17.5 Lemma 17.5.2 (a): finite-region pseudo-mass `m⁻(σ, A)` is
continuous in `β` on the high-temperature window** (`ContinuousOn` form).

The finite-region pseudo-mass is continuous on the open high-temperature window
`Ioo 0 (1 / (J · 2d))`, obtained by upgrading the pointwise `ContinuousAt`
statement (each interior point has the window as a neighbourhood).

References: Glimm--Jaffe §17.5, Lemma 17.5.2, p.~311. -/
theorem finiteRegionPseudoMassDist_beta_continuousOn_high_temp
    {α d : ℕ} (hα : 1 ≤ α) (hd : 1 ≤ d)
    (A : Finset (Fin d → ℤ))
    (hA : (finiteRegionDistinctPairs A).Nonempty)
    {J : ℝ} (hJ : 0 < J) :
    ContinuousOn
      (fun β => finiteRegionPseudoMassDist hα (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) A hA)
      (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))) := by
  intro β₀ hβ₀
  exact (finiteRegionPseudoMassDist_beta_continuousAt_of_high_temp
    hα hd A hA hJ hβ₀).continuousWithinAt

/-- **GJ §17.5 Lemma 17.5.2 (b): finite-region pseudo-mass `m⁻(σ, A)` is strictly
positive** at every `0 < β` (cubic exhaustion).

For a bounded cubic-lattice region `A` with at least one distinct pair, the
finite-region pseudo-mass is `> 0`.  Each distinct cubic-lattice pair is active
(`correlationInfinite_pair_active_of_betaJ_pos`), so its per-pair pseudo-mass is
strictly positive (`pseudoMass_pos`); a finite infimum of strictly positive reals
is strictly positive (`Finset.lt_inf'_iff`).

References: Glimm--Jaffe §17.5, Lemma 17.5.2, p.~311. -/
theorem finiteRegionPseudoMassDist_pos_of_betaJ_pos
    {α d : ℕ} (hα : 1 ≤ α)
    (A : Finset (Fin d → ℤ))
    (hA : (finiteRegionDistinctPairs A).Nonempty)
    {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β) :
    0 < finiteRegionPseudoMassDist hα (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) A hA := by
  have hβJ_pos : 0 < β * J := mul_pos hβ hJ
  unfold finiteRegionPseudoMassDist
  rw [Finset.lt_inf'_iff]
  intro q hq
  have hq_ne : q.1 ≠ q.2 := (mem_finiteRegionDistinctPairs.mp hq).2.2
  have hdist_pos : (0 : ℝ) < (IsingModel.latticeDistance d q.1 q.2 : ℝ) := by
    have hne : IsingModel.latticeDistance d q.1 q.2 ≠ 0 :=
      fun h => hq_ne ((IsingModel.latticeDistance_eq_zero_iff d q.1 q.2).mp h)
    exact_mod_cast Nat.pos_of_ne_zero hne
  have hmem :
      Ambient.correlationInfinite (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ) {q.1, q.2}
        ∈ Set.Ioo (0 : ℝ) 2 :=
    correlationInfinite_pair_active_of_betaJ_pos hβ hβJ_pos q.1 q.2 hq_ne
  rw [pseudoMassFromParamsAtPairDist_of_ne hα (Ambient.cubicExhaustion d)
      (⟨J, 0, β⟩ : IsingParams ℝ) hq_ne hdist_pos,
    pseudoMassExt_of_mem hα hdist_pos hmem]
  exact pseudoMass_pos hα hdist_pos hmem

end Ambient
end IsingModel
