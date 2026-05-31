import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.Predicates

/-!
# GJ §17.5 Lemma 17.5.2 Part B — global pseudo-mass and all-rate reduction

This module is part of the split
`IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2` development.  It
introduces the **system pseudo-mass** `m⁻(σ)` of Glimm--Jaffe §17.5 as the lower
envelope of the per-pair pseudo-masses, and reduces the named upper-bound
predicate `Lemma_17_5_2_UpperBound` to a single explicitly-named analytic input:
the transfer-matrix all-rate comparison `Lemma_17_5_2_GlobalAllRateComparison`.

Glimm--Jaffe pp.~311--312 define `m⁻(σ)` for the whole system and write
`m⁻(x₀, y₀, σ) = m⁻(σ)` at a minimizing pair, so the system pseudo-mass is the
lower envelope (infimum over active distinct pairs) of the per-pair
`pseudoMassFromParamsAtPair`.  The upper-bound side `m(σ) ≤ const · m⁻(σ)` of
Lemma 17.5.2 is derived in the book from the transfer matrix giving exponential
decay of all correlations at rate `e^{-m·dist}`; that step is *not* the Lipschitz
continuity argument used for Theorem 17.5.1, so this module keeps the
transfer-matrix comparison as a clearly named hypothesis rather than smuggling it
through the Lipschitz bridge.

Tracking issue: <https://github.com/phasetr/ising-model/issues/3378>
(parent <https://github.com/phasetr/ising-model/issues/1645>).

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Lemma 17.5.2, pp.~311--312.
-/

namespace IsingModel
namespace Ambient

/-- **Active pair predicate for the system pseudo-mass**: the distinct pair
`(x, z)` contributes to the system pseudo-mass exactly when the infinite-volume
two-point correlation lies in the active window `Ioo 0 2`, i.e. precisely when
`pseudoMassFromParamsAtPair` is the genuine pseudo-mass rather than the `0`
fallback used for inactive pairs.

Restricting the lower envelope to active pairs prevents the inactive-pair value
`pseudoMassFromParamsAtPair = 0` from collapsing the infimum trivially. -/
def ActivePseudoMassPair
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (x z : Fin d → ℤ) : Prop :=
  x ≠ z ∧
    Ambient.correlationInfinite (IsingModel.latticeGraph d) Λ p {x, z}
      ∈ Set.Ioo (0 : ℝ) 2

/-- **Value set of the system pseudo-mass**: the set of per-pair pseudo-masses
`pseudoMassFromParamsAtPair … x z` ranging over all *active* distinct pairs
`(x, z)`.  The system pseudo-mass is its infimum (when nonempty).

References: Glimm--Jaffe §17.5, p.~311. -/
def globalPseudoMassSet {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) : Set ℝ :=
  {m | ∃ x z : Fin d → ℤ,
    ActivePseudoMassPair Λ p x z ∧
      m = pseudoMassFromParamsAtPair hα hr d Λ p x z}

/-- **System (global) pseudo-mass** `m⁻(σ)` of Glimm--Jaffe §17.5: the lower
envelope (infimum over active distinct pairs) of the per-pair pseudo-masses,
with the convention that it is `0` when no active pair exists.

This is the lattice-mass-independent system pseudo-mass appearing on the
upper-bound side `m(σ) ≤ const · m⁻(σ)` of Lemma 17.5.2.  It is not derived from
`latticeMass`: the relation between the two is exactly the substantive content of
the transfer-matrix comparison.

References: Glimm--Jaffe §17.5, Lemma 17.5.2, pp.~311--312. -/
noncomputable def globalPseudoMass {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) : ℝ :=
  sInf (globalPseudoMassSet hα hr Λ p)

/-- **The system pseudo-mass value set is bounded below by `0`**: every per-pair
pseudo-mass is nonnegative (`pseudoMassFromParamsAtPair_nonneg`), so the infimum
defining the system pseudo-mass is well posed. -/
theorem globalPseudoMassSet_bddBelow {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) :
    BddBelow (globalPseudoMassSet hα hr Λ p) := by
  refine ⟨0, ?_⟩
  rintro m ⟨x, z, _, rfl⟩
  exact pseudoMassFromParamsAtPair_nonneg hα hr d Λ p x z

/-- **The system pseudo-mass is nonnegative**: either it is `0` (no active pair),
or it is the infimum of a set of nonnegative reals. -/
theorem globalPseudoMass_nonneg {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) :
    0 ≤ globalPseudoMass hα hr Λ p := by
  unfold globalPseudoMass
  refine Real.sInf_nonneg ?_
  rintro m ⟨x, z, _, rfl⟩
  exact pseudoMassFromParamsAtPair_nonneg hα hr d Λ p x z

/-- **System pseudo-mass is a lower envelope**: for any active distinct pair
`(x, z)`, the system pseudo-mass `m⁻(σ)` is bounded above by the per-pair
pseudo-mass `pseudoMassFromParamsAtPair … x z`.

This is the global-to-pair comparison `m⁻(σ) ≤ m⁻(x, z, σ)`; the proof is pure
order theory (`csInf_le` against the bounded-below value set).

References: Glimm--Jaffe §17.5, p.~311. -/
theorem globalPseudoMass_le_pseudoMassFromParamsAtPair_of_active
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) {x z : Fin d → ℤ}
    (hxz : ActivePseudoMassPair Λ p x z) :
    globalPseudoMass hα hr Λ p ≤
      pseudoMassFromParamsAtPair hα hr d Λ p x z := by
  have hmem :
      pseudoMassFromParamsAtPair hα hr d Λ p x z ∈
        globalPseudoMassSet hα hr Λ p :=
    ⟨x, z, hxz, rfl⟩
  exact csInf_le (globalPseudoMassSet_bddBelow hα hr Λ p) hmem

/-- **GJ §17.5 Lemma 17.5.2 transfer-matrix all-rate comparison (hypothesis
form)**: every admissible nonnegative exponential-decay rate `a` of the system at
`(⟨J, 0, β⟩)` is bounded by `C` times the system pseudo-mass `m⁻(σ)`.

This is the substantive analytic input on the upper-bound side of
Lemma 17.5.2.  Glimm--Jaffe derive it from the transfer matrix, which gives
exponential decay of all correlations at rate `e^{-m·dist}` with
`dist ≥ |x − y|/a₀`; here it is kept as a named hypothesis so the order-theoretic
reduction to `Lemma_17_5_2_UpperBound` is isolated from that analytic step.

References: Glimm--Jaffe §17.5, Lemma 17.5.2, pp.~311--312. -/
def Lemma_17_5_2_GlobalAllRateComparison {α d : ℕ} (hα : 1 ≤ α) {r : ℝ}
    (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) (C : ENNReal) : Prop :=
  ∀ a : NNReal,
    HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ) (a : ℝ) →
      (a : ENNReal) ≤
        C * ENNReal.ofReal
          (globalPseudoMass hα hr Λ (⟨J, 0, β⟩ : IsingParams ℝ))

/-- **All-rate bound at a pair from the global comparison**: the system-level
all-rate comparison, together with the lower-envelope inequality
`m⁻(σ) ≤ m⁻(x, z, σ)` at an active pair, bounds every admissible decay rate by
`C` times the per-pair pseudo-mass.

This is the order-theoretic transfer from the system pseudo-mass to the concrete
pair `(x, z)` consumed by `lemma_17_5_2_upper_bound_of_all_decay_rates_le`. -/
theorem lemma_17_5_2_all_decay_rates_le_of_global_all_rate_comparison
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) {x z : Fin d → ℤ} {C : ENNReal}
    (hglobal : Lemma_17_5_2_GlobalAllRateComparison hα hr Λ J β C)
    (hxz : ActivePseudoMassPair Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z) :
    ∀ a : NNReal,
      HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ) (a : ℝ) →
        (a : ENNReal) ≤
          C * ENNReal.ofReal
            (pseudoMassFromParamsAtPair hα hr d Λ
              (⟨J, 0, β⟩ : IsingParams ℝ) x z) := by
  intro a ha
  refine (hglobal a ha).trans ?_
  gcongr
  exact globalPseudoMass_le_pseudoMassFromParamsAtPair_of_active hα hr Λ
    (⟨J, 0, β⟩ : IsingParams ℝ) hxz

/-- **GJ §17.5 Lemma 17.5.2 upper bound from the transfer-matrix all-rate
comparison**: the system-level all-rate comparison at an active pair `(x, z)`
closes the named `latticeMass` upper-bound predicate.

This isolates the remaining substantive work to proving
`Lemma_17_5_2_GlobalAllRateComparison` (the transfer-matrix exponential-decay
input); everything downstream is the order-theoretic `sSup` assembly already in
`Predicates`.

References: Glimm--Jaffe §17.5, Lemma 17.5.2, pp.~311--312. -/
theorem lemma_17_5_2_upper_bound_of_global_all_rate_comparison
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) {x z : Fin d → ℤ} {C : ENNReal}
    (hglobal : Lemma_17_5_2_GlobalAllRateComparison hα hr Λ J β C)
    (hxz : ActivePseudoMassPair Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z) :
    Lemma_17_5_2_UpperBound hα hr Λ J β x z C :=
  lemma_17_5_2_upper_bound_of_all_decay_rates_le hα hr Λ J β x z C
    (lemma_17_5_2_all_decay_rates_le_of_global_all_rate_comparison hα hr Λ J β
      hglobal hxz)

end Ambient
end IsingModel
