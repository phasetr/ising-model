import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.GlobalPseudoMass

/-!
# GJ §17.5 Lemma 17.5.2 Part B — all-rate comparison from per-active-pair bounds

This module is part of the split
`IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2` development.  It
reduces the transfer-matrix all-rate comparison
`Lemma_17_5_2_GlobalAllRateComparison` (the named analytic input on the
upper-bound side of GJ Lemma 17.5.2) to a *per-active-pair* rate/pseudo-mass
lower bound.

The system pseudo-mass `globalPseudoMass` is an infimum over an infinite set of
active pairs, so a single pair only gives `globalPseudoMass ≤ m⁻(x,z)`
(`globalPseudoMass_le_pseudoMassFromParamsAtPair_of_active`); the reverse
direction `a/K ≤ globalPseudoMass` needs the per-pair estimate `a/K ≤ m⁻(x,z)`
to hold *uniformly over all active pairs*, after which `le_csInf` closes it.  The
infimum is genuine only when at least one active pair exists, so the reduction
takes an explicit active-pair witness (equivalently, nonemptiness of the value
set): without it the empty-active degenerate slice (e.g. `β = 0`, where every
decay rate is admissible but the system pseudo-mass is `0`) would make the
statement false.

Tracking issue: <https://github.com/phasetr/ising-model/issues/3378>
(parent <https://github.com/phasetr/ising-model/issues/1645>).

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Lemma 17.5.2, pp.~311--312.
-/

namespace IsingModel
namespace Ambient

/-- **The system pseudo-mass value set is nonempty once an active pair exists**:
an active distinct pair `(x, z)` contributes its per-pair pseudo-mass to
`globalPseudoMassSet`. -/
theorem globalPseudoMassSet_nonempty_of_active
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) {x z : Fin d → ℤ}
    (hxz : ActivePseudoMassPair Λ p x z) :
    (globalPseudoMassSet hα hr Λ p).Nonempty :=
  ⟨pseudoMassFromParamsAtPair hα hr d Λ p x z, x, z, hxz, rfl⟩

/-- **Lower bound for the system pseudo-mass from a uniform per-active-pair
bound**: if a real `c` is `≤ m⁻(x, z)` for *every* active pair `(x, z)` and at
least one active pair exists, then `c ≤ globalPseudoMass`.

This is the upper-envelope direction complementary to the lower-envelope
inequality `globalPseudoMass_le_pseudoMassFromParamsAtPair_of_active`; it is the
order-theoretic content `c ≤ ⨅_{active} m⁻(x,z)` proved by `le_csInf`. -/
theorem le_globalPseudoMass_of_forall_active_le_pseudoMassFromParamsAtPair
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) {c : ℝ}
    (hne : (globalPseudoMassSet hα hr Λ p).Nonempty)
    (hle : ∀ x z : Fin d → ℤ, ActivePseudoMassPair Λ p x z →
      c ≤ pseudoMassFromParamsAtPair hα hr d Λ p x z) :
    c ≤ globalPseudoMass hα hr Λ p := by
  unfold globalPseudoMass
  refine le_csInf hne ?_
  rintro m ⟨x, z, hxz, rfl⟩
  exact hle x z hxz

/-- **Rate-shaped system pseudo-mass lower bound**: the `c = (a : ℝ)/K`
specialization of
`le_globalPseudoMass_of_forall_active_le_pseudoMassFromParamsAtPair`, in the form
consumed by the all-rate reduction. -/
theorem globalPseudoMass_ge_rate_div_of_forall_active_rate_div_le
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (a : NNReal) {K : ℝ}
    (hne : (globalPseudoMassSet hα hr Λ p).Nonempty)
    (hle : ∀ x z : Fin d → ℤ, ActivePseudoMassPair Λ p x z →
      (a : ℝ) / K ≤ pseudoMassFromParamsAtPair hα hr d Λ p x z) :
    (a : ℝ) / K ≤ globalPseudoMass hα hr Λ p :=
  le_globalPseudoMass_of_forall_active_le_pseudoMassFromParamsAtPair hα hr Λ p
    hne hle

/-- **`ENNReal` rate transfer from a real division bound**: from `0 < K` and
`(a : ℝ)/K ≤ m`, the coerced rate is bounded by `ofReal K * ofReal m` in
`ENNReal`.  (No `0 ≤ m` hypothesis is needed: `(a : ℝ)/K ≤ m` with `a ≥ 0` and
`K > 0` already forces `0 ≤ m`.) -/
theorem ennreal_coe_nnreal_le_ofReal_mul_of_div_le
    {a : NNReal} {K m : ℝ} (hK : 0 < K)
    (hdiv : (a : ℝ) / K ≤ m) :
    (a : ENNReal) ≤ ENNReal.ofReal K * ENNReal.ofReal m := by
  have haK : (a : ℝ) ≤ K * m := by
    have h := mul_le_mul_of_nonneg_right hdiv hK.le
    rw [div_mul_cancel₀ (a : ℝ) hK.ne'] at h
    rwa [mul_comm] at h
  calc
    (a : ENNReal) = ENNReal.ofReal (a : ℝ) := ENNReal.ofReal_coe_nnreal.symm
    _ ≤ ENNReal.ofReal (K * m) := ENNReal.ofReal_le_ofReal haK
    _ = ENNReal.ofReal K * ENNReal.ofReal m := ENNReal.ofReal_mul hK.le

/-- **GJ §17.5 Lemma 17.5.2 per-active-pair rate / pseudo-mass lower bound
(hypothesis form)**: with a positive scale `K`, every admissible nonnegative
exponential-decay rate `a` at `(⟨J, 0, β⟩)`, divided by `K`, is bounded by the
per-pair pseudo-mass at *every* active pair.

This is the per-pair analytic content from which the system-level transfer-matrix
all-rate comparison follows.  It is kept as a named hypothesis: proving it for the
lattice model is the transfer-matrix exponential-decay step of Lemma 17.5.2.

References: Glimm--Jaffe §17.5, Lemma 17.5.2, pp.~311--312. -/
def Lemma_17_5_2_PerActivePairRatePseudoMassLowerBound {α d : ℕ} (hα : 1 ≤ α)
    {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β K : ℝ) : Prop :=
  0 < K ∧
    ∀ a : NNReal,
      HasExponentialDecay d Λ (⟨J, 0, β⟩ : IsingParams ℝ) (a : ℝ) →
        ∀ x z : Fin d → ℤ,
          ActivePseudoMassPair Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z →
            (a : ℝ) / K ≤
              pseudoMassFromParamsAtPair hα hr d Λ
                (⟨J, 0, β⟩ : IsingParams ℝ) x z

/-- **GJ §17.5 Lemma 17.5.2 transfer-matrix all-rate comparison from a
per-active-pair rate lower bound**: given an active-pair witness (so the system
pseudo-mass is a genuine infimum over a nonempty set) and the per-active-pair
rate/pseudo-mass lower bound, the system-level `Lemma_17_5_2_GlobalAllRateComparison`
holds at coefficient `ofReal K`.

The proof passes each admissible decay rate through the uniform per-pair bound
into the infimum (`le_csInf`), then transfers the resulting real division bound
to `ENNReal`. -/
theorem lemma_17_5_2_global_all_rate_comparison_of_per_active_pair_rate_pseudoMass_lower_bound
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) {K : ℝ} {x₀ z₀ : Fin d → ℤ}
    (hwit : ActivePseudoMassPair Λ (⟨J, 0, β⟩ : IsingParams ℝ) x₀ z₀)
    (hpp : Lemma_17_5_2_PerActivePairRatePseudoMassLowerBound hα hr Λ J β K) :
    Lemma_17_5_2_GlobalAllRateComparison hα hr Λ J β (ENNReal.ofReal K) := by
  obtain ⟨hK, hbound⟩ := hpp
  intro a ha
  have hne :
      (globalPseudoMassSet hα hr Λ (⟨J, 0, β⟩ : IsingParams ℝ)).Nonempty :=
    globalPseudoMassSet_nonempty_of_active hα hr Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) hwit
  have hdiv :
      (a : ℝ) / K ≤ globalPseudoMass hα hr Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
    globalPseudoMass_ge_rate_div_of_forall_active_rate_div_le hα hr Λ
      (⟨J, 0, β⟩ : IsingParams ℝ) a hne (fun x z hxz => hbound a ha x z hxz)
  exact ennreal_coe_nnreal_le_ofReal_mul_of_div_le hK hdiv

/-- **GJ §17.5 Lemma 17.5.2 upper bound from a per-active-pair rate lower bound**:
at an active pair `(x, z)` (which also witnesses nonemptiness of the system
pseudo-mass value set), the per-active-pair rate/pseudo-mass lower bound closes
the named `latticeMass` upper-bound predicate with coefficient `ofReal K`.

This isolates the remaining substantive work to the per-pair rate bound
`Lemma_17_5_2_PerActivePairRatePseudoMassLowerBound` (transfer-matrix step);
everything downstream is order-theoretic. -/
theorem lemma_17_5_2_upper_bound_of_per_active_pair_rate_pseudoMass_lower_bound
    {α d : ℕ} (hα : 1 ≤ α) {r : ℝ} (hr : 0 < r)
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d)
                      (Λ.volume n)).edgeSet]
    (J β : ℝ) {K : ℝ} {x z : Fin d → ℤ}
    (hxz : ActivePseudoMassPair Λ (⟨J, 0, β⟩ : IsingParams ℝ) x z)
    (hpp : Lemma_17_5_2_PerActivePairRatePseudoMassLowerBound hα hr Λ J β K) :
    Lemma_17_5_2_UpperBound hα hr Λ J β x z (ENNReal.ofReal K) :=
  lemma_17_5_2_upper_bound_of_global_all_rate_comparison hα hr Λ J β
    (lemma_17_5_2_global_all_rate_comparison_of_per_active_pair_rate_pseudoMass_lower_bound
      hα hr Λ J β hxz hpp) hxz

end Ambient
end IsingModel
