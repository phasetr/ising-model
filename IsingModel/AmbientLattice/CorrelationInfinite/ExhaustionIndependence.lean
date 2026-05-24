import IsingModel.AmbientLattice.CorrelationInfinite.Bounds

/-!
# Infinite-volume correlation exhaustion independence

Finite-volume convergence to `correlationInfinite` and independence of the exhaustion.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Tendsto of the lifted `correlationΛ` sequence (explicit form)**:
given an explicit `N` and a hypothesis `hN : ∀ n ≥ N, A ⊆ Λ.volume n`,
the sequence `m ↦ correlationΛ G (Λ.volume (m+N)) p (liftFinset A …)`
converges to `correlationInfinite G Λ p A`.

The shifted sequence coincides with `correlationAlongExhaustion` on
indices `≥ N` (both branches of the dite agree since `A ⊆ Λ.volume (m+N)`),
and the base sequence's limit is `correlationInfinite` by
`tendsto_correlationAlongExhaustion_correlationInfinite`. -/
theorem tendsto_correlationΛ_correlationInfinite_of_subset
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    {A : Finset V} {N : ℕ}
    (hN : ∀ n ≥ N, A ⊆ Λ.volume n) :
    Filter.Tendsto
      (fun m : ℕ => correlationΛ G (Λ.volume (m + N)) p
        (liftFinset A (hN (m + N) (Nat.le_add_left N m))))
      Filter.atTop (nhds (correlationInfinite G Λ p A)) := by
  have hbase := tendsto_correlationAlongExhaustion_correlationInfinite G Λ p hf A
  have hshift :
      Filter.Tendsto (fun m : ℕ => correlationAlongExhaustion G Λ p A (m + N))
        Filter.atTop (nhds (correlationInfinite G Λ p A)) :=
    hbase.comp (Filter.tendsto_add_atTop_nat N)
  refine hshift.congr ?_
  intro m
  have hA : A ⊆ Λ.volume (m + N) := hN (m + N) (Nat.le_add_left N m)
  exact correlationAlongExhaustion_of_subset G Λ p hA

/-- **Tendsto of the lifted `correlationΛ` sequence (corollary)**:
using `Λ.exhaust` to produce an `N` with `A ⊆ Λ.volume n` for `n ≥ N`,
the sequence `m ↦ correlationΛ G (Λ.volume (m+N)) p (liftFinset A …)`
converges to `correlationInfinite G Λ p A`.

This is the physical statement: as the volume grows, the finite-volume
correlation converges to the thermodynamic-limit correlation. -/
theorem tendsto_correlationΛ_correlationInfinite
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset V) :
    ∃ N : ℕ, ∃ hN : ∀ n ≥ N, A ⊆ Λ.volume n,
      Filter.Tendsto
        (fun m : ℕ => correlationΛ G (Λ.volume (m + N)) p
          (liftFinset A (hN (m + N) (Nat.le_add_left N m))))
        Filter.atTop (nhds (correlationInfinite G Λ p A)) := by
  obtain ⟨N, hN⟩ := Λ.exhaust A
  exact ⟨N, hN, tendsto_correlationΛ_correlationInfinite_of_subset G Λ p hf hN⟩

/-! ## Exhaustion-independence of `correlationInfinite`

Although `correlationInfinite` is defined as a supremum tied to a
specific `Λ`, the value does not depend on the choice of exhaustion:
any two exhaustions yield the same thermodynamic-limit correlation. -/

/-- **Key sandwich lemma**: every value of `correlationAlongExhaustion`
along one exhaustion is bounded above by `correlationInfinite` along
another exhaustion of the same ambient type.

Proof sketch: if `A ⊆ Λ'.volume n`, apply `Λ.exhaust` to the finite
set `Λ'.volume n` to get `m` with `Λ'.volume n ⊆ Λ.volume m`; then
`correlationΛ_monotone_volume` sandwiches the two finite-volume
correlations, and `le_ciSup` moves from `Λ.volume m` to the supremum.
Otherwise `correlationAlongExhaustion Λ' n = 0 ≤ correlationInfinite Λ`
via `correlationInfinite_nonneg`. -/
theorem correlationAlongExhaustion_le_correlationInfinite_of_other
    (G : SimpleGraph V) (Λ Λ' : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Fintype (inducedGraph G (Λ'.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset V) (n : ℕ) :
    correlationAlongExhaustion G Λ' p A n ≤ correlationInfinite G Λ p A := by
  by_cases hAn : A ⊆ Λ'.volume n
  · -- A ⊆ Λ'.volume n: use Λ.exhaust on Λ'.volume n
    obtain ⟨m, hm⟩ := Λ.exhaust (Λ'.volume n)
    have hsubset : Λ'.volume n ⊆ Λ.volume m := hm m le_rfl
    have hAm : A ⊆ Λ.volume m := hAn.trans hsubset
    have hmono :
        correlationΛ G (Λ'.volume n) p (liftFinset A hAn) ≤
          correlationΛ G (Λ.volume m) p (liftFinset A hAm) :=
      correlationΛ_monotone_volume G hsubset p hf hAn
    calc correlationAlongExhaustion G Λ' p A n
        = correlationΛ G (Λ'.volume n) p (liftFinset A hAn) :=
          correlationAlongExhaustion_of_subset G Λ' p hAn
      _ ≤ correlationΛ G (Λ.volume m) p (liftFinset A hAm) := hmono
      _ = correlationAlongExhaustion G Λ p A m :=
          (correlationAlongExhaustion_of_subset G Λ p hAm).symm
      _ ≤ correlationInfinite G Λ p A :=
          le_ciSup (correlationAlongExhaustion_bddAbove G Λ p A) m
  · -- A ⊄ Λ'.volume n: LHS = 0 ≤ correlationInfinite (nonneg)
    rw [correlationAlongExhaustion_of_not_subset G Λ' p hAn]
    exact correlationInfinite_nonneg G Λ p hf A

/-- **Exhaustion-independence** of `correlationInfinite`: for any two
exhaustions `Λ, Λ'` of the same ambient type `V`, the thermodynamic-limit
correlation is the same:
`correlationInfinite G Λ p A = correlationInfinite G Λ' p A`.

Proof: both `≤` directions by `ciSup_le` applied to the sandwich
lemma `correlationAlongExhaustion_le_correlationInfinite_of_other`. -/
theorem correlationInfinite_indep_exhaustion
    (G : SimpleGraph V) (Λ Λ' : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Fintype (inducedGraph G (Λ'.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset V) :
    correlationInfinite G Λ p A = correlationInfinite G Λ' p A := by
  refine le_antisymm ?_ ?_
  · refine ciSup_le ?_
    intro n
    exact correlationAlongExhaustion_le_correlationInfinite_of_other
      G Λ' Λ p hf A n
  · refine ciSup_le ?_
    intro n
    exact correlationAlongExhaustion_le_correlationInfinite_of_other
      G Λ Λ' p hf A n

end Ambient
end IsingModel
