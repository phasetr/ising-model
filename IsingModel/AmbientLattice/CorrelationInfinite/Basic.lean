import IsingModel.AmbientLattice.Defs
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.Monotonicity.Volume

/-!
# Infinite-volume correlation basics

Convergence along an exhaustion and the basic `correlationInfinite` definition.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-! ## Convergence along an exhaustion

Apply `correlationΛ_monotone_volume` to show that the correlations
along an exhaustion converge. We use a shifted sequence
`n ↦ correlationΛ G (Λ.volume (n + N)) p (liftFinset A ...)` where
`N` is chosen so that `A ⊆ Λ.volume N` (from `Exhaustion.exhaust`).
Past `N`, `correlationAlongExhaustion` equals this shifted sequence. -/

/-- The shifted correlation sequence along an exhaustion: given
`N : ℕ` with `A ⊆ Λ.volume n` for `n ≥ N`, the sequence
`n ↦ correlationΛ G (Λ.volume (n + N)) p (liftFinset A ...)` is
monotone and bounded. -/
theorem correlationΛ_shifted_monotone_bounded
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    {A : Finset V} {N : ℕ}
    (hN : ∀ n ≥ N, A ⊆ Λ.volume n) :
    Monotone (fun n : ℕ =>
      correlationΛ G (Λ.volume (n + N)) p
        (liftFinset A (hN (n + N) (Nat.le_add_left N n))))
    ∧ ∀ n : ℕ,
      correlationΛ G (Λ.volume (n + N)) p
        (liftFinset A (hN (n + N) (Nat.le_add_left N n))) ≤ 1 := by
  refine ⟨?_, ?_⟩
  · intro n m hnm
    have hΛmono : Λ.volume (n + N) ⊆ Λ.volume (m + N) :=
      Λ.mono (Nat.add_le_add_right hnm N)
    exact correlationΛ_monotone_volume G hΛmono p hf
      (hN (n + N) (Nat.le_add_left N n))
  · intro n
    exact correlationΛ_le_one _ _ _ _

/-- **Tendsto convergence of the shifted correlation sequence**:
the shifted sequence (monotone and bounded by PR #88) converges
to its supremum by `tendsto_atTop_ciSup`. -/
theorem correlationΛ_shifted_tendsto
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    {A : Finset V} {N : ℕ}
    (hN : ∀ n ≥ N, A ⊆ Λ.volume n) :
    ∃ L : ℝ, Filter.Tendsto
      (fun m : ℕ => correlationΛ G (Λ.volume (m + N)) p
        (liftFinset A (hN (m + N) (Nat.le_add_left N m))))
      Filter.atTop (nhds L) := by
  obtain ⟨hmono, hbdd⟩ := correlationΛ_shifted_monotone_bounded G Λ p hf hN
  exact ⟨_, tendsto_atTop_ciSup hmono ⟨1, fun _ ⟨m, hm⟩ => hm ▸ hbdd m⟩⟩

/-- **Global monotonicity of `correlationAlongExhaustion`**:
because (1) for `n` where `A ⊆ Λ.volume n` fails, it equals 0;
(2) when it holds, `correlationΛ ≥ 0` by GKS-I; and (3) when both
endpoints satisfy the inclusion, `correlationΛ_monotone_volume`
(PR #87) applies. -/
theorem correlationAlongExhaustion_monotone
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset V) :
    Monotone (correlationAlongExhaustion G Λ p A) := by
  intro n m hnm
  by_cases hAn : A ⊆ Λ.volume n
  · by_cases hAm : A ⊆ Λ.volume m
    · rw [correlationAlongExhaustion_of_subset G Λ p hAn,
          correlationAlongExhaustion_of_subset G Λ p hAm]
      exact correlationΛ_monotone_volume G (Λ.mono hnm) p hf hAn
    · exact absurd (hAn.trans (Λ.mono hnm)) hAm
  · rw [correlationAlongExhaustion_of_not_subset G Λ p hAn]
    by_cases hAm : A ⊆ Λ.volume m
    · rw [correlationAlongExhaustion_of_subset G Λ p hAm]
      exact correlationΛ_nonneg G (Λ.volume m) p hf _
    · rw [correlationAlongExhaustion_of_not_subset G Λ p hAm]

/-- **Global upper bound of `correlationAlongExhaustion` by 1**:
either the value is 0 (when `A ⊄ Λ.volume n`) or it is bounded
by `correlationΛ_le_one`. -/
theorem correlationAlongExhaustion_le_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (A : Finset V) (n : ℕ) :
    correlationAlongExhaustion G Λ p A n ≤ 1 := by
  by_cases hAn : A ⊆ Λ.volume n
  · rw [correlationAlongExhaustion_of_subset G Λ p hAn]
    exact correlationΛ_le_one _ _ _ _
  · rw [correlationAlongExhaustion_of_not_subset G Λ p hAn]
    norm_num

/-- **Range is bounded above by 1**: the range of the sequence
`correlationAlongExhaustion G Λ p A` is bounded above. Witness `1`
via `correlationAlongExhaustion_le_one`. -/
theorem correlationAlongExhaustion_bddAbove
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (A : Finset V) :
    BddAbove (Set.range (correlationAlongExhaustion G Λ p A)) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact correlationAlongExhaustion_le_one G Λ p A n

/-- **Convergence of correlation along an exhaustion (explicit limit)**:
for a ferromagnetic Ising model and any exhaustion `Λₙ ↑ V` of an
ambient type `V`, the sequence `correlationAlongExhaustion` converges
to its supremum as `n → ∞`.

The limit is `⨆ n, correlationAlongExhaustion G Λ p A n`; this
exposes the limit's identity (as a supremum) so it can be related
to the thermodynamic-limit correlation once `Λ.exhaust` is used to
identify `A` with a subset of some `Λ.volume N`.

Note: this theorem itself only uses `Λ.mono` (monotonicity of the
exhaustion); `Λ.exhaust` is not required for convergence alone,
but is needed in downstream physical identifications of `L`. -/
theorem correlationAlongExhaustion_tendsto_ciSup
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset V) :
    Filter.Tendsto (correlationAlongExhaustion G Λ p A)
      Filter.atTop (nhds (⨆ n, correlationAlongExhaustion G Λ p A n)) := by
  exact tendsto_atTop_ciSup
    (correlationAlongExhaustion_monotone G Λ p hf A)
    (correlationAlongExhaustion_bddAbove G Λ p A)

/-- **Convergence of correlation along an exhaustion (existential form)**:
thin wrapper around `correlationAlongExhaustion_tendsto_ciSup`. Use
the `_tendsto_ciSup` form when the identity of `L` as a supremum is
needed (e.g. for physical identification with the thermodynamic limit). -/
theorem correlationAlongExhaustion_convergent
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset V) :
    ∃ L : ℝ, Filter.Tendsto
      (correlationAlongExhaustion G Λ p A)
      Filter.atTop (nhds L) :=
  ⟨_, correlationAlongExhaustion_tendsto_ciSup G Λ p hf A⟩

/-! ## Infinite-volume correlation function

The supremum exposed by `correlationAlongExhaustion_tendsto_ciSup`
is, by GKS-I and `Λ.exhaust`, the thermodynamic-limit correlation
for ferromagnetic Ising models on an ambient `V`.  We package it as
a `noncomputable def` and record its basic properties. -/

/-- **Infinite-volume correlation function**: for a ferromagnetic
Ising model on an ambient type `V` with an exhaustion `Λ` and a
finite `A : Finset V`,
`correlationInfinite G Λ p A := ⨆ n, correlationAlongExhaustion G Λ p A n`.
This is the thermodynamic-limit correlation identified via
`Λ.exhaust` (any finite `A` lies in some `Λ.volume N`). -/
noncomputable def correlationInfinite
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (A : Finset V) : ℝ :=
  ⨆ n, correlationAlongExhaustion G Λ p A n

/-- **`correlationInfinite` as `ciSup`**:
`correlationInfinite G Λ p A = ⨆ n, correlationAlongExhaustion G Λ p A n`
(named restatement of the definition for use in rewrites). -/
theorem correlationInfinite_eq_ciSup
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (A : Finset V) :
    correlationInfinite G Λ p A
      = ⨆ n, correlationAlongExhaustion G Λ p A n := rfl

/-- **Pointwise bound**: `correlationAlongExhaustion G Λ p A n ≤
correlationInfinite G Λ p A` at every `n`. Direct from `le_ciSup` +
`correlationAlongExhaustion_bddAbove`. -/
theorem correlationAlongExhaustion_le_correlationInfinite
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (A : Finset V) (n : ℕ) :
    correlationAlongExhaustion G Λ p A n ≤ correlationInfinite G Λ p A :=
  le_ciSup (correlationAlongExhaustion_bddAbove G Λ p A) n

/-- **Tendsto to infinite-volume correlation** (primary form):
`correlationAlongExhaustion` converges to `correlationInfinite`.
Restatement of `correlationAlongExhaustion_tendsto_ciSup` in terms
of the canonical `correlationInfinite` name. -/
theorem tendsto_correlationAlongExhaustion_correlationInfinite
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset V) :
    Filter.Tendsto (correlationAlongExhaustion G Λ p A)
      Filter.atTop (nhds (correlationInfinite G Λ p A)) :=
  correlationAlongExhaustion_tendsto_ciSup G Λ p hf A

end Ambient
end IsingModel
