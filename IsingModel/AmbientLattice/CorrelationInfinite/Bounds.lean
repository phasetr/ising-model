import IsingModel.AmbientLattice.CorrelationInfinite.Basic

/-!
# Infinite-volume correlation bounds

Pointwise, absolute-value, and interval bounds for `correlationInfinite`.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Upper bound**: `correlationInfinite ≤ 1`. Pointwise bound from
`correlationAlongExhaustion_le_one` + `ciSup_le`. -/
theorem correlationInfinite_le_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (A : Finset V) :
    correlationInfinite G Λ p A ≤ 1 := by
  refine ciSup_le ?_
  intro n
  exact correlationAlongExhaustion_le_one G Λ p A n

/-- **Pointwise `|correlationInfinite| ≤ 1`** (unconditional):
the infinite-volume correlation is bounded in absolute value by `1`
regardless of parameters. Upper side is `correlationInfinite_le_one`;
lower side uses `le_ciSup` with the stage-`0` pointwise bound
`correlationAlongExhaustion ≥ -1` (from `abs_correlationAlongExhaustion_le_one`). -/
theorem abs_correlationInfinite_le_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (A : Finset V) :
    |correlationInfinite G Λ p A| ≤ 1 := by
  refine abs_le.mpr ⟨?_, correlationInfinite_le_one G Λ p A⟩
  have h0 : -1 ≤ correlationAlongExhaustion G Λ p A 0 :=
    (abs_le.mp (abs_correlationAlongExhaustion_le_one G Λ p A 0)).1
  exact h0.trans (le_ciSup (correlationAlongExhaustion_bddAbove G Λ p A) 0)

/-- **Uniform stage bound ⟹ infinite-volume bound.**  If every exhaustion stage
satisfies `|correlationAlongExhaustion G Λ p A N| ≤ C`, then the infinite-volume
correlation satisfies `|correlationInfinite G Λ p A| ≤ C`.  The supremum is `≤ C` by
`ciSup_le`, and `≥ -C` from the stage-`0` lower bound; this generalises
`abs_correlationInfinite_le_one` (the case `C = 1`) and is the bridge from any uniform
finite-volume decay bound to the infinite-volume correlation. -/
theorem abs_correlationInfinite_le_of_forall_abs_correlationAlongExhaustion_le
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (A : Finset V) {C : ℝ}
    (h : ∀ N, |correlationAlongExhaustion G Λ p A N| ≤ C) :
    |correlationInfinite G Λ p A| ≤ C := by
  refine abs_le.mpr ⟨?_, ciSup_le fun N => (le_abs_self _).trans (h N)⟩
  exact (abs_le.mp (h 0)).1.trans (le_ciSup (correlationAlongExhaustion_bddAbove G Λ p A) 0)

/-- **`-1 ≤ correlationInfinite`** (unconditional).
Lower side of `abs_correlationInfinite_le_one`. -/
theorem neg_one_le_correlationInfinite
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (A : Finset V) :
    -1 ≤ correlationInfinite G Λ p A :=
  (abs_le.mp (abs_correlationInfinite_le_one G Λ p A)).1

/-- **`correlationInfinite² ≤ 1`** (unconditional). -/
theorem correlationInfinite_sq_le_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (A : Finset V) :
    correlationInfinite G Λ p A ^ 2 ≤ 1 := by
  have h := abs_correlationInfinite_le_one G Λ p A
  have : |correlationInfinite G Λ p A| ^ 2 ≤ 1 ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) h 2
  simpa [sq_abs] using this

/-- **`correlationInfinite < 2`** (unconditional): direct from
`correlationInfinite ≤ 1 < 2`. -/
theorem correlationInfinite_lt_two
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (A : Finset V) :
    correlationInfinite G Λ p A < 2 := by
  have h := correlationInfinite_le_one G Λ p A
  linarith

/-- **`correlationInfinite ∈ Icc (-1) 1`** (unconditional): combines
`abs_correlationInfinite_le_one` lower and upper sides. -/
theorem correlationInfinite_mem_Icc_neg_one_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (A : Finset V) :
    correlationInfinite G Λ p A ∈ Set.Icc (-1 : ℝ) 1 :=
  ⟨neg_one_le_correlationInfinite G Λ p A,
   correlationInfinite_le_one G Λ p A⟩

/-- **Nonnegativity** (ferromagnetic): `correlationInfinite ≥ 0`.
Uses `Λ.exhaust`: pick `N` with `A ⊆ Λ.volume N`; then
`correlationAlongExhaustion G Λ p A N ≥ 0` by GKS-I, and this is
a lower bound for the supremum (so the supremum is also `≥ 0`). -/
theorem correlationInfinite_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset V) :
    0 ≤ correlationInfinite G Λ p A := by
  obtain ⟨N, hN⟩ := Λ.exhaust A
  have hA : A ⊆ Λ.volume N := hN N le_rfl
  have hval : 0 ≤ correlationAlongExhaustion G Λ p A N := by
    rw [correlationAlongExhaustion_of_subset G Λ p hA]
    exact correlationΛ_nonneg G (Λ.volume N) p hf _
  exact hval.trans (le_ciSup (correlationAlongExhaustion_bddAbove G Λ p A) N)

/-- **`correlationInfinite ∈ Icc 0 1`** under ferromagnetic: combines
`correlationInfinite_nonneg` and `correlationInfinite_le_one`. -/
theorem correlationInfinite_mem_Icc_zero_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (A : Finset V) :
    correlationInfinite G Λ p A ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨correlationInfinite_nonneg G Λ p hf A,
   correlationInfinite_le_one G Λ p A⟩

/-- **`correlationInfinite ∈ Icc 0 2`** under ferromagnetic: combines
`correlationInfinite_nonneg` and `correlationInfinite_le_one ≤ 2`. -/
theorem correlationInfinite_mem_Icc_zero_two
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (A : Finset V) :
    correlationInfinite G Λ p A ∈ Set.Icc (0 : ℝ) 2 := by
  have h := correlationInfinite_le_one G Λ p A
  refine ⟨correlationInfinite_nonneg G Λ p hf A, ?_⟩
  linarith

/-- **`correlationInfinite ∈ Ioc 0 1`** when positive under ferromagnetic. -/
theorem correlationInfinite_mem_Ioc_zero_one_of_pos
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (_hf : Ferromagnetic p) (A : Finset V)
    (hpos : 0 < correlationInfinite G Λ p A) :
    correlationInfinite G Λ p A ∈ Set.Ioc (0 : ℝ) 1 :=
  ⟨hpos, correlationInfinite_le_one G Λ p A⟩

/-- **`correlationInfinite ∈ Ioo 0 2`** when positive under ferromagnetic. -/
theorem correlationInfinite_mem_Ioo_zero_two_of_pos
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (_hf : Ferromagnetic p) (A : Finset V)
    (hpos : 0 < correlationInfinite G Λ p A) :
    correlationInfinite G Λ p A ∈ Set.Ioo (0 : ℝ) 2 :=
  ⟨hpos, correlationInfinite_lt_two G Λ p A⟩

/-- **`correlationInfinite ∈ Ico 0 2`** under ferromagnetic. -/
theorem correlationInfinite_mem_Ico_zero_two
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (A : Finset V) :
    correlationInfinite G Λ p A ∈ Set.Ico (0 : ℝ) 2 :=
  ⟨correlationInfinite_nonneg G Λ p hf A,
   correlationInfinite_lt_two G Λ p A⟩

/-- **`correlationInfinite ∈ Iio 2`** (unconditional). -/
theorem correlationInfinite_mem_Iio_two
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (A : Finset V) :
    correlationInfinite G Λ p A ∈ Set.Iio (2 : ℝ) :=
  correlationInfinite_lt_two G Λ p A

/-- **`correlationInfinite ∈ Iic 1`** (unconditional). -/
theorem correlationInfinite_mem_Iic_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (A : Finset V) :
    correlationInfinite G Λ p A ∈ Set.Iic (1 : ℝ) :=
  correlationInfinite_le_one G Λ p A

/-- **`correlationInfinite ∈ Ici 0`** under ferromagnetic. -/
theorem correlationInfinite_mem_Ici_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (A : Finset V) :
    correlationInfinite G Λ p A ∈ Set.Ici (0 : ℝ) :=
  correlationInfinite_nonneg G Λ p hf A

/-- **`correlationInfinite ∉ Iio 0`** under ferromagnetic. -/
theorem correlationInfinite_not_mem_Iio_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (A : Finset V) :
    correlationInfinite G Λ p A ∉ Set.Iio (0 : ℝ) :=
  not_lt.mpr (correlationInfinite_nonneg G Λ p hf A)

/-- **`correlationInfinite ∉ Ioi 1`** (unconditional): direct from
`correlationInfinite_le_one`. -/
theorem correlationInfinite_not_mem_Ioi_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (A : Finset V) :
    correlationInfinite G Λ p A ∉ Set.Ioi (1 : ℝ) :=
  not_lt.mpr (correlationInfinite_le_one G Λ p A)

/-- **`0 < correlationInfinite ↔ correlationInfinite ≠ 0`** under
ferromagnetic: standard nonneg → pos iff ne_zero pattern. -/
theorem correlationInfinite_pos_iff_ne_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (A : Finset V) :
    0 < correlationInfinite G Λ p A ↔ correlationInfinite G Λ p A ≠ 0 :=
  (correlationInfinite_nonneg G Λ p hf A).lt_iff_ne.trans
    ⟨fun h => h.symm, fun h => h.symm⟩

/-- **`correlationInfinite ≤ 0 ↔ correlationInfinite = 0`** under
ferromagnetic: combines nonneg with antisymmetry. -/
theorem correlationInfinite_le_zero_iff_eq_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (A : Finset V) :
    correlationInfinite G Λ p A ≤ 0 ↔ correlationInfinite G Λ p A = 0 := by
  refine ⟨?_, fun h => le_of_eq h⟩
  intro hle
  exact le_antisymm hle (correlationInfinite_nonneg G Λ p hf A)

/-- **`¬(correlationInfinite < 0)`** under ferromagnetic: direct
from `correlationInfinite_nonneg`. -/
theorem correlationInfinite_not_lt_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (A : Finset V) :
    ¬ (correlationInfinite G Λ p A < 0) :=
  not_lt.mpr (correlationInfinite_nonneg G Λ p hf A)

end Ambient
end IsingModel
