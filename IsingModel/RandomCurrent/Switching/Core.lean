import IsingModel.RandomCurrent.BoundedExpansion
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Aizenman switching lemma infrastructure

Sub-current operations, pair-Finset parameterizations, joint factors,
source-set algebra, and connectivity results leading to the
Aizenman switching lemma (FV Lemma 3.55, p. 144 / Aizenman 1982 Lemma 3.2,
p. 7, eq. (3.5)).

## References

* Glimm–Jaffe, *Quantum Physics*, §5.1; Friedli–Velenik §3.10.6, pp. 143–145.
* Aizenman, M. (1982). Geometric analysis of φ⁴ fields.
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
/-- **Pointwise order on currents**: `n ≤ m` iff `n e ≤ m e` for every edge `e`.
The Pi LE on `Current G Λ` unfolds definitionally to the pointwise order.
Used in the Aizenman switching lemma (Aizenman 1982 Lemma 4.1 / FV §3.10.6). -/
theorem Current.le_def (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n m : Current G Λ) :
    n ≤ m ↔ ∀ e, n e ≤ m e := Iff.rfl

omit [DecidableEq V] in
/-- **Zero is the least current**: `(0 : Current G Λ) ≤ n` for any
current `n`. Each component `0 ≤ n e` in `ℕ`. -/
theorem Current.zero_le (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n : Current G Λ) :
    (0 : Current G Λ) ≤ n := fun _ => Nat.zero_le _

omit [DecidableEq V] in
/-- **Left summand is below the sum**: `n ≤ n + m`, since
`n e ≤ n e + m e` for every edge `e`. -/
theorem Current.le_self_add_right (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n m : Current G Λ) :
    n ≤ n + m := fun _ => Nat.le_add_right _ _

omit [DecidableEq V] in
/-- **Right summand is below the sum**: `n ≤ m + n`, since
`n e ≤ m e + n e` for every edge `e`. -/
theorem Current.le_self_add_left (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n m : Current G Λ) :
    n ≤ m + n := fun _ => Nat.le_add_left _ _

/-- **Finset of currents bounded by `n`**: the `Finset` of currents
`m` with `m ≤ n` pointwise, enumerated via
`Fintype.piFinset (fun e => Finset.range (n e + 1))`. This is the
parameterizing set for the Aizenman switching pair-bijection
`{(n₁, n₂) : n₁ + n₂ = n} ↔ {m : m ≤ n}` (Aizenman 1982 Lemma 4.1 /
FV §3.10.6). -/
def Current.subFinset (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n : Current G Λ) :
    Finset (Current G Λ) :=
  Fintype.piFinset (fun e => Finset.range (n e + 1))

set_option linter.unusedDecidableInType false in
/-- **Membership in `subFinset`**: `m ∈ subFinset n ↔ m ≤ n`,
via `Fintype.mem_piFinset` + `Finset.mem_range` + `Nat.lt_succ_iff`. -/
@[simp]
theorem Current.mem_subFinset_iff (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (n m : Current G Λ) :
    m ∈ Current.subFinset G Λ n ↔ m ≤ n := by
  unfold Current.subFinset
  rw [Fintype.mem_piFinset]
  simp only [Finset.mem_range, Nat.lt_succ_iff]
  rfl

set_option linter.unusedDecidableInType false in
/-- **Cardinality of `subFinset`**:
`#(subFinset n) = ∏_e (n e + 1)`. The number of currents `m ≤ n` is
the product of per-edge multiplicities `n e + 1`, by
`Fintype.card_piFinset` + `Finset.card_range`. The combinatorial
count behind the joint factor `∏_e Nat.choose (n e) (m e)` in
`Current.weight_mul_weight_eq_weight_add_mul_jointFactor`
(PR #845). -/
theorem Current.subFinset_card_eq_prod (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n : Current G Λ) :
    (Current.subFinset G Λ n).card
      = ∏ e : (inducedGraph G Λ).edgeSet, (n e + 1) := by
  unfold Current.subFinset
  rw [Fintype.card_piFinset]
  simp [Finset.card_range]

/-- **Pointwise truncated subtraction** of currents: `(n - m) e := n e - m e`
in `ℕ` (which is `Nat.sub`, cut off at `0`). The truncation primitive
needed for the switching pair-bijection (Aizenman 1982 Lemma 4.1 /
FV §3.10.6), parameterized by `m ↦ (m, n - m)` for `m ≤ n`. -/
instance Current.instSub (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] : Sub (Current G Λ) :=
  ⟨fun n m => fun e => n e - m e⟩

omit [DecidableEq V] in
/-- **Pointwise sub**: `(n - m) e = n e - m e` (by definition of
`Current.instSub`, which uses `Nat.sub`). -/
@[simp]
theorem Current.sub_apply (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (n m : Current G Λ) (e : (inducedGraph G Λ).edgeSet) :
    (n - m) e = n e - m e := rfl

omit [DecidableEq V] in
/-- **Truncation cancels under `m ≤ n`**: `(n - m) + m = n`.
Pointwise via `Nat.sub_add_cancel`. The naming `sub_add_cancel`
follows mathlib's `Nat.sub_add_cancel` / `tsub_add_cancel_of_le`. -/
theorem Current.sub_add_cancel_of_le (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {n m : Current G Λ} (h : m ≤ n) :
    (n - m) + m = n := by
  ext e
  simp [Nat.sub_add_cancel (h e)]

omit [DecidableEq V] in
/-- **Truncation cancels (commuted form) under `m ≤ n`**:
`m + (n - m) = n`. By commutativity + `sub_add_cancel_of_le`. -/
theorem Current.add_sub_cancel_of_le (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {n m : Current G Λ} (h : m ≤ n) :
    m + (n - m) = n := by
  rw [add_comm]
  exact Current.sub_add_cancel_of_le G Λ h

omit [DecidableEq V] in
/-- **Truncated sub is bounded above by the minuend**:
`n - m ≤ n` for any currents `n, m`. Pointwise via `Nat.sub_le`. -/
theorem Current.sub_le_self (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (n m : Current G Λ) :
    n - m ≤ n := fun _ => Nat.sub_le _ _

end Ambient
end IsingModel
