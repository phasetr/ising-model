import IsingModel.TransferMatrix.MarkedTrace

/-!
# Marked closed-walk trace identity (GJ §17.1)

The marked closed-walk trace identity
`Tr(D·Mᵃ·D·Mᵇ) = ∑_{τ : Fin (a+b) → ι} d(τ 0)·d(τ a)·closedWalkWeight M τ`
realises the Gibbs two-point function `⟨σ₀σₙ⟩ = Tr(S·Tⁿ·S·T^{N-n})/Tr(Tᴺ)` as a sum
over closed spin walks with diagonal marks at the two insertion sites.

The key step, avoiding all cyclic `Fin`-arithmetic, is the identity
`closedWalkWeight M τ = pathWeight M (Fin.snoc τ (τ 0))`: appending the first vertex
turns the cyclic closed walk into an open path returning to its start, whose
open-path weight is the cyclic weight.

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §17.1.
-/

namespace IsingModel

namespace TransferMatrix

open scoped BigOperators
open Matrix

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommSemiring R]

omit [Fintype ι] [DecidableEq ι] in
/-- **Cyclic closed-walk weight as an open-path weight**:
`closedWalkWeight M τ = pathWeight M (Fin.snoc τ (τ 0))`.  Appending the first
vertex `τ 0` at the end turns the closed walk into an open path returning to its
start, whose open-path weight coincides with the cyclic weight.  This converts the
cyclic `Fin`-`+1` product of `closedWalkWeight` into the boundary-free open-path
product, the technical key to the marked closed-walk trace identity. -/
theorem closedWalkWeight_eq_pathWeight_snoc_zero (M : Matrix ι ι R) {m : ℕ}
    (τ : Fin (m + 1) → ι) :
    closedWalkWeight M τ = pathWeight M (Fin.snoc τ (τ 0)) := by
  have hz : (0 : Fin (m + 1 + 1)) = (0 : Fin (m + 1)).castSucc := by ext; simp
  have e0 : (Fin.snoc τ (τ 0) : Fin (m + 1 + 1) → ι) 0 = τ 0 := by
    rw [hz, Fin.snoc_castSucc]
  have eL : (Fin.snoc τ (τ 0) : Fin (m + 1 + 1) → ι) (Fin.last (m + 1)) = τ 0 := by
    simp only [Fin.snoc_last]
  rw [pathWeight_eq_closedWalkWeight_init M (Fin.snoc τ (τ 0)) (e0.trans eL.symm),
    Fin.init_snoc]

/-- The **marked closed-walk weight**: a closed walk `τ : Fin (a+b) → ι` weighted by
its cyclic edge product `closedWalkWeight M τ` together with the two diagonal marks
`d(τ 0)` and `d(τ a)` at the insertion sites `0` and `a`.  Summing this over all
closed walks gives `Tr(D·Mᵃ·D·Mᵇ)` (the marked closed-walk trace identity, the next
step). -/
def markedClosedWalkWeight (M : Matrix ι ι R) (d : ι → R) {a b : ℕ} (hb : 0 < b)
    [NeZero (a + b)] (τ : Fin (a + b) → ι) : R :=
  d (τ 0) * d (τ ⟨a, Nat.lt_add_of_pos_right hb⟩) * closedWalkWeight M τ

omit [Fintype ι] [DecidableEq ι] in
/-- The marked closed-walk weight in open-path form: the cyclic `closedWalkWeight`
is the open-path weight of the returning walk `Fin.snoc τ (τ 0)`
(via `closedWalkWeight_eq_pathWeight_snoc_zero`). -/
theorem markedClosedWalkWeight_eq (M : Matrix ι ι R) (d : ι → R) {a m : ℕ}
    (hb : 0 < m + 1) (τ : Fin (a + (m + 1)) → ι) :
    markedClosedWalkWeight M d (a := a) (b := m + 1) hb τ
      = d (τ 0) * d (τ ⟨a, Nat.lt_add_of_pos_right hb⟩)
          * pathWeight M (Fin.snoc τ (τ 0)) := by
  rw [markedClosedWalkWeight, closedWalkWeight_eq_pathWeight_snoc_zero]

end TransferMatrix

end IsingModel
