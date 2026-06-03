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

omit [Fintype ι] [DecidableEq ι] in
/-- **Path weight of a head-to-tail glue**: gluing the open path `σ : Fin (a+1) → ι`
to `ρ : Fin (b+1) → ι` at a shared vertex (`ρ 0 = σ (last a)`) by appending the
interior `Fin.init σ` to `ρ` multiplies their path weights:
`pathWeight M (Fin.append (init σ) ρ) = pathWeight M σ · pathWeight M ρ`.  Proved by
induction on `b`, peeling `ρ` with `Fin.append_snoc` and `pathWeight_snoc`. -/
theorem pathWeight_append (M : Matrix ι ι R) {a : ℕ} (σ : Fin (a + 1) → ι) :
    ∀ {b : ℕ} (ρ : Fin (b + 1) → ι), ρ 0 = σ (Fin.last a) →
      pathWeight M (Fin.append (Fin.init σ) ρ : Fin (a + (b + 1)) → ι)
        = pathWeight M σ * pathWeight M ρ
  | 0, ρ, hρ => by
    rw [Fin.append_right_eq_snoc, hρ, Fin.snoc_init_self]
    simp [pathWeight]
  | b + 1, ρ, hρ => by
    have hir0 : (Fin.init ρ) 0 = σ (Fin.last a) := by
      rw [Fin.init_def]; simpa using hρ
    have key : (Fin.append (Fin.init σ) (Fin.init ρ)) (Fin.last (a + b))
        = (Fin.init ρ) (Fin.last b) := by
      rw [← Fin.natAdd_last, Fin.append_right]
    conv_lhs => rw [← Fin.snoc_init_self ρ]
    rw [Fin.append_snoc, pathWeight_snoc, pathWeight_append M σ (Fin.init ρ) hir0]
    simp only [Nat.add_eq]
    conv_rhs => rw [← Fin.snoc_init_self ρ]
    rw [pathWeight_snoc, key]
    ring

/-- The **marked glue** of two open paths `σ : Fin (a+1) → ι`, `ρ : Fin (b+1) → ι`
into a closed walk `Fin (a+b) → ι`: the interior vertices of `σ` followed by the
interior vertices of `ρ`, `Fin.append (Fin.init σ) (Fin.init ρ)`.  Under the gluing
conditions `ρ 0 = σ (last a)` and `ρ (last b) = σ 0`, its cyclic closed-walk weight
factors as `pathWeight M σ · pathWeight M ρ` (`closedWalkWeight_markedGlue`, the next
step). -/
def markedGlue {a b : ℕ} (σ : Fin (a + 1) → ι) (ρ : Fin (b + 1) → ι) : Fin (a + b) → ι :=
  Fin.append (Fin.init σ) (Fin.init ρ)

omit [Fintype ι] [DecidableEq ι] in
/-- The marked glue starts at `σ 0`: `markedGlue σ ρ 0 = σ 0` (`a ≥ 1`). -/
theorem markedGlue_apply_zero {a b : ℕ} (σ : Fin (a + 1 + 1) → ι) (ρ : Fin (b + 1) → ι) :
    markedGlue σ ρ 0 = σ 0 := by
  have h0 : (0 : Fin (a + 1 + b)) = Fin.castAdd b (0 : Fin (a + 1)) := by ext; simp
  rw [markedGlue, h0, Fin.append_left, Fin.init_def]; simp

omit [Fintype ι] [DecidableEq ι] in
/-- The marked glue reaches `ρ 0` at the insertion site `a`:
`markedGlue σ ρ ⟨a, _⟩ = ρ 0` (`b ≥ 1`). -/
theorem markedGlue_apply_a {a b : ℕ} (σ : Fin (a + 1) → ι) (ρ : Fin (b + 1 + 1) → ι)
    (ha : a < a + (b + 1)) :
    markedGlue σ ρ ⟨a, ha⟩ = ρ 0 := by
  have ha' : (⟨a, ha⟩ : Fin (a + (b + 1))) = Fin.natAdd a (0 : Fin (b + 1)) := by ext; simp
  rw [markedGlue, ha', Fin.append_right, Fin.init_def]; simp

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
