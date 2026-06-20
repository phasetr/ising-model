import IsingModel.ClusterExpansion.RootedParentActive
import IsingModel.ClusterExpansion.Incompatibility
import IsingModel.ClusterExpansion.Families.EvenSubgraphs

/-!
# The moment-weighted constrained active sum (GJ §18.5)

The rooted-tree Kotecky--Preiss leaf-peel induction bounds a moment-weighted sum
over polymer labellings of the active vertices, subject to the per-edge
incompatibility constraints.  This file defines that sum.

For a parent function `par : Fin n → Fin (n+1)`, an active-closed set
`A : Finset (Fin n)` (`hclosed`), and a moment-exponent function `k : Fin (n+1) → ℕ`,
`rootedParentActiveSum G par A hclosed k t` is the sum over labellings
`ω : {v // v ∈ rootedParentActiveVertices A} → allPolymers G` of the moment-weighted
activity `∏_v |ω v|^{k v}·(e|t|)^{|ω v|}`, restricted to the labellings satisfying
`ω (succ j) ∼ ω (par j)` for every active `j ∈ A`.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.4--§18.5, pp.~332--336.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems*, §5.4
  (Theorem 5.4, the Kotecky--Preiss criterion).
-/

namespace IsingModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- The subtype of active vertices of `A` (the root `0` together with the active
non-root vertices). -/
abbrev RootedParentActive (A : Finset (Fin n)) : Type :=
  {v : Fin (n + 1) // v ∈ rootedParentActiveVertices A}

/-- The active vertex `Fin.succ j` for an active `j ∈ A`. -/
def rootedParentActiveChild {A : Finset (Fin n)} {j : Fin n} (hj : j ∈ A) :
    RootedParentActive A :=
  ⟨Fin.succ j, succ_mem_rootedParentActiveVertices.mpr hj⟩

/-- The active parent vertex `par j` for an active `j ∈ A` (active by closedness). -/
def rootedParentActiveParent {par : Fin n → Fin (n + 1)} {A : Finset (Fin n)}
    (hclosed : RootedParentActiveClosed par A) {j : Fin n} (hj : j ∈ A) :
    RootedParentActive A :=
  ⟨par j, hclosed j hj⟩

/-- **The moment-weighted constrained active sum.**  The sum over labellings of the
active vertices of `A` by polymers of `G`, of the moment-weighted activity
`∏_v |ω v|^{k v}·(e|t|)^{|ω v|}`, restricted to the labellings with
`ω (succ j) ∼ ω (par j)` for every active `j ∈ A`. -/
noncomputable def rootedParentActiveSum (G : SimpleGraph ι) [Fintype G.edgeSet]
    (par : Fin n → Fin (n + 1)) (A : Finset (Fin n))
    (hclosed : RootedParentActiveClosed par A) (k : Fin (n + 1) → ℕ) (t : ℝ) : ℝ :=
  ∑ ω ∈ Fintype.piFinset (fun _ : RootedParentActive A => allPolymers G),
    (if ∀ j : Fin n, ∀ hj : j ∈ A,
        PolymersIncompatible (ω (rootedParentActiveChild hj))
          (ω (rootedParentActiveParent hclosed hj)) then
      ∏ v : RootedParentActive A,
        ((ω v).card : ℝ) ^ k v.1 * (Real.exp 1 * |t|) ^ (ω v).card
    else 0)

/-- The active vertices of the empty active set are just the root `{0}`. -/
@[simp]
theorem rootedParentActiveVertices_empty :
    rootedParentActiveVertices (∅ : Finset (Fin n)) = {0} := by
  simp [rootedParentActiveVertices]

/-- The coercion of the active child vertex is `Fin.succ j`. -/
@[simp]
theorem rootedParentActiveChild_coe {A : Finset (Fin n)} {j : Fin n} (hj : j ∈ A) :
    (rootedParentActiveChild hj : Fin (n + 1)) = Fin.succ j := rfl

/-- The coercion of the active parent vertex is `par j`. -/
@[simp]
theorem rootedParentActiveParent_coe {par : Fin n → Fin (n + 1)} {A : Finset (Fin n)}
    (hclosed : RootedParentActiveClosed par A) {j : Fin n} (hj : j ∈ A) :
    (rootedParentActiveParent hclosed hj : Fin (n + 1)) = par j := rfl

/-- For the empty active set, the only active vertex is the root `0`. -/
instance : Unique (RootedParentActive (∅ : Finset (Fin n))) where
  default := ⟨0, by simp⟩
  uniq := by
    rintro ⟨v, hv⟩
    rw [rootedParentActiveVertices_empty, Finset.mem_singleton] at hv
    exact Subtype.ext hv

/-- **Base case of the active sum.**  On the empty active set there are no
constraints and only the root vertex `0`, so the active sum reduces to the
root-only moment-weighted activity `∑_P |P|^{k 0}·(e|t|)^{|P|}`. -/
theorem rootedParentActiveSum_empty (G : SimpleGraph ι) [Fintype G.edgeSet]
    (par : Fin n → Fin (n + 1))
    (hclosed : RootedParentActiveClosed par (∅ : Finset (Fin n)))
    (k : Fin (n + 1) → ℕ) (t : ℝ) :
    rootedParentActiveSum G par ∅ hclosed k t
      = ∑ P ∈ allPolymers G, (P.card : ℝ) ^ k 0 * (Real.exp 1 * |t|) ^ P.card := by
  rw [rootedParentActiveSum]
  refine Finset.sum_bij' (fun ω _ => ω default) (fun P _ => fun _ => P)
    (fun ω hω => ?_) (fun P hP => ?_) (fun ω hω => ?_) (fun P hP => ?_) (fun ω hω => ?_)
  · exact (Fintype.mem_piFinset.mp hω) default
  · exact Fintype.mem_piFinset.mpr (fun _ => hP)
  · funext v; rw [Unique.eq_default v]
  · rfl
  · rw [if_pos (by simp), Fintype.prod_unique]
    rfl

end IsingModel
