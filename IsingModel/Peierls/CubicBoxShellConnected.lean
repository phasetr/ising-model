import IsingModel.Peierls.CubicBoxBoundaryShell
import IsingModel.Peierls.PeierlsMagnetizationPosFilled

/-!
# Connectedness of the outer boundary shell of the canonical cubic box (FV §3.7.2)

The Peierls magnetization bound needs a *connected* boundary `B n` (the `hBconn` hypothesis). For
the canonical cubic box `[-n, n]²` the outer boundary shell `cubicOuterBoundaryTwo n` is connected:
every shell vertex reaches the north-east corner `(n, n)` by walking along the sides — each leg
fixes one coordinate at `±n` (so the whole leg stays on the shell) and steps the other coordinate
one unit at a time.

* `reachableWithin_shell_fix0` / `reachableWithin_shell_fix1` — the side-walk primitives.
* `cubicOuterBoundaryTwo_connected` — the boundary shell is a connected droplet (`hBconn` supply).
* `cubicCornerNE_mem_outerBoundary` — the north-east corner lies on the shell (`hgB` supply).

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset SimpleGraph Ambient GridEdge2

/-- **A two-coordinate box-membership helper**: `![a, b] ∈ [-n, n]²` when `a, b ∈ [-n, n]`. -/
theorem mem_cubicBox_two {n : ℕ} {a b : ℤ} (ha : -(n : ℤ) ≤ a ∧ a ≤ n)
    (hb : -(n : ℤ) ≤ b ∧ b ≤ n) : (![a, b] : Fin 2 → ℤ) ∈ cubicBox 2 n := by
  rw [mem_cubicBox]
  intro i
  fin_cases i <;> norm_num [ha, hb]

/-- **Second-coordinate bound from box membership**: `![f, a] ∈ [-n, n]²` gives `a ∈ [-n, n]`. -/
theorem cubicBox_two_snd_bound {n : ℕ} {f a : ℤ} (h : (![f, a] : Fin 2 → ℤ) ∈ cubicBox 2 n) :
    -(n : ℤ) ≤ a ∧ a ≤ n := by
  have h1 := (mem_cubicBox).mp h 1
  norm_num at h1
  exact h1

/-- **The first-coordinate bound from box membership**: `![a, f] ∈ [-n, n]²` gives `a ∈ [-n, n]`. -/
theorem cubicBox_two_fst_bound {n : ℕ} {f a : ℤ} (h : (![a, f] : Fin 2 → ℤ) ∈ cubicBox 2 n) :
    -(n : ℤ) ≤ a ∧ a ≤ n := by
  have h0 := (mem_cubicBox).mp h 0
  norm_num at h0
  exact h0

/-- **Walk along coordinate 1 keeping coordinate 0 fixed at a shell value `f = ±n`**: the points
`⟨![f, a], _⟩` for `a` ranging over `[-n, n]` are all connected within the boundary shell. -/
theorem reachableWithin_shell_fix0 (n : ℕ) (f : ℤ) (hf : f = (n : ℤ) ∨ f = -(n : ℤ)) :
    ∀ (k : ℕ) (a b : ℤ) (_hk : (b - a).natAbs = k)
      (hma : (![f, a] : Fin 2 → ℤ) ∈ cubicBox 2 n) (hmb : (![f, b] : Fin 2 → ℤ) ∈ cubicBox 2 n),
      ReachableWithin (Ambient.inducedGraph (latticeGraph 2) (cubicBox 2 n))
        (cubicOuterBoundaryTwo n) ⟨![f, a], hma⟩ ⟨![f, b], hmb⟩ := by
  intro k
  induction k with
  | zero =>
    intro a b hk hma hmb
    have hab : a = b := by omega
    subst hab
    exact Relation.ReflTransGen.refl
  | succ k ih =>
    intro a b hk hma hmb
    have ha := cubicBox_two_snd_bound hma
    have hb := cubicBox_two_snd_bound hmb
    have hne : a ≠ b := by rintro rfl; simp at hk
    -- step `a` one unit toward `b`
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- a < b: step `a → a + 1`
      have ha' : -(n : ℤ) ≤ a + 1 ∧ a + 1 ≤ (n : ℤ) := by omega
      have hma' : (![f, a + 1] : Fin 2 → ℤ) ∈ cubicBox 2 n :=
        mem_cubicBox_two (by
          rcases hf with h | h <;> · subst h; constructor <;> simp) ha'
      have hadj0 : (latticeGraph 2).Adj (![f, a] : Fin 2 → ℤ) ![f, a + 1] := by
        have heq : (![f, a + 1] : Fin 2 → ℤ) = ![f, a] + unitVec2 1 := by
          funext i; fin_cases i <;> simp [unitVec2]
        rw [heq]; exact latticeGraph_adj_add_unitVec2 ![f, a] 1
      have hadj : (Ambient.inducedGraph (latticeGraph 2) (cubicBox 2 n)).Adj
          ⟨![f, a], hma⟩ ⟨![f, a + 1], hma'⟩ := hadj0
      have hxB : (⟨![f, a], hma⟩ : ↑(cubicBox 2 n)) ∈ cubicOuterBoundaryTwo n := by
        rw [mem_cubicOuterBoundaryTwo]; rcases hf with h | h <;> simp [h]
      have hyB : (⟨![f, a + 1], hma'⟩ : ↑(cubicBox 2 n)) ∈ cubicOuterBoundaryTwo n := by
        rw [mem_cubicOuterBoundaryTwo]; rcases hf with h | h <;> simp [h]
      exact Relation.ReflTransGen.head ⟨hadj, hxB, hyB⟩
        (ih (a + 1) b (by omega) hma' hmb)
    · -- a > b: step `a → a - 1`
      have ha' : -(n : ℤ) ≤ a - 1 ∧ a - 1 ≤ (n : ℤ) := by omega
      have hma' : (![f, a - 1] : Fin 2 → ℤ) ∈ cubicBox 2 n :=
        mem_cubicBox_two (by
          rcases hf with h | h <;> · subst h; constructor <;> simp) ha'
      have hadj0 : (latticeGraph 2).Adj (![f, a] : Fin 2 → ℤ) ![f, a - 1] := by
        have heq : (![f, a] : Fin 2 → ℤ) = ![f, a - 1] + unitVec2 1 := by
          funext i; fin_cases i <;> simp [unitVec2]
        rw [heq]; exact (latticeGraph_adj_add_unitVec2 ![f, a - 1] 1).symm
      have hadj : (Ambient.inducedGraph (latticeGraph 2) (cubicBox 2 n)).Adj
          ⟨![f, a], hma⟩ ⟨![f, a - 1], hma'⟩ := hadj0
      have hxB : (⟨![f, a], hma⟩ : ↑(cubicBox 2 n)) ∈ cubicOuterBoundaryTwo n := by
        rw [mem_cubicOuterBoundaryTwo]; rcases hf with h | h <;> simp [h]
      have hyB : (⟨![f, a - 1], hma'⟩ : ↑(cubicBox 2 n)) ∈ cubicOuterBoundaryTwo n := by
        rw [mem_cubicOuterBoundaryTwo]; rcases hf with h | h <;> simp [h]
      exact Relation.ReflTransGen.head ⟨hadj, hxB, hyB⟩
        (ih (a - 1) b (by omega) hma' hmb)

/-- **Walk along coordinate 0 keeping coordinate 1 fixed at a shell value `f = ±n`**: the points
`⟨![a, f], _⟩` for `a` ranging over `[-n, n]` are all connected within the boundary shell. -/
theorem reachableWithin_shell_fix1 (n : ℕ) (f : ℤ) (hf : f = (n : ℤ) ∨ f = -(n : ℤ)) :
    ∀ (k : ℕ) (a b : ℤ) (_hk : (b - a).natAbs = k)
      (hma : (![a, f] : Fin 2 → ℤ) ∈ cubicBox 2 n) (hmb : (![b, f] : Fin 2 → ℤ) ∈ cubicBox 2 n),
      ReachableWithin (Ambient.inducedGraph (latticeGraph 2) (cubicBox 2 n))
        (cubicOuterBoundaryTwo n) ⟨![a, f], hma⟩ ⟨![b, f], hmb⟩ := by
  intro k
  induction k with
  | zero =>
    intro a b hk hma hmb
    have hab : a = b := by omega
    subst hab
    exact Relation.ReflTransGen.refl
  | succ k ih =>
    intro a b hk hma hmb
    have ha := cubicBox_two_fst_bound hma
    have hb := cubicBox_two_fst_bound hmb
    have hne : a ≠ b := by rintro rfl; simp at hk
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- a < b: step `a → a + 1`
      have ha' : -(n : ℤ) ≤ a + 1 ∧ a + 1 ≤ (n : ℤ) := by omega
      have hma' : (![a + 1, f] : Fin 2 → ℤ) ∈ cubicBox 2 n :=
        mem_cubicBox_two ha' (by rcases hf with h | h <;> · subst h; constructor <;> simp)
      have hadj0 : (latticeGraph 2).Adj (![a, f] : Fin 2 → ℤ) ![a + 1, f] := by
        have heq : (![a + 1, f] : Fin 2 → ℤ) = ![a, f] + unitVec2 0 := by
          funext i; fin_cases i <;> simp [unitVec2]
        rw [heq]; exact latticeGraph_adj_add_unitVec2 ![a, f] 0
      have hadj : (Ambient.inducedGraph (latticeGraph 2) (cubicBox 2 n)).Adj
          ⟨![a, f], hma⟩ ⟨![a + 1, f], hma'⟩ := hadj0
      have hxB : (⟨![a, f], hma⟩ : ↑(cubicBox 2 n)) ∈ cubicOuterBoundaryTwo n := by
        rw [mem_cubicOuterBoundaryTwo]; rcases hf with h | h <;> simp [h]
      have hyB : (⟨![a + 1, f], hma'⟩ : ↑(cubicBox 2 n)) ∈ cubicOuterBoundaryTwo n := by
        rw [mem_cubicOuterBoundaryTwo]; rcases hf with h | h <;> simp [h]
      exact Relation.ReflTransGen.head ⟨hadj, hxB, hyB⟩
        (ih (a + 1) b (by omega) hma' hmb)
    · -- a > b: step `a → a - 1`
      have ha' : -(n : ℤ) ≤ a - 1 ∧ a - 1 ≤ (n : ℤ) := by omega
      have hma' : (![a - 1, f] : Fin 2 → ℤ) ∈ cubicBox 2 n :=
        mem_cubicBox_two ha' (by rcases hf with h | h <;> · subst h; constructor <;> simp)
      have hadj0 : (latticeGraph 2).Adj (![a, f] : Fin 2 → ℤ) ![a - 1, f] := by
        have heq : (![a, f] : Fin 2 → ℤ) = ![a - 1, f] + unitVec2 0 := by
          funext i; fin_cases i <;> simp [unitVec2]
        rw [heq]; exact (latticeGraph_adj_add_unitVec2 ![a - 1, f] 0).symm
      have hadj : (Ambient.inducedGraph (latticeGraph 2) (cubicBox 2 n)).Adj
          ⟨![a, f], hma⟩ ⟨![a - 1, f], hma'⟩ := hadj0
      have hxB : (⟨![a, f], hma⟩ : ↑(cubicBox 2 n)) ∈ cubicOuterBoundaryTwo n := by
        rw [mem_cubicOuterBoundaryTwo]; rcases hf with h | h <;> simp [h]
      have hyB : (⟨![a - 1, f], hma'⟩ : ↑(cubicBox 2 n)) ∈ cubicOuterBoundaryTwo n := by
        rw [mem_cubicOuterBoundaryTwo]; rcases hf with h | h <;> simp [h]
      exact Relation.ReflTransGen.head ⟨hadj, hxB, hyB⟩
        (ih (a - 1) b (by omega) hma' hmb)

/-- **The north-east corner `(n, n)` of the cubic box**, the basepoint of the boundary shell. -/
noncomputable def cubicCornerNE (n : ℕ) : ↑(cubicBox 2 n) :=
  ⟨![(n : ℤ), (n : ℤ)], mem_cubicBox_two ⟨by omega, le_refl _⟩ ⟨by omega, le_refl _⟩⟩

/-- **The north-east corner lies on the boundary shell** (the `hgB` supply). -/
theorem cubicCornerNE_mem_outerBoundary (n : ℕ) :
    cubicCornerNE n ∈ cubicOuterBoundaryTwo n := by
  rw [mem_cubicOuterBoundaryTwo]
  left
  rfl

/-- **Every shell vertex reaches the north-east corner within the shell** (coordinate form): by the
side it lies on, walk to the corner (one leg for the right/top side, two legs for the left/bottom
side). -/
theorem reachableWithin_shell_corner_coord (n : ℕ) (x0 x1 : ℤ)
    (hm : (![x0, x1] : Fin 2 → ℤ) ∈ cubicBox 2 n)
    (hx : (⟨![x0, x1], hm⟩ : ↑(cubicBox 2 n)) ∈ cubicOuterBoundaryTwo n) :
    ReachableWithin (Ambient.inducedGraph (latticeGraph 2) (cubicBox 2 n))
      (cubicOuterBoundaryTwo n) ⟨![x0, x1], hm⟩ (cubicCornerNE n) := by
  have hb0 := cubicBox_two_fst_bound hm
  have hb1 := cubicBox_two_snd_bound hm
  rw [mem_cubicOuterBoundaryTwo] at hx
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hx
  rcases hx with h | h | h | h
  · -- right side `x0 = n`
    subst h
    exact reachableWithin_shell_fix0 n (n : ℤ) (Or.inl rfl) ((n : ℤ) - x1).natAbs x1 (n : ℤ) rfl hm
      (mem_cubicBox_two ⟨by omega, le_refl _⟩ ⟨by omega, le_refl _⟩)
  · -- left side `x0 = -n`: two legs
    subst h
    have leg1 := reachableWithin_shell_fix0 n (-(n : ℤ)) (Or.inr rfl) ((n : ℤ) - x1).natAbs
      x1 (n : ℤ) rfl hm
      (mem_cubicBox_two ⟨by omega, by omega⟩ ⟨by omega, le_refl _⟩)
    have leg2 := reachableWithin_shell_fix1 n (n : ℤ) (Or.inl rfl) ((n : ℤ) - (-(n : ℤ))).natAbs
      (-(n : ℤ)) (n : ℤ) rfl
      (mem_cubicBox_two ⟨by omega, by omega⟩ ⟨by omega, le_refl _⟩)
      (mem_cubicBox_two ⟨by omega, le_refl _⟩ ⟨by omega, le_refl _⟩)
    exact leg1.trans leg2
  · -- top side `x1 = n`
    subst h
    exact reachableWithin_shell_fix1 n (n : ℤ) (Or.inl rfl) ((n : ℤ) - x0).natAbs x0 (n : ℤ) rfl hm
      (mem_cubicBox_two ⟨by omega, le_refl _⟩ ⟨by omega, le_refl _⟩)
  · -- bottom side `x1 = -n`: two legs
    subst h
    have leg1 := reachableWithin_shell_fix1 n (-(n : ℤ)) (Or.inr rfl) ((n : ℤ) - x0).natAbs
      x0 (n : ℤ) rfl hm
      (mem_cubicBox_two ⟨by omega, le_refl _⟩ ⟨by omega, by omega⟩)
    have leg2 := reachableWithin_shell_fix0 n (n : ℤ) (Or.inl rfl) ((n : ℤ) - (-(n : ℤ))).natAbs
      (-(n : ℤ)) (n : ℤ) rfl
      (mem_cubicBox_two ⟨by omega, le_refl _⟩ ⟨by omega, by omega⟩)
      (mem_cubicBox_two ⟨by omega, le_refl _⟩ ⟨by omega, le_refl _⟩)
    exact leg1.trans leg2

/-- **The outer boundary shell is a connected droplet** (the `hBconn` supply): every two shell
vertices are connected within the shell, via the north-east corner. -/
theorem cubicOuterBoundaryTwo_connected (n : ℕ) :
    IsConnectedDroplet (Ambient.inducedGraph (latticeGraph 2) (cubicBox 2 n))
      (cubicOuterBoundaryTwo n) := by
  have hsymm : Symmetric (fun a b : ↑(cubicBox 2 n) =>
      (Ambient.inducedGraph (latticeGraph 2) (cubicBox 2 n)).Adj a b ∧
        a ∈ cubicOuterBoundaryTwo n ∧ b ∈ cubicOuterBoundaryTwo n) :=
    fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩
  have hcorner : ∀ x : ↑(cubicBox 2 n), x ∈ cubicOuterBoundaryTwo n →
      ReachableWithin (Ambient.inducedGraph (latticeGraph 2) (cubicBox 2 n))
        (cubicOuterBoundaryTwo n) x (cubicCornerNE n) := by
    intro x hx
    have hxval : x = ⟨![x.val 0, x.val 1], by
        rw [mem_cubicBox]; intro i
        have := (mem_cubicBox).mp x.property
        fin_cases i <;> simpa using this _⟩ := by
      apply Subtype.ext
      funext i; fin_cases i <;> rfl
    rw [hxval] at hx ⊢
    exact reachableWithin_shell_corner_coord n (x.val 0) (x.val 1) _ hx
  intro x hx y hy
  exact (hcorner x hx).trans (Relation.ReflTransGen.symmetric hsymm (hcorner y hy))

/-- **The Peierls phase transition for the canonical 2D Ising model** (FV §3.7.2): at low
temperature (`32 q < 1` and `2·32 q/(1-32 q) < 1` with `q = exp(-2βJ)`, i.e. `β` large) the genuine
`+`-state spontaneous magnetization at the origin is **positive** along the cubic exhaustion
`[-n, n]²`, with **no** remaining hypothesis — the boundary (`hBconn`/`hgB`), dual-support
(`hdual`), and neighbour-closure (`hne`) inputs are all discharged by the canonical-box geometry,
and the discrete-Jordan core by `planarBondHypothesis`. This is `m*(β) > 0` at low
temperature, which implies `β_c < ∞`. -/
theorem peierls_spontaneous_magnetization_pos_cubic (J β : ℝ)
    (hr0 : 0 < 32 * Real.exp (-2 * β * J)) (hr1 : 32 * Real.exp (-2 * β * J) < 1)
    (hsmall : 2 * (32 * Real.exp (-2 * β * J) / (1 - 32 * Real.exp (-2 * β * J))) < 1) :
    0 < plusGibbsExpectationLiminf (latticeGraph 2) (Ambient.cubicExhaustion 2)
          (⟨J, 0, β⟩ : IsingParams ℝ) (fun n => cubicOuterBoundaryTwo n)
          (fun n σ => Spin.sign ℝ (σ ⟨0, zero_mem_cubicBox_two n⟩)) := by
  classical
  refine peierls_plusGibbsLiminf_pos_filled (Ambient.cubicExhaustion 2)
    (fun n => cubicBox 2 n) J β (fun n => cubicOuterBoundaryTwo n)
    (fun n => ⟨0, zero_mem_cubicBox_two n⟩) (fun n => cubicCornerNE n)
    (fun n => inducedCubicBox_two_preconnected n)
    (fun n => cubicOuterBoundaryTwo_connected n)
    (fun n => cubicCornerNE_mem_outerBoundary n) ?_ ?_ hr0 hr1 hsmall
  · -- hdual: dual support of any filter droplet stays in `[-n, n]²`
    rintro (_ | k) S hS
    · -- `n = 0`: the filter is empty (the origin lies on the shell)
      have hi := (Finset.mem_filter.mp hS).2.1
      have hdisj := (Finset.mem_filter.mp hS).2.2.1
      have hiB : (⟨0, zero_mem_cubicBox_two 0⟩ : ↑(cubicBox 2 0)) ∈ cubicOuterBoundaryTwo 0 := by
        rw [mem_cubicOuterBoundaryTwo]; left; rfl
      exact ((Finset.disjoint_left.mp hdisj hi) hiB).elim
    · -- `n = k + 1`: interior image, dual support in `[-(k+1), k+1]²`
      have hdisj := (Finset.mem_filter.mp hS).2.2.1
      exact dualSupport_subset_cubicBox_succ
        (image_subset_cubicBox_of_disjoint_outerBoundary hdisj)
  · -- hne: any filter droplet is neighbour-closed
    rintro (_ | k) S hS
    · -- `n = 0`: the filter is empty
      have hi := (Finset.mem_filter.mp hS).2.1
      have hdisj := (Finset.mem_filter.mp hS).2.2.1
      have hiB : (⟨0, zero_mem_cubicBox_two 0⟩ : ↑(cubicBox 2 0)) ∈ cubicOuterBoundaryTwo 0 := by
        rw [mem_cubicOuterBoundaryTwo]; left; rfl
      exact ((Finset.disjoint_left.mp hdisj hi) hiB).elim
    · -- `n = k + 1`
      have hdisj := (Finset.mem_filter.mp hS).2.2.1
      exact neighbourClosed_of_disjoint_outerBoundary hdisj

end IsingModel
