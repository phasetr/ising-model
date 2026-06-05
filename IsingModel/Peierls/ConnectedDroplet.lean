import IsingModel.Peierls.DownSpinsMagnetization
import IsingModel.Peierls.PlusBoundary

/-!
# Connected droplet refinement of the Peierls bound (FV §3.7.2)

The Peierls / Friedli–Velenik §3.7.2 low-temperature argument is sharpened by restricting
the contour sum to **connected** spin droplets. When `σ_i = -1`, the connected component of
`i` in the down-spins (the droplet `downComponent`) is a connected vertex set whose edge
boundary is contained in the phase boundary `∂σ`. This restriction to connected droplets is
the foundation of the volume-independent contour counting needed for `m*(β)>0` (Issue #3631).

* `ReachableWithin` — reachability via a walk staying inside a vertex set.
* `downComponent` — the connected component of `i` in the down-spins.
* `cutEdges_downComponent_subset_phaseBoundary` — the droplet's boundary is broken bonds.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Reachability within a vertex set**: `x` reaches `y` by a chain of `G`-adjacencies that
stays inside `T`. The connectivity relation defining a droplet. -/
def ReachableWithin (G : SimpleGraph ι) (T : Finset ι) (x y : ι) : Prop :=
  Relation.ReflTransGen (fun a b => G.Adj a b ∧ a ∈ T ∧ b ∈ T) x y

/-- **The down-spin droplet of `i`**: the connected component of `i` in the down-spins,
i.e. the vertices reachable from `i` through down-spins. -/
noncomputable def downComponent (G : SimpleGraph ι) [DecidableRel G.Adj] (σ : Config ι)
    (i : ι) : Finset ι := by
  classical
  exact Finset.univ.filter (fun j => ReachableWithin G (downSpins σ) i j)

omit [DecidableEq ι] in
/-- Membership in the droplet. -/
theorem mem_downComponent {G : SimpleGraph ι} [DecidableRel G.Adj] {σ : Config ι} {i j : ι} :
    j ∈ downComponent G σ i ↔ ReachableWithin G (downSpins σ) i j := by
  classical
  unfold downComponent
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ j)

omit [DecidableEq ι] in
/-- The origin lies in its own droplet. -/
theorem self_mem_downComponent (G : SimpleGraph ι) [DecidableRel G.Adj] (σ : Config ι)
    (i : ι) : i ∈ downComponent G σ i :=
  mem_downComponent.mpr Relation.ReflTransGen.refl

omit [DecidableEq ι] in
/-- **The droplet consists of down-spins**: if `i` is a down-spin, every vertex of its
droplet is a down-spin. -/
theorem downComponent_subset_downSpins {G : SimpleGraph ι} [DecidableRel G.Adj]
    {σ : Config ι} {i : ι} (hi : σ i = Spin.down) :
    downComponent G σ i ⊆ downSpins σ := by
  intro j hj
  rw [mem_downComponent] at hj
  induction hj with
  | refl => exact (mem_downSpins σ i).mpr hi
  | tail _ hstep _ => exact hstep.2.2

/-- **The droplet boundary is broken bonds** (the key contour fact): every cut edge of the
droplet `downComponent G σ i` (with `σ_i = -1`) lies in the phase boundary `∂σ` — a cut edge
joins a droplet down-spin to a non-droplet vertex, which must then be an up-spin. -/
theorem cutEdges_downComponent_subset_phaseBoundary {G : SimpleGraph ι} [DecidableRel G.Adj]
    [Fintype G.edgeSet] {σ : Config ι} {i : ι} (hi : σ i = Spin.down) :
    cutEdges G (downComponent G σ i) ⊆ phaseBoundary G σ := by
  classical
  intro e he
  rw [cutEdges, Finset.mem_filter] at he
  obtain ⟨heG, hcross⟩ := he
  rw [mem_phaseBoundary]
  refine ⟨heG, ?_⟩
  -- `e = s(x, y)` with exactly one endpoint in the droplet
  induction e with
  | h x y =>
    rw [edgeCrosses, Sym2.lift_mk] at hcross
    rw [edgeDisagrees, Sym2.lift_mk]
    -- WLOG `x ∈ droplet`, `y ∉ droplet`
    have hadj : G.Adj x y := by
      have := G.mem_edgeFinset.mp heG; rwa [SimpleGraph.mem_edgeSet] at this
    have key : ∀ a b : ι, G.Adj a b → a ∈ downComponent G σ i → b ∉ downComponent G σ i →
        σ a ≠ σ b := by
      intro a b hab haC hbC
      have hda : σ a = Spin.down := (mem_downSpins σ a).mp (downComponent_subset_downSpins hi haC)
      have hdb : σ b ≠ Spin.down := by
        intro hdb
        exact hbC (mem_downComponent.mpr ((mem_downComponent.mp haC).tail
          ⟨hab, downComponent_subset_downSpins hi haC, (mem_downSpins σ b).mpr hdb⟩))
      rw [hda]; exact fun h => hdb h.symm
    by_cases hx : x ∈ downComponent G σ i <;> by_cases hy : y ∈ downComponent G σ i
    · simp [hx, hy] at hcross
    · exact decide_eq_true (key x y hadj hx hy)
    · exact decide_eq_true (fun h => key y x hadj.symm hy hx h.symm)
    · simp [hx, hy] at hcross

omit [DecidableEq ι] in
/-- **Reachability within the droplet**: a within-down-spins chain from `i` stays inside the
droplet `downComponent G σ i`. -/
theorem reachableWithin_downComponent_of_reachableWithin {G : SimpleGraph ι}
    [DecidableRel G.Adj] {σ : Config ι} {i j : ι}
    (hij : ReachableWithin G (downSpins σ) i j) :
    ReachableWithin G (downComponent G σ i) i j := by
  induction hij with
  | refl => exact Relation.ReflTransGen.refl
  | @tail a b hia hab ih =>
    have haC : a ∈ downComponent G σ i := mem_downComponent.mpr hia
    have hbC : b ∈ downComponent G σ i := mem_downComponent.mpr (hia.tail hab)
    exact ih.tail ⟨hab.1, haC, hbC⟩

/-- **A vertex set is a connected droplet** when any two of its vertices are reachable
within it. -/
def IsConnectedDroplet (G : SimpleGraph ι) (S : Finset ι) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ReachableWithin G S x y

omit [DecidableEq ι] in
/-- **The droplet is connected**: any two vertices of `downComponent G σ i` are reachable
within it (through the origin `i`). -/
theorem isConnectedDroplet_downComponent (G : SimpleGraph ι) [DecidableRel G.Adj]
    (σ : Config ι) (i : ι) : IsConnectedDroplet G (downComponent G σ i) := by
  have hsymm : Symmetric
      (fun a b : ι => G.Adj a b ∧ a ∈ downComponent G σ i ∧ b ∈ downComponent G σ i) :=
    fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩
  intro x hx y hy
  have hix : ReachableWithin G (downComponent G σ i) i x :=
    reachableWithin_downComponent_of_reachableWithin (mem_downComponent.mp hx)
  have hiy : ReachableWithin G (downComponent G σ i) i y :=
    reachableWithin_downComponent_of_reachableWithin (mem_downComponent.mp hy)
  exact (Relation.ReflTransGen.symmetric hsymm hix).trans hiy

open Classical in
/-- **Connected-droplet refinement of the down-spin indicator** (FV §3.7.2): when `σ_i=-1`,
the connected droplet `downComponent G σ i` witnesses the bound, so the indicator is bounded
by the sum over **connected** droplets `S ∋ i` with `cut S ⊆ ∂σ`. -/
theorem indicator_spin_down_le_connected_contour_sum (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (σ : Config ι) (i : ι) :
    (if σ i = Spin.down then (1 : ℝ) else 0) ≤
      ∑ S ∈ Finset.univ.filter
        (fun S : Finset ι => i ∈ S ∧ IsConnectedDroplet G S),
        if cutEdges G S ⊆ phaseBoundary G σ then 1 else 0 := by
  classical
  have hnn : ∀ S ∈ Finset.univ.filter (fun S : Finset ι => i ∈ S ∧ IsConnectedDroplet G S),
      (0 : ℝ) ≤ if cutEdges G S ⊆ phaseBoundary G σ then 1 else 0 :=
    fun S _ => by by_cases h : cutEdges G S ⊆ phaseBoundary G σ <;> simp [h]
  split
  · next hi =>
    have hmem : downComponent G σ i ∈ Finset.univ.filter
        (fun S : Finset ι => i ∈ S ∧ IsConnectedDroplet G S) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        self_mem_downComponent G σ i, isConnectedDroplet_downComponent G σ i⟩
    have hterm : (if cutEdges G (downComponent G σ i) ⊆ phaseBoundary G σ then (1 : ℝ) else 0)
        = 1 := if_pos (cutEdges_downComponent_subset_phaseBoundary hi)
    calc (1 : ℝ) = _ := hterm.symm
      _ ≤ _ := Finset.single_le_sum hnn hmem
  · exact Finset.sum_nonneg hnn

end IsingModel
