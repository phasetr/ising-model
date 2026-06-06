import IsingModel.Peierls.FilledRegionIdempotent

/-!
# The filled region is connected (FV §3.7.2)

Filling the holes of a connected droplet `S` keeps it connected: a hole is a bounded
complementary component of `S`, and in a (pre)connected graph it must be adjacent to `S`, so every
hole vertex reaches `S` within the filled region. Together with the connectivity of `S` this makes
`filledRegion G S g` a connected droplet — the hypothesis needed to count its boundary as a single
edge-connected contour.

* `exists_first_entry` — a walk from outside `S` to inside `S` has a first crossing edge, reached
  while staying outside `S`.
* `mem_filled_of_reachableWithin_compl` — a vertex reached from `x ∈ F` avoiding `S` is in `F`.
* `reachableWithin_filled_of_reachableWithin_compl` — such a within-`Sᶜ` walk stays in `F`.
* `isConnectedDroplet_filledRegion` — the filled region is connected.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **First entry into `S`**: a walk from `x ∉ S` to `u ∈ S` contains an edge `a → b` with `a ∉ S`,
`b ∈ S`, and `a` reachable from `x` while staying outside `S`. -/
theorem exists_first_entry {G : SimpleGraph ι} {S : Finset ι} {x u : ι} (hx : x ∉ S)
    (w : G.Walk x u) (hu : u ∈ S) :
    ∃ a b, a ∉ S ∧ b ∈ S ∧ G.Adj a b ∧ ReachableWithin G (Finset.univ \ S) x a := by
  induction w with
  | nil => exact absurd hu hx
  | @cons x y t hadj w' ih =>
    by_cases hy : y ∈ S
    · exact ⟨x, y, hx, hy, hadj, Relation.ReflTransGen.refl⟩
    · obtain ⟨a, b, ha, hb, hab, hreach⟩ := ih hy hu
      refine ⟨a, b, ha, hb, hab, ?_⟩
      refine Relation.ReflTransGen.head ⟨hadj, ?_, ?_⟩ hreach
      · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hx⟩
      · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hy⟩

/-- **Vertices reached from a filled-region vertex avoiding `S` are in the filled region**: such a
vertex lies in `x`'s hole, never the outside (else `x` itself would be in the outside). -/
theorem mem_filled_of_reachableWithin_compl {G : SimpleGraph ι} [DecidableRel G.Adj]
    {S : Finset ι} {g x w : ι} (hxF : x ∈ filledRegion G S g)
    (hxw : ReachableWithin G (Finset.univ \ S) x w) : w ∈ filledRegion G S g := by
  rw [mem_filledRegion]
  intro hwout
  rw [mem_outsideComponent] at hwout
  have hsymm : Symmetric
      (fun p q : ι => G.Adj p q ∧ p ∈ Finset.univ \ S ∧ q ∈ Finset.univ \ S) :=
    fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩
  exact (mem_filledRegion.mp hxF)
    (mem_outsideComponent.mpr (hwout.trans (Relation.ReflTransGen.symmetric hsymm hxw)))

/-- A within-`Sᶜ` walk from a filled-region vertex stays inside the filled region. -/
theorem reachableWithin_filled_of_reachableWithin_compl {G : SimpleGraph ι} [DecidableRel G.Adj]
    {S : Finset ι} {g x v : ι} (hxF : x ∈ filledRegion G S g)
    (h : ReachableWithin G (Finset.univ \ S) x v) :
    ReachableWithin G (filledRegion G S g) x v := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail a b hxa hab ih =>
    exact ih.tail ⟨hab.1, mem_filled_of_reachableWithin_compl hxF hxa,
      mem_filled_of_reachableWithin_compl hxF (hxa.tail hab)⟩

/-- **The filled region is connected**: filling the holes of a connected droplet `S` (with `g ∉ S`)
in a preconnected graph yields a connected droplet. -/
theorem isConnectedDroplet_filledRegion {G : SimpleGraph ι} [DecidableRel G.Adj]
    (hconn : G.Preconnected) {S : Finset ι} {g : ι} (hSne : S.Nonempty)
    (hS : IsConnectedDroplet G S) (hg : g ∉ S) :
    IsConnectedDroplet G (filledRegion G S g) := by
  obtain ⟨s₀, hs₀⟩ := hSne
  have hsymm : Symmetric
      (fun p q : ι => G.Adj p q ∧ p ∈ filledRegion G S g ∧ q ∈ filledRegion G S g) :=
    fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩
  -- every vertex of `F` reaches the anchor `s₀ ∈ S` within `F`
  have key : ∀ x ∈ filledRegion G S g, ReachableWithin G (filledRegion G S g) x s₀ := by
    intro x hxF
    by_cases hxS : x ∈ S
    · exact reachableWithin_mono (subset_filledRegion hg) (hS x hxS s₀ hs₀)
    · obtain ⟨w⟩ := hconn x s₀
      obtain ⟨a, b, ha, hb, hab, hreach⟩ := exists_first_entry hxS w hs₀
      have hxa : ReachableWithin G (filledRegion G S g) x a :=
        reachableWithin_filled_of_reachableWithin_compl hxF hreach
      have haF : a ∈ filledRegion G S g := mem_filled_of_reachableWithin_compl hxF hreach
      have hbF : b ∈ filledRegion G S g := subset_filledRegion hg hb
      have hab' : ReachableWithin G (filledRegion G S g) a b :=
        Relation.ReflTransGen.single ⟨hab, haF, hbF⟩
      have hbs₀ : ReachableWithin G (filledRegion G S g) b s₀ :=
        reachableWithin_mono (subset_filledRegion hg) (hS b hb s₀ hs₀)
      exact (hxa.trans hab').trans hbs₀
  intro x hx y hy
  exact (key x hx).trans (Relation.ReflTransGen.symmetric hsymm (key y hy))

end IsingModel
