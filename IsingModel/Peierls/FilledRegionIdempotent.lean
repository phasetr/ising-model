import IsingModel.Peierls.FilledRegion

/-!
# Idempotence of hole-filling (FV §3.7.2)

Hole-filling is idempotent: filling a region that is already filled changes nothing. This makes
`filledRegion` a well-defined projection onto the **filled regions** (those equal to their own
filling), which is the index set for the single-contour Peierls sum.

The key is that the outside component is unchanged by filling: a walk from the ground vertex `g`
avoiding `S` automatically avoids all of `filledRegion G S g` (its vertices are themselves in the
outside, never in a hole), and conversely filling only enlarges the avoided set.

* `reachableWithin_mono` — monotonicity of within-set reachability.
* `outsideComponent_filledRegion_eq` — the outside is unchanged by filling.
* `filledRegion_idempotent` — `filledRegion (filledRegion S) = filledRegion S`.
* `IsFilled`, `isFilled_filledRegion` — the filled-region predicate and that fillings satisfy it.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- **Monotonicity of within-set reachability**: enlarging the allowed vertex set `T` only adds
reachable pairs. -/
theorem reachableWithin_mono {G : SimpleGraph ι} {T T' : Finset ι} (hTT' : T ⊆ T') {x y : ι}
    (h : ReachableWithin G T x y) : ReachableWithin G T' x y := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail a b _ hstep ih => exact ih.tail ⟨hstep.1, hTT' hstep.2.1, hTT' hstep.2.2⟩

/-- **Filling shrinks the outside reachability set**: filling enlarges the avoided set
`univ \ S`, so the outside of the filled region is contained in the outside of `S`. -/
theorem outsideComponent_filledRegion_subset {G : SimpleGraph ι} [DecidableRel G.Adj]
    {S : Finset ι} {g : ι} (hg : g ∉ S) :
    outsideComponent G (filledRegion G S g) g ⊆ outsideComponent G S g := by
  intro v hv
  rw [mem_outsideComponent] at hv ⊢
  refine reachableWithin_mono ?_ hv
  intro x hx
  rw [Finset.mem_sdiff] at hx ⊢
  exact ⟨hx.1, fun hxS => hx.2 (subset_filledRegion hg hxS)⟩

/-- **Filling does not shrink the outside reachability set**: a walk from `g` avoiding `S` stays
inside the outside component (its vertices are themselves in the outside, never in a hole), so it
also avoids the filled region. -/
theorem outsideComponent_subset_filledRegion {G : SimpleGraph ι} [DecidableRel G.Adj]
    {S : Finset ι} {g : ι} :
    outsideComponent G S g ⊆ outsideComponent G (filledRegion G S g) g := by
  intro v hv
  rw [mem_outsideComponent] at hv ⊢
  induction hv with
  | refl => exact Relation.ReflTransGen.refl
  | @tail a b hga hab ih =>
    have ha_out : a ∈ outsideComponent G S g := mem_outsideComponent.mpr hga
    have hb_out : b ∈ outsideComponent G S g := mem_outsideComponent.mpr (hga.tail hab)
    refine ih.tail ⟨hab.1, ?_, ?_⟩
    · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, fun h => (mem_filledRegion.mp h) ha_out⟩
    · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ b, fun h => (mem_filledRegion.mp h) hb_out⟩

/-- **The outside is unchanged by filling** (for `g ∉ S`). -/
theorem outsideComponent_filledRegion_eq {G : SimpleGraph ι} [DecidableRel G.Adj]
    {S : Finset ι} {g : ι} (hg : g ∉ S) :
    outsideComponent G (filledRegion G S g) g = outsideComponent G S g :=
  Finset.Subset.antisymm (outsideComponent_filledRegion_subset hg)
    outsideComponent_subset_filledRegion

/-- **Hole-filling is idempotent** (for `g ∉ S`): filling an already-filled region is a no-op. -/
theorem filledRegion_idempotent {G : SimpleGraph ι} [DecidableRel G.Adj] {S : Finset ι} {g : ι}
    (hg : g ∉ S) : filledRegion G (filledRegion G S g) g = filledRegion G S g :=
  congrArg (Finset.univ \ ·) (outsideComponent_filledRegion_eq hg)

/-- **A region is filled** when it equals its own hole-filling (its complement is the single
outside component anchored at `g`). -/
def IsFilled (G : SimpleGraph ι) [DecidableRel G.Adj] (g : ι) (F : Finset ι) : Prop :=
  filledRegion G F g = F

/-- **Fillings are filled** (for `g ∉ S`): `filledRegion G S g` is a fixed point of filling. -/
theorem isFilled_filledRegion {G : SimpleGraph ι} [DecidableRel G.Adj] {S : Finset ι} {g : ι}
    (hg : g ∉ S) : IsFilled G g (filledRegion G S g) :=
  filledRegion_idempotent hg

/-- **The ground vertex is outside a filled region**: if `IsFilled G g F` then `g ∉ F`. -/
theorem ground_not_mem_of_isFilled {G : SimpleGraph ι} [DecidableRel G.Adj] {g : ι}
    {F : Finset ι} (hF : IsFilled G g F) : g ∉ F := by
  rw [← hF]; exact ground_not_mem_filledRegion G F g

end IsingModel
