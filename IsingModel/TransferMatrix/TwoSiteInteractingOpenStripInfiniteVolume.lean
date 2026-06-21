import IsingModel.TransferMatrix.TwoSiteInteractingOpenStripDecay
import IsingModel.AmbientLattice.CorrelationInfinite.Bounds
import IsingModel.PartitionFunctionIso
import IsingModel.AmbientLatticeSum.InducedUnion

/-!
# Infinite-volume `K2` open-strip exponential decay (GJ §17.1)

This file passes the finite interacting `K2` (fixed transverse width `2`) open-strip
decay bound of `TwoSiteInteractingOpenStripDecay` to a *centred* box exhaustion of the
ambient lattice `ℤ × Fin 2`, and on to `correlationInfinite`.  The ambient graph is the
two-row strip graph `stripGraph` on `ℤ × Fin 2` (longitudinal nearest-neighbour edges
plus the transverse rung), and the box `stripBox N = [-N, N] ×ˢ univ` is identified with
the open strip `twoSiteOpenStrip (2N)` via the shift `(z, s) ↦ ![z + N, s]`
(`stripBoxEquiv`).  Hence by `correlation_map_equiv` the finite-volume
`correlationAlongExhaustion` at stage `N` equals the transported open-strip two-point
correlation, which is bounded by `prefactor · exp(-mass · sep)`.  Because the bound is a
constant in `N` (independent of the box), the supremum collapses to it, yielding the
interacting infinite-volume `K2`-strip exponential decay.

This is the interacting analogue of the free-field `InfiniteVolumeOneD` capstone.  The
decay rate is `mass = twoSiteInteractingMass (βJ) = -log(flipOdd / top)`, and the prefactor
is the spectral prefactor `k2StripPrefactor` of the boundary-marked transfer-matrix data.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.1, pp. 304--306.
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.5, pp. 311--312.
-/

namespace IsingModel

namespace TransferMatrix

open scoped BigOperators
open SimpleGraph Finset
open Matrix

/-! ## The prefactor abbreviation -/

/-- The spectral prefactor of the finite `K2` open-strip decay bound, abbreviated for
readability: the boundary-marked spectral prefactor divided by the boundary spectral
partition prefactor of the boundary-balanced two-site interacting layer data. -/
noncomputable def k2StripPrefactor (p : IsingParams ℝ) (hp : p.h = 0) (x : Fin 2) : ℝ :=
  (twoSiteInteractingLayerOrthogonalSpectralData p hp).boundaryMarkedSpectralPrefactor
      (layerSpinAt x)
      (layerOpenBalancedBoundaryVector
        (layerInternalWeight (SimpleGraph.completeGraph (Fin 2)) p))
      (layerOpenBalancedBoundaryVector
        (layerInternalWeight (SimpleGraph.completeGraph (Fin 2)) p)) /
    (twoSiteInteractingLayerOrthogonalSpectralData p hp).boundarySpectralPartitionPrefactor
      (layerOpenBalancedBoundaryVector
        (layerInternalWeight (SimpleGraph.completeGraph (Fin 2)) p))
      twoSiteInteractingLayerTop (twoSiteInteractingTheta (p.β * p.J))

/-! ## The strip graph and centred box exhaustion -/

/-- The two-row strip graph on `ℤ × Fin 2`: a transverse rung (same longitudinal
coordinate, distinct transverse sites) or a longitudinal nearest-neighbour step
(consecutive longitudinal coordinates, same transverse site). -/
def stripGraph : SimpleGraph (ℤ × Fin 2) where
  Adj p q := (p.1 = q.1 ∧ p.2 ≠ q.2) ∨ ((p.1 - q.1).natAbs = 1 ∧ p.2 = q.2)
  symm := by
    rintro p q (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨h1.symm, fun h => h2 h.symm⟩
    · refine Or.inr ⟨?_, h2.symm⟩
      rw [← Int.natAbs_neg]; simpa using h1
  loopless := ⟨fun p hp => by
    rcases hp with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact h2 rfl
    · simp at h1⟩

/-- Adjacency in `stripGraph` is decidable. -/
instance : DecidableRel stripGraph.Adj := fun p q => by
  unfold stripGraph
  infer_instance

/-- Adjacency in the induced subgraph of `stripGraph` on any finite volume is decidable
(it reduces to `stripGraph`-adjacency of the underlying values).  Providing this makes the
canonical `SimpleGraph.fintypeEdgeSet` instance available on the induced edge sets, so all
`correlation` terms below share one cheap `Fintype`-instance. -/
instance (Λ : Finset (ℤ × Fin 2)) :
    DecidableRel (Ambient.inducedGraph stripGraph Λ).Adj := fun a b =>
  decidable_of_iff (stripGraph.Adj a.val b.val) (by
    rw [Ambient.inducedGraph_apply, SimpleGraph.induce_adj])

/-- The centred box `[-N, N] ×ˢ univ` of the strip lattice `ℤ × Fin 2`. -/
noncomputable def stripBox (N : ℕ) : Finset (ℤ × Fin 2) :=
  (Finset.Icc (-(N : ℤ)) N) ×ˢ Finset.univ

/-- Membership in the centred strip box: the longitudinal coordinate lies in `[-N, N]`. -/
theorem mem_stripBox {N : ℕ} {p : ℤ × Fin 2} :
    p ∈ stripBox N ↔ -(N : ℤ) ≤ p.1 ∧ p.1 ≤ N := by
  rw [stripBox, Finset.mem_product, Finset.mem_Icc]
  simp only [Finset.mem_univ, and_true]

/-- The centred strip box is monotone in `N`. -/
theorem stripBox_mono : Monotone stripBox := by
  intro m n hmn p hp
  rw [mem_stripBox] at hp ⊢
  have : (m : ℤ) ≤ n := by exact_mod_cast hmn
  omega

/-- The centred box exhaustion of `ℤ × Fin 2`. -/
noncomputable def stripExhaustion : Ambient.Exhaustion (ℤ × Fin 2) where
  volume := stripBox
  mono := stripBox_mono
  exhaust := fun A => ⟨A.sup (fun p => p.1.natAbs), fun n hn p hp => by
    have hle : p.1.natAbs ≤ A.sup (fun q => q.1.natAbs) :=
      Finset.le_sup (f := fun q => q.1.natAbs) hp
    have hn' : A.sup (fun q => q.1.natAbs) ≤ n := hn
    rw [mem_stripBox]
    have : p.1.natAbs ≤ n := hle.trans hn'
    omega⟩

/-- The exhaustion's volume at stage `N` is the centred box `stripBox N`. -/
@[simp]
theorem stripExhaustion_volume (N : ℕ) : stripExhaustion.volume N = stripBox N := rfl

/-! ## Box ≅ open-strip identification -/

/-- The open-strip point of a box element: shift the longitudinal coordinate by `N` so
the centred range `[-N, N]` becomes `[0, 2N]`, keeping the transverse coordinate. -/
def stripBoxPoint (N : ℕ) (p : ↑(stripBox N)) : Fin 2 → ℤ :=
  ![p.val.1 + N, (p.val.2 : ℤ)]

/-- The shifted box point lies in the open strip `twoSiteOpenStrip (2N)`. -/
theorem stripBoxPoint_mem (N : ℕ) (p : ↑(stripBox N)) :
    stripBoxPoint N p ∈ twoSiteOpenStrip (2 * N) := by
  rw [mem_twoSiteOpenStrip, stripBoxPoint]
  have hb := mem_stripBox.mp p.2
  have h2 := p.val.2.isLt
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  refine ⟨by omega, by push_cast; omega, by positivity, by omega⟩

/-- **Box ≅ open-strip equivalence**: `↑(stripBox N) ≃ ↑(twoSiteOpenStrip (2N))` via the
longitudinal shift `(z, s) ↦ ![z + N, s]`. -/
def stripBoxEquiv (N : ℕ) : ↑(stripBox N) ≃ ↑(twoSiteOpenStrip (2 * N)) where
  toFun p := ⟨stripBoxPoint N p, stripBoxPoint_mem N p⟩
  invFun y :=
    ⟨(y.val 0 - N, ⟨(y.val 1).toNat, by
        have h := mem_twoSiteOpenStrip.mp y.2; omega⟩), by
      rw [mem_stripBox]
      have h := mem_twoSiteOpenStrip.mp y.2
      simp only; omega⟩
  left_inv p := by
    apply Subtype.ext
    obtain ⟨⟨z, s⟩, hp⟩ := p
    have h2 := s.isLt
    refine Prod.ext ?_ (Fin.ext ?_)
    · simp [stripBoxPoint]
    · simp only [stripBoxPoint, Matrix.cons_val_one, Matrix.cons_val_zero]
      omega
  right_inv y := by
    apply Subtype.ext
    funext k
    have h := mem_twoSiteOpenStrip.mp y.2
    fin_cases k
    · change y.val 0 - (N : ℤ) + (N : ℤ) = y.val 0
      ring
    · change ((y.val 1).toNat : ℤ) = y.val 1
      omega

/-- Evaluation of the box ≅ strip equivalence: the underlying strip point is
`![z + N, s]`. -/
@[simp]
theorem stripBoxEquiv_apply_val (N : ℕ) (p : ↑(stripBox N)) :
    ((stripBoxEquiv N p).val : Fin 2 → ℤ) = stripBoxPoint N p := rfl

/-- **Box ≅ open-strip graph isomorphism**: the induced subgraph of `stripGraph` on the
centred box, transported by `stripBoxEquiv`, is the induced subgraph of `latticeGraph 2`
on the open strip `twoSiteOpenStrip (2N)`.  Both adjacencies reduce to the same
strip/lattice nearest-neighbour relation, which is invariant under the longitudinal shift
`(z, s) ↦ ![z + N, s]`. -/
theorem stripGraph_induce_map_eq (N : ℕ) :
    (Ambient.inducedGraph stripGraph (stripBox N)).map (stripBoxEquiv N).toEmbedding
      = Ambient.inducedGraph (latticeGraph 2) (twoSiteOpenStrip (2 * N)) := by
  ext u v
  rw [SimpleGraph.map_adj]
  -- Reduce induced-graph adjacency to the ambient graphs on the underlying values.
  have hindStrip : ∀ a b : ↑(stripBox N),
      (Ambient.inducedGraph stripGraph (stripBox N)).Adj a b ↔ stripGraph.Adj a.val b.val := by
    intro a b; rw [Ambient.inducedGraph_apply, SimpleGraph.induce_adj]
  have hindLat :
      (Ambient.inducedGraph (latticeGraph 2) (twoSiteOpenStrip (2 * N))).Adj u v
        ↔ (latticeGraph 2).Adj u.val v.val := by
    rw [Ambient.inducedGraph_apply, SimpleGraph.induce_adj]
  rw [hindLat]
  -- A characterization of `latticeGraph 2` adjacency on the strip points.
  have hlat : ∀ a b : ↑(stripBox N),
      (latticeGraph 2).Adj (stripBoxPoint N a) (stripBoxPoint N b)
        ↔ stripGraph.Adj a.val b.val := by
    intro a b
    rw [latticeGraph, stripBoxPoint, stripBoxPoint]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    obtain ⟨⟨a1, a2⟩, ha⟩ := a; obtain ⟨⟨b1, b2⟩, hb⟩ := b
    simp only [stripGraph, ne_eq]
    constructor
    · intro h
      by_cases hc : a2 = b2
      · subst hc
        refine Or.inr ⟨?_, rfl⟩
        simp only [sub_self, abs_zero, add_zero] at h
        have heq : |(a1 + (N:ℤ)) - (b1 + N)| = |a1 - b1| := by ring_nf
        rw [heq, Int.abs_eq_natAbs] at h
        exact_mod_cast h
      · refine Or.inl ⟨?_, hc⟩
        have ha2 := a2.isLt; have hb2 := b2.isLt
        have hne : (a2 : ℤ) ≠ (b2 : ℤ) := by simpa [Fin.val_inj] using hc
        have hd : |(a2 : ℤ) - (b2 : ℤ)| = 1 := by
          interval_cases h2a : a2.val <;> interval_cases h2b : b2.val <;> simp_all
        rw [hd] at h
        have h0 : |(a1 + (N:ℤ)) - (b1 + N)| = 0 := by omega
        have hsub : (a1 + (N:ℤ)) - (b1 + N) = 0 := by rwa [abs_eq_zero] at h0
        omega
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · subst h1
        have hd : |(a2 : ℤ) - (b2 : ℤ)| = 1 := by
          have ha2 := a2.isLt; have hb2 := b2.isLt
          have hne : (a2 : ℤ) ≠ (b2 : ℤ) := by simpa [Fin.val_inj] using h2
          interval_cases h2a : a2.val <;> interval_cases h2b : b2.val <;> simp_all
        have hz : |(a1 + (N:ℤ)) - (a1 + N)| = 0 := by simp
        rw [hz, zero_add, hd]
      · subst h2
        have hz : |(a2 : ℤ) - (a2 : ℤ)| = 0 := by simp
        rw [hz, add_zero]
        have heq : |(a1 + (N:ℤ)) - (b1 + N)| = |a1 - b1| := by ring_nf
        rw [heq, Int.abs_eq_natAbs]
        exact_mod_cast h1
  constructor
  · rintro ⟨a, b, hab, hu, hv⟩
    rw [hindStrip] at hab
    have key : (latticeGraph 2).Adj (stripBoxPoint N a) (stripBoxPoint N b) :=
      (hlat a b).mpr hab
    have hua : stripBoxPoint N a = u.val :=
      congrArg Subtype.val (by simpa using hu)
    have hvb : stripBoxPoint N b = v.val :=
      congrArg Subtype.val (by simpa using hv)
    rwa [hua, hvb] at key
  · intro huv
    refine ⟨(stripBoxEquiv N).symm u, (stripBoxEquiv N).symm v, ?_, ?_, ?_⟩
    · rw [hindStrip]
      apply (hlat _ _).mp
      have hu' : stripBoxPoint N ((stripBoxEquiv N).symm u) = u.val :=
        congrArg Subtype.val ((stripBoxEquiv N).apply_symm_apply u)
      have hv' : stripBoxPoint N ((stripBoxEquiv N).symm v) = v.val :=
        congrArg Subtype.val ((stripBoxEquiv N).apply_symm_apply v)
      rwa [hu', hv']
    · simp
    · simp

/-! ## Finite explicit-pair bound -/

/-- **Finite explicit-pair `K2` open-strip bound**: for a box `twoSiteOpenStrip M` large
enough (`c + sep ≤ M`), the correlation of the explicit same-transverse-site pair
`{![c, x], ![c + sep, x]}` decays as `k2StripPrefactor · exp(-mass · sep)`.  This
dissolves the dependent index type of `twoSiteInteractingOpenStripTwoPoint` by writing
`M = c + sep + r` and matching the explicit pair to the transported two-point observable. -/
theorem strip_pair_abs_le (p : IsingParams ℝ) (hp : p.h = 0) (hβJ : 0 < p.β * p.J)
    (x : Fin 2) (M c sep : ℕ) (hcsep : c + sep ≤ M) (hsep : 0 < sep)
    (hc : (![(c : ℤ), (x.val : ℤ)] : Fin 2 → ℤ) ∈ twoSiteOpenStrip M)
    (hcs : (![(c : ℤ) + (sep : ℤ), (x.val : ℤ)] : Fin 2 → ℤ) ∈ twoSiteOpenStrip M) :
    |correlation (Ambient.inducedGraph (latticeGraph 2) (twoSiteOpenStrip M)) p
        (({⟨![(c : ℤ), (x.val : ℤ)], hc⟩,
            ⟨![(c : ℤ) + (sep : ℤ), (x.val : ℤ)], hcs⟩} :
          Finset ↑(twoSiteOpenStrip M)))|
      ≤ k2StripPrefactor p hp x * Real.exp (-(twoSiteInteractingMass (p.β * p.J)) * sep) := by
  classical
  obtain ⟨r, rfl⟩ : ∃ r, M = c + sep + r := ⟨M - c - sep, by omega⟩
  -- The explicit pair equals the transported strip two-point observable.
  have hpair :
      ({⟨![(c : ℤ), (x.val : ℤ)], hc⟩,
          ⟨![(c : ℤ) + (sep : ℤ), (x.val : ℤ)], hcs⟩} :
        Finset ↑(twoSiteOpenStrip (c + sep + r)))
        = twoSiteInteractingOpenStripTwoPoint x c sep r := by
    rw [twoSiteInteractingOpenStripTwoPoint, twoSiteInteractingOpenSlabTwoPoint,
      Finset.map_insert, Finset.map_singleton]
    have hleft : (twoSiteOpenStripEquiv (c + sep + r)).toEmbedding
        (layerOpenLeftIndex c sep r, x)
        = (⟨![(c : ℤ), (x.val : ℤ)], hc⟩ : ↑(twoSiteOpenStrip (c + sep + r))) := by
      apply Subtype.ext
      simp only [Equiv.coe_toEmbedding, twoSiteOpenStripEquiv_apply_val,
        twoSiteOpenStripPoint_left]
    have hright : (twoSiteOpenStripEquiv (c + sep + r)).toEmbedding
        (layerOpenRightIndex c sep r, x)
        = (⟨![(c : ℤ) + (sep : ℤ), (x.val : ℤ)], hcs⟩ :
            ↑(twoSiteOpenStrip (c + sep + r))) := by
      apply Subtype.ext
      simp only [Equiv.coe_toEmbedding, twoSiteOpenStripEquiv_apply_val,
        twoSiteOpenStripPoint_right]
      funext k
      fin_cases k <;> simp
    rw [hleft, hright]
  rw [hpair]
  exact correlation_induced_latticeGraph_two_strip_abs_le_exp_neg_mass p hp hβJ x c sep r hsep

/-! ## Axis two-point observable and stagewise / infinite-volume decay -/

/-- The strip axis two-point observable: two same-transverse-site points at longitudinal
positions `0` and `sep`. -/
def stripAxisTwoPoint (x : Fin 2) (sep : ℕ) : Finset (ℤ × Fin 2) :=
  {((0 : ℤ), x), ((sep : ℤ), x)}

/-- **Stagewise centred-box `K2` open-strip decay**: at each exhaustion stage `N`, the
strip-axis two-point correlation is bounded by `k2StripPrefactor · exp(-mass · sep)`,
independently of `N`.  When the box contains the pair, transport along `stripBoxEquiv`
identifies it with the explicit open-strip pair (`strip_pair_abs_le`); otherwise the
correlation vanishes and the nonnegative constant bound is immediate. -/
theorem abs_correlationAlongExhaustion_stripGraph_axis_le
    (p : IsingParams ℝ) (hp : p.h = 0) (hβJ : 0 < p.β * p.J)
    (x : Fin 2) (sep : ℕ) (hsep : 0 < sep) (N : ℕ) :
    |Ambient.correlationAlongExhaustion stripGraph stripExhaustion p
        (stripAxisTwoPoint x sep) N|
      ≤ k2StripPrefactor p hp x * Real.exp (-(twoSiteInteractingMass (p.β * p.J)) * sep) := by
  classical
  by_cases hA : stripAxisTwoPoint x sep ⊆ stripExhaustion.volume N
  · -- Membership of the two endpoints in the box.
    have hmem0 : ((0 : ℤ), x) ∈ stripExhaustion.volume N :=
      hA (by simp [stripAxisTwoPoint])
    have hmemSep : ((sep : ℤ), x) ∈ stripExhaustion.volume N :=
      hA (by simp [stripAxisTwoPoint])
    have hsepN : sep ≤ N := by
      have := mem_stripBox.mp hmemSep
      simp only at this; omega
    -- Membership of the shifted explicit pair in the open strip `twoSiteOpenStrip (2N)`.
    have hc : (![((N : ℕ) : ℤ), (x.val : ℤ)] : Fin 2 → ℤ)
        ∈ twoSiteOpenStrip (2 * N) := by
      rw [mem_twoSiteOpenStrip]
      have := x.isLt
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      refine ⟨by positivity, by push_cast; omega, by positivity, by omega⟩
    have hcs : (![((N : ℕ) : ℤ) + (sep : ℤ), (x.val : ℤ)] : Fin 2 → ℤ)
        ∈ twoSiteOpenStrip (2 * N) := by
      rw [mem_twoSiteOpenStrip]
      have := x.isLt
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      refine ⟨by positivity, by push_cast; omega, by positivity, by omega⟩
    -- The lifted axis pair is the `stripBoxEquiv`-image of the explicit shifted pair.
    haveI : Fintype ((Ambient.inducedGraph stripGraph (stripBox N)).map
        (stripBoxEquiv N).toEmbedding).edgeSet :=
      (stripGraph_induce_map_eq N) ▸ inferInstance
    have hlift :
        (Ambient.liftFinset (stripAxisTwoPoint x sep) hA).map (stripBoxEquiv N).toEmbedding
          = ({⟨![((N : ℕ) : ℤ), (x.val : ℤ)], hc⟩,
              ⟨![((N : ℕ) : ℤ) + (sep : ℤ), (x.val : ℤ)], hcs⟩} :
              Finset ↑(twoSiteOpenStrip (2 * N))) := by
      have hpairlift : Ambient.liftFinset (stripAxisTwoPoint x sep) hA
          = ({⟨((0 : ℤ), x), hmem0⟩, ⟨((sep : ℤ), x), hmemSep⟩} :
              Finset ↑(stripBox N)) :=
        Ambient.liftFinset_pair hA hmem0 hmemSep
      rw [hpairlift, Finset.map_insert, Finset.map_singleton]
      have he0 : (stripBoxEquiv N).toEmbedding ⟨((0 : ℤ), x), hmem0⟩
          = (⟨![((N : ℕ) : ℤ), (x.val : ℤ)], hc⟩ : ↑(twoSiteOpenStrip (2 * N))) := by
        apply Subtype.ext
        simp only [Equiv.coe_toEmbedding, stripBoxEquiv_apply_val, stripBoxPoint]
        funext k; fin_cases k <;> simp
      have heSep : (stripBoxEquiv N).toEmbedding ⟨((sep : ℤ), x), hmemSep⟩
          = (⟨![((N : ℕ) : ℤ) + (sep : ℤ), (x.val : ℤ)], hcs⟩ :
              ↑(twoSiteOpenStrip (2 * N))) := by
        apply Subtype.ext
        simp only [Equiv.coe_toEmbedding, stripBoxEquiv_apply_val, stripBoxPoint]
        funext k
        fin_cases k
        · change ((sep : ℤ) + (N : ℤ)) = (N : ℤ) + (sep : ℤ)
          ring
        · simp
      rw [he0, heSep]
    have hbound := strip_pair_abs_le p hp hβJ x (2 * N) N sep (by omega) hsep hc hcs
    -- Transport the induced-box correlation to the open strip.
    have hcorr :
        correlation (Ambient.inducedGraph stripGraph (stripBox N)) p
            (Ambient.liftFinset (stripAxisTwoPoint x sep) hA)
          = correlation (Ambient.inducedGraph (latticeGraph 2) (twoSiteOpenStrip (2 * N))) p
              (({⟨![((N : ℕ) : ℤ), (x.val : ℤ)], hc⟩,
                  ⟨![((N : ℕ) : ℤ) + (sep : ℤ), (x.val : ℤ)], hcs⟩} :
                  Finset ↑(twoSiteOpenStrip (2 * N)))) := by
      rw [← hlift,
        ← correlation_map_equiv (stripBoxEquiv N)
          (Ambient.inducedGraph stripGraph (stripBox N)) p
          (Ambient.liftFinset (stripAxisTwoPoint x sep) hA)]
      exact correlation_congr_of_eq (stripGraph_induce_map_eq N) p _
    -- Unfold `correlationAlongExhaustion` on the goal, reduce the `dite` with `hA`,
    -- normalise the volume to `stripBox N`, and transport via `hcorr`.
    -- Transport the goal's correlation to the open strip entirely by rewriting *the goal*,
    -- with all `Fintype`-instances pinned to the canonical `fintypeEdgeSet` (available via the
    -- induced-graph `DecidableRel` instance above), so every rewrite is syntactic.
    rw [@Ambient.correlationAlongExhaustion_of_subset (ℤ × Fin 2) _ stripGraph stripExhaustion
        (fun n => (Ambient.inducedGraph stripGraph (stripExhaustion.volume n)).fintypeEdgeSet) p
        (stripAxisTwoPoint x sep) N hA]
    -- Reduce `stripExhaustion.volume N` to `stripBox N` in the `correlationΛ` (and its lifted
    -- observable) so the subsequent transport runs at the `stripBox N` vertex type.
    simp only [stripExhaustion_volume, Ambient.correlationΛ_apply]
    -- The goal's `correlation` (with the canonical `fintypeEdgeSet` instance) coincides with the
    -- LHS of the already-established transport `hcorr`; rewriting by `hcorr` swaps it for the
    -- open-strip correlation, which is bounded by `hbound`.  This avoids forcing any `whnf` on the
    -- expensive `FinCategory` edge-set instance of the mapped lattice graph.
    change |@correlation ↑(stripBox N) _ _ (Ambient.inducedGraph stripGraph (stripBox N))
        (Ambient.inducedGraph stripGraph (stripBox N)).fintypeEdgeSet p
        (Ambient.liftFinset (stripAxisTwoPoint x sep) hA)| ≤ _
    rw [hcorr]
    -- The goal now matches `hbound` up to the (`Subsingleton`) `Fintype`-edge-set instance of the
    -- induced lattice graph.  `convert` reconciles that instance structurally, avoiding any
    -- `whnf` on the expensive `FinCategory` edge-set instance that an `exact`/`simpa` would force.
    convert hbound using 3
  · simp only [Ambient.correlationAlongExhaustion, hA, dif_neg, not_false_iff, abs_zero]
    -- The RHS is nonnegative because it bounds an absolute value (e.g. at `M = 2*sep`).
    have hc : (![((sep : ℕ) : ℤ), (x.val : ℤ)] : Fin 2 → ℤ)
        ∈ twoSiteOpenStrip (2 * sep) := by
      rw [mem_twoSiteOpenStrip]
      have := x.isLt
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      refine ⟨by positivity, by push_cast; omega, by positivity, by omega⟩
    have hcs : (![((sep : ℕ) : ℤ) + (sep : ℤ), (x.val : ℤ)] : Fin 2 → ℤ)
        ∈ twoSiteOpenStrip (2 * sep) := by
      rw [mem_twoSiteOpenStrip]
      have := x.isLt
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      refine ⟨by positivity, by push_cast; omega, by positivity, by omega⟩
    exact (abs_nonneg _).trans
      (strip_pair_abs_le p hp hβJ x (2 * sep) sep sep (by omega) hsep hc hcs)

/-- **Infinite-volume `K2` open-strip exponential decay** (Glimm–Jaffe §17.1): the
project's infinite-volume two-point correlation of two same-transverse-site points
separated by `sep` along the axis of the two-row strip `ℤ × Fin 2` decays as
`k2StripPrefactor · exp(-mass · sep)`, with `mass = twoSiteInteractingMass (βJ)`.  This is
the interacting analogue of the free-field 1D capstone `twoPointFunction_one_eq_tanh_pow`:
the centred-box correlation is bounded by the constant `prefactor · exp(-mass · sep)` at
every stage (`abs_correlationAlongExhaustion_stripGraph_axis_le`), so the supremum is too. -/
theorem abs_correlationInfinite_stripGraph_axis_le
    (p : IsingParams ℝ) (hp : p.h = 0) (hβJ : 0 < p.β * p.J)
    (x : Fin 2) (sep : ℕ) (hsep : 0 < sep) :
    |Ambient.correlationInfinite stripGraph stripExhaustion p (stripAxisTwoPoint x sep)|
      ≤ k2StripPrefactor p hp x * Real.exp (-(twoSiteInteractingMass (p.β * p.J)) * sep) :=
  Ambient.abs_correlationInfinite_le_of_forall_abs_correlationAlongExhaustion_le _ _ _ _
    (fun N => abs_correlationAlongExhaustion_stripGraph_axis_le p hp hβJ x sep hsep N)

end TransferMatrix

end IsingModel
