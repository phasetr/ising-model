import IsingModel.TransferMatrix.TwoSiteInteractingOpenStripInfiniteVolume
import IsingModel.TransferMatrix.TwoSiteInteractingLayerOpenCrossBoundaryWindow

/-!
# Infinite-volume `K2` open-strip cross-transverse-site exponential decay (GJ §17.1)

This file generalizes the same-transverse-site infinite-volume `K2` open-strip
decay of `TwoSiteInteractingOpenStripInfiniteVolume` (#4142) to arbitrary
transverse sites `x y : Fin 2` and arbitrary longitudinal positions `a b : ℤ`.
The finite cross-site decay of `TwoSiteInteractingLayerOpenCrossBoundaryWindow`
(#4145) is transported, exactly as in the same-site route, to a centred box
exhaustion of the ambient strip lattice `ℤ × Fin 2`, and on to
`correlationInfinite`.

The decay rate is the same `mass = twoSiteInteractingMass (βJ) = -log(flipOdd /
top)`; only the prefactor changes from the single-mark spectral prefactor
`k2StripPrefactor` to the two-mark spectral prefactor `k2CrossStripPrefactor`,
which agrees with the former on the diagonal `x = y`
(`k2CrossStripPrefactor_self`).  Because the two-marked spectral prefactor is
symmetric under swapping marks when the two boundary vectors coincide
(`k2CrossStripPrefactor_comm`, from `markedMatrix_comm`), the general headline
holds for every distinct ordered pair `a ≠ b` with a single prefactor
`k2CrossStripPrefactor p hp x y`.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.1, pp. 304--306.
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.5, pp. 311--312.
-/

namespace IsingModel

namespace TransferMatrix

open scoped BigOperators
open SimpleGraph Finset
open Matrix

/-! ## The cross prefactor abbreviation -/

/-- The spectral prefactor of the finite cross-transverse-site `K2` open-strip
decay bound: the boundary *two*-marked spectral prefactor (left mark
`layerSpinAt x`, right mark `layerSpinAt y`) divided by the boundary spectral
partition prefactor of the boundary-balanced two-site interacting layer data.
On the diagonal `x = y` this reduces to `k2StripPrefactor`. -/
noncomputable def k2CrossStripPrefactor (p : IsingParams ℝ) (hp : p.h = 0)
    (x y : Fin 2) : ℝ :=
  (twoSiteInteractingLayerOrthogonalSpectralData p hp).boundaryTwoMarkedSpectralPrefactor
      (layerSpinAt x) (layerSpinAt y)
      (layerOpenBalancedBoundaryVector
        (layerInternalWeight (SimpleGraph.completeGraph (Fin 2)) p))
      (layerOpenBalancedBoundaryVector
        (layerInternalWeight (SimpleGraph.completeGraph (Fin 2)) p)) /
    (twoSiteInteractingLayerOrthogonalSpectralData p hp).boundarySpectralPartitionPrefactor
      (layerOpenBalancedBoundaryVector
        (layerInternalWeight (SimpleGraph.completeGraph (Fin 2)) p))
      twoSiteInteractingLayerTop (twoSiteInteractingTheta (p.β * p.J))

/-- On the diagonal `x = y` the cross prefactor reduces to the single-mark
`k2StripPrefactor` (via `boundaryTwoMarkedSpectralPrefactor_self`). -/
@[simp]
theorem k2CrossStripPrefactor_self (p : IsingParams ℝ) (hp : p.h = 0) (x : Fin 2) :
    k2CrossStripPrefactor p hp x x = k2StripPrefactor p hp x := by
  rw [k2CrossStripPrefactor, k2StripPrefactor,
    RealOrthogonalSpectralData.boundaryTwoMarkedSpectralPrefactor_self]

/-- **Mark-swap symmetry of the two-marked spectral prefactor** when the two
boundary vectors coincide: `boundaryTwoMarkedSpectralPrefactor f g v v =
boundaryTwoMarkedSpectralPrefactor g f v v`.  The triple sum
`∑ᵢⱼₗ |bc v i · M f i j · M g j l · bc v l|` maps to the `g, f` version by the
reindexing `i ↔ l` (with `j` fixed) together with the symmetry
`markedMatrix_comm` of each marked matrix and commutativity of the absolute
product. -/
theorem boundaryTwoMarkedSpectralPrefactor_comm_of_eq_boundary
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (f g v : Ω → ℝ) :
    E.boundaryTwoMarkedSpectralPrefactor f g v v =
      E.boundaryTwoMarkedSpectralPrefactor g f v v := by
  rw [RealOrthogonalSpectralData.boundaryTwoMarkedSpectralPrefactor,
    RealOrthogonalSpectralData.boundaryTwoMarkedSpectralPrefactor]
  -- Pointwise: term of the `f g` sum at `(i, j, l)` equals the `g f` term at `(l, j, i)`.
  have hterm : ∀ i j l : Ω,
      |E.boundaryCoordinates v i * E.markedMatrix f i j *
          E.markedMatrix g j l * E.boundaryCoordinates v l|
        = |E.boundaryCoordinates v l * E.markedMatrix g l j *
            E.markedMatrix f j i * E.boundaryCoordinates v i| := by
    intro i j l
    rw [E.markedMatrix_comm g l j, E.markedMatrix_comm f j i]
    congr 1
    ring
  -- Rewrite the `f g` triple sum termwise into the `g f` term evaluated at `(l, j, i)`.
  rw [Finset.sum_congr rfl (fun i _ =>
        Finset.sum_congr rfl (fun j _ =>
          Finset.sum_congr rfl (fun l _ => hterm i j l)))]
  -- Reindex `∑ i ∑ j ∑ l G(l, j, i) = ∑ i ∑ j ∑ l G(i, j, l)` by swapping the
  -- outermost (`i`) and innermost (`l`) summation variables.
  rw [show (∑ i, ∑ j, ∑ l, |E.boundaryCoordinates v l * E.markedMatrix g l j *
          E.markedMatrix f j i * E.boundaryCoordinates v i|)
      = ∑ i, ∑ l, ∑ j, |E.boundaryCoordinates v l * E.markedMatrix g l j *
          E.markedMatrix f j i * E.boundaryCoordinates v i|
      from Finset.sum_congr rfl (fun i _ => Finset.sum_comm)]
  rw [Finset.sum_comm]
  -- Finally swap the remaining inner two summations for each fixed outer index.
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_comm]

/-- **Mark-swap symmetry of `k2CrossStripPrefactor`**: swapping the two
transverse marks leaves the cross prefactor unchanged, because the two boundary
vectors coincide.  Reduces to
`boundaryTwoMarkedSpectralPrefactor_comm_of_eq_boundary`. -/
theorem k2CrossStripPrefactor_comm (p : IsingParams ℝ) (hp : p.h = 0)
    (x y : Fin 2) :
    k2CrossStripPrefactor p hp x y = k2CrossStripPrefactor p hp y x := by
  rw [k2CrossStripPrefactor, k2CrossStripPrefactor,
    boundaryTwoMarkedSpectralPrefactor_comm_of_eq_boundary]

/-! ## Cross finite slab observable and its strip image -/

/-- The `K2` open-slab cross-transverse-site two-point observable: the left
endpoint carries transverse site `x`, the right endpoint carries `y`. -/
def twoSiteInteractingOpenSlabCrossTwoPoint (x y : Fin 2) (left sep right : ℕ) :
    Finset (LayerOpenSlabSite (left + sep + right) (Fin 2)) :=
  {Prod.mk (layerOpenLeftIndex left sep right) x,
    Prod.mk (layerOpenRightIndex left sep right) y}

/-- The transported strip cross two-point observable. -/
noncomputable def twoSiteInteractingOpenStripCrossTwoPoint (x y : Fin 2)
    (left sep right : ℕ) :
    Finset ↑(twoSiteOpenStrip (left + sep + right)) :=
  (twoSiteInteractingOpenSlabCrossTwoPoint x y left sep right).map
    (twoSiteOpenStripEquiv (left + sep + right)).toEmbedding

/-- **Mass-form cross interacting decay on the induced ambient `latticeGraph 2`
strip**: finite cross-transverse-site decay with rate `m = -log(flipOdd / top)`
and uniform (left/right-independent) prefactor `k2CrossStripPrefactor`. -/
theorem correlation_induced_latticeGraph_two_strip_cross_abs_le_exp_neg_mass
    (p : IsingParams ℝ) (hp : p.h = 0) (hβJ : 0 < p.β * p.J)
    (x y : Fin 2) (left sep right : ℕ) (hsep : 0 < sep) :
    |correlation (Ambient.inducedGraph (latticeGraph 2)
          (twoSiteOpenStrip (left + sep + right))) p
        (twoSiteInteractingOpenStripCrossTwoPoint x y left sep right)|
      ≤ k2CrossStripPrefactor p hp x y *
          Real.exp (-(twoSiteInteractingMass (p.β * p.J)) * sep) := by
  -- Mass form of the finite slab cross bound via `theta ^ sep = exp(-mass·sep)`.
  have hslab :
      |correlation
          (layerOpenSlabGraph (S := Fin 2) (SimpleGraph.completeGraph (Fin 2))
            (layerIdentityTransitionPairs (Fin 2)) (left + sep + right)) p
          (twoSiteInteractingOpenSlabCrossTwoPoint x y left sep right)|
        ≤ k2CrossStripPrefactor p hp x y *
            Real.exp (-(twoSiteInteractingMass (p.β * p.J)) * sep) := by
    rw [twoSiteInteractingOpenSlabCrossTwoPoint,
      ← twoSiteInteractingTheta_pow_eq_exp_neg_mass hβJ sep, k2CrossStripPrefactor]
    exact correlation_twoSiteInteractingLayerOpenSlabGraph_cross_abs_le_of_simpleSpectrum
      p hp hβJ x y left sep right hsep
  exact abs_correlation_induced_latticeGraph_two_strip_le_of_openSlab _ p
    (twoSiteInteractingOpenSlabCrossTwoPoint x y left sep right) hslab

/-! ## Finite explicit-pair cross bound -/

/-- **Finite explicit-pair cross `K2` open-strip bound**: for a box
`twoSiteOpenStrip M` large enough (`c + sep ≤ M`), the correlation of the
explicit cross pair `{![c, x], ![c + sep, y]}` decays as
`k2CrossStripPrefactor · exp(-mass · sep)`.  Mirrors `strip_pair_abs_le` with the
right endpoint now carrying the transverse site `y`. -/
theorem strip_pair_cross_abs_le (p : IsingParams ℝ) (hp : p.h = 0)
    (hβJ : 0 < p.β * p.J) (x y : Fin 2) (M c sep : ℕ) (hcsep : c + sep ≤ M)
    (hsep : 0 < sep)
    (hc : (![(c : ℤ), (x.val : ℤ)] : Fin 2 → ℤ) ∈ twoSiteOpenStrip M)
    (hcs : (![(c : ℤ) + (sep : ℤ), (y.val : ℤ)] : Fin 2 → ℤ) ∈ twoSiteOpenStrip M) :
    |correlation (Ambient.inducedGraph (latticeGraph 2) (twoSiteOpenStrip M)) p
        (({⟨![(c : ℤ), (x.val : ℤ)], hc⟩,
            ⟨![(c : ℤ) + (sep : ℤ), (y.val : ℤ)], hcs⟩} :
          Finset ↑(twoSiteOpenStrip M)))|
      ≤ k2CrossStripPrefactor p hp x y *
          Real.exp (-(twoSiteInteractingMass (p.β * p.J)) * sep) := by
  classical
  obtain ⟨r, rfl⟩ : ∃ r, M = c + sep + r := ⟨M - c - sep, by omega⟩
  -- The explicit cross pair equals the transported strip cross two-point observable.
  have hpair :
      ({⟨![(c : ℤ), (x.val : ℤ)], hc⟩,
          ⟨![(c : ℤ) + (sep : ℤ), (y.val : ℤ)], hcs⟩} :
        Finset ↑(twoSiteOpenStrip (c + sep + r)))
        = twoSiteInteractingOpenStripCrossTwoPoint x y c sep r := by
    rw [twoSiteInteractingOpenStripCrossTwoPoint, twoSiteInteractingOpenSlabCrossTwoPoint,
      Finset.map_insert, Finset.map_singleton]
    have hleft : (twoSiteOpenStripEquiv (c + sep + r)).toEmbedding
        (layerOpenLeftIndex c sep r, x)
        = (⟨![(c : ℤ), (x.val : ℤ)], hc⟩ : ↑(twoSiteOpenStrip (c + sep + r))) := by
      apply Subtype.ext
      simp only [Equiv.coe_toEmbedding, twoSiteOpenStripEquiv_apply_val,
        twoSiteOpenStripPoint_left]
    have hright : (twoSiteOpenStripEquiv (c + sep + r)).toEmbedding
        (layerOpenRightIndex c sep r, y)
        = (⟨![(c : ℤ) + (sep : ℤ), (y.val : ℤ)], hcs⟩ :
            ↑(twoSiteOpenStrip (c + sep + r))) := by
      apply Subtype.ext
      simp only [Equiv.coe_toEmbedding, twoSiteOpenStripEquiv_apply_val,
        twoSiteOpenStripPoint_right]
      funext k
      fin_cases k <;> simp
    rw [hleft, hright]
  rw [hpair]
  exact correlation_induced_latticeGraph_two_strip_cross_abs_le_exp_neg_mass
    p hp hβJ x y c sep r hsep

/-! ## Strip cross two-point observable and stagewise / infinite-volume decay -/

/-- The strip cross two-point observable: two points at longitudinal positions
`a, b : ℤ` with (possibly distinct) transverse sites `x, y`. -/
def stripTwoPoint (x y : Fin 2) (a b : ℤ) : Finset (ℤ × Fin 2) :=
  {((a : ℤ), x), ((b : ℤ), y)}

/-- Pair symmetry of the strip cross two-point observable: swapping the two
endpoints (positions and transverse sites together) leaves the unordered pair
unchanged. -/
theorem stripTwoPoint_comm (x y : Fin 2) (a b : ℤ) :
    stripTwoPoint x y a b = stripTwoPoint y x b a := by
  rw [stripTwoPoint, stripTwoPoint, Finset.pair_comm]

/-- **Stagewise centred-box cross `K2` open-strip decay for `a < b`**: at each
exhaustion stage `N`, the strip cross two-point correlation is bounded by
`k2CrossStripPrefactor · exp(-mass · (b - a).natAbs)`, independently of `N`.
When the box contains the pair, transport along `stripBoxEquiv` identifies it
with the explicit open-strip cross pair (`strip_pair_cross_abs_le`); otherwise
the correlation vanishes and the nonnegative constant bound is immediate. -/
theorem abs_correlationAlongExhaustion_stripGraph_cross_ordered_le
    (p : IsingParams ℝ) (hp : p.h = 0) (hβJ : 0 < p.β * p.J)
    (x y : Fin 2) (a b : ℤ) (hab : a < b) (N : ℕ) :
    |Ambient.correlationAlongExhaustion stripGraph stripExhaustion p
        (stripTwoPoint x y a b) N|
      ≤ k2CrossStripPrefactor p hp x y *
          Real.exp (-(twoSiteInteractingMass (p.β * p.J)) * (b - a).natAbs) := by
  classical
  by_cases hA : stripTwoPoint x y a b ⊆ stripExhaustion.volume N
  · -- Membership of the two endpoints in the box.
    have hmemA : ((a : ℤ), x) ∈ stripExhaustion.volume N :=
      hA (by simp [stripTwoPoint])
    have hmemB : ((b : ℤ), y) ∈ stripExhaustion.volume N :=
      hA (by simp [stripTwoPoint])
    have hboxA := mem_stripBox.mp hmemA
    have hboxB := mem_stripBox.mp hmemB
    simp only at hboxA hboxB
    -- Set `c := (a + N).toNat`, `sep := (b - a).toNat`.
    set c : ℕ := (a + N).toNat with hc_def
    set sep : ℕ := (b - a).toNat with hsep_def
    have hcN : ((c : ℤ)) = a + N := by rw [hc_def]; omega
    have hsepN : ((sep : ℤ)) = b - a := by rw [hsep_def]; omega
    have hsep_pos : 0 < sep := by omega
    have hcsep : c + sep ≤ 2 * N := by omega
    have hsep_eq : sep = (b - a).natAbs := by rw [hsep_def]; omega
    -- Membership of the shifted explicit cross pair in `twoSiteOpenStrip (2N)`.
    have hc : (![(c : ℤ), (x.val : ℤ)] : Fin 2 → ℤ)
        ∈ twoSiteOpenStrip (2 * N) := by
      rw [mem_twoSiteOpenStrip]
      have := x.isLt
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      refine ⟨by omega, by push_cast; omega, by positivity, by omega⟩
    have hcs : (![(c : ℤ) + (sep : ℤ), (y.val : ℤ)] : Fin 2 → ℤ)
        ∈ twoSiteOpenStrip (2 * N) := by
      rw [mem_twoSiteOpenStrip]
      have := y.isLt
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      refine ⟨by omega, by push_cast; omega, by positivity, by omega⟩
    -- The lifted cross pair is the `stripBoxEquiv`-image of the explicit shifted pair.
    haveI : Fintype ((Ambient.inducedGraph stripGraph (stripBox N)).map
        (stripBoxEquiv N).toEmbedding).edgeSet :=
      (stripGraph_induce_map_eq N) ▸ inferInstance
    have hlift :
        (Ambient.liftFinset (stripTwoPoint x y a b) hA).map (stripBoxEquiv N).toEmbedding
          = ({⟨![(c : ℤ), (x.val : ℤ)], hc⟩,
              ⟨![(c : ℤ) + (sep : ℤ), (y.val : ℤ)], hcs⟩} :
              Finset ↑(twoSiteOpenStrip (2 * N))) := by
      have hpairlift : Ambient.liftFinset (stripTwoPoint x y a b) hA
          = ({⟨((a : ℤ), x), hmemA⟩, ⟨((b : ℤ), y), hmemB⟩} :
              Finset ↑(stripBox N)) :=
        Ambient.liftFinset_pair hA hmemA hmemB
      rw [hpairlift, Finset.map_insert, Finset.map_singleton]
      have heA : (stripBoxEquiv N).toEmbedding ⟨((a : ℤ), x), hmemA⟩
          = (⟨![(c : ℤ), (x.val : ℤ)], hc⟩ : ↑(twoSiteOpenStrip (2 * N))) := by
        apply Subtype.ext
        simp only [Equiv.coe_toEmbedding, stripBoxEquiv_apply_val, stripBoxPoint]
        funext k
        fin_cases k
        · change a + (N : ℤ) = (c : ℤ); rw [hcN]
        · simp
      have heB : (stripBoxEquiv N).toEmbedding ⟨((b : ℤ), y), hmemB⟩
          = (⟨![(c : ℤ) + (sep : ℤ), (y.val : ℤ)], hcs⟩ :
              ↑(twoSiteOpenStrip (2 * N))) := by
        apply Subtype.ext
        simp only [Equiv.coe_toEmbedding, stripBoxEquiv_apply_val, stripBoxPoint]
        funext k
        fin_cases k
        · change b + (N : ℤ) = (c : ℤ) + (sep : ℤ); rw [hcN, hsepN]; ring
        · simp
      rw [heA, heB]
    have hbound :=
      strip_pair_cross_abs_le p hp hβJ x y (2 * N) c sep hcsep hsep_pos hc hcs
    -- Transport the induced-box correlation to the open strip.
    have hcorr :
        correlation (Ambient.inducedGraph stripGraph (stripBox N)) p
            (Ambient.liftFinset (stripTwoPoint x y a b) hA)
          = correlation (Ambient.inducedGraph (latticeGraph 2) (twoSiteOpenStrip (2 * N))) p
              (({⟨![(c : ℤ), (x.val : ℤ)], hc⟩,
                  ⟨![(c : ℤ) + (sep : ℤ), (y.val : ℤ)], hcs⟩} :
                  Finset ↑(twoSiteOpenStrip (2 * N)))) := by
      rw [← hlift,
        ← correlation_map_equiv (stripBoxEquiv N)
          (Ambient.inducedGraph stripGraph (stripBox N)) p
          (Ambient.liftFinset (stripTwoPoint x y a b) hA)]
      exact correlation_congr_of_eq (stripGraph_induce_map_eq N) p _
    -- Transport the goal's correlation to the open strip and apply `hbound`.
    rw [@Ambient.correlationAlongExhaustion_of_subset (ℤ × Fin 2) _ stripGraph stripExhaustion
        (fun n => (Ambient.inducedGraph stripGraph (stripExhaustion.volume n)).fintypeEdgeSet) p
        (stripTwoPoint x y a b) N hA]
    simp only [stripExhaustion_volume, Ambient.correlationΛ_apply]
    change |@correlation ↑(stripBox N) _ _ (Ambient.inducedGraph stripGraph (stripBox N))
        (Ambient.inducedGraph stripGraph (stripBox N)).fintypeEdgeSet p
        (Ambient.liftFinset (stripTwoPoint x y a b) hA)| ≤ _
    rw [hcorr, ← hsep_eq]
    convert hbound using 3
  · simp only [Ambient.correlationAlongExhaustion, hA, dif_neg, not_false_iff, abs_zero]
    -- The RHS is nonnegative because it bounds an absolute value.
    set sep : ℕ := (b - a).natAbs with hsep_def
    have hsep_pos : 0 < sep := by rw [hsep_def]; omega
    have hc : (![((sep : ℕ) : ℤ), (x.val : ℤ)] : Fin 2 → ℤ)
        ∈ twoSiteOpenStrip (2 * sep) := by
      rw [mem_twoSiteOpenStrip]
      have := x.isLt
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      refine ⟨by positivity, by push_cast; omega, by positivity, by omega⟩
    have hcs : (![((sep : ℕ) : ℤ) + (sep : ℤ), (y.val : ℤ)] : Fin 2 → ℤ)
        ∈ twoSiteOpenStrip (2 * sep) := by
      rw [mem_twoSiteOpenStrip]
      have := y.isLt
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      refine ⟨by positivity, by push_cast; omega, by positivity, by omega⟩
    have hbd := strip_pair_cross_abs_le p hp hβJ x y (2 * sep) sep sep
      (by omega) hsep_pos hc hcs
    exact (abs_nonneg _).trans hbd

/-- **Infinite-volume cross `K2` open-strip exponential decay for `a < b`**: the
infinite-volume two-point correlation of two points at longitudinal positions
`a < b` and transverse sites `x, y` along the two-row strip `ℤ × Fin 2` decays as
`k2CrossStripPrefactor · exp(-mass · (b - a).natAbs)`. -/
theorem abs_correlationInfinite_stripGraph_cross_ordered_le
    (p : IsingParams ℝ) (hp : p.h = 0) (hβJ : 0 < p.β * p.J)
    (x y : Fin 2) (a b : ℤ) (hab : a < b) :
    |Ambient.correlationInfinite stripGraph stripExhaustion p (stripTwoPoint x y a b)|
      ≤ k2CrossStripPrefactor p hp x y *
          Real.exp (-(twoSiteInteractingMass (p.β * p.J)) * (b - a).natAbs) :=
  Ambient.abs_correlationInfinite_le_of_forall_abs_correlationAlongExhaustion_le _ _ _ _
    (fun N => abs_correlationAlongExhaustion_stripGraph_cross_ordered_le p hp hβJ x y a b hab N)

/-! ## General headline -/

/-- **Infinite-volume `K2` open-strip cross-transverse-site exponential decay**
(Glimm–Jaffe §17.1): for any two distinct longitudinal positions `a ≠ b` and any
transverse sites `x y : Fin 2`, the infinite-volume two-point correlation of the
strip points `(a, x)` and `(b, y)` decays as
`k2CrossStripPrefactor · exp(-mass · (a - b).natAbs)`, with
`mass = twoSiteInteractingMass (βJ)`.  This generalizes the same-site headline
`abs_correlationInfinite_stripGraph_axis_le` (#4142) to arbitrary positions and
transverse sites.

For `a < b` this is `abs_correlationInfinite_stripGraph_cross_ordered_le`
directly.  For `a > b` the unordered pair symmetry `stripTwoPoint_comm` swaps the
problem to `stripTwoPoint y x b a` with `b < a`, and the swapped prefactor
`k2CrossStripPrefactor p hp y x` is rewritten back to `k2CrossStripPrefactor p hp
x y` via `k2CrossStripPrefactor_comm`. -/
theorem abs_correlationInfinite_stripGraph_cross_le
    (p : IsingParams ℝ) (hp : p.h = 0) (hβJ : 0 < p.β * p.J)
    (x y : Fin 2) (a b : ℤ) (hab : a ≠ b) :
    |Ambient.correlationInfinite stripGraph stripExhaustion p (stripTwoPoint x y a b)|
      ≤ k2CrossStripPrefactor p hp x y *
          Real.exp (-(twoSiteInteractingMass (p.β * p.J)) * (a - b).natAbs) := by
  rcases lt_trichotomy a b with hlt | heq | hgt
  · -- `a < b`: direct ordered bound, with `(a - b).natAbs = (b - a).natAbs`.
    have hnat : (a - b).natAbs = (b - a).natAbs := by omega
    rw [hnat]
    exact abs_correlationInfinite_stripGraph_cross_ordered_le p hp hβJ x y a b hlt
  · exact absurd heq hab
  · -- `a > b`: swap the pair to `stripTwoPoint y x b a` with `b < a`.
    rw [stripTwoPoint_comm, k2CrossStripPrefactor_comm]
    exact abs_correlationInfinite_stripGraph_cross_ordered_le p hp hβJ y x b a hgt

end TransferMatrix

end IsingModel
