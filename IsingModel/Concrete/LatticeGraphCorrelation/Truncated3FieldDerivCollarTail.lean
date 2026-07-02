import IsingModel.Concrete.LatticeGraphCorrelation.Truncated2GeneralFieldFiniteVolumeMajorant
import IsingModel.AmbientLattice.Exhaustion

/-!
# Tail/collar uniform-smallness bound for the ∂/∂h site-sum (GJ Thm 17.6.1)

Brick 3 toward the `h`-derivative of the connected two-point function on
`ℤ^d` (tracking issue #4413), sitting strictly between brick 2 (the field-
and volume-uniform summable majorant, `Truncated2GeneralFieldFiniteVolumeMajorant.lean`)
and the finite-head equicontinuity "wall" of the eventual capstone.  This is
the *tail/collar* domination layer of the head/collar/tail split behind
Glimm--Jaffe Theorem 17.6.1 (*Quantum Physics*, 2nd ed., p. 313): a pure
Weierstrass-`M`-test unit that touches **no** infinite-volume object, **no**
equicontinuity, and **no** derivative-limit machinery.

Writing `m = simonLiebRate β J d` and, for a fixed site `a`,
`g_a(x) = exp(m) · exp(-m · d_{ℓ¹}(a, x))` (brick 2's per-site majorant term),
this file proves the two Weierstrass estimates:

* **(3a)** `tendsto_finiteVolumeMajorant_compl_atTop_zero`: the two-tail
  majorant complement `∑_{x ∉ Λ_N} g_i(x) + ∑_{x ∉ Λ_N} g_j(x)` tends to `0`
  as the cutoff `N → ∞`.  No summability hypothesis is needed
  (`tendsto_tsum_compl_atTop_zero` is unconditional); it is reindexed from the
  `Finset`-`atTop` complement limit along the exhaustion by
  `Exhaustion.tendsto_volume_atTop`.
* **(3b)** `sum_abs_truncated3_collar_le_majorant_tail`: over any bare cutoff
  `Λcut ⊆ Λfull`, the collar off-diagonal Ursell site-sum
  `∑_{k ∈ Λfull, k ∉ Λcut} |truncated3(i, j, k)|` is bounded, **uniformly in the
  volume and in the field `h ≥ 0`**, by the complement tsums
  `∑_{x ∉ Λcut} g_i(x) + ∑_{x ∉ Λcut} g_j(x)` that (3a) makes vanish.  The chain
  is brick 1 `abs_truncated3_le` followed by two applications of brick 2a
  `truncated2_inducedLatticeGraph_le_exp_neg_simonLiebRate_of_field_nonneg`, then
  `Finset.sum_add_distrib` and a complement reindex of brick 2's
  `sum_majorant_subtype_le_tsum` move.

Since `i, j ∈ Λcut` and every collar index `k ∉ Λcut` satisfies `k ≠ i, j`, no
degenerate diagonal `-2⟨σ⟩τ₂` term appears on the collar; brick 3 is stated
purely in `truncated3`.  The symmetric infinite-volume `g'`-tail (3c) pulls in
`U^∞`/`g'` scaffolding shared with the capstone and is deferred there.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Theorem 17.6.1 (p. 313);
  §4.3, Cor. 4.3.4 (GHS), Cor. 4.3.3 (GKS-II); §18.7 (exponential decay).
* Fernández--Fröhlich--Sokal, *Random Walks, Critical Phenomena, and
  Triviality* (1992), Ch 12 (Simon--Lieb decay).
-/

namespace IsingModel

namespace Ambient

open Finset

/-- **(3a) The majorant tail vanishes** (GJ Thm 17.6.1, p. 313, Weierstrass
`M`-test tail): for a positive Simon--Lieb rate `m = simonLiebRate β J d` and
fixed sites `i, j`, the two-tail complement majorant
`∑_{x ∉ Λ_N} g_i(x) + ∑_{x ∉ Λ_N} g_j(x)`, with
`g_a(x) = exp(m) · exp(-m · d_{ℓ¹}(a, x))`, tends to `0` as the exhaustion
cutoff `N → ∞`.

The tail-to-zero mechanism is unconditional (`tendsto_tsum_compl_atTop_zero`
needs no summability hypothesis); the `Finset`-`atTop` complement limit is
reindexed along the `ℕ`-indexed exhaustion by `Exhaustion.tendsto_volume_atTop`.
The rate positivity `hm` is kept as the intended high-temperature regime
marker. -/
theorem tendsto_finiteVolumeMajorant_compl_atTop_zero
    {d : ℕ} {β J : ℝ} (_hm : 0 < simonLiebRate β J d)
    (Λ : Exhaustion (Fin d → ℤ)) (i j : Fin d → ℤ) :
    Filter.Tendsto
      (fun N : ℕ =>
        (∑' x : {x : Fin d → ℤ // x ∉ Λ.volume N},
            Real.exp (simonLiebRate β J d)
              * Real.exp (-(simonLiebRate β J d)
                  * (latticeDistance d i (x : Fin d → ℤ) : ℝ)))
        + (∑' x : {x : Fin d → ℤ // x ∉ Λ.volume N},
            Real.exp (simonLiebRate β J d)
              * Real.exp (-(simonLiebRate β J d)
                  * (latticeDistance d j (x : Fin d → ℤ) : ℝ))))
      Filter.atTop (nhds 0) := by
  have Ti := (tendsto_tsum_compl_atTop_zero
      (fun x : Fin d → ℤ => Real.exp (simonLiebRate β J d)
        * Real.exp (-(simonLiebRate β J d) * (latticeDistance d i x : ℝ)))).comp
      Λ.tendsto_volume_atTop
  have Tj := (tendsto_tsum_compl_atTop_zero
      (fun x : Fin d → ℤ => Real.exp (simonLiebRate β J d)
        * Real.exp (-(simonLiebRate β J d) * (latticeDistance d j x : ℝ)))).comp
      Λ.tendsto_volume_atTop
  simpa using Ti.add Tj

/-- **Finite complement site-sum bounded by the complement majorant tsum**:
for a positive Simon--Lieb rate and any finset `T` of lattice sites all lying
outside the cutoff (`y ∈ T → y ∉ Λcut`), the finite sum of the majorant term
`g_a(y) = exp(m) · exp(-m · d_{ℓ¹}(a, y))` over `T` is bounded by the full
complement tsum over `{x : ℤ^d ∣ x ∉ Λcut}`.  The complement analogue of
brick 2's `sum_majorant_subtype_le_tsum`: `T` is transported to the complement
subtype by `Finset.sum_subtype_of_mem`, where summability is the
`Subtype.val`-restriction of `summable_truncated2FiniteVolumeMajorant` and each
term is non-negative, whence `Summable.sum_le_tsum` applies.  (Stated over a
value-finset `T` with the `∉Λcut` side-condition rather than over a subtype
finset, so that the caller's collar reindex uses only the pattern-friendly
`Finset.sum_image`.) -/
private lemma sum_majorant_collar_le_tsum_compl
    {d : ℕ} (Λcut : Finset (Fin d → ℤ)) {β J : ℝ} (hm : 0 < simonLiebRate β J d)
    (a : Fin d → ℤ) (T : Finset (Fin d → ℤ)) (hT : ∀ y ∈ T, y ∉ Λcut) :
    ∑ y ∈ T, (Real.exp (simonLiebRate β J d)
        * Real.exp (-(simonLiebRate β J d) * (latticeDistance d a y : ℝ)))
      ≤ ∑' x : {x : Fin d → ℤ // x ∉ Λcut}, (Real.exp (simonLiebRate β J d)
          * Real.exp (-(simonLiebRate β J d)
              * (latticeDistance d a (x : Fin d → ℤ) : ℝ))) := by
  have hsummable : Summable (fun x : {x : Fin d → ℤ // x ∉ Λcut} =>
      Real.exp (simonLiebRate β J d)
        * Real.exp (-(simonLiebRate β J d)
            * (latticeDistance d a (x : Fin d → ℤ) : ℝ))) :=
    (summable_truncated2FiniteVolumeMajorant hm a).comp_injective Subtype.coe_injective
  calc ∑ y ∈ T, (Real.exp (simonLiebRate β J d)
          * Real.exp (-(simonLiebRate β J d) * (latticeDistance d a y : ℝ)))
      = ∑ x ∈ T.subtype (· ∉ Λcut), (Real.exp (simonLiebRate β J d)
          * Real.exp (-(simonLiebRate β J d)
              * (latticeDistance d a (x : Fin d → ℤ) : ℝ))) :=
        (Finset.sum_subtype_of_mem _ hT).symm
    _ ≤ ∑' x : {x : Fin d → ℤ // x ∉ Λcut}, (Real.exp (simonLiebRate β J d)
          * Real.exp (-(simonLiebRate β J d)
              * (latticeDistance d a (x : Fin d → ℤ) : ℝ))) :=
        Summable.sum_le_tsum _ (fun x _ => by positivity) hsummable

/-- **(3b) The collar bound, volume- and field-uniform** (GJ Thm 17.6.1,
p. 313): over any bare cutoff `Λcut ⊆ Λfull`, on the `Preconnected` finite
induced subgraph `inducedGraph (latticeGraph d) Λfull`, for a ferromagnetic
field `⟨J, h, β⟩` with `h ≥ 0`, strict high temperature `0 < β J · 2d < 1`, and
distinct sites `i ≠ j` with `i, j ∈ Λcut`, the collar off-diagonal Ursell
site-sum is bounded by the two complement tsums:
`∑_{k ∈ Λfull, k ∉ Λcut} |truncated3(i,j,k)|
≤ ∑_{x ∉ Λcut} g_i(x) + ∑_{x ∉ Λcut} g_j(x)`,
`g_a(x) = exp(m) · exp(-m · d_{ℓ¹}(a,x))`, `m = simonLiebRate β J d`, with the
bound **independent of `h` and of `Λfull`** (it depends only on `Λcut`, the pair
`i, j`, and the rate).

Since `i, j ∈ Λcut` and each collar index `k ∉ Λcut` has `k ≠ i`, `k ≠ j`, no
degenerate diagonal term appears.  Chain: brick 1 `abs_truncated3_le` gives
`|U₃(i,j,k)| ≤ τ₂(i,k) + τ₂(j,k)`; brick 2a
`truncated2_inducedLatticeGraph_le_exp_neg_simonLiebRate_of_field_nonneg` bounds
each `τ₂(a,k) ≤ g_a(k)` (reachability from `Preconnected`); `Finset.sum_add_distrib`
splits the two collar site-sums, each dominated by its complement tsum via the
complement reindex `sum_majorant_collar_le_tsum_compl`. -/
theorem sum_abs_truncated3_collar_le_majorant_tail
    (d : ℕ) (Λcut Λfull : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λfull).edgeSet]
    (_hsub : Λcut ⊆ Λfull)
    {β J h : ℝ} (hf : Ferromagnetic (⟨J, h, β⟩ : IsingParams ℝ))
    (hβJ2d_pos : 0 < β * J * (2 * (d : ℝ))) (hβJ2d_lt : β * J * (2 * (d : ℝ)) < 1)
    (hconn : (inducedGraph (IsingModel.latticeGraph d) Λfull).Preconnected)
    {i j : ↑Λfull} (hi : (i : Fin d → ℤ) ∈ Λcut) (hj : (j : Fin d → ℤ) ∈ Λcut)
    (hij : i ≠ j) :
    ∑ k ∈ Finset.univ.filter (fun k : ↑Λfull => (k : Fin d → ℤ) ∉ Λcut),
        |truncated3 (inducedGraph (IsingModel.latticeGraph d) Λfull)
          (⟨J, h, β⟩ : IsingParams ℝ) i j k|
      ≤ (∑' x : {x : Fin d → ℤ // x ∉ Λcut},
            Real.exp (simonLiebRate β J d)
              * Real.exp (-(simonLiebRate β J d)
                  * (latticeDistance d (i : Fin d → ℤ) (x : Fin d → ℤ) : ℝ)))
        + (∑' x : {x : Fin d → ℤ // x ∉ Λcut},
            Real.exp (simonLiebRate β J d)
              * Real.exp (-(simonLiebRate β J d)
                  * (latticeDistance d (j : Fin d → ℤ) (x : Fin d → ℤ) : ℝ))) := by
  have hβJ2d_le : β * J * (2 * (d : ℝ)) ≤ 1 := hβJ2d_lt.le
  have hm : 0 < simonLiebRate β J d := simonLiebRate_pos hβJ2d_pos hβJ2d_lt
  -- Per-site collar sum bounded by the complement tsum (complement reindex).
  have hcollar : ∀ a : Fin d → ℤ,
      ∑ k ∈ Finset.univ.filter (fun k : ↑Λfull => (k : Fin d → ℤ) ∉ Λcut),
          (Real.exp (simonLiebRate β J d)
            * Real.exp (-(simonLiebRate β J d)
                * (latticeDistance d a (k : Fin d → ℤ) : ℝ)))
        ≤ ∑' x : {x : Fin d → ℤ // x ∉ Λcut},
            (Real.exp (simonLiebRate β J d)
              * Real.exp (-(simonLiebRate β J d)
                  * (latticeDistance d a (x : Fin d → ℤ) : ℝ))) := by
    intro a
    have himg : ∀ y ∈
        (Finset.univ.filter (fun k : ↑Λfull => (k : Fin d → ℤ) ∉ Λcut)).image
          (Subtype.val : ↑Λfull → (Fin d → ℤ)), y ∉ Λcut := by
      intro y hy
      rw [Finset.mem_image] at hy
      obtain ⟨k, hk, rfl⟩ := hy
      exact (Finset.mem_filter.mp hk).2
    calc ∑ k ∈ Finset.univ.filter (fun k : ↑Λfull => (k : Fin d → ℤ) ∉ Λcut),
            (Real.exp (simonLiebRate β J d)
              * Real.exp (-(simonLiebRate β J d)
                  * (latticeDistance d a (k : Fin d → ℤ) : ℝ)))
        = ∑ y ∈ (Finset.univ.filter (fun k : ↑Λfull => (k : Fin d → ℤ) ∉ Λcut)).image
              (Subtype.val : ↑Λfull → (Fin d → ℤ)),
            (Real.exp (simonLiebRate β J d)
              * Real.exp (-(simonLiebRate β J d)
                  * (latticeDistance d a y : ℝ))) := by
          rw [Finset.sum_image (fun x _ y _ hxy => Subtype.ext hxy)]
      _ ≤ ∑' x : {x : Fin d → ℤ // x ∉ Λcut},
            (Real.exp (simonLiebRate β J d)
              * Real.exp (-(simonLiebRate β J d)
                  * (latticeDistance d a (x : Fin d → ℤ) : ℝ))) :=
          sum_majorant_collar_le_tsum_compl Λcut hm a _ himg
  -- Termwise majorisation of each Ursell term on the collar.
  have hstep : ∑ k ∈ Finset.univ.filter (fun k : ↑Λfull => (k : Fin d → ℤ) ∉ Λcut),
        |truncated3 (inducedGraph (IsingModel.latticeGraph d) Λfull)
          (⟨J, h, β⟩ : IsingParams ℝ) i j k|
      ≤ ∑ k ∈ Finset.univ.filter (fun k : ↑Λfull => (k : Fin d → ℤ) ∉ Λcut),
          (Real.exp (simonLiebRate β J d)
              * Real.exp (-(simonLiebRate β J d)
                  * (latticeDistance d (i : Fin d → ℤ) (k : Fin d → ℤ) : ℝ))
            + Real.exp (simonLiebRate β J d)
              * Real.exp (-(simonLiebRate β J d)
                  * (latticeDistance d (j : Fin d → ℤ) (k : Fin d → ℤ) : ℝ))) := by
    apply Finset.sum_le_sum
    intro k hk
    rw [Finset.mem_filter] at hk
    have hknotin : (k : Fin d → ℤ) ∉ Λcut := hk.2
    have hki : i ≠ k := fun hik => hknotin (hik ▸ hi)
    have hkj : j ≠ k := fun hjk => hknotin (hjk ▸ hj)
    have hbrick := abs_truncated3_le (inducedGraph (IsingModel.latticeGraph d) Λfull)
      (⟨J, h, β⟩ : IsingParams ℝ) hf hij hkj hki
    have hik := truncated2_inducedLatticeGraph_le_exp_neg_simonLiebRate_of_field_nonneg
      d Λfull hf hβJ2d_pos hβJ2d_le hki (hconn i k)
    have hjk' := truncated2_inducedLatticeGraph_le_exp_neg_simonLiebRate_of_field_nonneg
      d Λfull hf hβJ2d_pos hβJ2d_le hkj (hconn j k)
    linarith
  refine hstep.trans ?_
  rw [Finset.sum_add_distrib]
  exact add_le_add (hcollar (i : Fin d → ℤ)) (hcollar (j : Fin d → ℤ))

end Ambient

end IsingModel
