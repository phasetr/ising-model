import IsingModel.TransferMatrix.PathGraphPairTwoPoint
import IsingModel.Concrete.LatticeGraphCorrelation.TwoPoint
import IsingModel.PartitionFunctionIso
import IsingModel.AmbientLatticeSum.InducedUnion

/-!
# Infinite-volume 1D Ising two-point function `twoPointFunction 1 = (tanh βJ)^dist` (GJ §17.1)

Capstone of the infinite-volume 1D programme (Issue #3532): the project's
infinite-volume Gibbs two-point function equals the exact geometric decay

  `twoPointFunction 1 ⟨J,0,β⟩ r = (tanh βJ)^(latticeDistance 1 0 r)`  (ferromagnetic),

the project's stated most-important long-term goal in 1D.

The induced subgraph of `latticeGraph 1` on the centred box `cubicBox 1 N = [-N,N]`
is isomorphic to the open chain `pathGraph (2N+1)` via the relabelling `k ↦ k - N`
(`boxEquiv`).  Hence by `correlation_map_equiv` the finite-volume
`correlationAlongExhaustion` at stage `N` equals the open-chain pair two-point
`(tanh βJ)^|r|` (#3534).  The sequence is eventually constant in `N`, so the
supremum `correlationInfinite` collapses to `(tanh βJ)^|r|`.

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §17.1, pp. 304–306.
-/

namespace IsingModel

namespace TransferMatrix

open scoped BigOperators
open SimpleGraph Finset

/-- The lattice point at position `k` of the centred box `[-N, N]`: `k ↦ k - N`. -/
def boxPoint (N : ℕ) (k : Fin (2 * N + 1)) : Fin 1 → ℤ :=
  fun _ => (k : ℤ) - N

/-- The box point `k - N` lies in `cubicBox 1 N`. -/
theorem boxPoint_mem (N : ℕ) (k : Fin (2 * N + 1)) :
    boxPoint N k ∈ Ambient.cubicBox 1 N := by
  rw [Ambient.mem_cubicBox]
  intro i
  simp only [boxPoint]
  have := k.isLt
  omega

/-- **Box ≅ path relabelling** (GJ §17.1): the equivalence `Fin (2N+1) ≃ ↑(cubicBox 1 N)`
sending the path index `k` to the lattice point `k - N` of the centred box. -/
def boxEquiv (N : ℕ) : Fin (2 * N + 1) ≃ ↑(Ambient.cubicBox 1 N) where
  toFun k := ⟨boxPoint N k, boxPoint_mem N k⟩
  invFun x := ⟨(x.val 0 + N).toNat, by
    have := (Ambient.mem_cubicBox.mp x.2) 0; omega⟩
  left_inv k := by
    ext
    simp only [boxPoint]
    have := k.isLt
    omega
  right_inv x := by
    apply Subtype.ext
    funext i
    have h0 : i = 0 := Subsingleton.elim _ _
    subst h0
    simp only [boxPoint]
    have := (Ambient.mem_cubicBox.mp x.2) 0
    omega

/-- The cubic exhaustion's volume at stage `N` is the box `cubicBox d N`. -/
@[simp] theorem cubicExhaustion_volume (d N : ℕ) :
    (Ambient.cubicExhaustion d).volume N = Ambient.cubicBox d N := rfl

/-- The underlying lattice point of `boxEquiv N k` is the constant function `k - N`. -/
@[simp] theorem boxEquiv_apply_val (N : ℕ) (k : Fin (2 * N + 1)) :
    ((boxEquiv N k).val : Fin 1 → ℤ) = fun _ => (k : ℤ) - N := rfl

/-- The path index of `boxEquiv⁻¹ u` is `(u₀ + N).toNat`. -/
@[simp] theorem boxEquiv_symm_val (N : ℕ) (u : ↑(Ambient.cubicBox 1 N)) :
    (((boxEquiv N).symm u : Fin (2 * N + 1)) : ℕ) = (u.val 0 + N).toNat := rfl

/-- **Box ≅ path graph isomorphism** (GJ §17.1): the open chain `pathGraph (2N+1)`,
relabelled by `boxEquiv`, is exactly the induced subgraph of `latticeGraph 1` on the
centred box `[-N,N]`.  Adjacency on both sides reduces to `|u₀ − v₀| = 1`. -/
theorem pathGraph_map_boxEquiv (N : ℕ) :
    (pathGraph (2 * N + 1)).map (boxEquiv N).toEmbedding
      = Ambient.inducedGraph (latticeGraph 1) (Ambient.cubicBox 1 N) := by
  ext u v
  rw [SimpleGraph.map_adj]
  have hbound_u := (Ambient.mem_cubicBox.mp u.2) 0
  have hbound_v := (Ambient.mem_cubicBox.mp v.2) 0
  rw [show (Ambient.inducedGraph (latticeGraph 1) (Ambient.cubicBox 1 N)).Adj u v
      ↔ (∑ i : Fin 1, |u.val i - v.val i|) = 1 from Iff.rfl, Fin.sum_univ_one]
  constructor
  · rintro ⟨u', v', hadj, hu, hv⟩
    rw [pathGraph_adj] at hadj
    have hu' : ((u' : ℕ) : ℤ) - N = u.val 0 := by
      have := congrArg (fun w : ↑(Ambient.cubicBox 1 N) => w.val 0) hu
      simpa [boxPoint] using this
    have hv' : ((v' : ℕ) : ℤ) - N = v.val 0 := by
      have := congrArg (fun w : ↑(Ambient.cubicBox 1 N) => w.val 0) hv
      simpa [boxPoint] using this
    have := u'.isLt; have := v'.isLt
    rw [abs_eq (by norm_num : (0 : ℤ) ≤ 1)]
    omega
  · intro hadj
    rw [abs_eq (by norm_num : (0 : ℤ) ≤ 1)] at hadj
    refine ⟨(boxEquiv N).symm u, (boxEquiv N).symm v, ?_,
      (boxEquiv N).apply_symm_apply u, (boxEquiv N).apply_symm_apply v⟩
    rw [pathGraph_adj, boxEquiv_symm_val, boxEquiv_symm_val]
    omega

/-- The image of `0 : Fin 1 → ℤ` under `boxEquiv⁻¹`, i.e. the path index `N` of the
centre of the box. -/
private def centreIdx (N : ℕ) : Fin (2 * N + 1) := ⟨N, by omega⟩

/-- The image of `r` under `boxEquiv⁻¹`, the path index `r₀ + N`. -/
private def shiftIdx (N : ℕ) (r : Fin 1 → ℤ) (h : (r 0).natAbs ≤ N) :
    Fin (2 * N + 1) := ⟨(r 0 + N).toNat, by
  omega⟩

/-- `boxEquiv` sends the centre index `N` to the lattice point `0`. -/
private theorem boxEquiv_centreIdx (N : ℕ) :
    (boxEquiv N (centreIdx N)).val = (0 : Fin 1 → ℤ) := by
  funext i; simp only [boxEquiv_apply_val, centreIdx, Pi.zero_apply]; ring

/-- `boxEquiv` sends the shift index `r₀ + N` to the lattice point `r`. -/
private theorem boxEquiv_shiftIdx (N : ℕ) (r : Fin 1 → ℤ) (h : (r 0).natAbs ≤ N) :
    (boxEquiv N (shiftIdx N r h)).val = r := by
  funext i
  have h0 : i = 0 := Subsingleton.elim _ _
  subst h0
  simp only [boxEquiv_apply_val, shiftIdx]
  omega

/-- **Finite-volume value of the 1D two-point function** (GJ §17.1): for `r ≠ 0` and a
box large enough to contain `r` (`|r₀| ≤ N`), the correlation along the cubic
exhaustion at stage `N` is the exact `(tanh βJ)^dist`, by transporting the open-chain
pair two-point along the box ≅ path isomorphism. -/
theorem correlationAlongExhaustion_pair_eq (N : ℕ) {J β : ℝ} (r : Fin 1 → ℤ)
    (hr0 : r 0 ≠ 0) (hrN : (r 0).natAbs ≤ N) :
    Ambient.correlationAlongExhaustion (latticeGraph 1) (Ambient.cubicExhaustion 1)
        (⟨J, 0, β⟩ : IsingParams ℝ) ({0, r} : Finset (Fin 1 → ℤ)) N
      = Real.tanh (β * J) ^ latticeDistance 1 0 r := by
  classical
  have hbox : -(N : ℤ) ≤ r 0 ∧ r 0 ≤ N := by omega
  have hsub : ({0, r} : Finset (Fin 1 → ℤ)) ⊆ Ambient.cubicBox 1 N := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Ambient.mem_cubicBox]
    rcases hx with rfl | rfl
    · intro i; simp
    · intro i; have h0 : i = 0 := Subsingleton.elim _ _; subst h0; exact hbox
  rw [Ambient.correlationAlongExhaustion_of_subset _ _ _ hsub, Ambient.correlationΛ_apply]
  simp only [cubicExhaustion_volume]
  -- the lattice pair, lifted to the box subtype, is the `boxEquiv`-image of the path pair
  have hlift : Ambient.liftFinset ({0, r} : Finset (Fin 1 → ℤ)) hsub
      = ({centreIdx N, shiftIdx N r hrN} : Finset (Fin (2 * N + 1))).map
          (boxEquiv N).toEmbedding := by
    ext w
    simp only [Ambient.mem_liftFinset, Finset.mem_map, Finset.mem_insert,
      Finset.mem_singleton, Equiv.coe_toEmbedding]
    constructor
    · rintro (h | h)
      · refine ⟨centreIdx N, Or.inl rfl, ?_⟩
        apply Subtype.ext; rw [boxEquiv_centreIdx]; exact h.symm
      · refine ⟨shiftIdx N r hrN, Or.inr rfl, ?_⟩
        apply Subtype.ext; rw [boxEquiv_shiftIdx]; exact h.symm
    · rintro ⟨a, (rfl | rfl), rfl⟩
      · left; rw [boxEquiv_centreIdx]
      · right; rw [boxEquiv_shiftIdx]
  haveI : Fintype ((pathGraph (2 * N + 1)).map (boxEquiv N).toEmbedding).edgeSet :=
    pathGraph_map_boxEquiv N ▸ inferInstance
  rw [hlift]
  -- transport the induced-graph correlation to the open chain `pathGraph (2N+1)`
  have hchain : correlation (Ambient.inducedGraph (latticeGraph 1) (Ambient.cubicBox 1 N))
        (⟨J, 0, β⟩ : IsingParams ℝ)
        (({centreIdx N, shiftIdx N r hrN} : Finset (Fin (2 * N + 1))).map
          (boxEquiv N).toEmbedding)
      = correlation (pathGraph (2 * N + 1)) (⟨J, 0, β⟩ : IsingParams ℝ)
          {centreIdx N, shiftIdx N r hrN} :=
    (correlation_congr_of_eq (pathGraph_map_boxEquiv N).symm _ _).trans
      (correlation_map_equiv (boxEquiv N) (pathGraph (2 * N + 1)) _ _)
  refine hchain.trans ?_
  rw [correlation_pathGraph_pair_eq_tanh_pow (2 * N) (centreIdx N)
    (shiftIdx N r hrN) (by simp only [centreIdx, shiftIdx, ne_eq, Fin.mk.injEq]; omega)]
  congr 1
  simp only [centreIdx, shiftIdx, latticeDistance, Fin.sum_univ_one, Fin.val_mk,
    Pi.zero_apply]
  omega

/-- **Infinite-volume 1D Ising two-point function** (Glimm–Jaffe §17.1, capstone of
Issue #3532): the project's infinite-volume Gibbs two-point function equals the exact
geometric decay `(tanh βJ)^dist`,
`twoPointFunction 1 ⟨J,0,β⟩ r = (tanh βJ)^(latticeDistance 1 0 r)` for `r ≠ 0`
(ferromagnetic `0 ≤ J`, `0 < β`).  The induced subgraph on each centred box `[-N,N]`
is an open chain (`pathGraph_map_boxEquiv`), so the finite-volume correlation is the
exact pair two-point `(tanh βJ)^|r|` (#3534); it is eventually constant in `N`, so the
thermodynamic-limit supremum collapses to it.  This is the project's most-important
long-term goal realised in one dimension. -/
theorem twoPointFunction_one_eq_tanh_pow {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (r : Fin 1 → ℤ) (hr0 : r 0 ≠ 0) :
    Ambient.twoPointFunction 1 (⟨J, 0, β⟩ : IsingParams ℝ) r
      = Real.tanh (β * J) ^ latticeDistance 1 0 r := by
  have hferm : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ, le_refl 0, hβ⟩
  rw [Ambient.twoPointFunction, Ambient.correlationInfinite_eq_ciSup]
  have htendsto := Ambient.correlationAlongExhaustion_tendsto_ciSup (latticeGraph 1)
    (Ambient.cubicExhaustion 1) (⟨J, 0, β⟩ : IsingParams ℝ) hferm
    ({0, r} : Finset (Fin 1 → ℤ))
  have heventually : ∀ᶠ N in Filter.atTop,
      Ambient.correlationAlongExhaustion (latticeGraph 1) (Ambient.cubicExhaustion 1)
        (⟨J, 0, β⟩ : IsingParams ℝ) ({0, r} : Finset (Fin 1 → ℤ)) N
        = Real.tanh (β * J) ^ latticeDistance 1 0 r := by
    rw [Filter.eventually_atTop]
    exact ⟨(r 0).natAbs, fun N hN => correlationAlongExhaustion_pair_eq N r hr0 hN⟩
  exact tendsto_nhds_unique htendsto
    (Filter.Tendsto.congr' (Filter.EventuallyEq.symm heventually) tendsto_const_nhds)

end TransferMatrix

end IsingModel
