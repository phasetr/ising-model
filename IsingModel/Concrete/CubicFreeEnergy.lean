import IsingModel.Concrete.CubicTiling
import IsingModel.Concrete.LatticeGraphCorrelation.PartitionFreeEnergySuperadditivity
import IsingModel.Concrete.LatticeGraphCorrelation.PartitionFreeEnergySuperadditivityDisjointUnion
import IsingModel.Concrete.LatticeGraphCorrelation.PartitionFreeEnergySuperadditivityFE
import IsingModel.Concrete.LatticeGraphCorrelation.TranslationShiftsVaddFinset
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.AmbientLatticeSumFreeEnergy
import IsingModel.AmbientLatticeSumGeFerromagnetic

/-!
# Free-energy convergence on the cubic exhaustion — analytic layer (GJ §4.6)

The analytic side of GJ Proposition 4.6.1 on the cubic exhaustion: the family form of the
ferromagnetic `log Z` super-additivity, ready to be applied to the cubic tiling of
`IsingModel.Concrete.CubicTiling`.

* `log_partitionFunctionΛ_latticeGraph_biUnion_super_additive` — `∑_i log Z_{B i} ≤ log Z_{⋃ B i}`
  for pairwise disjoint families.

References: Glimm–Jaffe, *Quantum Physics*, 2nd ed. (Springer, 1987), §4.6,
Proposition 4.6.1, p. 68.
-/

namespace IsingModel

namespace Ambient

open Finset

/-- **`log Z` is super-additive over finite disjoint families** (ferromagnetic, ℤ^d): Finset
induction over the binary disjoint-union super-additivity, with the ferromagnetic
non-negativity of `log Z` at the empty family. -/
theorem log_partitionFunctionΛ_latticeGraph_biUnion_super_additive
    {d : ℕ} {ι : Type*} (I : Finset ι) (B : ι → Finset (Fin d → ℤ))
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (B i) (B j))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    ∑ i ∈ I, Real.log (partitionFunctionΛ (latticeGraph d) (B i) p)
      ≤ Real.log (partitionFunctionΛ (latticeGraph d) (I.biUnion B) p) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, Finset.biUnion_empty]
    exact log_partitionFunctionΛ_nonneg_of_ferromagnetic _ _ p hf
  | insert a I ha ih =>
    rw [Finset.sum_insert ha, Finset.biUnion_insert]
    have hd : Disjoint (B a) (I.biUnion B) := by
      rw [Finset.disjoint_biUnion_right]
      intro j hj
      exact hdisj a (Finset.mem_insert_self a I) j (Finset.mem_insert_of_mem hj)
        (fun h => ha (h ▸ hj))
    have hih := ih (fun i hi j hj hij =>
      hdisj i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij)
    calc Real.log (partitionFunctionΛ (latticeGraph d) (B a) p)
          + ∑ i ∈ I, Real.log (partitionFunctionΛ (latticeGraph d) (B i) p)
        ≤ Real.log (partitionFunctionΛ (latticeGraph d) (B a) p)
          + Real.log (partitionFunctionΛ (latticeGraph d) (I.biUnion B) p) := by
          exact add_le_add le_rfl hih
      _ ≤ Real.log (partitionFunctionΛ (latticeGraph d) (B a ∪ I.biUnion B) p) :=
          log_partitionFunctionΛ_latticeGraph_disjUnion_super_additive d hd p hf

/-- **Tiling lower bound for `log Z` on cubes** (ferromagnetic): the cube of radius
`(2r+1)M + r` contains `(2M+1)^d` disjoint translates of the radius-`r` cube, so
`(2M+1)^d · log Z_{B_r} ≤ log Z_{B_{(2r+1)M+r}}`. -/
theorem log_partitionFunctionΛ_cubicBox_tiling_le (d r M : ℕ) (p : IsingParams ℝ)
    (hf : Ferromagnetic p) :
    ((2 * M + 1 : ℕ) ^ d : ℝ)
        * Real.log (partitionFunctionΛ (latticeGraph d) (cubicBox d r) p)
      ≤ Real.log (partitionFunctionΛ (latticeGraph d)
          (cubicBox d ((2 * r + 1) * M + r)) p) := by
  have hsum := log_partitionFunctionΛ_latticeGraph_biUnion_super_additive
    (cubicBox d M) (cubicTile d r)
    (fun i _ j _ hij => cubicTile_disjoint hij) p hf
  have hterm : ∀ k ∈ cubicBox d M,
      Real.log (partitionFunctionΛ (latticeGraph d) (cubicTile d r k) p)
        = Real.log (partitionFunctionΛ (latticeGraph d) (cubicBox d r) p) := by
    intro k _
    exact log_partitionFunctionΛ_latticeGraph_vaddFinset_eq d (cubicTileCenter r k)
      (cubicBox d r) p
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, card_cubicBox, nsmul_eq_mul] at hsum
  rw [partitionFunctionΛ_latticeGraph_congr_finset d (biUnion_cubicTile d r M) p] at hsum
  exact_mod_cast hsum

/-- The **inner tiling radius**: the largest radius of the form `(2r+1)M + r` not exceeding `N`
(for `r ≤ N`), realising the almost-full tiling of `cubicBox d N`. -/
def innerRadius (r N : ℕ) : ℕ := (2 * r + 1) * ((N - r) / (2 * r + 1)) + r

/-- **The inner radius is at most `N`** (for `r ≤ N`). -/
theorem innerRadius_le {r N : ℕ} (h : r ≤ N) : innerRadius r N ≤ N := by
  have h2 : (2 * r + 1) * ((N - r) / (2 * r + 1)) ≤ N - r := by
    rw [mul_comm]
    exact Nat.div_mul_le_self _ _
  unfold innerRadius
  omega

/-- **The inner radius is within `2r` of `N`**. -/
theorem le_innerRadius_add (r N : ℕ) : N ≤ innerRadius r N + 2 * r := by
  rcases le_total r N with h | h
  · have hmod := Nat.div_add_mod (N - r) (2 * r + 1)
    have hlt : (N - r) % (2 * r + 1) < 2 * r + 1 := Nat.mod_lt _ (by omega)
    unfold innerRadius
    omega
  · have h0 : N - r = 0 := by omega
    unfold innerRadius
    rw [h0, Nat.zero_div, mul_zero]
    omega

/-- **The cardinality ratio of the inner cube tends to `1`**: the inner radius differs from `N`
by at most `2r`, so the side ratio `(2·innerRadius+1)/(2N+1)` is squeezed between
`1 - 4r/(2N+1)` and `1`, and so is its `d`-th power. -/
theorem tendsto_cubicBox_innerRadius_card_ratio (d r : ℕ) :
    Filter.Tendsto (fun N : ℕ =>
        ((cubicBox d (innerRadius r N)).card : ℝ) / ((cubicBox d N).card : ℝ))
      Filter.atTop (nhds 1) := by
  have hden : Filter.Tendsto (fun N : ℕ => ((2 * N + 1 : ℕ) : ℝ)) Filter.atTop
      Filter.atTop := by
    apply Filter.tendsto_atTop_mono (fun N => ?_) tendsto_natCast_atTop_atTop
    push_cast
    linarith
  have hbase : Filter.Tendsto (fun N : ℕ =>
      ((2 * innerRadius r N + 1 : ℕ) : ℝ) / ((2 * N + 1 : ℕ) : ℝ)) Filter.atTop (nhds 1) := by
    have hlow : Filter.Tendsto (fun N : ℕ =>
        1 - (4 * r : ℝ) / ((2 * N + 1 : ℕ) : ℝ)) Filter.atTop (nhds 1) := by
      have h0 : Filter.Tendsto (fun N : ℕ =>
          (4 * r : ℝ) / ((2 * N + 1 : ℕ) : ℝ)) Filter.atTop (nhds 0) :=
        Filter.Tendsto.div_atTop tendsto_const_nhds hden
      simpa using tendsto_const_nhds.sub h0
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
    · filter_upwards with N
      have hpos : (0 : ℝ) < ((2 * N + 1 : ℕ) : ℝ) := by positivity
      rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hpos]
      have hN : 2 * N + 1 ≤ (2 * innerRadius r N + 1) + 4 * r := by
        have := le_innerRadius_add r N
        omega
      have := (Nat.cast_le (α := ℝ)).mpr hN
      push_cast at this ⊢
      linarith
    · filter_upwards [Filter.eventually_ge_atTop r] with N hN
      have hpos : (0 : ℝ) < ((2 * N + 1 : ℕ) : ℝ) := by positivity
      rw [div_le_one hpos]
      have hle : 2 * innerRadius r N + 1 ≤ 2 * N + 1 := by
        have := innerRadius_le hN
        omega
      exact_mod_cast hle
  have hpow := hbase.pow d
  rw [one_pow] at hpow
  refine hpow.congr (fun N => ?_)
  rw [card_cubicBox, card_cubicBox]
  push_cast
  rw [div_pow]

/-- **Cubes are nonempty**: the origin belongs to every `cubicBox`. -/
theorem cubicBox_nonempty (d n : ℕ) : (cubicBox d n).Nonempty := by
  refine ⟨0, ?_⟩
  rw [mem_cubicBox]
  intro i
  simp

/-- **`log Z` is monotone along nested cubes** (ferromagnetic): enlarge by the disjoint
difference. -/
theorem log_partitionFunctionΛ_cubicBox_mono (d : ℕ) {m n : ℕ} (h : m ≤ n)
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    Real.log (partitionFunctionΛ (latticeGraph d) (cubicBox d m) p)
      ≤ Real.log (partitionFunctionΛ (latticeGraph d) (cubicBox d n) p) := by
  classical
  have hsub : cubicBox d m ⊆ cubicBox d n := cubicBox_mono d h
  calc Real.log (partitionFunctionΛ (latticeGraph d) (cubicBox d m) p)
      ≤ Real.log (partitionFunctionΛ (latticeGraph d)
          (cubicBox d m ∪ (cubicBox d n \ cubicBox d m)) p) :=
        log_partitionFunctionΛ_latticeGraph_le_of_disjoint_union d
          Finset.disjoint_sdiff p hf
    _ = Real.log (partitionFunctionΛ (latticeGraph d) (cubicBox d n) p) := by
        rw [partitionFunctionΛ_latticeGraph_congr_finset d
          (Finset.union_sdiff_of_subset hsub) p]

/-- **Stage lower bound by the tiling ratio**: for `r ≤ N`,
`(|B_{innerRadius}|/|B_N|) · f_r ≤ f_N`. -/
theorem ratio_mul_freeEnergyΛ_cubicBox_le (d r : ℕ) (p : IsingParams ℝ)
    (hf : Ferromagnetic p) {N : ℕ} (hrN : r ≤ N) :
    ((cubicBox d (innerRadius r N)).card : ℝ) / ((cubicBox d N).card : ℝ)
        * freeEnergyΛ (latticeGraph d) (cubicBox d r) p
      ≤ freeEnergyΛ (latticeGraph d) (cubicBox d N) p := by
  have hcardpos : (0 : ℝ) < ((cubicBox d N).card : ℝ) := by
    rw [card_cubicBox]; positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hcardpos]
  have hfr := card_mul_freeEnergyΛ_latticeGraph_eq_log_partitionFunctionΛ_of_nonempty d
    (cubicBox_nonempty d r) p
  have hfN := card_mul_freeEnergyΛ_latticeGraph_eq_log_partitionFunctionΛ_of_nonempty d
    (cubicBox_nonempty d N) p
  have hcards : ((cubicBox d (innerRadius r N)).card : ℝ)
      = ((2 * ((N - r) / (2 * r + 1)) + 1 : ℕ) ^ d : ℝ) * ((cubicBox d r).card : ℝ) := by
    rw [card_cubicBox, card_cubicBox]
    push_cast
    rw [← mul_pow]
    congr 1
    unfold innerRadius
    push_cast
    ring
  calc ((cubicBox d (innerRadius r N)).card : ℝ)
        * freeEnergyΛ (latticeGraph d) (cubicBox d r) p
      = ((2 * ((N - r) / (2 * r + 1)) + 1 : ℕ) ^ d : ℝ)
          * (((cubicBox d r).card : ℝ)
            * freeEnergyΛ (latticeGraph d) (cubicBox d r) p) := by
        rw [hcards]; ring
    _ = ((2 * ((N - r) / (2 * r + 1)) + 1 : ℕ) ^ d : ℝ)
          * Real.log (partitionFunctionΛ (latticeGraph d) (cubicBox d r) p) := by
        rw [hfr]
    _ ≤ Real.log (partitionFunctionΛ (latticeGraph d)
          (cubicBox d (innerRadius r N)) p) :=
        log_partitionFunctionΛ_cubicBox_tiling_le d r ((N - r) / (2 * r + 1)) p hf
    _ ≤ Real.log (partitionFunctionΛ (latticeGraph d) (cubicBox d N) p) :=
        log_partitionFunctionΛ_cubicBox_mono d (innerRadius_le hrN) p hf
    _ = freeEnergyΛ (latticeGraph d) (cubicBox d N) p * ((cubicBox d N).card : ℝ) := by
        rw [← hfN]; ring

/-- **Every stage value bounds the `liminf` from below**: the tiling ratio tends to `1`, so the
stage bound survives the limit. -/
theorem freeEnergyΛ_cubicBox_le_liminf (d r : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    freeEnergyΛ (latticeGraph d) (cubicBox d r) p
      ≤ Filter.liminf
          (freeEnergyAlongExhaustion (latticeGraph d) (cubicExhaustion d) p)
          Filter.atTop := by
  have hratio := (tendsto_cubicBox_innerRadius_card_ratio d r).mul_const
    (freeEnergyΛ (latticeGraph d) (cubicBox d r) p)
  rw [one_mul] at hratio
  have hev : ∀ᶠ N in Filter.atTop,
      ((cubicBox d (innerRadius r N)).card : ℝ) / ((cubicBox d N).card : ℝ)
          * freeEnergyΛ (latticeGraph d) (cubicBox d r) p
        ≤ freeEnergyAlongExhaustion (latticeGraph d) (cubicExhaustion d) p N := by
    filter_upwards [Filter.eventually_ge_atTop r] with N hN
    exact ratio_mul_freeEnergyΛ_cubicBox_le d r p hf hN
  have hbdd : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (freeEnergyAlongExhaustion (latticeGraph d) (cubicExhaustion d) p) := by
    obtain ⟨c, hc⟩ := BddAbove_freeEnergyAlongExhaustion_range (latticeGraph d)
      (cubicExhaustion d) p (boundedEdgeDensity_latticeGraph_cubicExhaustion d)
    exact ⟨c, Filter.eventually_map.mpr
      (Filter.Eventually.of_forall (fun n => hc (Set.mem_range_self n)))⟩
  calc freeEnergyΛ (latticeGraph d) (cubicBox d r) p
      = Filter.liminf (fun N : ℕ =>
          ((cubicBox d (innerRadius r N)).card : ℝ) / ((cubicBox d N).card : ℝ)
            * freeEnergyΛ (latticeGraph d) (cubicBox d r) p) Filter.atTop :=
        hratio.liminf_eq.symm
    _ ≤ _ := Filter.liminf_le_liminf hev hratio.isBoundedUnder_ge hbdd.isCoboundedUnder_ge

/-- **GJ Proposition 4.6.1 on the cubic exhaustion** (unconditional, ferromagnetic): the
free-energy density along the cubic boxes of `ℤ^d` converges to the infinite-volume free
energy. Every stage bounds the `liminf` from below (tiling), hence
`limsup ≤ liminf`, and `freeEnergyInfinite` is the `limsup` by definition. -/
theorem freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_tendsto (d : ℕ)
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    Filter.Tendsto (freeEnergyAlongExhaustion (latticeGraph d) (cubicExhaustion d) p)
      Filter.atTop
      (nhds (freeEnergyInfinite (latticeGraph d) (cubicExhaustion d) p)) := by
  have hbddA : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (freeEnergyAlongExhaustion (latticeGraph d) (cubicExhaustion d) p) := by
    obtain ⟨c, hc⟩ := BddAbove_freeEnergyAlongExhaustion_range (latticeGraph d)
      (cubicExhaustion d) p (boundedEdgeDensity_latticeGraph_cubicExhaustion d)
    exact ⟨c, Filter.eventually_map.mpr
      (Filter.Eventually.of_forall (fun n => hc (Set.mem_range_self n)))⟩
  have hbddB : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
      (freeEnergyAlongExhaustion (latticeGraph d) (cubicExhaustion d) p) :=
    ⟨0, Filter.eventually_map.mpr (Filter.Eventually.of_forall (fun n =>
      freeEnergyAlongExhaustion_nonneg_of_ferromagnetic (latticeGraph d)
        (cubicExhaustion d) p hf (cubicBox_nonempty d n)))⟩
  have hkey : Filter.limsup
      (freeEnergyAlongExhaustion (latticeGraph d) (cubicExhaustion d) p) Filter.atTop
      ≤ Filter.liminf
          (freeEnergyAlongExhaustion (latticeGraph d) (cubicExhaustion d) p)
          Filter.atTop := by
    apply Filter.limsup_le_of_le hbddB.isCoboundedUnder_le
    exact Filter.Eventually.of_forall (fun r => freeEnergyΛ_cubicBox_le_liminf d r p hf)
  exact tendsto_of_le_liminf_of_limsup_le hkey le_rfl hbddA hbddB

end Ambient

end IsingModel
