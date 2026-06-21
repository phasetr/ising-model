import IsingModel.TransferMatrix.TwoSiteInteractingOpenStripCrossInfiniteVolume
import IsingModel.AmbientLattice.TruncatedFunctions
import IsingModel.LatticeExpSum

/-!
# Cluster property for the `K2` open strip (GJ §17.1)

The infinite-volume `K2` open-strip two-point correlation decays exponentially in
the longitudinal separation (`abs_correlationInfinite_stripGraph_cross_le`, #4146).
At zero external field this exponential decay is summable over the ambient lattice
`ℤ × Fin 2`, so the graph-general cluster property
(`Ambient.clusterProperty`) holds for the strip exhaustion.

The summability argument proceeds in three steps:

* **Step A** (`summable_abs_correlationInfinite_stripGraph_cross_fiber`): for a
  fixed longitudinal position `a : ℤ` and transverse sites `x y : Fin 2`, the
  function `b ↦ |corr (stripTwoPoint x y a b)|` is summable over `b : ℤ`.  The
  exponential cross bound `abs_correlationInfinite_stripGraph_cross_le` dominates
  every off-diagonal term `b ≠ a` by `(C + 1) · exp(-m · |a - b|)`, the diagonal
  term `b = a` by `(C + 1) · 1 ≥ 1 ≥ |corr|`, and the majorant is summable via the
  shift reindexing of `summable_exp_neg_int_natAbs`.

* **Step B** (`summable_abs_correlationInfinite_stripGraph_cross_prod`): the
  product summability over `j : ℤ × Fin 2` follows from `summable_prod_of_nonneg`
  with the finite transverse factor `Fin 2` as the inner sum.

* **Step C** (`clusterProperty_stripGraph`): the truncated two-point function at
  zero field equals the bare correlation (`truncated2Infinite_h_zero`), so the
  per-site summability hypothesis of `clusterProperty_of_summable` is discharged.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.1, pp. 304--306.
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.5, pp. 311--312.
* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.1, pp. 304--306.
-/

namespace IsingModel

namespace TransferMatrix

open scoped BigOperators

/-- **Step A: per-fiber summability of the absolute cross correlation.**  For a
fixed longitudinal position `a : ℤ` and transverse sites `x y : Fin 2`, the
function `b ↦ |correlationInfinite (stripTwoPoint x y a b)|` is summable over
`b : ℤ` (at zero external field, high temperature).

The majorant is `g b := (k2CrossStripPrefactor p hp x y + 1) · exp(-m · |a - b|)`
with `m := twoSiteInteractingMass (β J) > 0`.  Off-diagonal terms `b ≠ a` are
bounded by the exponential cross decay `abs_correlationInfinite_stripGraph_cross_le`
(the prefactor `C ≤ C + 1`); the diagonal term `b = a` is bounded by
`g a = C + 1 ≥ 1 ≥ |corr|` via `abs_correlationInfinite_le_one`.  Summability of
`g` follows from the shift reindexing `b ↦ a - b` of `summable_exp_neg_int_natAbs`.
-/
theorem summable_abs_correlationInfinite_stripGraph_cross_fiber
    {J β : ℝ} (_hJ : 0 ≤ J) (hβJ : 0 < β * J) (x y : Fin 2) (a : ℤ) :
    Summable (fun b : ℤ =>
      |Ambient.correlationInfinite stripGraph stripExhaustion
        (⟨J, 0, β⟩ : IsingParams ℝ) (stripTwoPoint x y a b)|) := by
  classical
  set p : IsingParams ℝ := ⟨J, 0, β⟩ with hp_def
  have hp : p.h = 0 := rfl
  have hβJ' : 0 < p.β * p.J := hβJ
  set m : ℝ := twoSiteInteractingMass (p.β * p.J) with hm_def
  have hm : 0 < m := twoSiteInteractingMass_pos hβJ'
  set C : ℝ := k2CrossStripPrefactor p hp x y with hC_def
  -- The majorant `g b = (C + 1) · exp(-m · |a - b|)`.
  set g : ℤ → ℝ := fun b => (C + 1) * Real.exp (-m * (a - b).natAbs) with hg_def
  -- Summability of the un-prefactored shifted exponential.
  have hshift : Summable (fun b : ℤ => Real.exp (-m * (a - b).natAbs)) := by
    have hinj : Function.Injective (fun b : ℤ => a - b) := by
      intro b₁ b₂ h
      simpa using sub_right_injective h
    exact (summable_exp_neg_int_natAbs hm).comp_injective hinj
  have hg_summable : Summable g := by
    simpa only [hg_def] using hshift.mul_left (C + 1)
  -- The cross prefactor `C` is nonnegative (it bounds an absolute value at some `b ≠ a`).
  have hCnn : 0 ≤ C := by
    have hbd := abs_correlationInfinite_stripGraph_cross_le p hp hβJ' x y a (a + 1)
      (by omega)
    have hle : (0 : ℝ) ≤ C * Real.exp (-m * (a - (a + 1)).natAbs) :=
      (abs_nonneg _).trans hbd
    nlinarith [Real.exp_pos (-m * (a - (a + 1)).natAbs)]
  -- Pointwise domination `|corr| ≤ g b`.
  refine Summable.of_nonneg_of_le (fun b => abs_nonneg _) (fun b => ?_) hg_summable
  by_cases hba : b = a
  · -- Diagonal term: `g b = (C + 1) · 1 ≥ 1 ≥ |corr|`.
    have h1 : |Ambient.correlationInfinite stripGraph stripExhaustion p
        (stripTwoPoint x y a b)| ≤ 1 :=
      Ambient.abs_correlationInfinite_le_one _ _ _ _
    have hgb : (1 : ℝ) ≤ g b := by
      rw [hg_def, hba]
      simp only [sub_self, Int.natAbs_zero, Nat.cast_zero, mul_zero, Real.exp_zero, mul_one]
      linarith
    exact h1.trans hgb
  · -- Off-diagonal term: exponential cross decay with `C ≤ C + 1`.
    have hab : a ≠ b := fun h => hba h.symm
    have hbd := abs_correlationInfinite_stripGraph_cross_le p hp hβJ' x y a b hab
    refine hbd.trans ?_
    rw [hg_def]
    have hexp : 0 < Real.exp (-m * (a - b).natAbs) := Real.exp_pos _
    nlinarith [hexp]

/-- **Step B: product summability of the absolute cross correlation.**  For a
fixed basepoint `i : ℤ × Fin 2`, the function
`j ↦ |correlationInfinite (stripTwoPoint i.2 j.2 i.1 j.1)|` is summable over
`j : ℤ × Fin 2`.

By `summable_prod_of_nonneg` (with `α := ℤ`, `β := Fin 2`), this reduces to: the
inner sum over the finite transverse factor `Fin 2` is summable for each `ℤ`
(automatic, `Fin 2` is finite), and the outer sum over `ℤ` of the inner `tsum` is
summable.  The inner `tsum` over `Fin 2` is the finite sum
`f(b, 0) + f(b, 1)`, whose outer summability is the sum of two `Step A` fibers. -/
theorem summable_abs_correlationInfinite_stripGraph_cross_prod
    {J β : ℝ} (hJ : 0 ≤ J) (hβJ : 0 < β * J) (i : ℤ × Fin 2) :
    Summable (fun j : ℤ × Fin 2 =>
      |Ambient.correlationInfinite stripGraph stripExhaustion
        (⟨J, 0, β⟩ : IsingParams ℝ) (stripTwoPoint i.2 j.2 i.1 j.1)|) := by
  classical
  set p : IsingParams ℝ := ⟨J, 0, β⟩ with hp_def
  set f : ℤ × Fin 2 → ℝ := fun j =>
    |Ambient.correlationInfinite stripGraph stripExhaustion p
      (stripTwoPoint i.2 j.2 i.1 j.1)| with hf_def
  have hnn : 0 ≤ f := fun _ => abs_nonneg _
  rw [summable_prod_of_nonneg hnn]
  refine ⟨fun a => ?_, ?_⟩
  · -- Inner sum over the finite transverse factor `Fin 2`.
    exact (hasSum_fintype _).summable
  · -- Outer sum over `ℤ` of the inner `tsum` over `Fin 2`.
    have hinner : ∀ a : ℤ, (∑' y : Fin 2, f (a, y)) = f (a, 0) + f (a, 1) := by
      intro a
      rw [tsum_fintype]
      simp [Fin.sum_univ_two]
    refine Summable.congr (f := fun a : ℤ => f (a, 0) + f (a, 1)) ?_ (fun a => (hinner a).symm)
    exact (summable_abs_correlationInfinite_stripGraph_cross_fiber hJ hβJ i.2 0 i.1).add
      (summable_abs_correlationInfinite_stripGraph_cross_fiber hJ hβJ i.2 1 i.1)

/-- **Cluster property for the `K2` open strip** (Glimm--Jaffe §17.1 / §5.1): at
zero external field and high temperature (`0 ≤ J`, `0 < β`, `0 < β J`), the
ferromagnetic `K2` open strip on the ambient lattice `ℤ × Fin 2` satisfies the
graph-general cluster property along the centred-box exhaustion.

At zero field the truncated two-point function equals the bare two-point
correlation (`truncated2Infinite_h_zero`), and the latter is absolutely summable
in each fiber (`Step B`, after identifying `({i, j} : Finset (ℤ × Fin 2))` with
`stripTwoPoint i.2 j.2 i.1 j.1`).  Hence `clusterProperty_of_summable` applies. -/
theorem clusterProperty_stripGraph {J β : ℝ} (hJ : 0 ≤ J) (_hβ : 0 < β)
    (hβJ : 0 < β * J) :
    Ambient.clusterProperty stripGraph stripExhaustion (⟨J, 0, β⟩ : IsingParams ℝ) := by
  classical
  set p : IsingParams ℝ := ⟨J, 0, β⟩ with hp_def
  -- Per-site absolute summability of the truncated two-point function.
  have habs : ∀ i : ℤ × Fin 2,
      Summable (fun j : ℤ × Fin 2 =>
        |Ambient.truncated2Infinite stripGraph stripExhaustion p i j|) := by
    intro i
    have hcorr := summable_abs_correlationInfinite_stripGraph_cross_prod hJ hβJ i
    refine hcorr.congr (fun j => ?_)
    -- `({i, j} : Finset (ℤ × Fin 2)) = stripTwoPoint i.2 j.2 i.1 j.1`.
    have hset : ({i, j} : Finset (ℤ × Fin 2)) = stripTwoPoint i.2 j.2 i.1 j.1 := by
      rw [stripTwoPoint]
    rw [Ambient.truncated2Infinite_h_zero, hset]
  -- Drop the absolute values for the summability hypothesis of the cluster property.
  have hsum : ∀ i : ℤ × Fin 2,
      Summable (fun j : ℤ × Fin 2 =>
        Ambient.truncated2Infinite stripGraph stripExhaustion p i j) :=
    fun i => (habs i).of_abs
  exact Ambient.clusterProperty_of_summable stripGraph stripExhaustion p hsum

end TransferMatrix

end IsingModel
