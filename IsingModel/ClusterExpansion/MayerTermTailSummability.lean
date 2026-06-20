import IsingModel.ClusterExpansion.MayerTermPeelBoundTail
import IsingModel.ClusterExpansion.RootedParentActivePeelBoundFactorial
import IsingModel.ClusterExpansion.Penrose.TreeChildCountFactorialBound
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Summability of the Mayer expansion (cluster-expansion convergence, GJ §18.5)

Assembling the tail Mayer-term bound (`mayerExpansionTerm_succ_abs_le_sum_pow_peelBound`,
#4133), the factorial-product form of the peel bound
(`rootedParentActivePeelBound_univ_zero_le_card_mul_prod_childCount_factorial_div`,
#4131), and the spanning-tree factorial bound
(`sum_completeGraphTrees_prod_childCount_factorial_le_four_pow_mul_factorial`, #4126)
yields the geometric per-order bound

`|mayerExpansionTerm G (n + 1) t| ≤ |V|/(1−r)·(4r/(1−r)²)^n`  (`r = Δ²e|t|`),

hence the absolute summability of the Mayer expansion when `4r/(1−r)² < 1` — the
high-temperature convergence of the cluster expansion (FV Theorem 5.4).

* `sum_pow_rootedParentActivePeelBound_le`.
* `mayerExpansionTerm_succ_abs_le_card_div_mul_geometric`.
* `summable_abs_mayerExpansionTerm_succ_of_tail_condition`.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.4--§18.5, pp.~332--336.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems*, §5.4
  (Theorem 5.4, the Kotecky--Preiss criterion).
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The `(Δ²e|t|)^n`-weighted summed peel bound in closed factorial form.**  Summing
the factorial-product form (#4131) over the spanning trees and bounding the factorial sum
by `4^n·n!` (#4126): for `Δ²e|t| < 1`,
`∑_T (Δ²e|t|)^n·peelBound ≤ ((Δ²e|t|)^n·|V|·4^n·n!)/(1−Δ²e|t|)^{2n+1}`. -/
theorem sum_pow_rootedParentActivePeelBound_le (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (n : ℕ) {t : ℝ}
    (hkp : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1) :
    (∑ T : {S : Finset (Sym2 (Fin (n + 1))) //
        S ∈ Penrose.spanningTreeEdgeSubsets (⊤ : SimpleGraph (Fin (n + 1)))},
        ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ n
          * rootedParentActivePeelBound G (Penrose.completeGraphTreeParentCode n T)
              (Finset.univ : Finset (Fin n)) (fun _ => 0) t)
      ≤ (((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ n
          * (Fintype.card ι : ℝ) * (4 : ℝ) ^ n * (n.factorial : ℝ))
          / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ (2 * n + 1) := by
  set rr : ℝ := (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) with hrr
  set q : ℝ := 1 - rr with hq
  have hqpos : 0 < q := by rw [hq]; linarith [hkp]
  have hrr0 : 0 ≤ rr := by rw [hrr]; positivity
  -- The cast of the spanning-tree factorial bound (#4126).
  have hcast : (∑ T : {S : Finset (Sym2 (Fin (n + 1))) //
        S ∈ Penrose.spanningTreeEdgeSubsets (⊤ : SimpleGraph (Fin (n + 1)))},
        ∏ v : Fin (n + 1),
          ((rootedParentChildCount (Penrose.completeGraphTreeParentCode n T)
            (Finset.univ : Finset (Fin n)) v).factorial : ℝ))
      ≤ (4 : ℝ) ^ n * (n.factorial : ℝ) := by
    have h := sum_completeGraphTrees_prod_childCount_factorial_le_four_pow_mul_factorial
      (n := n)
    calc (∑ T, ∏ v : Fin (n + 1),
            ((rootedParentChildCount (Penrose.completeGraphTreeParentCode n T)
              (Finset.univ : Finset (Fin n)) v).factorial : ℝ))
          = ((∑ T, ∏ v : Fin (n + 1),
              (rootedParentChildCount (Penrose.completeGraphTreeParentCode n T)
                (Finset.univ : Finset (Fin n)) v).factorial : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((4 ^ n * n.factorial : ℕ) : ℝ) := by exact_mod_cast h
      _ = (4 : ℝ) ^ n * (n.factorial : ℝ) := by push_cast; ring
  -- ∑_T rr^n·peelBound = rr^n·∑_T peelBound ≤ rr^n·(|V|/q^{2n+1})·(4^n·n!).
  rw [← Finset.mul_sum]
  have hpeel : (∑ T : {S : Finset (Sym2 (Fin (n + 1))) //
        S ∈ Penrose.spanningTreeEdgeSubsets (⊤ : SimpleGraph (Fin (n + 1)))},
        rootedParentActivePeelBound G (Penrose.completeGraphTreeParentCode n T)
          (Finset.univ : Finset (Fin n)) (fun _ => 0) t)
      ≤ ((Fintype.card ι : ℝ) / q ^ (2 * n + 1)) * ((4 : ℝ) ^ n * (n.factorial : ℝ)) := by
    calc (∑ T, rootedParentActivePeelBound G (Penrose.completeGraphTreeParentCode n T)
            (Finset.univ : Finset (Fin n)) (fun _ => 0) t)
          ≤ ∑ T, ((Fintype.card ι : ℝ)
              * ∏ v : Fin (n + 1),
                  ((rootedParentChildCount (Penrose.completeGraphTreeParentCode n T)
                    (Finset.univ : Finset (Fin n)) v).factorial : ℝ))
              / q ^ (2 * n + 1) := by
            refine Finset.sum_le_sum fun T _ => ?_
            exact rootedParentActivePeelBound_univ_zero_le_card_mul_prod_childCount_factorial_div
              G (Penrose.completeGraphTreeParentCode n T) hqpos
      _ = ((Fintype.card ι : ℝ) / q ^ (2 * n + 1))
            * ∑ T, ∏ v : Fin (n + 1),
                ((rootedParentChildCount (Penrose.completeGraphTreeParentCode n T)
                  (Finset.univ : Finset (Fin n)) v).factorial : ℝ) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun T _ => ?_
            rw [mul_div_right_comm]
      _ ≤ ((Fintype.card ι : ℝ) / q ^ (2 * n + 1)) * ((4 : ℝ) ^ n * (n.factorial : ℝ)) := by
            refine mul_le_mul_of_nonneg_left hcast ?_
            exact div_nonneg (by positivity) (le_of_lt (pow_pos hqpos _))
  calc rr ^ n
        * ∑ T, rootedParentActivePeelBound G (Penrose.completeGraphTreeParentCode n T)
            (Finset.univ : Finset (Fin n)) (fun _ => 0) t
        ≤ rr ^ n * (((Fintype.card ι : ℝ) / q ^ (2 * n + 1)) * ((4 : ℝ) ^ n * (n.factorial : ℝ))) :=
          mul_le_mul_of_nonneg_left hpeel (pow_nonneg hrr0 n)
    _ = (rr ^ n * (Fintype.card ι : ℝ) * (4 : ℝ) ^ n * (n.factorial : ℝ)) / q ^ (2 * n + 1) := by
          ring

/-- **The geometric per-order bound on the Mayer expansion term.**  For `Δ²e|t| < 1`,
`|mayerExpansionTerm G (n + 1) t| ≤ |V|/(1−r)·(4r/(1−r)²)^n` with `r = Δ²e|t|`.  This
combines the tail Mayer-term bound (#4133) with the summed peel bound
`sum_pow_rootedParentActivePeelBound_le`, using `(n+1)!⁻¹·n! ≤ 1`. -/
theorem mayerExpansionTerm_succ_abs_le_card_div_mul_geometric (G : SimpleGraph ι)
    [DecidableRel G.Adj] [Fintype G.edgeSet] (n : ℕ) {t : ℝ}
    (hkp : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1) :
    |mayerExpansionTerm G (n + 1) t|
      ≤ (Fintype.card ι : ℝ) / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|))
        * (4 * ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|))
            / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ 2) ^ n := by
  set rr : ℝ := (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) with hrr
  set q : ℝ := 1 - rr with hq
  have hqpos : 0 < q := by rw [hq]; linarith [hkp]
  have hrr0 : 0 ≤ rr := by rw [hrr]; positivity
  -- Combine #4133 with the summed peel bound.
  refine (mayerExpansionTerm_succ_abs_le_sum_pow_peelBound G n hkp).trans ?_
  refine (mul_le_mul_of_nonneg_left (sum_pow_rootedParentActivePeelBound_le G n hkp)
    (by positivity)).trans ?_
  -- ((n+1)!)⁻¹ · (rr^n·|V|·4^n·n!)/q^{2n+1} ≤ |V|/q · (4rr/q²)^n.
  have hfact : ((n + 1).factorial : ℝ)⁻¹ * (n.factorial : ℝ) ≤ 1 := by
    rw [← div_eq_inv_mul, div_le_one (by positivity)]
    exact_mod_cast Nat.factorial_le (Nat.le_succ n)
  have hqne : q ≠ 0 := ne_of_gt hqpos
  have hq2ne : (q ^ 2) ^ n ≠ 0 := by positivity
  have hq2 : q ^ (2 * n + 1) = (q ^ 2) ^ n * q := by rw [pow_succ, pow_mul]
  have hgoal_nonneg : (0 : ℝ) ≤ (Fintype.card ι : ℝ) / q
      * (4 * rr / q ^ 2) ^ n := by positivity
  -- The left-hand side equals `((n+1)!⁻¹·n!)` times the geometric right-hand side.
  have hLHS : ((n + 1).factorial : ℝ)⁻¹
        * ((rr ^ n * (Fintype.card ι : ℝ) * (4 : ℝ) ^ n * (n.factorial : ℝ))
            / q ^ (2 * n + 1))
      = (((n + 1).factorial : ℝ)⁻¹ * (n.factorial : ℝ))
          * ((Fintype.card ι : ℝ) / q * (4 * rr / q ^ 2) ^ n) := by
    rw [div_pow, mul_pow, hq2]
    field_simp
    ring
  rw [hLHS]
  calc (((n + 1).factorial : ℝ)⁻¹ * (n.factorial : ℝ))
        * ((Fintype.card ι : ℝ) / q * (4 * rr / q ^ 2) ^ n)
      ≤ 1 * ((Fintype.card ι : ℝ) / q * (4 * rr / q ^ 2) ^ n) :=
        mul_le_mul_of_nonneg_right hfact hgoal_nonneg
    _ = (Fintype.card ι : ℝ) / q * (4 * rr / q ^ 2) ^ n := one_mul _

/-- **Absolute summability of the Mayer expansion (cluster-expansion convergence).**  If
`Δ²e|t| < 1` and `4·Δ²e|t|/(1−Δ²e|t|)² < 1`, then `n ↦ |mayerExpansionTerm G (n + 1) t|`
is summable: the cluster expansion converges absolutely (FV Theorem 5.4).  The geometric
majorant `|V|/(1−r)·(4r/(1−r)²)^n` (`mayerExpansionTerm_succ_abs_le_card_div_mul_geometric`)
is summable since its ratio is `< 1`. -/
theorem summable_abs_mayerExpansionTerm_succ_of_tail_condition (G : SimpleGraph ι)
    [DecidableRel G.Adj] [Fintype G.edgeSet] {t : ℝ}
    (hkp : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1)
    (hρ : 4 * ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|))
        / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ 2 < 1) :
    Summable fun n : ℕ => |mayerExpansionTerm G (n + 1) t| := by
  set rr : ℝ := (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) with hrr
  set q : ℝ := 1 - rr with hq
  have hqpos : 0 < q := by rw [hq]; linarith [hkp]
  set ρ : ℝ := 4 * rr / q ^ 2 with hρdef
  have hρ0 : 0 ≤ ρ := by rw [hρdef]; positivity
  have hgeo : Summable fun n : ℕ => (Fintype.card ι : ℝ) / q * ρ ^ n :=
    (summable_geometric_of_lt_one hρ0 hρ).mul_left _
  refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_) hgeo
  exact mayerExpansionTerm_succ_abs_le_card_div_mul_geometric G n hkp

end IsingModel
