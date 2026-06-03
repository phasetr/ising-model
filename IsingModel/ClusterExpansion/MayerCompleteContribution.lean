import IsingModel.ClusterExpansion.MayerRootComponent
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Mayer expansion contribution of a fully-incompatible cluster (GJ §18.4)

Builds on the Mayer `K_n` closed form
`alternatingConnectedSubgraphSum K_n = (-1)^(n-1)(n-1)!` and the resulting Ursell
coefficient `ϕ^T(ω) = (-1)^(n-1)/n` for a fully-incompatible polymer sequence
(`ursellCoefficient_complete_eq`). Here we record the absolute value of that
coefficient, its `n = 2` consistency with the pair Ursell value, and the factored
Mayer-term contribution of the complete (all pairwise incompatible) clusters.

These connect the combinatorial `K_n` identity to the actual cluster expansion
`log Ξ = ∑_{n ≥ 1} ∑_ω ϕ^T(ω) z(ω)` of Glimm–Jaffe §18.4.
-/

namespace IsingModel

open Finset

/-- **Absolute Ursell coefficient of a complete cluster**: for `n` pairwise
incompatible polymers, `|ϕ^T(ω)| = 1/n`. Immediate from
`ursellCoefficient_complete_eq` since `|(-1)^(n-1)| = 1` and `n > 0`. -/
theorem ursellCoefficient_complete_abs_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} {ω : Fin n → Finset (Sym2 ι)}
    (hn : 1 ≤ n) (h : ∀ i j, i ≠ j → PolymersIncompatible (ω i) (ω j)) :
    |ursellCoefficient ω| = 1 / (n : ℝ) := by
  rw [ursellCoefficient_complete_eq hn h, abs_div, abs_pow, abs_neg, abs_one, one_pow,
    abs_of_pos (by exact_mod_cast (show 0 < n by omega))]

/-- **`n = 2` consistency**: a pair of incompatible polymers (`Fin 2`) has
`ϕ^T(ω) = -1/2`, recovering `ursellCoefficient_pair_incompatible` from the
general complete-cluster formula `ursellCoefficient_complete_eq` (`(-1)^1/2`). -/
theorem ursellCoefficient_complete_eq_two
    {ι : Type*} [Fintype ι] [DecidableEq ι] {ω : Fin 2 → Finset (Sym2 ι)}
    (h : PolymersIncompatible (ω 0) (ω 1)) :
    ursellCoefficient ω = -1 / 2 := by
  have hcomplete : ∀ i j : Fin 2, i ≠ j → PolymersIncompatible (ω i) (ω j) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact h
    · exact h.symm
    · exact absurd rfl hij
  rw [ursellCoefficient_complete_eq (by omega) hcomplete]
  norm_num

/-- **Mayer-term contribution of the complete clusters**: the part of the Mayer
expansion term over fully-incompatible polymer sequences factors the constant
Ursell coefficient `(-1)^(n-1)/n` out of the activity sum. With
`ursellCoefficient_complete_eq` every term shares the same coefficient, so the
sum collapses to `((-1)^(n-1)/n)·∑ z(ω)` over the complete clusters. -/
theorem mayerExpansionTerm_completeClusterSubsum_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    (∑ ω ∈ (Fintype.piFinset (fun _ : Fin n => allPolymers G)).filter
        (fun ω => ∀ i j, i ≠ j → PolymersIncompatible (ω i) (ω j)),
        ursellCoefficient ω * clusterSeqActivity t ω)
      = ((-1 : ℝ) ^ (n - 1) / (n : ℝ))
        * ∑ ω ∈ (Fintype.piFinset (fun _ : Fin n => allPolymers G)).filter
            (fun ω => ∀ i j, i ≠ j → PolymersIncompatible (ω i) (ω j)),
            clusterSeqActivity t ω := by
  classical
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun ω hω => ?_)
  rw [Finset.mem_filter] at hω
  rw [ursellCoefficient_complete_eq hn hω.2]

/-- **Cluster activity of a repeated single polymer**: the activity of the constant
sequence `(P, …, P)` of length `m` equals `(t^|P|)^m`. -/
theorem clusterSeqActivity_const
    {ι : Type*} [Fintype ι] [DecidableEq ι] (t : ℝ) {m : ℕ} (P : Finset (Sym2 ι)) :
    clusterSeqActivity t (fun _ : Fin m => P) = (t ^ P.card) ^ m := by
  rw [clusterSeqActivity, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **Repeated-polymer Mayer term in closed form**: the multiplicity-`m+1`
contribution `ϕ^T(P, …, P) · z` of a single polymer `P` equals
`-((-(t^|P|))^{m+1}/(m+1))`. The repeated sequence is a self-incompatible complete
cluster, so its Ursell coefficient is the closed form `(-1)^m/(m+1)`. -/
theorem singlePolymer_ursell_term_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : SimpleGraph ι} [Fintype G.edgeSet] {P : Finset (Sym2 ι)} (hP : IsPolymer G P)
    (t : ℝ) (m : ℕ) :
    ursellCoefficient (fun _ : Fin (m + 1) => P)
        * clusterSeqActivity t (fun _ : Fin (m + 1) => P)
      = -((-(t ^ P.card)) ^ (m + 1) / ((m : ℝ) + 1)) := by
  rw [ursellCoefficient_complete_eq (Nat.le_add_left 1 m)
      (fun i j _ => PolymersIncompatible.self_of_isPolymer hP),
    clusterSeqActivity_const, Nat.add_sub_cancel]
  have hexp : (-(t ^ P.card)) ^ (m + 1) = -((-1 : ℝ) ^ m * (t ^ P.card) ^ (m + 1)) := by
    rw [neg_pow, pow_succ]; ring
  rw [hexp]; push_cast; ring

/-- **Single-polymer cluster contribution equals `log(1 + activity)`** (GJ §18.4–§18.5):
the classic cluster-expansion identity that a single polymer `P` contributes
`log(1 + t^|P|)` to `log Ξ`. Summing the multiplicity-`m+1` repeated-polymer term
`ϕ^T(P, …, P) · z = ((-1)^m/(m+1))·(t^|P|)^{m+1}` over `m` gives the logarithm power
series: the repeated sequence is a complete (self-incompatible) cluster, so its
Ursell coefficient is `(-1)^(m)/(m+1)` (`ursellCoefficient_complete_eq` via
`PolymersIncompatible.self_of_isPolymer`), and `hasSum_pow_div_log_of_abs_lt_one`
sums the resulting alternating series to `log(1 + t^|P|)` whenever `|t^|P|| < 1`.
This is the log structure at the heart of why the cluster expansion exponentiates. -/
theorem hasSum_singlePolymer_ursell_eq_log
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : SimpleGraph ι} [Fintype G.edgeSet] {P : Finset (Sym2 ι)} (hP : IsPolymer G P)
    {t : ℝ} (ht : |t ^ P.card| < 1) :
    HasSum (fun m : ℕ => ursellCoefficient (fun _ : Fin (m + 1) => P)
        * clusterSeqActivity t (fun _ : Fin (m + 1) => P))
      (Real.log (1 + t ^ P.card)) := by
  have hterm : ∀ m : ℕ, ursellCoefficient (fun _ : Fin (m + 1) => P)
        * clusterSeqActivity t (fun _ : Fin (m + 1) => P)
      = -((-(t ^ P.card)) ^ (m + 1) / ((m : ℝ) + 1)) :=
    fun m => singlePolymer_ursell_term_eq hP t m
  have hbase : HasSum (fun m : ℕ => -((-(t ^ P.card)) ^ (m + 1) / ((m : ℝ) + 1)))
      (Real.log (1 + t ^ P.card)) := by
    have h := Real.hasSum_pow_div_log_of_abs_lt_one (x := -(t ^ P.card)) (by rwa [abs_neg])
    rw [sub_neg_eq_add] at h
    simpa using h.neg
  have hfun : (fun m : ℕ => ursellCoefficient (fun _ : Fin (m + 1) => P)
      * clusterSeqActivity t (fun _ : Fin (m + 1) => P))
      = (fun m : ℕ => -((-(t ^ P.card)) ^ (m + 1) / ((m : ℝ) + 1))) := funext hterm
  rw [hfun]
  exact hbase

/-- **Single-polymer cluster contribution (`tsum` form)**: the repeated-polymer
Mayer sum evaluates to `log(1 + t^|P|)`. Direct `tsum` form of
`hasSum_singlePolymer_ursell_eq_log`. -/
theorem tsum_singlePolymer_ursell_eq_log
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : SimpleGraph ι} [Fintype G.edgeSet] {P : Finset (Sym2 ι)} (hP : IsPolymer G P)
    {t : ℝ} (ht : |t ^ P.card| < 1) :
    (∑' m : ℕ, ursellCoefficient (fun _ : Fin (m + 1) => P)
        * clusterSeqActivity t (fun _ : Fin (m + 1) => P))
      = Real.log (1 + t ^ P.card) :=
  (hasSum_singlePolymer_ursell_eq_log hP ht).tsum_eq

/-- **Absolute convergence of the single-polymer Mayer series** (GJ §18.5,
convergence): for non-negative `t` with `t^|P| < 1`, the absolute values of the
repeated-polymer terms sum to `-log(1 - t^|P|)`. Since the activity `z = t^|P|`
is non-negative, `|ϕ^T(P,…,P)·z| = z^{m+1}/(m+1)`, and the logarithm power series
`hasSum_pow_div_log_of_abs_lt_one` (at `+z`) gives `-log(1 - z)`. The explicit
radius of convergence `t^|P| < 1` of the single-polymer cluster contribution. -/
theorem hasSum_abs_singlePolymer_ursell
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : SimpleGraph ι} [Fintype G.edgeSet] {P : Finset (Sym2 ι)} (hP : IsPolymer G P)
    {t : ℝ} (ht0 : 0 ≤ t) (ht : |t ^ P.card| < 1) :
    HasSum (fun m : ℕ => |ursellCoefficient (fun _ : Fin (m + 1) => P)
        * clusterSeqActivity t (fun _ : Fin (m + 1) => P)|)
      (-Real.log (1 - t ^ P.card)) := by
  have hz : 0 ≤ t ^ P.card := pow_nonneg ht0 _
  have hfun : (fun m : ℕ => |ursellCoefficient (fun _ : Fin (m + 1) => P)
      * clusterSeqActivity t (fun _ : Fin (m + 1) => P)|)
      = (fun n : ℕ => (t ^ P.card) ^ (n + 1) / ((n : ℝ) + 1)) := by
    funext m
    rw [singlePolymer_ursell_term_eq hP, abs_neg, abs_div, abs_pow, abs_neg,
      abs_of_nonneg hz, abs_of_nonneg (show (0 : ℝ) ≤ (m : ℝ) + 1 by positivity)]
  rw [hfun]
  exact Real.hasSum_pow_div_log_of_abs_lt_one (x := t ^ P.card) ht

/-- **`tsum` form of the absolute convergence**: `∑' |ϕ^T(P,…,P)·z| = -log(1 - t^|P|)`. -/
theorem tsum_abs_singlePolymer_ursell
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : SimpleGraph ι} [Fintype G.edgeSet] {P : Finset (Sym2 ι)} (hP : IsPolymer G P)
    {t : ℝ} (ht0 : 0 ≤ t) (ht : |t ^ P.card| < 1) :
    (∑' m : ℕ, |ursellCoefficient (fun _ : Fin (m + 1) => P)
        * clusterSeqActivity t (fun _ : Fin (m + 1) => P)|)
      = -Real.log (1 - t ^ P.card) :=
  (hasSum_abs_singlePolymer_ursell hP ht0 ht).tsum_eq

/-- **Summability of the single-polymer Mayer series**: the repeated-polymer terms
are summable for `|t^|P|| < 1` (from the `HasSum` to `log(1 + t^|P|)`; absolute
summability for `0 ≤ t` is `hasSum_abs_singlePolymer_ursell`). -/
theorem summable_singlePolymer_ursell
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : SimpleGraph ι} [Fintype G.edgeSet] {P : Finset (Sym2 ι)} (hP : IsPolymer G P)
    {t : ℝ} (ht : |t ^ P.card| < 1) :
    Summable (fun m : ℕ => ursellCoefficient (fun _ : Fin (m + 1) => P)
        * clusterSeqActivity t (fun _ : Fin (m + 1) => P)) :=
  (hasSum_singlePolymer_ursell_eq_log hP ht).summable

/-- **Convergence comparison**: the single-polymer contribution is dominated by its
absolute-convergence radius, `log(1 + t^|P|) ≤ -log(1 - t^|P|)` for `0 ≤ t^|P| < 1`
(equivalently `log(1 - (t^|P|)^2) ≤ 0`). -/
theorem singlePolymer_log_le_neg_log
    {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    Real.log (1 + z) ≤ -Real.log (1 - z) := by
  have h1 : Real.log (1 + z) + Real.log (1 - z) = Real.log ((1 + z) * (1 - z)) :=
    (Real.log_mul (by positivity) (by nlinarith)).symm
  have h2 : Real.log ((1 + z) * (1 - z)) ≤ 0 :=
    Real.log_nonpos (by nlinarith) (by nlinarith)
  linarith

end IsingModel
