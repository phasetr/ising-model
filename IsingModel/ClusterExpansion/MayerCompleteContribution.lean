import IsingModel.ClusterExpansion.MayerRootComponent
import IsingModel.ClusterExpansion.MayerCore.ZeroBounds
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

/-- **Polymer family sum is bounded by the product over single polymers**
(GJ §18.5, convergence): for `t ≥ 0`, `∑_Γ ∏_{P∈Γ} t^|P| ≤ ∏_P (1 + t^|P|)`. The
compatible families form a subset of *all* subsets of `allPolymers G`, and the
product expansion `Finset.prod_one_add` rewrites the full subset sum as the
product; the dropped (incompatible) families contribute non-negatively. The
"independent-polymer" upper bound, sharper than the `|E|`-based sandwich. -/
theorem vdPolymerFamilies_sum_le_prod_one_add
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] {t : ℝ} (ht0 : 0 ≤ t) :
    (∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, t ^ P.card)
      ≤ ∏ P ∈ allPolymers G, (1 + t ^ P.card) := by
  rw [Finset.prod_one_add]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro Γ hΓ
    rw [Finset.mem_powerset]
    exact (mem_vdCompatiblePolymerFamilies.mp hΓ).1
  · intro Γ _ _
    exact Finset.prod_nonneg (fun P _ => pow_nonneg ht0 _)

/-- **Polymer free energy is bounded by the sum of single-polymer logs** (GJ §18.5):
for `t ≥ 0`, `polymerFreeEnergy G t ≤ ∑_P log(1 + t^|P|)`. Monotonicity of `log`
applied to `vdPolymerFamilies_sum_le_prod_one_add`, with `Real.log_prod` turning the
product into the sum. The free energy is bounded by the independent-polymer
contributions. -/
theorem polymerFreeEnergy_le_sum_log_one_add
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] {t : ℝ} (ht0 : 0 ≤ t) :
    polymerFreeEnergy G t ≤ ∑ P ∈ allPolymers G, Real.log (1 + t ^ P.card) := by
  have hpos : ∀ P : Finset (Sym2 ι), (0 : ℝ) < 1 + t ^ P.card :=
    fun P => by have := pow_nonneg ht0 P.card; linarith
  rw [polymerFreeEnergy, ← Real.log_prod (fun P _ => (hpos P).ne'),
    Real.log_le_log_iff (vdPolymerFamilies_sum_pos_of_nonneg G ht0)
      (Finset.prod_pos (fun P _ => hpos P))]
  exact vdPolymerFamilies_sum_le_prod_one_add G ht0

/-- **Polymer free energy is bounded by the single-polymer cluster contributions**
(GJ §18.5): in the convergence regime `t^|P| < 1` for every polymer,
`polymerFreeEnergy G t ≤ ∑_P (∑'_m ϕ^T(P,…,P)·z)`, i.e. the free energy is dominated
by the sum of independent single-polymer Mayer contributions
(`tsum_singlePolymer_ursell_eq_log`, each `= log(1+t^|P|)`). -/
theorem polymerFreeEnergy_le_sum_singlePolymer_contribution
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] {t : ℝ} (ht0 : 0 ≤ t)
    (ht : ∀ P ∈ allPolymers G, |t ^ P.card| < 1) :
    polymerFreeEnergy G t
      ≤ ∑ P ∈ allPolymers G, ∑' m : ℕ, ursellCoefficient (fun _ : Fin (m + 1) => P)
          * clusterSeqActivity t (fun _ : Fin (m + 1) => P) := by
  refine (polymerFreeEnergy_le_sum_log_one_add G ht0).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl (fun P hP => ?_)
  exact (tsum_singlePolymer_ursell_eq_log (mem_allPolymers.mp hP) (ht P hP)).symm

/-- **A single polymer forms a compatible (vertex-disjoint) family**: `{P}` is a
compatible family whenever `P` is a polymer (the polymer condition holds and
pairwise disjointness is vacuous on a singleton). -/
theorem IsCompatiblePolymerFamilyVertexDisjoint.singleton
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : SimpleGraph ι} [Fintype G.edgeSet] {P : Finset (Sym2 ι)} (hP : IsPolymer G P) :
    IsCompatiblePolymerFamilyVertexDisjoint G {P} := by
  refine ⟨?_, ?_⟩
  · intro Q hQ
    rw [Finset.mem_singleton] at hQ
    exact hQ ▸ hP
  · rw [Finset.coe_singleton]
    exact Set.pairwise_singleton P _

/-- **Polymer family sum lower bound by the single polymers** (GJ §18.5): for
`t ≥ 0`, `1 + ∑_P t^|P| ≤ ∑_Γ ∏_{P∈Γ} t^|P|`. The empty family contributes `1`
and each single-polymer family `{P}` contributes `t^|P|`; these are compatible
families (`IsCompatiblePolymerFamilyVertexDisjoint.empty` / `.singleton`), and the
remaining families contribute non-negatively. -/
theorem one_add_sum_le_vdPolymerFamilies_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] {t : ℝ} (ht0 : 0 ≤ t) :
    1 + ∑ P ∈ allPolymers G, t ^ P.card
      ≤ ∑ Γ ∈ vdCompatiblePolymerFamilies G, ∏ P ∈ Γ, t ^ P.card := by
  classical
  have hsub : insert (∅ : Finset (Finset (Sym2 ι)))
      ((allPolymers G).image (fun P => ({P} : Finset (Finset (Sym2 ι)))))
      ⊆ vdCompatiblePolymerFamilies G := by
    intro Γ hΓ
    rw [Finset.mem_insert] at hΓ
    rw [mem_vdCompatiblePolymerFamilies]
    rcases hΓ with rfl | hΓ
    · exact ⟨Finset.empty_subset _, IsCompatiblePolymerFamilyVertexDisjoint.empty G⟩
    · rw [Finset.mem_image] at hΓ
      obtain ⟨P, hP, rfl⟩ := hΓ
      exact ⟨Finset.singleton_subset_iff.mpr hP,
        IsCompatiblePolymerFamilyVertexDisjoint.singleton (mem_allPolymers.mp hP)⟩
  have hnotmem : (∅ : Finset (Finset (Sym2 ι)))
      ∉ (allPolymers G).image (fun P => ({P} : Finset (Finset (Sym2 ι)))) := by
    rw [Finset.mem_image]
    rintro ⟨P, _, hP⟩
    exact absurd hP (Finset.singleton_ne_empty P)
  have hinj : Set.InjOn (fun P => ({P} : Finset (Finset (Sym2 ι)))) (allPolymers G) :=
    fun a _ b _ hab => by simpa using hab
  have heval : ∑ Γ ∈ insert (∅ : Finset (Finset (Sym2 ι)))
      ((allPolymers G).image (fun P => ({P} : Finset (Finset (Sym2 ι))))),
      ∏ P ∈ Γ, t ^ P.card = 1 + ∑ P ∈ allPolymers G, t ^ P.card := by
    rw [Finset.sum_insert hnotmem, Finset.sum_image hinj, Finset.prod_empty]
    simp
  rw [← heval]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun Γ _ _ => Finset.prod_nonneg (fun P _ => pow_nonneg ht0 _))

/-- **Polymer free energy lower bound** (GJ §18.5): for `t ≥ 0`,
`log(1 + ∑_P t^|P|) ≤ polymerFreeEnergy G t`. Monotonicity of `log` applied to
`one_add_sum_le_vdPolymerFamilies_sum`. -/
theorem log_one_add_sum_le_polymerFreeEnergy
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] {t : ℝ} (ht0 : 0 ≤ t) :
    Real.log (1 + ∑ P ∈ allPolymers G, t ^ P.card) ≤ polymerFreeEnergy G t := by
  have hpos : (0 : ℝ) < 1 + ∑ P ∈ allPolymers G, t ^ P.card := by
    have : (0 : ℝ) ≤ ∑ P ∈ allPolymers G, t ^ P.card :=
      Finset.sum_nonneg (fun P _ => pow_nonneg ht0 _)
    linarith
  rw [polymerFreeEnergy, Real.log_le_log_iff hpos (vdPolymerFamilies_sum_pos_of_nonneg G ht0)]
  exact one_add_sum_le_vdPolymerFamilies_sum G ht0

/-- **Independent-polymer sandwich for the polymer free energy** (GJ §18.5):
for `t ≥ 0`, `log(1 + ∑_P t^|P|) ≤ polymerFreeEnergy G t ≤ ∑_P log(1 + t^|P|)`.
The free energy is bracketed by the two independent-polymer expressions
(`log_one_add_sum_le_polymerFreeEnergy`, `polymerFreeEnergy_le_sum_log_one_add`). -/
theorem polymerFreeEnergy_sandwich_independent
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] {t : ℝ} (ht0 : 0 ≤ t) :
    Real.log (1 + ∑ P ∈ allPolymers G, t ^ P.card) ≤ polymerFreeEnergy G t
      ∧ polymerFreeEnergy G t ≤ ∑ P ∈ allPolymers G, Real.log (1 + t ^ P.card) :=
  ⟨log_one_add_sum_le_polymerFreeEnergy G ht0, polymerFreeEnergy_le_sum_log_one_add G ht0⟩

/-- **Ising free energy independent-polymer sandwich** (GJ §18.5): substituting the
polymer-free-energy sandwich into the polymer decomposition of the Ising free
energy (`freeEnergy_eq_polymerFreeEnergy`) brackets the physical free energy by
the independent-polymer expressions at activity `tanh(β·J)`. For `0 ≤ β·J` and a
non-empty vertex set,
`log 2 + (|E|/|ι|)·log cosh(β·J) + log(1 + ∑_P tanh(β·J)^|P|)/|ι| ≤ freeEnergy
≤ … + (∑_P log(1 + tanh(β·J)^|P|))/|ι|`. -/
theorem freeEnergy_sandwich_independent_polymer
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℝ) (hβJ : 0 ≤ β * J)
    (hne : 0 < Fintype.card ι) :
    Real.log 2 + (G.edgeFinset.card : ℝ) / Fintype.card ι * Real.log (Real.cosh (β * J))
          + Real.log (1 + ∑ P ∈ allPolymers G, Real.tanh (β * J) ^ P.card)
            / Fintype.card ι
        ≤ freeEnergy G ⟨J, 0, β⟩
      ∧ freeEnergy G ⟨J, 0, β⟩
        ≤ Real.log 2 + (G.edgeFinset.card : ℝ) / Fintype.card ι * Real.log (Real.cosh (β * J))
          + (∑ P ∈ allPolymers G, Real.log (1 + Real.tanh (β * J) ^ P.card))
            / Fintype.card ι := by
  have ht0 : 0 ≤ Real.tanh (β * J) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr hβJ) (Real.cosh_pos _).le
  have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hne
  obtain ⟨hlo, hhi⟩ := polymerFreeEnergy_sandwich_independent G ht0
  rw [freeEnergy_eq_polymerFreeEnergy G J β hβJ hne]
  refine ⟨?_, ?_⟩ <;> gcongr

/-- **Ising free energy explicit upper bound** (GJ §18.5): a coarser but explicit
upper bound `freeEnergy ≤ log 2 + (|E|/|ι|)·log cosh(β·J) + (∑_P tanh(β·J)^|P|)/|ι|`,
using `log(1 + x) ≤ x` on the independent-polymer sandwich. -/
theorem freeEnergy_le_log_two_plus_sum_tanh_pow
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℝ) (hβJ : 0 ≤ β * J)
    (hne : 0 < Fintype.card ι) :
    freeEnergy G ⟨J, 0, β⟩
      ≤ Real.log 2 + (G.edgeFinset.card : ℝ) / Fintype.card ι * Real.log (Real.cosh (β * J))
        + (∑ P ∈ allPolymers G, Real.tanh (β * J) ^ P.card) / Fintype.card ι := by
  have ht0 : 0 ≤ Real.tanh (β * J) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr hβJ) (Real.cosh_pos _).le
  have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hne
  refine (freeEnergy_sandwich_independent_polymer G J β hβJ hne).2.trans ?_
  have hsum : (∑ P ∈ allPolymers G, Real.log (1 + Real.tanh (β * J) ^ P.card))
      ≤ ∑ P ∈ allPolymers G, Real.tanh (β * J) ^ P.card := by
    refine Finset.sum_le_sum (fun P _ => ?_)
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + Real.tanh (β * J) ^ P.card by
      have := pow_nonneg ht0 P.card; linarith)
    linarith
  gcongr

/-- **Total cluster-activity over `piFinset` is a power** (GJ §18.4): summing the
cluster activity over *all* length-`n` polymer sequences factorises,
`∑_{ω} ∏_i t^|ω_i| = (∑_P t^|P|)^n`, by `Finset.prod_univ_sum` (the product over
the `n` coordinates of the per-coordinate activity sum). -/
theorem sum_clusterSeqActivity_piFinset_eq_pow
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (n : ℕ) (t : ℝ) :
    ∑ ω ∈ Fintype.piFinset (fun _ : Fin n => allPolymers G), clusterSeqActivity t ω
      = (∑ P ∈ allPolymers G, t ^ P.card) ^ n := by
  classical
  unfold clusterSeqActivity
  rw [Finset.sum_prod_piFinset (allPolymers G) (fun (_ : Fin n) P => t ^ P.card)]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **Absolute bound on the complete-cluster Mayer subsum** (GJ §18.4): the
fully-incompatible part of the `n`-th Mayer term has absolute value at most
`(1/n) · ∑ |clusterSeqActivity|`.  From the closed form
`mayerExpansionTerm_completeClusterSubsum_eq` (the subsum is
`((-1)^{n-1}/n)·∑ clusterSeqActivity`) with `|(-1)^{n-1}/n| = 1/n` and the
triangle inequality on the activity sum. -/
theorem abs_mayerExpansionTerm_completeClusterSubsum_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    |∑ ω ∈ (Fintype.piFinset (fun _ : Fin n => allPolymers G)).filter
        (fun ω => ∀ i j, i ≠ j → PolymersIncompatible (ω i) (ω j)),
        ursellCoefficient ω * clusterSeqActivity t ω|
      ≤ (1 / (n : ℝ)) * ∑ ω ∈ (Fintype.piFinset (fun _ : Fin n => allPolymers G)).filter
          (fun ω => ∀ i j, i ≠ j → PolymersIncompatible (ω i) (ω j)),
          |clusterSeqActivity t ω| := by
  rw [mayerExpansionTerm_completeClusterSubsum_eq G hn t, abs_mul]
  have habs : |((-1 : ℝ) ^ (n - 1) / (n : ℝ))| = 1 / (n : ℝ) := by
    rw [abs_div, abs_pow, abs_neg, abs_one, one_pow, Nat.abs_cast]
  rw [habs]
  gcongr
  exact Finset.abs_sum_le_sum_abs _ _

/-- **Complete-cluster Mayer subsum bound for non-negative activity** (GJ §18.4):
for `0 ≤ t` the activity factors are non-negative, so the bound simplifies to
`(1/n) · ∑ clusterSeqActivity` (absolute values dropped). -/
theorem abs_mayerExpansionTerm_completeClusterSubsum_le_of_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : 0 ≤ t) :
    |∑ ω ∈ (Fintype.piFinset (fun _ : Fin n => allPolymers G)).filter
        (fun ω => ∀ i j, i ≠ j → PolymersIncompatible (ω i) (ω j)),
        ursellCoefficient ω * clusterSeqActivity t ω|
      ≤ (1 / (n : ℝ)) * ∑ ω ∈ (Fintype.piFinset (fun _ : Fin n => allPolymers G)).filter
          (fun ω => ∀ i j, i ≠ j → PolymersIncompatible (ω i) (ω j)),
          clusterSeqActivity t ω := by
  refine le_trans (abs_mayerExpansionTerm_completeClusterSubsum_le G hn t) ?_
  gcongr with ω _
  exact (abs_of_nonneg (clusterSeqActivity_nonneg ht ω)).le

/-- **Closed-form bound on the complete-cluster Mayer subsum** (GJ §18.4): for
`0 ≤ t`, the fully-incompatible part of the `n`-th Mayer term is bounded by
`(1/n)·(∑_P t^|P|)^n`.  The complete filter is enlarged to the full `piFinset`
(non-negative terms) and the total activity sum is the power
`sum_clusterSeqActivity_piFinset_eq_pow` — a clean closed bound on the dominant
(fully-incompatible) cluster contribution at every order. -/
theorem abs_mayerExpansionTerm_completeClusterSubsum_le_pow
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : 0 ≤ t) :
    |∑ ω ∈ (Fintype.piFinset (fun _ : Fin n => allPolymers G)).filter
        (fun ω => ∀ i j, i ≠ j → PolymersIncompatible (ω i) (ω j)),
        ursellCoefficient ω * clusterSeqActivity t ω|
      ≤ (1 / (n : ℝ)) * (∑ P ∈ allPolymers G, t ^ P.card) ^ n := by
  refine le_trans (abs_mayerExpansionTerm_completeClusterSubsum_le_of_nonneg G hn ht) ?_
  gcongr
  rw [← sum_clusterSeqActivity_piFinset_eq_pow G n t, Finset.sum_filter]
  refine Finset.sum_le_sum (fun ω _ => ?_)
  split_ifs with hp
  · exact le_refl _
  · exact clusterSeqActivity_nonneg ht ω

/-- **Summability (absolute) of the complete-cluster contributions** (GJ §18.5):
for `0 ≤ t` and total activity `∑_P t^|P| < 1`, the magnitudes of the
fully-incompatible Mayer subsums are summable in the cluster size `n`.  Comparison
with the geometric series: `|complete subsum_{n+1}| ≤ (∑_P t^|P|)^{n+1}` (from
`abs_mayerExpansionTerm_completeClusterSubsum_le_pow` with `1/(n+1) ≤ 1`), and the
geometric series in `S = ∑_P t^|P| < 1` is summable. -/
theorem summable_abs_completeClusterSubsum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] {t : ℝ} (ht : 0 ≤ t)
    (hS : (∑ P ∈ allPolymers G, t ^ P.card) < 1) :
    Summable (fun n => |∑ ω ∈ (Fintype.piFinset (fun _ : Fin n => allPolymers G)).filter
        (fun ω => ∀ i j, i ≠ j → PolymersIncompatible (ω i) (ω j)),
        ursellCoefficient ω * clusterSeqActivity t ω|) := by
  set S := ∑ P ∈ allPolymers G, t ^ P.card with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun P _ => pow_nonneg ht _)
  have hmaj : Summable (fun n : ℕ => S ^ (n + 1)) :=
    (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hS0 hS)
  rw [← summable_nat_add_iff 1]
  refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_) hmaj
  refine le_trans (abs_mayerExpansionTerm_completeClusterSubsum_le_pow G (by omega) ht) ?_
  rw [← hSdef]
  have hpow : (0 : ℝ) ≤ S ^ (n + 1) := pow_nonneg hS0 _
  have hle1 : (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ≤ 1 := by
    rw [div_le_one (by positivity)]
    push_cast; linarith [Nat.cast_nonneg (α := ℝ) n]
  calc (1 / ((n + 1 : ℕ) : ℝ)) * S ^ (n + 1)
      ≤ 1 * S ^ (n + 1) := mul_le_mul_of_nonneg_right hle1 hpow
    _ = S ^ (n + 1) := one_mul _

/-- **Summability of the complete-cluster contributions** (GJ §18.5): the
fully-incompatible Mayer subsums themselves are summable in `n` (for `0 ≤ t`,
`∑_P t^|P| < 1`), since absolute summability implies summability over `ℝ`. -/
theorem summable_completeClusterSubsum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] {t : ℝ} (ht : 0 ≤ t)
    (hS : (∑ P ∈ allPolymers G, t ^ P.card) < 1) :
    Summable (fun n => ∑ ω ∈ (Fintype.piFinset (fun _ : Fin n => allPolymers G)).filter
        (fun ω => ∀ i j, i ≠ j → PolymersIncompatible (ω i) (ω j)),
        ursellCoefficient ω * clusterSeqActivity t ω) :=
  summable_abs_iff.mp (summable_abs_completeClusterSubsum G ht hS)

/-- **High-temperature Ising complete-cluster bound** (GJ §18.4–18.5): the Ising
specialisation of `abs_mayerExpansionTerm_completeClusterSubsum_le_pow` at the
physical activity `t = tanh(βJ)` (for `0 ≤ βJ`).  The fully-incompatible part of
the `n`-th cluster term is bounded by `(1/n)·(∑_P tanh(βJ)^|P|)^n`. -/
theorem abs_mayerExpansionTerm_completeClusterSubsum_le_pow_tanh
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] {n : ℕ} (hn : 1 ≤ n) {β J : ℝ}
    (hβJ : 0 ≤ β * J) :
    |∑ ω ∈ (Fintype.piFinset (fun _ : Fin n => allPolymers G)).filter
        (fun ω => ∀ i j, i ≠ j → PolymersIncompatible (ω i) (ω j)),
        ursellCoefficient ω * clusterSeqActivity (Real.tanh (β * J)) ω|
      ≤ (1 / (n : ℝ)) * (∑ P ∈ allPolymers G, Real.tanh (β * J) ^ P.card) ^ n :=
  abs_mayerExpansionTerm_completeClusterSubsum_le_pow G hn (real_tanh_nonneg hβJ)

/-- **High-temperature Ising complete-cluster summability (absolute)** (GJ
§18.5): the Ising specialisation of `summable_abs_completeClusterSubsum` at the
physical activity `tanh(βJ)`, valid when `∑_P tanh(βJ)^|P| < 1`. -/
theorem summable_abs_completeClusterSubsum_tanh
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hS : (∑ P ∈ allPolymers G, Real.tanh (β * J) ^ P.card) < 1) :
    Summable (fun n => |∑ ω ∈ (Fintype.piFinset (fun _ : Fin n => allPolymers G)).filter
        (fun ω => ∀ i j, i ≠ j → PolymersIncompatible (ω i) (ω j)),
        ursellCoefficient ω * clusterSeqActivity (Real.tanh (β * J)) ω|) :=
  summable_abs_completeClusterSubsum G (real_tanh_nonneg hβJ) hS

/-- **High-temperature Ising complete-cluster summability** (GJ §18.5): for
`0 ≤ βJ` and `∑_P tanh(βJ)^|P| < 1`, the fully-incompatible cluster contributions
to the Ising high-temperature expansion are summable — the dominant part of the
Ising cluster expansion converges in this explicit high-temperature regime. -/
theorem summable_completeClusterSubsum_tanh
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hS : (∑ P ∈ allPolymers G, Real.tanh (β * J) ^ P.card) < 1) :
    Summable (fun n => ∑ ω ∈ (Fintype.piFinset (fun _ : Fin n => allPolymers G)).filter
        (fun ω => ∀ i j, i ≠ j → PolymersIncompatible (ω i) (ω j)),
        ursellCoefficient ω * clusterSeqActivity (Real.tanh (β * J)) ω) :=
  summable_completeClusterSubsum G (real_tanh_nonneg hβJ) hS

/-- **Mayer expansion convergence reduced to an Ursell-coefficient bound** (GJ
§18.5): if the Ursell coefficients satisfy a per-order bound `|ϕ^T(ω)| ≤ M n`
(uniformly over length-`n` sequences) and the majorant series `∑_n M n·(∑_P t^|P|)^n`
is summable, then the full Mayer expansion `∑_n mayerExpansionTerm G n t` is
summable (for `0 ≤ t`).  Proof: `|mayerExpansionTerm G n t| ≤ ∑_ω |ϕ^T(ω)|·z(ω) ≤
M n·∑_ω z(ω) = M n·(∑_P t^|P|)^n` (triangle inequality, the per-order bound, and
`sum_clusterSeqActivity_piFinset_eq_pow`), then comparison.  This isolates the
sole remaining hard input of Kotecký–Preiss convergence — the tree-graph/Penrose
bound supplying `M n = n^{n-2}/n!` — from the analytic comparison step. -/
theorem summable_mayerExpansionTerm_of_ursell_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] {t : ℝ} (ht : 0 ≤ t)
    {M : ℕ → ℝ}
    (hM : ∀ n, ∀ ω ∈ Fintype.piFinset (fun _ : Fin n => allPolymers G),
      |ursellCoefficient ω| ≤ M n)
    (hsum : Summable (fun n => M n * (∑ P ∈ allPolymers G, t ^ P.card) ^ n)) :
    Summable (fun n => mayerExpansionTerm G n t) := by
  have hbound : ∀ n, |mayerExpansionTerm G n t|
      ≤ M n * (∑ P ∈ allPolymers G, t ^ P.card) ^ n := by
    intro n
    unfold mayerExpansionTerm
    calc |∑ ω ∈ Fintype.piFinset (fun _ : Fin n => allPolymers G),
            ursellCoefficient ω * clusterSeqActivity t ω|
        ≤ ∑ ω ∈ Fintype.piFinset (fun _ : Fin n => allPolymers G),
            |ursellCoefficient ω * clusterSeqActivity t ω| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ ω ∈ Fintype.piFinset (fun _ : Fin n => allPolymers G),
            M n * clusterSeqActivity t ω := by
            refine Finset.sum_le_sum (fun ω hω => ?_)
            rw [abs_mul, abs_of_nonneg (clusterSeqActivity_nonneg ht ω)]
            exact mul_le_mul_of_nonneg_right (hM n ω hω) (clusterSeqActivity_nonneg ht ω)
      _ = M n * ∑ ω ∈ Fintype.piFinset (fun _ : Fin n => allPolymers G),
            clusterSeqActivity t ω := by rw [← Finset.mul_sum]
      _ = M n * (∑ P ∈ allPolymers G, t ^ P.card) ^ n := by
            rw [sum_clusterSeqActivity_piFinset_eq_pow]
  exact summable_abs_iff.mp
    (Summable.of_nonneg_of_le (fun n => abs_nonneg _) hbound hsum)

/-- **Mayer expansion convergence reduced to an Ursell bound — Ising form** (GJ
§18.5): the `t = tanh(βJ)` specialisation of
`summable_mayerExpansionTerm_of_ursell_le`, for `0 ≤ βJ`.  Given a per-order
Ursell bound and summability of `∑_n M n·(∑_P tanh(βJ)^|P|)^n`, the Ising
high-temperature Mayer expansion converges. -/
theorem summable_mayerExpansionTerm_of_ursell_le_tanh
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] {β J : ℝ} (hβJ : 0 ≤ β * J)
    {M : ℕ → ℝ}
    (hM : ∀ n, ∀ ω ∈ Fintype.piFinset (fun _ : Fin n => allPolymers G),
      |ursellCoefficient ω| ≤ M n)
    (hsum : Summable (fun n => M n * (∑ P ∈ allPolymers G, Real.tanh (β * J) ^ P.card) ^ n)) :
    Summable (fun n => mayerExpansionTerm G n (Real.tanh (β * J))) :=
  summable_mayerExpansionTerm_of_ursell_le G (real_tanh_nonneg hβJ) hM hsum

end IsingModel
