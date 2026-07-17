import IsingModel.InfiniteVolume.Boundedness

/-!
# GHS inequality split — truncated 2- and 3-point function definitions and special values

Part of the split GHS-inequality layer (Issue #1850).
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Truncated correlation functions -/

/-- The truncated 2-point function (connected correlation):
`⟨σ_i; σ_j⟩ = ⟨σ_iσ_j⟩ - ⟨σ_i⟩⟨σ_j⟩`. -/
noncomputable def truncated2 (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (i j : ι) : ℝ :=
  correlation G p {i, j} - correlation G p {i} * correlation G p {j}

/-- The truncated 3-point function (Ursell function) for distinct sites:
`⟨σ_i; σ_j; σ_k⟩ = ⟨σ_iσ_jσ_k⟩ - ⟨σ_i⟩⟨σ_jσ_k⟩ - ⟨σ_j⟩⟨σ_iσ_k⟩
  - ⟨σ_k⟩⟨σ_iσ_j⟩ + 2⟨σ_i⟩⟨σ_j⟩⟨σ_k⟩`. -/
noncomputable def truncated3 (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (i j k : ι) : ℝ :=
  correlation G p {i, j, k}
  - correlation G p {i} * correlation G p {j, k}
  - correlation G p {j} * correlation G p {i, k}
  - correlation G p {k} * correlation G p {i, j}
  + 2 * correlation G p {i} * correlation G p {j} * correlation G p {k}

/-- **Non-interacting (`J = 0`) factorisation of the truncated
2-point function**: for any distinct sites `i ≠ j`, any `h, β ∈ ℝ`,
and any ambient graph `G`, `truncated2 G ⟨0, h, β⟩ i j = 0`.

At `J = 0` the sites are non-interacting, and `correlation_J_zero`
gives `⟨σ^A⟩ = tanh(β·h)^|A|`; for `i ≠ j` one has `{i,j}.card = 2`,
so `⟨σ_i σ_j⟩ = tanh(β·h)^2 = ⟨σ_i⟩ · ⟨σ_j⟩`.

This is the trivial non-interacting slice of the cluster property
discussion in Glimm–Jaffe *Quantum Physics* 2nd ed., §5.1
pp. 72–74. No distance / separation hypothesis is needed: at
`J = 0` the factorisation is identically true for any two distinct
sites, since the Hamiltonian has no `J`-coupling term to link
them. This is disjoint from the high-temperature (`β` small)
regime; here `β` is arbitrary. -/
theorem truncated2_J_zero_of_ne (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h β : ℝ) {i j : ι} (hij : i ≠ j) :
    truncated2 G (⟨0, h, β⟩ : IsingParams ℝ) i j = 0 := by
  unfold truncated2
  rw [correlation_J_zero, correlation_J_zero, correlation_J_zero]
  have hcard_pair : ({i, j} : Finset ι).card = 2 := by
    rw [Finset.card_pair hij]
  have hcard_i : ({i} : Finset ι).card = 1 := Finset.card_singleton i
  have hcard_j : ({j} : Finset ι).card = 1 := Finset.card_singleton j
  rw [hcard_pair, hcard_i, hcard_j]
  ring

/-- **Infinite-temperature (`β = 0`) vanishing of the truncated
2-point function**: for any ambient graph `G`, any `J, h ∈ ℝ`, and
any sites `i, j : ι` (not necessarily distinct),
`truncated2 G ⟨J, h, 0⟩ i j = 0`.

At `β = 0` the Boltzmann weight is identically `1`, so
`correlation G ⟨J, h, 0⟩` is the uniform spin average; by
`correlation_beta_zero_vanish_of_nonempty_A`, this vanishes on
any nonempty subset. Hence each of `correlation G ⟨J, h, 0⟩ {i, j}`,
`correlation G ⟨J, h, 0⟩ {i}`, and `correlation G ⟨J, h, 0⟩ {j}`
is `0`, so the difference is `0`.

Companion to `truncated2_J_zero_of_ne`. Unlike the `J = 0` case,
this statement needs no `i ≠ j` hypothesis. When `i = j` the
`truncated2` definition uses the Finset `{i, j} = {i}`, so the
first term is `correlation G ⟨J, h, 0⟩ {i}`, not the physics
product `⟨σ_i σ_i⟩ = 1`; this finset-level first term also
vanishes at `β = 0`.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.1 pp. 72–74
(cluster property context); §4.1 infinite-temperature slice of
the correlation function. -/
theorem truncated2_beta_zero (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h : ℝ) (i j : ι) :
    truncated2 G (⟨J, h, 0⟩ : IsingParams ℝ) i j = 0 := by
  unfold truncated2
  rw [correlation_beta_zero_vanish_of_nonempty_A G J h {i, j}
        ⟨i, by simp⟩,
      correlation_beta_zero_vanish_of_nonempty_A G J h {i}
        (Finset.singleton_nonempty i),
      correlation_beta_zero_vanish_of_nonempty_A G J h {j}
        (Finset.singleton_nonempty j)]
  ring

/-- **Non-interacting (`J = 0`) vanishing of the truncated 3-point
function (Ursell)**: for pairwise distinct sites `i ≠ j`, `j ≠ k`,
`i ≠ k`, any `h, β ∈ ℝ`, and any ambient graph `G`,
`truncated3 G ⟨0, h, β⟩ i j k = 0`.

At `J = 0` the sites are non-interacting, and `correlation_J_zero`
gives `⟨σ^A⟩ = tanh(β·h)^|A|`. With `t := tanh(β·h)` and the
Ursell combination
`⟨σ^{i,j,k}⟩ - ⟨σ^{i}⟩⟨σ^{j,k}⟩ - ⟨σ^{j}⟩⟨σ^{i,k}⟩
 - ⟨σ^{k}⟩⟨σ^{i,j}⟩ + 2⟨σ^{i}⟩⟨σ^{j}⟩⟨σ^{k}⟩`,
the cardinalities are `3, 1+2, 1+2, 1+2, 1+1+1`, all giving `t^3`;
the algebraic combination is `t³ - 3·t³ + 2·t³ = 0`.

Pairwise distinctness is needed so that `{i,j,k}.card = 3` and
the three 2-point subsets each have card `2`. Companion to
`truncated2_J_zero_of_ne`. Reference: Glimm–Jaffe *Quantum Physics*
2nd ed., §5.1 pp. 72–74 (cluster property context); §4.3 (Ursell
functions / GHS inequalities). -/
theorem truncated3_J_zero_of_pairwise_distinct
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h β : ℝ) {i j k : ι}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    truncated3 G (⟨0, h, β⟩ : IsingParams ℝ) i j k = 0 := by
  unfold truncated3
  rw [correlation_J_zero, correlation_J_zero, correlation_J_zero,
      correlation_J_zero, correlation_J_zero, correlation_J_zero,
      correlation_J_zero]
  have hcard_i : ({i} : Finset ι).card = 1 := Finset.card_singleton i
  have hcard_j : ({j} : Finset ι).card = 1 := Finset.card_singleton j
  have hcard_k : ({k} : Finset ι).card = 1 := Finset.card_singleton k
  have hcard_ij : ({i, j} : Finset ι).card = 2 := Finset.card_pair hij
  have hcard_jk : ({j, k} : Finset ι).card = 2 := Finset.card_pair hjk
  have hcard_ik : ({i, k} : Finset ι).card = 2 := Finset.card_pair hik
  have hi_nin_jk : i ∉ ({j, k} : Finset ι) := by
    simp [hij, hik]
  have hcard_ijk : ({i, j, k} : Finset ι).card = 3 := by
    rw [show ({i, j, k} : Finset ι) = insert i ({j, k} : Finset ι) from rfl,
        Finset.card_insert_of_notMem hi_nin_jk, hcard_jk]
  rw [hcard_i, hcard_j, hcard_k, hcard_ij, hcard_jk, hcard_ik, hcard_ijk]
  ring

/-- **Infinite-temperature (`β = 0`) vanishing of the truncated
3-point function (Ursell)**: for any ambient graph `G`, any
`J, h ∈ ℝ`, and any sites `i, j, k : ι` (distinct or not),
`truncated3 G ⟨J, h, 0⟩ i j k = 0`.

At `β = 0`, `correlation_beta_zero_vanish_of_nonempty_A` makes each
Finset correlation in the Ursell combination zero (all subsets
`{i,j,k}`, `{i}`, `{j}`, `{k}`, `{j,k}`, `{i,k}`, `{i,j}` are
nonempty), so the whole linear combination vanishes trivially.

Companion to `truncated2_beta_zero` and
`truncated3_J_zero_of_pairwise_distinct`. No distinctness
hypotheses are needed at `β = 0`. Reference: Glimm–Jaffe
*Quantum Physics* 2nd ed., §5.1 pp. 72–74 (cluster property
context); §4.1 infinite-temperature slice of the correlation
function. -/
theorem truncated3_beta_zero (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h : ℝ) (i j k : ι) :
    truncated3 G (⟨J, h, 0⟩ : IsingParams ℝ) i j k = 0 := by
  unfold truncated3
  rw [correlation_beta_zero_vanish_of_nonempty_A G J h {i, j, k}
        ⟨i, by simp⟩,
      correlation_beta_zero_vanish_of_nonempty_A G J h {i}
        (Finset.singleton_nonempty i),
      correlation_beta_zero_vanish_of_nonempty_A G J h {j}
        (Finset.singleton_nonempty j),
      correlation_beta_zero_vanish_of_nonempty_A G J h {k}
        (Finset.singleton_nonempty k),
      correlation_beta_zero_vanish_of_nonempty_A G J h {j, k}
        ⟨j, by simp⟩,
      correlation_beta_zero_vanish_of_nonempty_A G J h {i, k}
        ⟨i, by simp⟩,
      correlation_beta_zero_vanish_of_nonempty_A G J h {i, j}
        ⟨i, by simp⟩]
  ring

/-- The truncated 2-point function is non-negative by GKS-II. -/
theorem truncated2_nonneg (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j : ι) :
    0 ≤ truncated2 G p i j := by
  unfold truncated2
  by_cases hij : i = j
  · subst hij
    have h1 := gks_first G p hf {i}
    have h2 := abs_correlation_le_one G p {i}
    have h3 : correlation G p {i} ≤ 1 := le_trans (le_abs_self _) h2
    have hpair : ({i, i} : Finset ι) = {i} := by simp
    rw [hpair]; nlinarith
  · have h := gks_second G p hf {i} {j}
    have hsym : symmDiff {i} {j} = ({i, j} : Finset ι) := by
      ext x; simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_insert]
      exact ⟨fun h => h.elim (fun ⟨h, _⟩ => Or.inl h) (fun ⟨h, _⟩ => Or.inr h),
        fun h => h.elim (fun h => Or.inl ⟨h, h ▸ hij⟩)
          (fun h => Or.inr ⟨h, h ▸ Ne.symm hij⟩)⟩
    rw [hsym] at h; linarith


end IsingModel
