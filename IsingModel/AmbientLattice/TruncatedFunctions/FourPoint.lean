import IsingModel.AmbientLattice.TruncatedFunctions.ThreePoint

/-!
# Infinite-volume truncated four-point functions

Mechanical child split from `AmbientLattice/TruncatedFunctions.lean`.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-! ## Truncated 4-point correlation + `U_4 ≤ 0` at `h = 0`

Lift `IsingModel.cor_4_3_3` (finite-volume `U_4 ≤ 0` at $h = 0$) to
the thermodynamic limit. For ferromagnetic Ising at $h = 0$ and
four pairwise-distinct sites:
$U_4(i, j, k, l) := \langle \sigma^{\{i,j,k,l\}} \rangle_\infty
  - \sum_\text{pairings} \langle \sigma^{\{·,·\}} \rangle_\infty
    \langle \sigma^{\{·,·\}} \rangle_\infty \le 0$.

Reference: Glimm–Jaffe §4.3 Corollary 4.3.3, pp. 68ff;
Friedli–Velenik §3.6.4. -/

/-- **Truncated 4-point correlation at infinite volume**:
the thermodynamic-limit analog of `IsingModel.truncated4`. -/
noncomputable def truncated4Infinite
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i j k l : V) : ℝ :=
  correlationInfinite G Λ p {i, j, k, l}
    - correlationInfinite G Λ p {i, j} * correlationInfinite G Λ p {k, l}
    - correlationInfinite G Λ p {i, k} * correlationInfinite G Λ p {j, l}
    - correlationInfinite G Λ p {i, l} * correlationInfinite G Λ p {j, k}

/-- **Unfolding of `truncated4Infinite`**: the defining pair-split
Ursell 4-point formula as a named identity. -/
theorem truncated4Infinite_apply
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i j k l : V) :
    truncated4Infinite G Λ p i j k l
      = correlationInfinite G Λ p {i, j, k, l}
        - correlationInfinite G Λ p {i, j} * correlationInfinite G Λ p {k, l}
        - correlationInfinite G Λ p {i, k} * correlationInfinite G Λ p {j, l}
        - correlationInfinite G Λ p {i, l} * correlationInfinite G Λ p {j, k} := rfl

/-- **`truncated4Infinite` symmetry under swapping `i, j`**: adjacent
swap. The pair-split formula is fully symmetric in the four arguments. -/
theorem truncated4Infinite_swap_ij
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i j k l : V) :
    truncated4Infinite G Λ p i j k l = truncated4Infinite G Λ p j i k l := by
  unfold truncated4Infinite
  have h1 : ({i, j, k, l} : Finset V) = {j, i, k, l} := by rw [Finset.insert_comm]
  have h2 : ({i, j} : Finset V) = {j, i} := Finset.pair_comm i j
  rw [h1, h2]
  ring

/-- **`truncated4Infinite` symmetry under swapping `k, l`**: adjacent swap. -/
theorem truncated4Infinite_swap_kl
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i j k l : V) :
    truncated4Infinite G Λ p i j k l = truncated4Infinite G Λ p i j l k := by
  unfold truncated4Infinite
  have h1 : ({i, j, k, l} : Finset V) = {i, j, l, k} := by
    congr 1; congr 1
    exact Finset.pair_comm k l
  have h2 : ({k, l} : Finset V) = {l, k} := Finset.pair_comm k l
  rw [h1, h2]
  ring

/-- **`truncated4Infinite` symmetry under swapping `j, k`**: adjacent swap. -/
theorem truncated4Infinite_swap_jk
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i j k l : V) :
    truncated4Infinite G Λ p i j k l = truncated4Infinite G Λ p i k j l := by
  unfold truncated4Infinite
  have h1 : ({i, j, k, l} : Finset V) = {i, k, j, l} := by
    congr 1
    rw [Finset.insert_comm]
  have h2 : ({j, k} : Finset V) = {k, j} := Finset.pair_comm j k
  rw [h1, h2]
  ring

/-- **Truncated 4-point along an exhaustion** (local helper): evaluates
the `truncated4`-style algebraic expression at the `n`-th volume of
the exhaustion, using `correlationAlongExhaustion` instead of the
limit `correlationInfinite`.  This is the pointwise sequence whose
limit as `n → ∞` is `truncated4Infinite`; established separately so
that the `le_of_tendsto`-based `_nonpos_h_zero` proof can apply the
finite-volume `cor_4_3_3` to each term of the sequence. -/
private noncomputable def truncated4AlongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i j k l : V) (n : ℕ) : ℝ :=
  correlationAlongExhaustion G Λ p {i, j, k, l} n
    - correlationAlongExhaustion G Λ p {i, j} n
      * correlationAlongExhaustion G Λ p {k, l} n
    - correlationAlongExhaustion G Λ p {i, k} n
      * correlationAlongExhaustion G Λ p {j, l} n
    - correlationAlongExhaustion G Λ p {i, l} n
      * correlationAlongExhaustion G Λ p {j, k} n

/-- **Tendsto for the truncated 4-point sequence**: the pointwise
`truncated4AlongExhaustion` converges to `truncated4Infinite`.

This is the key technical step establishing that the thermodynamic
limit of the finite-volume truncated 4-point correlation exists and
equals the infinite-volume definition.  Proof: apply `Tendsto.sub`
and `Tendsto.mul` to the 7 `correlationInfinite` convergences from
`tendsto_correlationAlongExhaustion_correlationInfinite`. -/
private theorem tendsto_truncated4AlongExhaustion_truncated4Infinite
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j k l : V) :
    Filter.Tendsto
      (truncated4AlongExhaustion G Λ p i j k l)
      Filter.atTop
      (nhds (truncated4Infinite G Λ p i j k l)) := by
  unfold truncated4AlongExhaustion truncated4Infinite
  have h_ijkl := tendsto_correlationAlongExhaustion_correlationInfinite
    G Λ p hf {i,j,k,l}
  have h_ij := tendsto_correlationAlongExhaustion_correlationInfinite
    G Λ p hf {i,j}
  have h_kl := tendsto_correlationAlongExhaustion_correlationInfinite
    G Λ p hf {k,l}
  have h_ik := tendsto_correlationAlongExhaustion_correlationInfinite
    G Λ p hf {i,k}
  have h_jl := tendsto_correlationAlongExhaustion_correlationInfinite
    G Λ p hf {j,l}
  have h_il := tendsto_correlationAlongExhaustion_correlationInfinite
    G Λ p hf {i,l}
  have h_jk := tendsto_correlationAlongExhaustion_correlationInfinite
    G Λ p hf {j,k}
  exact ((h_ijkl.sub (h_ij.mul h_kl)).sub (h_ik.mul h_jl)).sub
    (h_il.mul h_jk)

/-- **`U_4 ≤ 0` at `h = 0`** at infinite volume: for a ferromagnetic
Ising model at vanishing external field and four pairwise-distinct
sites, $U_4 \le 0$.

Proof: at each `n` with `{i, j, k, l} ⊆ Λ.volume n`, the
finite-volume `cor_4_3_3` gives `truncated4AlongExhaustion n ≤ 0`
after identifying `liftFinset` patterns with the required subtype
Finsets.  Pass to the limit using
`tendsto_truncated4AlongExhaustion_truncated4Infinite` and
`le_of_tendsto`. -/
theorem truncated4Infinite_nonpos_h_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hf : Ferromagnetic ⟨J, (0 : ℝ), β⟩)
    {i j k l : V}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    truncated4Infinite G Λ ⟨J, 0, β⟩ i j k l ≤ 0 := by
  refine le_of_tendsto
    (tendsto_truncated4AlongExhaustion_truncated4Infinite G Λ _ hf i j k l) ?_
  obtain ⟨N, hN⟩ := Λ.exhaust ({i, j, k, l} : Finset V)
  rw [Filter.eventually_atTop]
  refine ⟨N, fun n hn => ?_⟩
  have habcd : ({i, j, k, l} : Finset V) ⊆ Λ.volume n := hN n hn
  -- Site memberships
  have mem_i : i ∈ Λ.volume n := habcd (by simp)
  have mem_j : j ∈ Λ.volume n := habcd (by simp)
  have mem_k : k ∈ Λ.volume n := habcd (by simp)
  have mem_l : l ∈ Λ.volume n := habcd (by simp)
  -- Pair subsets via a reusable helper
  have pair_sub : ∀ {a b : V}, a ∈ Λ.volume n → b ∈ Λ.volume n →
      ({a, b} : Finset V) ⊆ Λ.volume n := by
    intro a b ha hb x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hab : ({i, j} : Finset V) ⊆ Λ.volume n := pair_sub mem_i mem_j
  have hcd : ({k, l} : Finset V) ⊆ Λ.volume n := pair_sub mem_k mem_l
  have hac : ({i, k} : Finset V) ⊆ Λ.volume n := pair_sub mem_i mem_k
  have hbd : ({j, l} : Finset V) ⊆ Λ.volume n := pair_sub mem_j mem_l
  have had : ({i, l} : Finset V) ⊆ Λ.volume n := pair_sub mem_i mem_l
  have hbc : ({j, k} : Finset V) ⊆ Λ.volume n := pair_sub mem_j mem_k
  change truncated4AlongExhaustion G Λ ⟨J, 0, β⟩ i j k l n ≤ 0
  unfold truncated4AlongExhaustion
  rw [correlationAlongExhaustion_of_subset G Λ ⟨J, 0, β⟩ habcd,
      correlationAlongExhaustion_of_subset G Λ ⟨J, 0, β⟩ hab,
      correlationAlongExhaustion_of_subset G Λ ⟨J, 0, β⟩ hcd,
      correlationAlongExhaustion_of_subset G Λ ⟨J, 0, β⟩ hac,
      correlationAlongExhaustion_of_subset G Λ ⟨J, 0, β⟩ hbd,
      correlationAlongExhaustion_of_subset G Λ ⟨J, 0, β⟩ had,
      correlationAlongExhaustion_of_subset G Λ ⟨J, 0, β⟩ hbc]
  -- Apply finite-volume cor_4_3_3
  have hfin := IsingModel.cor_4_3_3 (inducedGraph G (Λ.volume n)) J β hf
    ⟨i, mem_i⟩ ⟨j, mem_j⟩ ⟨k, mem_k⟩ ⟨l, mem_l⟩
    (by intro h; apply hij; exact Subtype.mk.inj h)
    (by intro h; apply hik; exact Subtype.mk.inj h)
    (by intro h; apply hil; exact Subtype.mk.inj h)
    (by intro h; apply hjk; exact Subtype.mk.inj h)
    (by intro h; apply hjl; exact Subtype.mk.inj h)
    (by intro h; apply hkl; exact Subtype.mk.inj h)
  unfold IsingModel.truncated4 at hfin
  -- Identify liftFinset patterns
  have hlift_ijkl : liftFinset ({i, j, k, l} : Finset V) habcd
      = ({⟨i, mem_i⟩, ⟨j, mem_j⟩, ⟨k, mem_k⟩, ⟨l, mem_l⟩} :
          Finset (↑(Λ.volume n) : Type _)) := by
    ext x
    simp only [mem_liftFinset, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨?_, ?_⟩
    · intro hx; rcases hx with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))
    · rintro (rfl | rfl | rfl | rfl) <;> simp
  have hlift_ij : liftFinset ({i, j} : Finset V) hab
      = ({⟨i, mem_i⟩, ⟨j, mem_j⟩} : Finset (↑(Λ.volume n) : Type _)) := by
    ext x; simp only [mem_liftFinset, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨?_, ?_⟩
    · intro hx; rcases hx with rfl | rfl; exacts [Or.inl rfl, Or.inr rfl]
    · rintro (rfl | rfl) <;> simp
  have hlift_kl : liftFinset ({k, l} : Finset V) hcd
      = ({⟨k, mem_k⟩, ⟨l, mem_l⟩} : Finset (↑(Λ.volume n) : Type _)) := by
    ext x; simp only [mem_liftFinset, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨?_, ?_⟩
    · intro hx; rcases hx with rfl | rfl; exacts [Or.inl rfl, Or.inr rfl]
    · rintro (rfl | rfl) <;> simp
  have hlift_ik : liftFinset ({i, k} : Finset V) hac
      = ({⟨i, mem_i⟩, ⟨k, mem_k⟩} : Finset (↑(Λ.volume n) : Type _)) := by
    ext x; simp only [mem_liftFinset, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨?_, ?_⟩
    · intro hx; rcases hx with rfl | rfl; exacts [Or.inl rfl, Or.inr rfl]
    · rintro (rfl | rfl) <;> simp
  have hlift_jl : liftFinset ({j, l} : Finset V) hbd
      = ({⟨j, mem_j⟩, ⟨l, mem_l⟩} : Finset (↑(Λ.volume n) : Type _)) := by
    ext x; simp only [mem_liftFinset, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨?_, ?_⟩
    · intro hx; rcases hx with rfl | rfl; exacts [Or.inl rfl, Or.inr rfl]
    · rintro (rfl | rfl) <;> simp
  have hlift_il : liftFinset ({i, l} : Finset V) had
      = ({⟨i, mem_i⟩, ⟨l, mem_l⟩} : Finset (↑(Λ.volume n) : Type _)) := by
    ext x; simp only [mem_liftFinset, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨?_, ?_⟩
    · intro hx; rcases hx with rfl | rfl; exacts [Or.inl rfl, Or.inr rfl]
    · rintro (rfl | rfl) <;> simp
  have hlift_jk : liftFinset ({j, k} : Finset V) hbc
      = ({⟨j, mem_j⟩, ⟨k, mem_k⟩} : Finset (↑(Λ.volume n) : Type _)) := by
    ext x; simp only [mem_liftFinset, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨?_, ?_⟩
    · intro hx; rcases hx with rfl | rfl; exacts [Or.inl rfl, Or.inr rfl]
    · rintro (rfl | rfl) <;> simp
  simp only [correlationΛ, hlift_ijkl, hlift_ij, hlift_kl, hlift_ik,
    hlift_jl, hlift_il, hlift_jk]
  linarith [hfin]

/-- **GJ §17.3 key inequality (17.3.1) — lower bound on truncated 4-point function**
(Glimm–Jaffe §17.3 p. 308 eq. (17.3.1), 2nd ed.):
for a ferromagnetic Ising model at `h = 0` and pairwise distinct sites `i, j, k, l`,
`-(⟨σᵢσₖ⟩·⟨σⱼσₗ⟩ + ⟨σᵢσₗ⟩·⟨σⱼσₖ⟩) ≤ U₄^∞(i,j,k,l)`.

Combined with `truncated4Infinite_nonpos_h_zero` (upper bound `≤ 0`), this gives
the two-sided bound `0 ≤ -U₄^∞(i,j,k,l) ≤ ⟨σᵢσₖ⟩·⟨σⱼσₗ⟩ + ⟨σᵢσₗ⟩·⟨σⱼσₖ⟩`.

Proof: unfold `truncated4Infinite`; GKS-II (`correlationInfinite_gks_second`) gives
`⟨σᵢσⱼ⟩·⟨σₖσₗ⟩ ≤ ⟨σᵢσⱼσₖσₗ⟩` via `{i,j} △ {k,l} = {i,j,k,l}` (disjoint union);
subtract `⟨σᵢσₖ⟩·⟨σⱼσₗ⟩ + ⟨σᵢσₗ⟩·⟨σⱼσₖ⟩` from both sides. -/
theorem truncated4Infinite_ge_neg_pair_correlations
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hf : Ferromagnetic ⟨J, (0 : ℝ), β⟩)
    {i j k l : V}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    -(correlationInfinite G Λ ⟨J, 0, β⟩ {i, k} *
        correlationInfinite G Λ ⟨J, 0, β⟩ {j, l} +
      correlationInfinite G Λ ⟨J, 0, β⟩ {i, l} *
        correlationInfinite G Λ ⟨J, 0, β⟩ {j, k})
    ≤ truncated4Infinite G Λ ⟨J, 0, β⟩ i j k l := by
  rw [truncated4Infinite_apply]
  -- GKS-II: corr{i,j} * corr{k,l} ≤ corr{i,j,k,l}
  have hdisj : Disjoint ({i, j} : Finset V) {k, l} := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx1 hx2
    rcases hx1 with rfl | rfl <;> rcases hx2 with rfl | rfl
    · exact hik rfl
    · exact hil rfl
    · exact hjk rfl
    · exact hjl rfl
  have h_sdiff : ({i, j} : Finset V) ∆ {k, l} = {i, j, k, l} := by
    rw [hdisj.symmDiff_eq_sup, Finset.sup_eq_union]
    ext x
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have h_gks : correlationInfinite G Λ ⟨J, 0, β⟩ {i, j} *
      correlationInfinite G Λ ⟨J, 0, β⟩ {k, l}
      ≤ correlationInfinite G Λ ⟨J, 0, β⟩ {i, j, k, l} := by
    rw [← h_sdiff]
    exact correlationInfinite_gks_second G Λ ⟨J, 0, β⟩ hf {i, j} {k, l}
  linarith

/-- **Exhaustion-independence of `truncated4Infinite`**. -/
theorem truncated4Infinite_indep_exhaustion
    (G : SimpleGraph V) (Λ Λ' : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Fintype (inducedGraph G (Λ'.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j k l : V) :
    truncated4Infinite G Λ p i j k l = truncated4Infinite G Λ' p i j k l := by
  unfold truncated4Infinite
  rw [correlationInfinite_indep_exhaustion G Λ Λ' p hf {i, j, k, l},
      correlationInfinite_indep_exhaustion G Λ Λ' p hf {i, j},
      correlationInfinite_indep_exhaustion G Λ Λ' p hf {k, l},
      correlationInfinite_indep_exhaustion G Λ Λ' p hf {i, k},
      correlationInfinite_indep_exhaustion G Λ Λ' p hf {j, l},
      correlationInfinite_indep_exhaustion G Λ Λ' p hf {i, l},
      correlationInfinite_indep_exhaustion G Λ Λ' p hf {j, k}]

/-- **∞-volume Lebowitz 4-point vanishes at `β = 0`** for any sites
`i, j, k, l : V`. Infinite-volume counterpart of
`truncated4_beta_zero` (finite volume, PR #214 in
`Inequalities/GHS.lean`).

Each of the seven Finset correlations in the Lebowitz combination
is over a nonempty Finset (every subset contains at least one of
the supplied sites), so
`correlationInfinite_beta_zero_vanish` makes every
term zero and the linear combination vanishes.

Unlike the `β = 0` case, `truncated4Infinite` at `J = 0` is
`-2·t⁴` (with `t = tanh(β·h)`) for pairwise distinct sites, which
is non-zero when `β·h ≠ 0`. So only the `β = 0` slice is added
here.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.1 pp. 72–74
(cluster property context); §4.3 Cor. 4.3.3. -/
theorem truncated4Infinite_beta_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (i j k l : V) :
    truncated4Infinite G Λ (⟨J, h, 0⟩ : IsingParams ℝ) i j k l = 0 := by
  unfold truncated4Infinite
  rw [correlationInfinite_beta_zero_vanish G Λ J h
        {i, j, k, l} ⟨i, by simp⟩,
      correlationInfinite_beta_zero_vanish G Λ J h
        {i, j} ⟨i, by simp⟩,
      correlationInfinite_beta_zero_vanish G Λ J h
        {k, l} ⟨k, by simp⟩,
      correlationInfinite_beta_zero_vanish G Λ J h
        {i, k} ⟨i, by simp⟩,
      correlationInfinite_beta_zero_vanish G Λ J h
        {j, l} ⟨j, by simp⟩,
      correlationInfinite_beta_zero_vanish G Λ J h
        {i, l} ⟨i, by simp⟩,
      correlationInfinite_beta_zero_vanish G Λ J h
        {j, k} ⟨j, by simp⟩]
  ring

/-- **∞-volume Lebowitz 4-point closed form at `J = 0`** for
ferromagnetic `⟨0, h, β⟩` and pairwise distinct sites:
`truncated4Infinite G Λ ⟨0, h, β⟩ i j k l = -2 · tanh(β·h)^4`.

Infinite-volume counterpart of
`truncated4_J_zero_of_pairwise_distinct` (finite volume, PR #215
in `Inequalities/GHS.lean`). Uses the ∞-vol closed form
`correlationInfinite_J_zero` at the four Finsets of card 4 and
six Finsets of card 2.

Complements `truncated4Infinite_beta_zero` (vanishing slice at
`β = 0`): this is the J=0 slice with explicit closed form `-2·t⁴`,
which over the `Ferromagnetic` range `0 ≤ h`, `0 < β` is `0` exactly
when the external field vanishes and is strictly negative otherwise.
Note `-2·t⁴ ≤ 0` always, consistent with
`truncated4Infinite_nonpos_h_zero`.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.1 pp. 72–74
(cluster context); §4.3 Cor. 4.3.3 / Lebowitz. -/
theorem truncated4Infinite_J_zero_of_pairwise_distinct
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    {i j k l : V}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    truncated4Infinite G Λ (⟨0, h, β⟩ : IsingParams ℝ) i j k l
      = -2 * Real.tanh (β * h) ^ 4 := by
  unfold truncated4Infinite
  rw [correlationInfinite_J_zero G Λ h β hf,
      correlationInfinite_J_zero G Λ h β hf,
      correlationInfinite_J_zero G Λ h β hf,
      correlationInfinite_J_zero G Λ h β hf,
      correlationInfinite_J_zero G Λ h β hf,
      correlationInfinite_J_zero G Λ h β hf,
      correlationInfinite_J_zero G Λ h β hf]
  have hcard_ijkl : ({i, j, k, l} : Finset V).card = 4 := by
    have h_jkl_card : ({j, k, l} : Finset V).card = 3 := by
      rw [show ({j, k, l} : Finset V) = insert j ({k, l} : Finset V) from rfl,
          Finset.card_insert_of_notMem (by simp [hjk, hjl]),
          Finset.card_pair hkl]
    have h_i_nin : i ∉ ({j, k, l} : Finset V) := by
      simp [hij, hik, hil]
    rw [show ({i, j, k, l} : Finset V) = insert i ({j, k, l} : Finset V)
            from rfl,
        Finset.card_insert_of_notMem h_i_nin, h_jkl_card]
  have hcard_ij : ({i, j} : Finset V).card = 2 := Finset.card_pair hij
  have hcard_ik : ({i, k} : Finset V).card = 2 := Finset.card_pair hik
  have hcard_il : ({i, l} : Finset V).card = 2 := Finset.card_pair hil
  have hcard_jk : ({j, k} : Finset V).card = 2 := Finset.card_pair hjk
  have hcard_jl : ({j, l} : Finset V).card = 2 := Finset.card_pair hjl
  have hcard_kl : ({k, l} : Finset V).card = 2 := Finset.card_pair hkl
  rw [hcard_ijkl, hcard_ij, hcard_kl, hcard_ik, hcard_jl, hcard_il, hcard_jk]
  ring

/-- **∞-volume Lebowitz 4-point at `J = 0` one-pair coincidence**
(ferromagnetic): if `i ≠ k`, `i ≠ l`, `k ≠ l`, then
`truncated4Infinite ⟨0,h,β⟩ i i k l = -2 · tanh(β·h)⁴`.

Same closed form as the pairwise-distinct case
(`truncated4Infinite_J_zero_of_pairwise_distinct`). Proof uses the
Finset collapses `{i,i,k,l} = {i,k,l}` (card 3) and `{i,i} = {i}`
(card 1); the three pair-pair products reduce to
`t³ + t⁴ + t⁴` giving `U_4 = t³ − t³ − 2t⁴ = −2t⁴`.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.1 pp. 72–74. -/
theorem truncated4Infinite_J_zero_of_one_pair_coincidence
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    {i k l : V} (hik : i ≠ k) (hil : i ≠ l) (hkl : k ≠ l) :
    truncated4Infinite G Λ (⟨0, h, β⟩ : IsingParams ℝ) i i k l
      = -2 * Real.tanh (β * h) ^ 4 := by
  unfold truncated4Infinite
  have hii : ({i, i} : Finset V) = {i} := by simp
  have hiikl : ({i, i, k, l} : Finset V) = {i, k, l} := by ext x; simp
  rw [hiikl, hii]
  rw [correlationInfinite_J_zero G Λ h β hf,
      correlationInfinite_J_zero G Λ h β hf,
      correlationInfinite_J_zero G Λ h β hf,
      correlationInfinite_J_zero G Λ h β hf,
      correlationInfinite_J_zero G Λ h β hf]
  have hcard_i : ({i} : Finset V).card = 1 := Finset.card_singleton i
  have hcard_ik : ({i, k} : Finset V).card = 2 := Finset.card_pair hik
  have hcard_il : ({i, l} : Finset V).card = 2 := Finset.card_pair hil
  have hcard_kl : ({k, l} : Finset V).card = 2 := Finset.card_pair hkl
  have hcard_ikl : ({i, k, l} : Finset V).card = 3 := by
    have h_i_nin : i ∉ ({k, l} : Finset V) := by simp [hik, hil]
    rw [show ({i, k, l} : Finset V) = insert i ({k, l} : Finset V) from rfl,
        Finset.card_insert_of_notMem h_i_nin, hcard_kl]
  rw [hcard_i, hcard_ik, hcard_il, hcard_kl, hcard_ikl]
  ring

/-- **∞-volume Lebowitz 4-point at `J = 0` two-pair coincidence**
(ferromagnetic): if `i ≠ k`, then
`truncated4Infinite ⟨0,h,β⟩ i i k k = -2 · tanh(β·h)⁴`.

Same closed form as pairwise-distinct and one-pair cases. Finset
collapses `{i,i,k,k} = {i,k}` (card 2), `{i,i} = {i}`, `{k,k} = {k}`
(card 1 each). U_4 = `t² − t² − 2t⁴ = −2t⁴`.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.1 pp. 72–74. -/
theorem truncated4Infinite_J_zero_of_two_pair_coincidence
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    {i k : V} (hik : i ≠ k) :
    truncated4Infinite G Λ (⟨0, h, β⟩ : IsingParams ℝ) i i k k
      = -2 * Real.tanh (β * h) ^ 4 := by
  unfold truncated4Infinite
  have h1i : correlationInfinite G Λ (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ) {i}
      = Real.tanh (β * h) := by
    rw [correlationInfinite_J_zero G Λ h β hf, Finset.card_singleton, pow_one]
  have h1k : correlationInfinite G Λ (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ) {k}
      = Real.tanh (β * h) := by
    rw [correlationInfinite_J_zero G Λ h β hf, Finset.card_singleton, pow_one]
  have hik2 : correlationInfinite G Λ (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ) {i, k}
      = Real.tanh (β * h) ^ 2 := by
    rw [correlationInfinite_J_zero G Λ h β hf, Finset.card_pair hik]
  have hii : ({i, i} : Finset V) = {i} := by simp
  have hkk : ({k, k} : Finset V) = {k} := by simp
  have hiikk : ({i, i, k, k} : Finset V) = {i, k} := by ext x; simp
  rw [hiikk, hii, hkk, h1i, h1k, hik2]
  ring

/-- **∞-volume Lebowitz 4-point at `J = 0` triple coincidence**
(ferromagnetic): if `i ≠ l`, then
`truncated4Infinite ⟨0,h,β⟩ i i i l = t² − 3·t³` with `t = tanh(β·h)`.

Unlike the pair / two-pair / one-pair coincidence cases (all giving
`−2t⁴`), triple coincidence produces the asymmetric closed form
`t² − 3t³`. Finset collapses `{i,i,i,l} = {i,l}` (card 2),
`{i,i} = {i}` (card 1); each of the three pair-pair products equals
`t · t² = t³`, yielding `U_4 = t² − 3t³`.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.1 pp. 72–74. -/
theorem truncated4Infinite_J_zero_of_triple_coincidence
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    {i l : V} (hil : i ≠ l) :
    truncated4Infinite G Λ (⟨0, h, β⟩ : IsingParams ℝ) i i i l
      = Real.tanh (β * h) ^ 2 - 3 * Real.tanh (β * h) ^ 3 := by
  unfold truncated4Infinite
  have h1i : correlationInfinite G Λ (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ) {i}
      = Real.tanh (β * h) := by
    rw [correlationInfinite_J_zero G Λ h β hf, Finset.card_singleton, pow_one]
  have hil2 : correlationInfinite G Λ (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ) {i, l}
      = Real.tanh (β * h) ^ 2 := by
    rw [correlationInfinite_J_zero G Λ h β hf, Finset.card_pair hil]
  have hii : ({i, i} : Finset V) = {i} := by simp
  have hiiil : ({i, i, i, l} : Finset V) = {i, l} := by ext x; simp
  rw [hiiil, hii, h1i, hil2]
  ring

/-- **∞-volume Lebowitz 4-point at `J = 0` all-coincident**
(ferromagnetic): `truncated4Infinite ⟨0,h,β⟩ i i i i = t − 3·t²`
with `t = tanh(β·h)`.

Completes the J=0 trivial-slice cascade for the Lebowitz 4-point.
Finset collapses `{i,i,i,i} = {i}` (card 1), `{i,i} = {i}`; each of
the three pair-pair products equals `t · t = t²`, yielding
`U_4 = t − 3t²`.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.1 pp. 72–74. -/
theorem truncated4Infinite_J_zero_all_coincident
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    (i : V) :
    truncated4Infinite G Λ (⟨0, h, β⟩ : IsingParams ℝ) i i i i
      = Real.tanh (β * h) - 3 * Real.tanh (β * h) ^ 2 := by
  unfold truncated4Infinite
  have h1i : correlationInfinite G Λ (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ) {i}
      = Real.tanh (β * h) := by
    rw [correlationInfinite_J_zero G Λ h β hf, Finset.card_singleton, pow_one]
  have hii : ({i, i} : Finset V) = {i} := by simp
  have hiiii : ({i, i, i, i} : Finset V) = {i} := by ext x; simp
  rw [hiiii, hii, h1i]
  ring

-- (Steps 276-277 duplicates removed: see truncated3Infinite_J_zero_of_pairwise_distinct
-- and truncated4Infinite_J_zero_of_pairwise_distinct earlier in this file.)

end Ambient
end IsingModel
