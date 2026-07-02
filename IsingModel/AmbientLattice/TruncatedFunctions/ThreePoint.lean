import IsingModel.AmbientLattice.TruncatedFunctions.Cluster

/-!
# Infinite-volume truncated three-point functions

Mechanical child split from `AmbientLattice/TruncatedFunctions.lean`.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-! ## Truncated 3-point correlation + GHS at infinite volume

Lift the finite-volume GHS inequality (`ghs_inequality`,
`Inequalities/GHS.lean`) to the thermodynamic limit.
For ferromagnetic Ising and pairwise distinct sites,
$U_3(i, j, k) \le 0$ at infinite volume.

Reference: Glimm–Jaffe §4.3 Corollary 4.3.4, pp. 68ff;
Friedli–Velenik §3.6.4. -/

/-- **Truncated 3-point correlation at infinite volume**:
the thermodynamic-limit analog of `IsingModel.truncated3`:
$U_3 := \langle \sigma^{\{i,j,k\}} \rangle_\infty
  - \langle \sigma^{\{i\}} \rangle_\infty \langle \sigma^{\{j,k\}} \rangle_\infty
  - \langle \sigma^{\{j\}} \rangle_\infty \langle \sigma^{\{i,k\}} \rangle_\infty
  - \langle \sigma^{\{k\}} \rangle_\infty \langle \sigma^{\{i,j\}} \rangle_\infty
  + 2 \langle \sigma^{\{i\}} \rangle_\infty \langle \sigma^{\{j\}} \rangle_\infty
    \langle \sigma^{\{k\}} \rangle_\infty$. -/
noncomputable def truncated3Infinite
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i j k : V) : ℝ :=
  correlationInfinite G Λ p {i, j, k}
    - correlationInfinite G Λ p {i} * correlationInfinite G Λ p {j, k}
    - correlationInfinite G Λ p {j} * correlationInfinite G Λ p {i, k}
    - correlationInfinite G Λ p {k} * correlationInfinite G Λ p {i, j}
    + 2 * correlationInfinite G Λ p {i} * correlationInfinite G Λ p {j}
      * correlationInfinite G Λ p {k}

/-- **Unfolding of `truncated3Infinite`**: the defining Ursell 3-point
formula as a named identity. -/
theorem truncated3Infinite_apply
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i j k : V) :
    truncated3Infinite G Λ p i j k
      = correlationInfinite G Λ p {i, j, k}
        - correlationInfinite G Λ p {i} * correlationInfinite G Λ p {j, k}
        - correlationInfinite G Λ p {j} * correlationInfinite G Λ p {i, k}
        - correlationInfinite G Λ p {k} * correlationInfinite G Λ p {i, j}
        + 2 * correlationInfinite G Λ p {i} * correlationInfinite G Λ p {j}
          * correlationInfinite G Λ p {k} := rfl

/-- **`truncated3Infinite` symmetry under swapping `i, j`**. The defining
formula is symmetric in the three site arguments, using that Finsets are
unordered. -/
theorem truncated3Infinite_swap_ij
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i j k : V) :
    truncated3Infinite G Λ p i j k = truncated3Infinite G Λ p j i k := by
  unfold truncated3Infinite
  have h1 : ({i, j, k} : Finset V) = {j, i, k} := by
    rw [Finset.insert_comm]
  have h2 : ({i, j} : Finset V) = {j, i} := Finset.pair_comm i j
  rw [h1, h2]
  ring

/-- **`truncated3Infinite` symmetry under swapping `j, k`**. -/
theorem truncated3Infinite_swap_jk
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i j k : V) :
    truncated3Infinite G Λ p i j k = truncated3Infinite G Λ p i k j := by
  unfold truncated3Infinite
  have h1 : ({i, j, k} : Finset V) = {i, k, j} := by
    congr 1
    exact Finset.pair_comm j k
  have h2 : ({j, k} : Finset V) = {k, j} := Finset.pair_comm j k
  rw [h1, h2]
  ring

/-- **`truncated3Infinite` symmetry under swapping `i, k`**: obtained by
chaining the `ij` and `jk` swaps. -/
theorem truncated3Infinite_swap_ik
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i j k : V) :
    truncated3Infinite G Λ p i j k = truncated3Infinite G Λ p k j i := by
  rw [truncated3Infinite_swap_ij G Λ p i j k,
      truncated3Infinite_swap_jk G Λ p j i k,
      truncated3Infinite_swap_ij G Λ p j k i]

/-- **Truncated 3-point along an exhaustion** (local helper): evaluates
the `truncated3`-style algebraic expression at the `n`-th volume of
the exhaustion, using `correlationAlongExhaustion` instead of the
limit `correlationInfinite`.  Bridges the finite-volume
`ghs_inequality` and the infinite-volume `truncated3Infinite_nonpos`
via `le_of_tendsto`. -/
private noncomputable def truncated3AlongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i j k : V) (n : ℕ) : ℝ :=
  correlationAlongExhaustion G Λ p {i, j, k} n
    - correlationAlongExhaustion G Λ p {i} n
      * correlationAlongExhaustion G Λ p {j, k} n
    - correlationAlongExhaustion G Λ p {j} n
      * correlationAlongExhaustion G Λ p {i, k} n
    - correlationAlongExhaustion G Λ p {k} n
      * correlationAlongExhaustion G Λ p {i, j} n
    + 2 * correlationAlongExhaustion G Λ p {i} n
      * correlationAlongExhaustion G Λ p {j} n
      * correlationAlongExhaustion G Λ p {k} n

/-- **Tendsto for the truncated 3-point sequence**: the pointwise
`truncated3AlongExhaustion` converges to `truncated3Infinite`.

Key technical step establishing that the thermodynamic limit of
the finite-volume truncated 3-point correlation exists and equals
the infinite-volume definition.  Proof: apply `Tendsto.sub`,
`Tendsto.add`, and `Tendsto.mul` to the seven `correlationInfinite`
convergences from
`tendsto_correlationAlongExhaustion_correlationInfinite`. -/
theorem tendsto_truncated3AlongExhaustion_truncated3Infinite
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j k : V) :
    Filter.Tendsto
      (truncated3AlongExhaustion G Λ p i j k)
      Filter.atTop
      (nhds (truncated3Infinite G Λ p i j k)) := by
  unfold truncated3AlongExhaustion truncated3Infinite
  have h_ijk := tendsto_correlationAlongExhaustion_correlationInfinite G Λ p hf {i,j,k}
  have h_jk := tendsto_correlationAlongExhaustion_correlationInfinite G Λ p hf {j,k}
  have h_ik := tendsto_correlationAlongExhaustion_correlationInfinite G Λ p hf {i,k}
  have h_ij := tendsto_correlationAlongExhaustion_correlationInfinite G Λ p hf {i,j}
  have h_i := tendsto_correlationAlongExhaustion_correlationInfinite G Λ p hf {i}
  have h_j := tendsto_correlationAlongExhaustion_correlationInfinite G Λ p hf {j}
  have h_k := tendsto_correlationAlongExhaustion_correlationInfinite G Λ p hf {k}
  exact ((((h_ijk.sub (h_i.mul h_jk)).sub (h_j.mul h_ik)).sub
    (h_k.mul h_ij)).add
    (((tendsto_const_nhds (x := (2 : ℝ))).mul h_i).mul h_j |>.mul h_k))

/-- **Stagewise identification of `truncated3AlongExhaustion` with a
finite-volume `truncated3`**: once the three sites lie in the `n`-th volume
`Λ.volume n`, the along-exhaustion Ursell expression evaluates to the
finite-volume Ursell function on the induced subgraph, at the lifted sites
`⟨i, hi⟩, ⟨j, hj⟩, ⟨k, hk⟩`.

The bridge between the `atTop`-sequence `truncated3AlongExhaustion` and the
finite-volume brick lemmas (`abs_truncated3_le`, `ghs_inequality`, Simon--Lieb
decay): rewriting each `correlationAlongExhaustion` via
`correlationAlongExhaustion_of_subset` and identifying the seven `liftFinset`
supports with the corresponding subtype pairs/triples reduces both sides to the
same combination of `correlation (inducedGraph G (Λ.volume n)) p`. -/
theorem truncated3AlongExhaustion_eq_truncated3
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (i j k : V) {n : ℕ}
    (hi : i ∈ Λ.volume n) (hj : j ∈ Λ.volume n) (hk : k ∈ Λ.volume n) :
    truncated3AlongExhaustion G Λ p i j k n
      = IsingModel.truncated3 (inducedGraph G (Λ.volume n)) p ⟨i, hi⟩ ⟨j, hj⟩ ⟨k, hk⟩ := by
  have ha : ({i} : Finset V) ⊆ Λ.volume n := by
    intro x hx; rw [Finset.mem_singleton] at hx; exact hx ▸ hi
  have hb : ({j} : Finset V) ⊆ Λ.volume n := by
    intro x hx; rw [Finset.mem_singleton] at hx; exact hx ▸ hj
  have hc : ({k} : Finset V) ⊆ Λ.volume n := by
    intro x hx; rw [Finset.mem_singleton] at hx; exact hx ▸ hk
  have habc : ({i, j, k} : Finset V) ⊆ Λ.volume n := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hab : ({i, j} : Finset V) ⊆ Λ.volume n := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hac : ({i, k} : Finset V) ⊆ Λ.volume n := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hbc : ({j, k} : Finset V) ⊆ Λ.volume n := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  unfold truncated3AlongExhaustion IsingModel.truncated3
  rw [correlationAlongExhaustion_of_subset G Λ p habc,
      correlationAlongExhaustion_of_subset G Λ p ha,
      correlationAlongExhaustion_of_subset G Λ p hb,
      correlationAlongExhaustion_of_subset G Λ p hc,
      correlationAlongExhaustion_of_subset G Λ p hab,
      correlationAlongExhaustion_of_subset G Λ p hac,
      correlationAlongExhaustion_of_subset G Λ p hbc]
  have hlift_ijk : liftFinset ({i, j, k} : Finset V) habc
      = ({⟨i, hi⟩, ⟨j, hj⟩, ⟨k, hk⟩} : Finset (↑(Λ.volume n) : Type _)) := by
    ext x
    simp only [mem_liftFinset, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨?_, ?_⟩
    · intro hx
      rcases hx with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    · rintro (rfl | rfl | rfl) <;> simp
  have hlift_i : liftFinset ({i} : Finset V) ha
      = ({⟨i, hi⟩} : Finset (↑(Λ.volume n) : Type _)) := by
    ext x
    simp only [mem_liftFinset, Finset.mem_singleton]
    refine ⟨?_, ?_⟩
    · intro hx; subst hx; rfl
    · rintro rfl; rfl
  have hlift_j : liftFinset ({j} : Finset V) hb
      = ({⟨j, hj⟩} : Finset (↑(Λ.volume n) : Type _)) := by
    ext x
    simp only [mem_liftFinset, Finset.mem_singleton]
    refine ⟨?_, ?_⟩
    · intro hx; subst hx; rfl
    · rintro rfl; rfl
  have hlift_k : liftFinset ({k} : Finset V) hc
      = ({⟨k, hk⟩} : Finset (↑(Λ.volume n) : Type _)) := by
    ext x
    simp only [mem_liftFinset, Finset.mem_singleton]
    refine ⟨?_, ?_⟩
    · intro hx; subst hx; rfl
    · rintro rfl; rfl
  have hlift_ij : liftFinset ({i, j} : Finset V) hab
      = ({⟨i, hi⟩, ⟨j, hj⟩} : Finset (↑(Λ.volume n) : Type _)) := by
    ext x
    simp only [mem_liftFinset, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨?_, ?_⟩
    · intro hx; rcases hx with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl) <;> simp
  have hlift_ik : liftFinset ({i, k} : Finset V) hac
      = ({⟨i, hi⟩, ⟨k, hk⟩} : Finset (↑(Λ.volume n) : Type _)) := by
    ext x
    simp only [mem_liftFinset, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨?_, ?_⟩
    · intro hx; rcases hx with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl) <;> simp
  have hlift_jk : liftFinset ({j, k} : Finset V) hbc
      = ({⟨j, hj⟩, ⟨k, hk⟩} : Finset (↑(Λ.volume n) : Type _)) := by
    ext x
    simp only [mem_liftFinset, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨?_, ?_⟩
    · intro hx; rcases hx with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl) <;> simp
  simp only [correlationΛ, hlift_ijk, hlift_i, hlift_j, hlift_k,
    hlift_ij, hlift_ik, hlift_jk]

/-- **GHS at infinite volume**: for a ferromagnetic Ising model and
pairwise distinct sites `i, j, k`, $U_3(i, j, k) \le 0$.

Proof: at each `n` with `{i, j, k} ⊆ Λ.volume n`, the finite-volume
`ghs_inequality` gives `truncated3AlongExhaustion n ≤ 0` after
identifying the along-exhaustion sequence with the lifted
finite-volume `truncated3`.  Pass to the limit using
`tendsto_truncated3AlongExhaustion_truncated3Infinite` and
`le_of_tendsto`. -/
theorem truncated3Infinite_nonpos
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    {i j k : V} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    truncated3Infinite G Λ p i j k ≤ 0 := by
  refine le_of_tendsto
    (tendsto_truncated3AlongExhaustion_truncated3Infinite G Λ p hf i j k) ?_
  -- Eventually at atTop: truncated3AlongExhaustion n ≤ 0
  obtain ⟨N, hN⟩ := Λ.exhaust ({i, j, k} : Finset V)
  rw [Filter.eventually_atTop]
  refine ⟨N, fun n hn => ?_⟩
  have habc : ({i, j, k} : Finset V) ⊆ Λ.volume n := hN n hn
  have hi : i ∈ Λ.volume n := habc (by simp)
  have hj : j ∈ Λ.volume n := habc (by simp)
  have hk : k ∈ Λ.volume n := habc (by simp)
  rw [truncated3AlongExhaustion_eq_truncated3 G Λ p i j k hi hj hk]
  exact IsingModel.ghs_inequality (inducedGraph G (Λ.volume n)) p hf
    ⟨i, hi⟩ ⟨j, hj⟩ ⟨k, hk⟩
    (fun h => hij (Subtype.mk.inj h))
    (fun h => hjk (Subtype.mk.inj h))
    (fun h => hik (Subtype.mk.inj h))

/-- **`truncated3Infinite` at `h = 0`**: for pairwise distinct sites,
$U_3 = 0$ at vanishing external field.

All singletons $\{i\}, \{j\}, \{k\}$ have odd cardinality, so their
`correlationInfinite` at $h = 0$ vanishes (`correlationInfinite_h_zero`),
making the three product terms and the triple product vanish.  With
distinct sites, $\{i, j, k\}$ also has odd cardinality (= 3), so the
first term vanishes too.  All five terms are zero. -/
theorem truncated3Infinite_h_zero_of_distinct
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) {i j k : V} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    truncated3Infinite G Λ ⟨J, 0, β⟩ i j k = 0 := by
  unfold truncated3Infinite
  have h_ijk : Odd ({i, j, k} : Finset V).card := by
    rw [show ({i, j, k} : Finset V).card = 3 from ?_]
    · exact ⟨1, by norm_num⟩
    · rw [Finset.card_insert_of_notMem (by
        simp [Finset.mem_insert, Finset.mem_singleton, hij, hik])]
      rw [Finset.card_insert_of_notMem (by
        simp [Finset.mem_singleton, hjk])]
      simp
  have h_i : Odd ({i} : Finset V).card := by simp
  have h_j : Odd ({j} : Finset V).card := by simp
  have h_k : Odd ({k} : Finset V).card := by simp
  rw [correlationInfinite_h_zero G Λ J β _ h_ijk,
      correlationInfinite_h_zero G Λ J β _ h_i,
      correlationInfinite_h_zero G Λ J β _ h_j,
      correlationInfinite_h_zero G Λ J β _ h_k]
  ring

/-- **∞-volume Ursell 3-point at `h = 0` pair coincidence**:
for `i ≠ k`,
`truncated3Infinite ⟨J,0,β⟩ i i k = correlationInfinite ⟨J,0,β⟩ {i,k}`.

Extension of `truncated3Infinite_h_zero_of_distinct` (three distinct
→ 0) to the two-coincident case. Z₂ symmetry at `h = 0` kills all
odd-cardinality correlations via `correlationInfinite_h_zero`; the
Ursell 3-point retains only the `{i,i,k} = {i,k}` even-cardinality
term (card 2), so the 3-point reduces to the 2-point.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.1 pp. 72–74. -/
theorem truncated3Infinite_h_zero_of_pair_coincidence
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) {i k : V} (_hik : i ≠ k) :
    truncated3Infinite G Λ (⟨J, 0, β⟩ : IsingParams ℝ) i i k
      = correlationInfinite G Λ (⟨J, 0, β⟩ : IsingParams ℝ) {i, k} := by
  unfold truncated3Infinite
  have hii : ({i, i} : Finset V) = {i} := by simp
  have hiik : ({i, i, k} : Finset V) = {i, k} := by ext x; simp
  have h_i_odd : Odd ({i} : Finset V).card := by simp
  have h_k_odd : Odd ({k} : Finset V).card := by simp
  rw [hii, hiik,
      correlationInfinite_h_zero G Λ J β {i} h_i_odd,
      correlationInfinite_h_zero G Λ J β {k} h_k_odd]
  ring

/-- **∞-volume Ursell 3-point at `h = 0` all-coincident vanishes**:
`truncated3Infinite ⟨J,0,β⟩ i i i = 0`. All Finsets in the Ursell
formula collapse to `{i}` (card 1, odd), so Z₂ symmetry forces
every term to vanish.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.1 pp. 72–74. -/
theorem truncated3Infinite_h_zero_all_coincident
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (i : V) :
    truncated3Infinite G Λ (⟨J, 0, β⟩ : IsingParams ℝ) i i i = 0 := by
  unfold truncated3Infinite
  have hii : ({i, i} : Finset V) = {i} := by simp
  have hiii : ({i, i, i} : Finset V) = {i} := by ext x; simp
  have h_i_odd : Odd ({i} : Finset V).card := by simp
  rw [hiii, hii, correlationInfinite_h_zero G Λ J β {i} h_i_odd]
  ring

/-- **Exhaustion-independence of `truncated3Infinite`**: the value
does not depend on the choice of exhaustion. -/
theorem truncated3Infinite_indep_exhaustion
    (G : SimpleGraph V) (Λ Λ' : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Fintype (inducedGraph G (Λ'.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j k : V) :
    truncated3Infinite G Λ p i j k = truncated3Infinite G Λ' p i j k := by
  unfold truncated3Infinite
  rw [correlationInfinite_indep_exhaustion G Λ Λ' p hf {i, j, k},
      correlationInfinite_indep_exhaustion G Λ Λ' p hf {i},
      correlationInfinite_indep_exhaustion G Λ Λ' p hf {j},
      correlationInfinite_indep_exhaustion G Λ Λ' p hf {k},
      correlationInfinite_indep_exhaustion G Λ Λ' p hf {i, j},
      correlationInfinite_indep_exhaustion G Λ Λ' p hf {i, k},
      correlationInfinite_indep_exhaustion G Λ Λ' p hf {j, k}]

/-- **∞-volume Ursell 3-point vanishes at `J = 0`** (ferromagnetic,
pairwise distinct sites): infinite-volume counterpart of
`truncated3_J_zero_of_pairwise_distinct` (finite volume, PR #209).

For pairwise distinct `i, j, k` and `⟨0, h, β⟩` ferromagnetic,
`correlationInfinite G Λ ⟨0, h, β⟩ A = tanh(β·h)^|A|` gives
cardinalities `3, 1+2, 1+2, 1+2, 1+1+1`, and the Ursell
combination becomes `t³ - 3·t³ + 2·t³ = 0` where `t = tanh(β·h)`.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.1 pp. 72–74
(cluster property context); §4.1 / §4.3. -/
theorem truncated3Infinite_J_zero_of_pairwise_distinct
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    {i j k : V} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    truncated3Infinite G Λ (⟨0, h, β⟩ : IsingParams ℝ) i j k = 0 := by
  unfold truncated3Infinite
  rw [correlationInfinite_J_zero G Λ h β hf,
      correlationInfinite_J_zero G Λ h β hf,
      correlationInfinite_J_zero G Λ h β hf,
      correlationInfinite_J_zero G Λ h β hf,
      correlationInfinite_J_zero G Λ h β hf,
      correlationInfinite_J_zero G Λ h β hf,
      correlationInfinite_J_zero G Λ h β hf]
  have hcard_i : ({i} : Finset V).card = 1 := Finset.card_singleton i
  have hcard_j : ({j} : Finset V).card = 1 := Finset.card_singleton j
  have hcard_k : ({k} : Finset V).card = 1 := Finset.card_singleton k
  have hcard_ij : ({i, j} : Finset V).card = 2 := Finset.card_pair hij
  have hcard_jk : ({j, k} : Finset V).card = 2 := Finset.card_pair hjk
  have hcard_ik : ({i, k} : Finset V).card = 2 := Finset.card_pair hik
  have hi_nin_jk : i ∉ ({j, k} : Finset V) := by simp [hij, hik]
  have hcard_ijk : ({i, j, k} : Finset V).card = 3 := by
    rw [show ({i, j, k} : Finset V) = insert i ({j, k} : Finset V) from rfl,
        Finset.card_insert_of_notMem hi_nin_jk, hcard_jk]
  rw [hcard_i, hcard_j, hcard_k, hcard_ij, hcard_jk, hcard_ik, hcard_ijk]
  ring

/-- **∞-volume Ursell 3-point vanishes at `J = 0` with pair coincidence**
(ferromagnetic): if `i = j` and `i ≠ k`, then
`truncated3Infinite ⟨0,h,β⟩ i i k = 0`. Extension of
`truncated3Infinite_J_zero_of_pairwise_distinct` (all three distinct)
to the two-coincident case.

Proof: with `t := tanh(β·h)`, using Finset collapses `{i,i,k} = {i,k}`
(card 2) and `{i,i} = {i}` (card 1):
`U_3(i,i,k) = t² − t·t² − t·t² − t·t + 2·t·t·t = t² − 2t³ − t² + 2t³ = 0`.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.1 pp. 72–74. -/
theorem truncated3Infinite_J_zero_of_pair_coincidence
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    {i k : V} (hik : i ≠ k) :
    truncated3Infinite G Λ (⟨0, h, β⟩ : IsingParams ℝ) i i k = 0 := by
  unfold truncated3Infinite
  have hii : ({i, i} : Finset V) = {i} := by simp
  have hiik : ({i, i, k} : Finset V) = {i, k} := by
    ext x; simp
  rw [hii, hiik]
  rw [correlationInfinite_J_zero G Λ h β hf,
      correlationInfinite_J_zero G Λ h β hf,
      correlationInfinite_J_zero G Λ h β hf]
  have hcard_i : ({i} : Finset V).card = 1 := Finset.card_singleton i
  have hcard_k : ({k} : Finset V).card = 1 := Finset.card_singleton k
  have hcard_ik : ({i, k} : Finset V).card = 2 := Finset.card_pair hik
  rw [hcard_i, hcard_k, hcard_ik]
  ring

/-- **∞-volume Ursell 3-point at `J = 0` all-coincident closed form**
(ferromagnetic): `truncated3Infinite ⟨0,h,β⟩ i i i = t·(1−t)·(1−2t)`
with `t := tanh(β·h)`.

Completes the J=0 trivial-slice cascade: all-distinct vanishes
(`truncated3Infinite_J_zero_of_pairwise_distinct`), pair-coincident
vanishes (`truncated3Infinite_J_zero_of_pair_coincidence`), and
all-coincident is the cubic polynomial `t − 3t² + 2t³`.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.1 pp. 72–74. -/
theorem truncated3Infinite_J_zero_all_coincident
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    (i : V) :
    truncated3Infinite G Λ (⟨0, h, β⟩ : IsingParams ℝ) i i i
      = Real.tanh (β * h) * (1 - Real.tanh (β * h))
          * (1 - 2 * Real.tanh (β * h)) := by
  unfold truncated3Infinite
  have h1 : correlationInfinite G Λ (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ) {i}
      = Real.tanh (β * h) := by
    rw [correlationInfinite_J_zero G Λ h β hf, Finset.card_singleton, pow_one]
  have hii : ({i, i} : Finset V) = {i} := by simp
  have hiii : ({i, i, i} : Finset V) = {i} := by ext x; simp
  rw [hiii, hii, h1]
  ring

/-- **∞-volume Ursell 3-point vanishes at `β = 0`** for any sites.

Infinite-volume counterpart of `truncated3_beta_zero` (finite
volume, PR #209). Every correlation in the Ursell combination is
over a nonempty Finset, so
`correlationInfinite_beta_zero_vanish` makes each
term zero — the linear combination vanishes trivially. No
distinctness hypotheses are needed at `β = 0`.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.1 pp. 72–74
(cluster property context); §4.1 infinite-temperature slice. -/
theorem truncated3Infinite_beta_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (i j k : V) :
    truncated3Infinite G Λ (⟨J, h, 0⟩ : IsingParams ℝ) i j k = 0 := by
  unfold truncated3Infinite
  rw [correlationInfinite_beta_zero_vanish G Λ J h
        {i, j, k} ⟨i, by simp⟩,
      correlationInfinite_beta_zero_vanish G Λ J h
        {i} (Finset.singleton_nonempty i),
      correlationInfinite_beta_zero_vanish G Λ J h
        {j} (Finset.singleton_nonempty j),
      correlationInfinite_beta_zero_vanish G Λ J h
        {k} (Finset.singleton_nonempty k),
      correlationInfinite_beta_zero_vanish G Λ J h
        {j, k} ⟨j, by simp⟩,
      correlationInfinite_beta_zero_vanish G Λ J h
        {i, k} ⟨i, by simp⟩,
      correlationInfinite_beta_zero_vanish G Λ J h
        {i, j} ⟨i, by simp⟩]
  ring

end Ambient
end IsingModel
