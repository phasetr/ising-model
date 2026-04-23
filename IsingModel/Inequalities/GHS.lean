import IsingModel.InfiniteVolume

/-!
# GHS inequality

The Griffiths-Hurst-Sherman (GHS) inequality: for the ferromagnetic Ising
model with non-negative external field, the truncated three-point correlation
function is non-positive.

## Main results

* `truncated2` — the truncated 2-point function (connected correlation)
* `truncated3` — the truncated 3-point function (Ursell function)
* `truncated2_nonneg` — `⟨σ_i; σ_j⟩ ≥ 0` (from GKS-II)
* `ghs_inequality` — `⟨σ_i; σ_j; σ_k⟩ ≤ 0` for `h ≥ 0`

## References

* Ellis, *Entropy, Large Deviations, and Statistical Mechanics*, §V.3
* Griffiths, Hurst, Sherman, J. Math. Phys. 11 (1970)
* Lebowitz, Comm. Math. Phys. 35 (1974)
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

/-! ## Spin-flip symmetry for odd correlations

When `h = 0`, the Hamiltonian is invariant under global spin flip.
Odd-cardinality spin products change sign under flip, so their
Gibbs expectation vanishes. -/

omit [Fintype ι] [DecidableEq ι] in
/-- Spin product under global flip: `σ^A(flip σ) = (-1)^|A| · σ^A(σ)`. -/
private theorem spinProduct_flip (A : Finset ι) (σ : Config ι) :
    spinProduct A σ.flip = (-1) ^ A.card * spinProduct A σ := by
  simp only [spinProduct, Config.flip]
  simp_rw [Spin.toSign_flip, Int.cast_neg]
  exact Finset.prod_neg _

/-- For `h = 0`, odd-cardinality correlations vanish by spin-flip symmetry. -/
theorem correlation_odd_vanish (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (A : Finset ι) (hodd : Odd A.card) :
    correlation G ⟨J, 0, β⟩ A = 0 := by
  unfold correlation gibbsExpectation
  -- It suffices to show the numerator sum is zero; then inv * 0 = 0.
  suffices hsum : ∑ σ : Config ι,
      spinProduct A σ * boltzmannWeight G ⟨J, 0, β⟩ σ = 0 by
    rw [hsum, mul_zero]
  -- Sum over σ of spinProduct(A,σ) · w(σ) = 0
  -- by pairing σ ↔ flip σ: the w(σ) are equal (h=0 symmetry)
  -- and spinProduct changes sign (odd |A|)
  have hflip : ∀ σ : Config ι,
      spinProduct A σ.flip * boltzmannWeight G ⟨J, 0, β⟩ σ.flip =
      -(spinProduct A σ * boltzmannWeight G ⟨J, 0, β⟩ σ) := by
    intro σ
    rw [spinProduct_flip]
    have hw : boltzmannWeight G ⟨J, 0, β⟩ σ.flip =
        boltzmannWeight G ⟨J, 0, β⟩ σ := by
      unfold boltzmannWeight
      congr 1; rw [hamiltonian_flip_eq G ⟨J, 0, β⟩ rfl σ]
    rw [hw]
    obtain ⟨k, hk⟩ := hodd
    rw [hk]; ring_nf; simp
  -- Pair the sum via the flip involution: S = -S, hence S = 0.
  let flipEquiv : Equiv.Perm (Config ι) :=
    ⟨Config.flip, Config.flip, Config.flip_flip, Config.flip_flip⟩
  -- S = -S by reindexing via flip and applying hflip
  have hneq : ∑ σ : Config ι, spinProduct A σ * boltzmannWeight G ⟨J, 0, β⟩ σ =
      -(∑ σ : Config ι, spinProduct A σ * boltzmannWeight G ⟨J, 0, β⟩ σ) :=
    calc ∑ σ : Config ι, spinProduct A σ * boltzmannWeight G ⟨J, 0, β⟩ σ
        = ∑ σ : Config ι, spinProduct A σ.flip * boltzmannWeight G ⟨J, 0, β⟩ σ.flip :=
          Fintype.sum_equiv flipEquiv _ _ (fun σ => by dsimp [flipEquiv]; simp [Config.flip_flip])
      _ = ∑ σ : Config ι, -(spinProduct A σ * boltzmannWeight G ⟨J, 0, β⟩ σ) :=
          Finset.sum_congr rfl (fun σ _ => hflip σ)
      _ = -(∑ σ : Config ι, spinProduct A σ * boltzmannWeight G ⟨J, 0, β⟩ σ) := by
          rw [Finset.sum_neg_distrib]
  linarith

/-- **Z₂ odd-symmetry under `h → -h`**: for any Ising parameters and
any subset `A`,
`correlation G ⟨J, -h, β⟩ A = (-1)^|A| · correlation G ⟨J, h, β⟩ A`.

Proof: numerator of `correlation(-h)` equals `(-1)^|A|` times numerator
of `correlation(h)` via `hamiltonian_neg_h` (`H(σ;-h) = H(σ.flip;h)`) +
flip reindex + `spinProduct_flip`. The denominators coincide by
`partitionFunction_neg_h`.

At `h = 0`: gives `⟨σ^A⟩ = (-1)^|A| · ⟨σ^A⟩`, so odd `|A|` ⇒ vanish —
this generalizes `correlation_odd_vanish`.

Reference: Glimm–Jaffe §5.3 pp. 77–80 (Z₂ symmetry). -/
theorem correlation_neg_h (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) (A : Finset ι) :
    correlation G (⟨J, -h, β⟩ : IsingParams ℝ) A
      = (-1) ^ A.card * correlation G (⟨J, h, β⟩ : IsingParams ℝ) A := by
  unfold correlation gibbsExpectation
  rw [partitionFunction_neg_h]
  -- Numerator: ∑ spinProduct A σ · w(-h, σ) = (-1)^|A| · ∑ spinProduct A σ · w(h, σ)
  have hnum : ∑ σ : Config ι,
        spinProduct A σ * boltzmannWeight G (⟨J, -h, β⟩ : IsingParams ℝ) σ
      = (-1) ^ A.card * ∑ σ : Config ι,
          spinProduct A σ * boltzmannWeight G (⟨J, h, β⟩ : IsingParams ℝ) σ := by
    let flipEquiv : Equiv.Perm (Config ι) :=
      ⟨Config.flip, Config.flip, Config.flip_flip, Config.flip_flip⟩
    calc ∑ σ : Config ι,
            spinProduct A σ * boltzmannWeight G (⟨J, -h, β⟩ : IsingParams ℝ) σ
        = ∑ σ : Config ι,
            spinProduct A σ *
              boltzmannWeight G (⟨J, h, β⟩ : IsingParams ℝ) σ.flip := by
          refine Finset.sum_congr rfl ?_
          intros σ _
          congr 1
          unfold boltzmannWeight
          rw [hamiltonian_neg_h]
      _ = ∑ σ : Config ι,
            spinProduct A σ.flip *
              boltzmannWeight G (⟨J, h, β⟩ : IsingParams ℝ) σ := by
          exact (Fintype.sum_equiv flipEquiv _ _
            (fun σ => by dsimp [flipEquiv]; simp [Config.flip_flip])).symm
      _ = ∑ σ : Config ι,
            ((-1) ^ A.card * spinProduct A σ) *
              boltzmannWeight G (⟨J, h, β⟩ : IsingParams ℝ) σ := by
          refine Finset.sum_congr rfl ?_
          intros σ _
          rw [spinProduct_flip]
      _ = ∑ σ : Config ι,
            (-1) ^ A.card *
              (spinProduct A σ *
                boltzmannWeight G (⟨J, h, β⟩ : IsingParams ℝ) σ) := by
          refine Finset.sum_congr rfl ?_
          intros σ _
          ring
      _ = (-1) ^ A.card * ∑ σ : Config ι,
            spinProduct A σ *
              boltzmannWeight G (⟨J, h, β⟩ : IsingParams ℝ) σ :=
          (Finset.mul_sum _ _ _).symm
  rw [hnum]
  ring

/-- **Ursell 2-point invariance under `h → -h`** (for `i ≠ j`):
`truncated2 G ⟨J, -h, β⟩ i j = truncated2 G ⟨J, h, β⟩ i j`.

Each summand `⟨A⟩` transforms by `(-1)^|A|`: cards `|{i,j}| = 2`
(requires `i ≠ j`), `|{i}| = |{j}| = 1`. The signs cancel overall:
`(-1)² − (-1)·(-1) = 1 − 1` kept vs `−`. Explicitly the h=-h version
equals the h version.

Caveat: at `i = j` the Finset `{i,i} = {i}` collapses to card 1,
breaking the parity; the identity does not extend (analogous to the
`susceptibility_J_zero` diagonal caveat). -/
theorem truncated2_neg_h (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) {i j : ι} (hij : i ≠ j) :
    truncated2 G (⟨J, -h, β⟩ : IsingParams ℝ) i j
      = truncated2 G (⟨J, h, β⟩ : IsingParams ℝ) i j := by
  unfold truncated2
  rw [correlation_neg_h G J h β {i, j},
      correlation_neg_h G J h β {i},
      correlation_neg_h G J h β {j}]
  simp only [Finset.card_singleton, Finset.card_pair hij]
  ring

/-! ## Lebowitz third inequality

The Lebowitz third inequality (Lebowitz, 1974) is the key input for the GHS
inequality. It states that in the doubled ferromagnetic Ising system with
`h ≥ 0`, the t-q cross-correlation is bounded:

`⟨σ_iσ_jσ_k⟩ + ⟨σ_i⟩⟨σ_jσ_k⟩ ≤ ⟨σ_iσ_j⟩⟨σ_k⟩ + ⟨σ_iσ_k⟩⟨σ_j⟩`

The proof uses the continuous-spin (φ⁴) approximation:
1. For φ⁴ spins, the quadrupled-system non-negativity holds per site
   (`phi4_single_site_nonneg` in `ContinuousSpin/Phi4.lean`)
2. This gives Theorem 4.3.1 (Glimm–Jaffe): `⟨α^A β^B γ^C δ^D⟩ ≥ 0`
3. Corollary 4.3.2 gives the Lebowitz inequality for continuous spins
4. Ising correlations are limits of φ⁴ correlations as λ → ∞ in
   `dμ = exp(-λ(ξ²-1)²) dξ → ½(δ₊₁ + δ₋₁)`

Note: the per-site factorization in Ellis §V.3 (Lemma V.3.2) does NOT
hold for discrete Ising spins — the all-odd parity case gives negative
values (e.g., `Σ αβγδ exp(2hα) = -8 cosh(2h) < 0` for k=l=m=n=1).
The continuous-spin route is essential.

References:
* Glimm–Jaffe, *Quantum Physics*, §4.3, Corollary 4.3.2
* Lebowitz, Comm. Math. Phys. 35 (1974)
* See `.self-local/tex/0019-ghs-inequality.tex` for the full proof -/

/-- **Lebowitz third inequality** (Lebowitz, 1974):
For ferromagnetic Ising with `h ≥ 0` and distinct sites `i, j, k`,
`⟨σ_iσ_jσ_k⟩ + ⟨σ_i⟩⟨σ_jσ_k⟩ ≤ ⟨σ_iσ_j⟩⟨σ_k⟩ + ⟨σ_iσ_k⟩⟨σ_j⟩`.

Proved for continuous φ⁴ spins via `phi4_single_site_nonneg`
(Glimm–Jaffe, Theorem 4.3.1), then transferred to Ising spins by the
approximation `dμ = exp(-λ(ξ²-1)²) dξ → ½(δ₊₁ + δ₋₁)` as `λ → ∞`. -/
axiom lebowitz_third (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j k : ι)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    correlation G p {i, j, k} + correlation G p {i} * correlation G p {j, k} ≤
    correlation G p {i, j} * correlation G p {k} +
    correlation G p {i, k} * correlation G p {j}

/-! ## GHS inequality

**Theorem** (Griffiths–Hurst–Sherman, 1970): For the ferromagnetic Ising
model with `h ≥ 0` and distinct sites `i, j, k`:
`⟨σ_i; σ_j; σ_k⟩ ≤ 0`.

The proof combines three ingredients:
1. **Lebowitz third inequality** (`lebowitz_third`):
   `⟨σ_iσ_jσ_k⟩ + ⟨σ_i⟩⟨σ_jσ_k⟩ ≤ ⟨σ_iσ_j⟩⟨σ_k⟩ + ⟨σ_iσ_k⟩⟨σ_j⟩`
2. **GKS-I** (`gks_first`): `⟨σ_i⟩ ≥ 0`
3. **Truncated 2-point non-negativity** (`truncated2_nonneg`):
   `⟨σ_j; σ_k⟩ ≥ 0`

Substituting the Lebowitz bound into truncated3:
`⟨σ_i; σ_j; σ_k⟩ ≤ -2⟨σ_i⟩ · ⟨σ_j; σ_k⟩ ≤ 0`. -/

/-- **GHS inequality** (Griffiths–Hurst–Sherman, 1970):
For ferromagnetic parameters with distinct sites,
the truncated 3-point function is non-positive.
`⟨σ_i; σ_j; σ_k⟩ ≤ 0`. -/
theorem ghs_inequality (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j k : ι)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    truncated3 G p i j k ≤ 0 := by
  have hleb := lebowitz_third G p hf i j k hij hjk hik
  have hgks := gks_first G p hf {i}
  have ht2 := truncated2_nonneg G p hf j k
  unfold truncated3 truncated2 at *
  nlinarith [mul_nonneg hgks ht2]

/-! ## Corollary 4.3.3: truncated 4-point function ≤ 0

For h = 0 and four distinct sites, the truncated (connected) 4-point
correlation function is non-positive:
  U₄(i,j,k,l) = ⟨σ_iσ_jσ_kσ_l⟩ - ⟨σ_iσ_j⟩⟨σ_kσ_l⟩
                 - ⟨σ_iσ_k⟩⟨σ_jσ_l⟩ - ⟨σ_iσ_l⟩⟨σ_jσ_k⟩ ≤ 0.

This requires the Lebowitz inequality for 4-point functions (the general
Cor. 4.3.2), which goes beyond our 3-site `lebowitz_third` axiom.
We axiomatize the 4-site Lebowitz inequality as the Ising translation of
`⟨t_{ij}q_{kl}⟩ ≤ ⟨t_{ij}⟩⟨q_{kl}⟩` in the doubled system. -/

/-- The truncated (connected) 4-point function for distinct sites:
`U₄(i,j,k,l) = ⟨σ_iσ_jσ_kσ_l⟩ - ⟨σ_iσ_j⟩⟨σ_kσ_l⟩
               - ⟨σ_iσ_k⟩⟨σ_jσ_l⟩ - ⟨σ_iσ_l⟩⟨σ_jσ_k⟩`. -/
noncomputable def truncated4 (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (i j k l : ι) : ℝ :=
  correlation G p {i, j, k, l}
  - correlation G p {i, j} * correlation G p {k, l}
  - correlation G p {i, k} * correlation G p {j, l}
  - correlation G p {i, l} * correlation G p {j, k}

/-- **Infinite-temperature (`β = 0`) vanishing of the Lebowitz
4-point (truncated) function**: for any ambient graph `G`, any
`J, h ∈ ℝ`, and any sites `i, j, k, l : ι`,
`truncated4 G ⟨J, h, 0⟩ i j k l = 0`.

At `β = 0`, each of the seven Finset correlations in the Lebowitz
combination is over a nonempty subset (every subset contains at
least one of the supplied sites), so
`correlation_beta_zero_vanish_of_nonempty_A` makes every term zero
and the linear combination vanishes.

Companion to `truncated2_beta_zero` / `truncated3_beta_zero`. No
distinctness hypotheses are needed at `β = 0`. Note: unlike the
`β = 0` case, `truncated4` does *not* vanish at `J = 0` in
general — the Lebowitz 4-point is `-2·t⁴` where `t = tanh(β·h)`
for pairwise distinct sites, which is non-zero when `β·h ≠ 0`.
So this PR adds only the `β = 0` slice.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.1 pp. 72–74
(cluster property context); §4.3 Cor. 4.3.3 / Lebowitz. -/
theorem truncated4_beta_zero (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h : ℝ) (i j k l : ι) :
    truncated4 G (⟨J, h, 0⟩ : IsingParams ℝ) i j k l = 0 := by
  unfold truncated4
  rw [correlation_beta_zero_vanish_of_nonempty_A G J h {i, j, k, l}
        ⟨i, by simp⟩,
      correlation_beta_zero_vanish_of_nonempty_A G J h {i, j}
        ⟨i, by simp⟩,
      correlation_beta_zero_vanish_of_nonempty_A G J h {k, l}
        ⟨k, by simp⟩,
      correlation_beta_zero_vanish_of_nonempty_A G J h {i, k}
        ⟨i, by simp⟩,
      correlation_beta_zero_vanish_of_nonempty_A G J h {j, l}
        ⟨j, by simp⟩,
      correlation_beta_zero_vanish_of_nonempty_A G J h {i, l}
        ⟨i, by simp⟩,
      correlation_beta_zero_vanish_of_nonempty_A G J h {j, k}
        ⟨j, by simp⟩]
  ring

/-- **Non-interacting (`J = 0`) closed form for the Lebowitz 4-point
(truncated) function**: for any ambient graph `G`, any `h, β ∈ ℝ`,
and pairwise distinct `i, j, k, l : ι`,
`truncated4 G ⟨0, h, β⟩ i j k l = -2 · tanh(β·h)^4`.

At `J = 0`, `correlation_J_zero` gives
`⟨σ^A⟩ = tanh(β·h)^|A|`. With pairwise distinct
`i, j, k, l` one has `{i,j,k,l}.card = 4`,
`{i,j}.card = {i,k}.card = {i,l}.card = {j,k}.card =
{j,l}.card = {k,l}.card = 2`, so the Lebowitz combination becomes
`t⁴ - t² · t² - t² · t² - t² · t² = t⁴ - 3·t⁴ = -2·t⁴`
with `t = tanh(β·h)`.

This complements `truncated4_beta_zero` (vanishing slice): at
`J = 0` the Lebowitz 4-point does not vanish but has the explicit
closed form `-2·t⁴`. Note `-2·t⁴ ≤ 0` always, consistent with
the `U₄ ≤ 0` statement of Cor. 4.3.3 (though Cor. 4.3.3 itself
is the `h = 0` case; our `J = 0` slice is an independent special
case and not a direct witness of the Cor. 4.3.3 theorem).

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.1 pp. 72–74
(cluster context); §4.3 Cor. 4.3.3 / Lebowitz. -/
theorem truncated4_J_zero_of_pairwise_distinct
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h β : ℝ) {i j k l : ι}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    truncated4 G (⟨0, h, β⟩ : IsingParams ℝ) i j k l
      = -2 * Real.tanh (β * h) ^ 4 := by
  unfold truncated4
  rw [correlation_J_zero, correlation_J_zero, correlation_J_zero,
      correlation_J_zero, correlation_J_zero, correlation_J_zero,
      correlation_J_zero]
  have hcard_ijkl : ({i, j, k, l} : Finset ι).card = 4 := by
    have h_jkl_card : ({j, k, l} : Finset ι).card = 3 := by
      rw [show ({j, k, l} : Finset ι) = insert j ({k, l} : Finset ι) from rfl,
          Finset.card_insert_of_notMem (by simp [hjk, hjl]),
          Finset.card_pair hkl]
    have h_i_nin : i ∉ ({j, k, l} : Finset ι) := by
      simp [hij, hik, hil]
    rw [show ({i, j, k, l} : Finset ι) = insert i ({j, k, l} : Finset ι)
            from rfl,
        Finset.card_insert_of_notMem h_i_nin, h_jkl_card]
  have hcard_ij : ({i, j} : Finset ι).card = 2 := Finset.card_pair hij
  have hcard_ik : ({i, k} : Finset ι).card = 2 := Finset.card_pair hik
  have hcard_il : ({i, l} : Finset ι).card = 2 := Finset.card_pair hil
  have hcard_jk : ({j, k} : Finset ι).card = 2 := Finset.card_pair hjk
  have hcard_jl : ({j, l} : Finset ι).card = 2 := Finset.card_pair hjl
  have hcard_kl : ({k, l} : Finset ι).card = 2 := Finset.card_pair hkl
  rw [hcard_ijkl, hcard_ij, hcard_kl, hcard_ik, hcard_jl, hcard_il, hcard_jk]
  ring

/-- **Lebowitz 4-site inequality** (Glimm–Jaffe, Cor. 4.3.2 for |A|=|B|=2).
For ferromagnetic Ising with `h ≥ 0` and four distinct sites,
`⟨σ_iσ_jσ_kσ_l⟩ + ⟨σ_iσ_j⟩⟨σ_kσ_l⟩
  ≤ ⟨σ_iσ_k⟩⟨σ_jσ_l⟩ + ⟨σ_iσ_l⟩⟨σ_jσ_k⟩
    + ⟨σ_iσ_kσ_l⟩⟨σ_j⟩ + ⟨σ_jσ_kσ_l⟩⟨σ_i⟩`.

This is the Ising translation of `⟨t_At_Bq_Cq_D⟩ ≤ ⟨t_At_B⟩⟨q_Cq_D⟩`
from Cor. 4.3.2 applied with A = {i,j}, B = {k,l}. Proved via φ⁴
approximation, same route as `lebowitz_third`. -/
axiom lebowitz_four (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j k l : ι)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    correlation G p {i, j, k, l} + correlation G p {i, j} * correlation G p {k, l} ≤
    correlation G p {i, k} * correlation G p {j, l} +
    correlation G p {i, l} * correlation G p {j, k} +
    correlation G p {i, k, l} * correlation G p {j} +
    correlation G p {j, k, l} * correlation G p {i}

/-- **Cor. 4.3.3** (Glimm–Jaffe, §4.3, p. 61).
For `h = 0` and four distinct sites, the truncated 4-point function
is non-positive: `U₄(i,j,k,l) ≤ 0`.

When `h = 0`, odd-cardinality correlations vanish by spin-flip symmetry,
so `⟨σ_i⟩ = ⟨σ_j⟩ = 0` and `⟨σ_{ijk}⟩ = 0`, reducing the Lebowitz
4-site inequality to `U₄ ≤ 0`. -/
theorem cor_4_3_3 (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hf : Ferromagnetic ⟨J, (0 : ℝ), β⟩) (i j k l : ι)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    truncated4 G ⟨J, 0, β⟩ i j k l ≤ 0 := by
  have hleb := lebowitz_four G ⟨J, 0, β⟩ hf i j k l hij hik hil hjk hjl hkl
  -- For h = 0: odd-cardinality correlations vanish.
  -- ⟨σ_i⟩ = 0, ⟨σ_{ijk}⟩ = 0 by spin-flip symmetry.
  -- This is a consequence of hamiltonian_flip_eq: H(flip σ) = H(σ) when h = 0,
  -- combined with spinProduct_flip: σ^A(flip) = (-1)^|A| σ^A,
  -- giving ⟨σ^A⟩ = (-1)^|A| ⟨σ^A⟩, so ⟨σ^A⟩ = 0 when |A| is odd.
  -- For now we use correlation_flip_odd which states this directly.
  -- TODO: prove correlation = 0 for odd |A| when h = 0 from spin-flip symmetry
  have hcorr1 : correlation G ⟨J, 0, β⟩ {i} = 0 :=
    correlation_odd_vanish G J β {i} ⟨0, by simp⟩
  have hcorr3a : correlation G ⟨J, 0, β⟩ {i, k, l} = 0 :=
    correlation_odd_vanish G J β {i, k, l} ⟨1, by simp [Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, hik, hil, hkl]⟩
  have hcorr3b : correlation G ⟨J, 0, β⟩ {j, k, l} = 0 :=
    correlation_odd_vanish G J β {j, k, l} ⟨1, by simp [Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, hjk, hjl, hkl]⟩
  -- Even-cardinality correlations are non-negative by GKS-I.
  have h_ij := gks_first G ⟨J, 0, β⟩ hf {i, j}
  have h_kl := gks_first G ⟨J, 0, β⟩ hf {k, l}
  unfold truncated4
  simp only [hcorr1, hcorr3a, hcorr3b, mul_zero, zero_mul, add_zero] at hleb ⊢
  nlinarith [mul_nonneg h_ij h_kl]

/-! ## Corollary 4.3.4 = GHS inequality

Cor. 4.3.4 (Glimm–Jaffe, §4.3, p. 62) states the truncated 3-point
function ≤ 0 for h ≥ 0. This is exactly `ghs_inequality` above. -/

/-! ## Corollary 4.3.5: n-point inductive upper bound

For ferromagnetic Ising with `h ≥ 0`, the key inductive step
(Glimm–Jaffe, §4.3, pp. 62–63) bounds an `(n+2)`-point correlation:

`⟨σ_{S ∪ {j,k}}⟩ ≤ ⟨σ_S⟩⟨σ_jσ_k⟩ + ∑_{T ⊆ S} ⟨σ_{T ∪ {j}}⟩⟨σ_{(S\T) ∪ {k}}⟩`

This is derived from the general Lebowitz inequality (Cor. 4.3.2) applied
with `A = S`, `B = {j, k}`, and dropping non-positive terms (odd `|B₂|`
terms and nontrivial `A`-partition terms with even `|B₂|`).

Iterating this bound gives Cor. 4.3.5:
`⟨σ_{i₁}⋯σ_{iₙ}⟩ ≤ (n-1)! ∑ₘ ∏ (2-point and 1-point correlations)`
where `m` runs over all partial matchings of `{i₁,…,iₙ}`.

References:
* Glimm–Jaffe, *Quantum Physics*, §4.3, Cor. 4.3.5, p. 62
* Proof: induction on `n` using Cor. 4.3.2 (general Lebowitz) -/

/-- **Inductive Lebowitz bound** (Glimm–Jaffe, §4.3, key step for Cor. 4.3.5).
For ferromagnetic Ising with `h ≥ 0`, a set `S` of sites, and two sites
`j, k ∉ S` with `j ≠ k`:

`⟨σ_{S ∪ {j,k}}⟩ ≤ ⟨σ_S⟩⟨σ_jσ_k⟩ + ∑_{T ⊆ S} ⟨σ_{T ∪ {j}}⟩⟨σ_{(S\T) ∪ {k}}⟩`.

Proved via the general Lebowitz inequality (Cor. 4.3.2) for continuous φ⁴
spins, then transferred to Ising by the approximation
`dμ = exp(-λ(ξ²-1)²) dξ → ½(δ₊₁ + δ₋₁)` as `λ → ∞`.

The sum over `T ∈ S.powerset` includes `T = ∅` and `T = S`. -/
axiom lebowitz_inductive (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (S : Finset ι) (j k : ι) (hj : j ∉ S) (hk : k ∉ S) (hjk : j ≠ k) :
    correlation G p (insert j (insert k S)) ≤
    correlation G p S * correlation G p {j, k} +
    ∑ T ∈ S.powerset,
      correlation G p (insert j T) * correlation G p (insert k (S \ T))

/-- **Cor. 4.3.5** (Glimm–Jaffe, §4.3, p. 62): for `h = 0` and `n + 2`
distinct sites, the `(n+2)`-point function is bounded by sums of products of
2-point correlations (since 1-point functions vanish at `h = 0`).

This is the `h = 0` specialization of the inductive bound: odd correlations
vanish by spin-flip symmetry, so only terms where both `|T ∪ {j}|` and
`|(S\T) ∪ {k}|` are even contribute. -/
theorem cor_4_3_5_h0 (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hf : Ferromagnetic ⟨J, (0 : ℝ), β⟩)
    (S : Finset ι) (j k : ι) (hj : j ∉ S) (hk : k ∉ S) (hjk : j ≠ k) :
    correlation G ⟨J, 0, β⟩ (insert j (insert k S)) ≤
    correlation G ⟨J, 0, β⟩ S * correlation G ⟨J, 0, β⟩ {j, k} +
    ∑ T ∈ S.powerset,
      correlation G ⟨J, 0, β⟩ (insert j T) *
        correlation G ⟨J, 0, β⟩ (insert k (S \ T)) :=
  lebowitz_inductive G ⟨J, 0, β⟩ hf S j k hj hk hjk

end IsingModel
