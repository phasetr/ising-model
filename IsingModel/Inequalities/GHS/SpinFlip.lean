import IsingModel.Inequalities.GHS.TruncatedDefs

/-!
# GHS inequality split — spin-flip symmetry for odd correlations and h-negation

Part of the split GHS-inequality layer (Issue #1850).
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Spin-flip symmetry for odd correlations

When `h = 0`, the Hamiltonian is invariant under global spin flip.
Odd-cardinality spin products change sign under flip, so their
Gibbs expectation vanishes. -/

omit [Fintype ι] [DecidableEq ι] in
/-- Spin product under global flip: `σ^A(flip σ) = (-1)^|A| · σ^A(σ)`. -/
theorem spinProduct_flip (A : Finset ι) (σ : Config ι) :
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

/-- **Correlation at `|h|` for even-card `A`**: if `|A|` is even,
`correlation G ⟨J, h, β⟩ A = correlation G ⟨J, |h|, β⟩ A`.

At even card, `(-1)^|A| = 1` so `correlation_neg_h` gives invariance
under `h → -h`, hence the value is unchanged by replacing `h` with
`|h|`. Analog of `freeEnergy_eq_abs_h` for the correlation layer
(restricted to even-cardinality subsets).

For odd `|A|`, the identity fails: `correlation ⟨J, -h, β⟩ A =
-correlation ⟨J, h, β⟩ A` means the sign depends on `sign h`. -/
theorem correlation_eq_abs_h_of_even_card (G : SimpleGraph ι)
    [Fintype G.edgeSet] (J h β : ℝ) (A : Finset ι)
    (heven : Even A.card) :
    correlation G (⟨J, h, β⟩ : IsingParams ℝ) A
      = correlation G (⟨J, |h|, β⟩ : IsingParams ℝ) A := by
  rcases abs_choice h with habs | habs
  · rw [habs]
  · rw [habs, correlation_neg_h]
    obtain ⟨k, hk⟩ := heven
    rw [hk]
    have h2k : (-1 : ℝ) ^ (k + k) = 1 := by
      rw [show k + k = 2 * k from by omega]
      rw [pow_mul]
      simp
    rw [h2k, one_mul]


end IsingModel
