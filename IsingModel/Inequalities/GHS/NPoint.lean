import IsingModel.Inequalities.GHS.Truncated4
import IsingModel.Inequalities.Lebowitz.Cor435

/-!
# GHS inequality split — Cor 4.3.5 n-point bounds and J-continuity/differentiability

Part of the split GHS-inequality layer (Issue #1850).
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Corollary 4.3.4 = GHS inequality

Cor. 4.3.4 (Glimm–Jaffe, §4.3, p. 62) states the truncated 3-point
function ≤ 0 for h ≥ 0. This is exactly `ghs_inequality` above. -/

/-! ## Corollary 4.3.5: n-point inductive upper bound

For ferromagnetic Ising with `h ≥ 0`, the key inductive step
(Glimm–Jaffe, §4.3, pp. 62–63) bounds an `(n+2)`-point correlation:

`⟨σ_{S ∪ {j,k}}⟩ ≤ ⟨σ_S⟩⟨σ_jσ_k⟩ + ∑_{T ⊆ S} ⟨σ_{T ∪ {j}}⟩⟨σ_{(S\T) ∪ {k}}⟩`

This is `Lebowitz.lebowitz_inductive_bound` (`Inequalities/Lebowitz/Cor435.lean`),
proven from `cor_4_3_2_tq` at `A = S`, `B = {j,k}` by dropping the odd
right-hand part (GKS-I), cancelling the non-trivial even terms pairwise by
GKS-II, and moving the q-odd terms right after the reflection `X ↦ S \ X`.
It replaces the former `lebowitz_inductive` axiom (which, unlike
`lebowitz_four` and `lebowitz_third`, was true as stated).

Iterating this bound gives Cor. 4.3.5:
`⟨σ_{i₁}⋯σ_{iₙ}⟩ ≤ (n-1)! ∑ₘ ∏ (2-point and 1-point correlations)`
where `m` runs over all partial matchings of `{i₁,…,iₙ}`.

References:
* Glimm–Jaffe, *Quantum Physics*, §4.3, Cor. 4.3.5, p. 62 -/

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
  Lebowitz.lebowitz_inductive_bound G ⟨J, 0, β⟩ hf S j k hj hk hjk

/-- **Ursell 3-point antisymmetry under `h → -h`** (pairwise distinct):
`truncated3 G ⟨J, -h, β⟩ i j k = -truncated3 G ⟨J, h, β⟩ i j k`.

Ursell 3-point is ODD under `h → -h`: every summand has total Finset
card 3 (odd), so picks up factor `(-1)^3 = -1`. Specifically:
`|{i,j,k}| = 3`, `|{i}|·|{j,k}| = 1·2 = 3`, `|{i}|·|{j}|·|{k}| = 3`.
All contribute factor -1, yielding `U_3(-h) = -U_3(h)`.

Requires pairwise distinctness for the cards to be as stated. -/
theorem truncated3_neg_h (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) {i j k : ι}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    truncated3 G (⟨J, -h, β⟩ : IsingParams ℝ) i j k
      = -truncated3 G (⟨J, h, β⟩ : IsingParams ℝ) i j k := by
  unfold truncated3
  rw [correlation_neg_h G J h β {i, j, k},
      correlation_neg_h G J h β {i},
      correlation_neg_h G J h β {j, k},
      correlation_neg_h G J h β {j},
      correlation_neg_h G J h β {i, k},
      correlation_neg_h G J h β {k},
      correlation_neg_h G J h β {i, j}]
  have hcard_ij : ({i, j} : Finset ι).card = 2 := Finset.card_pair hij
  have hcard_jk : ({j, k} : Finset ι).card = 2 := Finset.card_pair hjk
  have hcard_ik : ({i, k} : Finset ι).card = 2 := Finset.card_pair hik
  have hcard_ijk : ({i, j, k} : Finset ι).card = 3 := by
    have h_i_nin : i ∉ ({j, k} : Finset ι) := by simp [hij, hik]
    rw [show ({i, j, k} : Finset ι) = insert i ({j, k} : Finset ι) from rfl,
        Finset.card_insert_of_notMem h_i_nin, hcard_jk]
  simp only [hcard_ij, hcard_jk, hcard_ik, hcard_ijk,
             Finset.card_singleton]
  ring

/-- **Lebowitz 4-point invariance under `h → -h`** (pairwise distinct):
`truncated4 G ⟨J, -h, β⟩ i j k l = truncated4 G ⟨J, h, β⟩ i j k l`.

Each summand's total Finset cards are: `|{i,j,k,l}| = 4` (factor +1),
and `|{a,b}|·|{c,d}| = 2·2 = 4` (factor +1). All signs cancel,
leaving `U_4` invariant. Requires pairwise distinctness so the
cards are 4 (not collapsed by Finset coincidences). -/
theorem truncated4_neg_h (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) {i j k l : ι}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    truncated4 G (⟨J, -h, β⟩ : IsingParams ℝ) i j k l
      = truncated4 G (⟨J, h, β⟩ : IsingParams ℝ) i j k l := by
  unfold truncated4
  rw [correlation_neg_h G J h β {i, j, k, l},
      correlation_neg_h G J h β {i, j},
      correlation_neg_h G J h β {k, l},
      correlation_neg_h G J h β {i, k},
      correlation_neg_h G J h β {j, l},
      correlation_neg_h G J h β {i, l},
      correlation_neg_h G J h β {j, k}]
  have hcard_ij : ({i, j} : Finset ι).card = 2 := Finset.card_pair hij
  have hcard_ik : ({i, k} : Finset ι).card = 2 := Finset.card_pair hik
  have hcard_il : ({i, l} : Finset ι).card = 2 := Finset.card_pair hil
  have hcard_jk : ({j, k} : Finset ι).card = 2 := Finset.card_pair hjk
  have hcard_jl : ({j, l} : Finset ι).card = 2 := Finset.card_pair hjl
  have hcard_kl : ({k, l} : Finset ι).card = 2 := Finset.card_pair hkl
  have hcard_ijkl : ({i, j, k, l} : Finset ι).card = 4 := by
    have h_jkl_card : ({j, k, l} : Finset ι).card = 3 := by
      rw [show ({j, k, l} : Finset ι) = insert j ({k, l} : Finset ι) from rfl,
          Finset.card_insert_of_notMem (by simp [hjk, hjl]),
          hcard_kl]
    have h_i_nin : i ∉ ({j, k, l} : Finset ι) := by simp [hij, hik, hil]
    rw [show ({i, j, k, l} : Finset ι) = insert i ({j, k, l} : Finset ι) from rfl,
        Finset.card_insert_of_notMem h_i_nin, h_jkl_card]
  simp only [hcard_ij, hcard_ik, hcard_il, hcard_jk, hcard_jl, hcard_kl, hcard_ijkl]
  ring

/-- **truncated2 Continuous in J** (Step 208).
At fixed h, β: `truncated2 G ⟨J, h, β⟩ i j` is continuous in J. -/
theorem truncated2_continuous_J (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h β : ℝ) (i j : ι) :
    Continuous (fun J' => truncated2 G (⟨J', h, β⟩ : IsingParams ℝ) i j) := by
  unfold truncated2
  exact (correlation_continuous_J G h β _).sub
    ((correlation_continuous_J G h β _).mul (correlation_continuous_J G h β _))

/-- **truncated3 Continuous in J** (Step 208). -/
theorem truncated3_continuous_J (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h β : ℝ) (i j k : ι) :
    Continuous (fun J' => truncated3 G (⟨J', h, β⟩ : IsingParams ℝ) i j k) := by
  unfold truncated3
  exact (((correlation_continuous_J G h β _).sub
    ((correlation_continuous_J G h β _).mul (correlation_continuous_J G h β _))).sub
    ((correlation_continuous_J G h β _).mul (correlation_continuous_J G h β _))).sub
    ((correlation_continuous_J G h β _).mul (correlation_continuous_J G h β _))
    |>.add (((continuous_const).mul (correlation_continuous_J G h β _)).mul
      (correlation_continuous_J G h β _) |>.mul
      (correlation_continuous_J G h β _))

/-- **truncated4 Continuous in J** (Step 208). -/
theorem truncated4_continuous_J (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h β : ℝ) (i j k l : ι) :
    Continuous (fun J' => truncated4 G (⟨J', h, β⟩ : IsingParams ℝ) i j k l) := by
  unfold truncated4
  exact (((correlation_continuous_J G h β _).sub
    ((correlation_continuous_J G h β _).mul (correlation_continuous_J G h β _))).sub
    ((correlation_continuous_J G h β _).mul (correlation_continuous_J G h β _))).sub
    ((correlation_continuous_J G h β _).mul (correlation_continuous_J G h β _))

/-- **truncated2 Differentiable in J** (Step 211). -/
theorem truncated2_differentiable_J (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h β : ℝ) (i j : ι) :
    Differentiable ℝ (fun J' => truncated2 G (⟨J', h, β⟩ : IsingParams ℝ) i j) := by
  unfold truncated2
  exact (correlation_differentiable_J G h β _).sub
    ((correlation_differentiable_J G h β _).mul (correlation_differentiable_J G h β _))

/-- **truncated3 Differentiable in J** (Step 211). -/
theorem truncated3_differentiable_J (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h β : ℝ) (i j k : ι) :
    Differentiable ℝ (fun J' => truncated3 G (⟨J', h, β⟩ : IsingParams ℝ) i j k) := by
  unfold truncated3
  exact (((correlation_differentiable_J G h β _).sub
    ((correlation_differentiable_J G h β _).mul (correlation_differentiable_J G h β _))).sub
    ((correlation_differentiable_J G h β _).mul (correlation_differentiable_J G h β _))).sub
    ((correlation_differentiable_J G h β _).mul (correlation_differentiable_J G h β _))
    |>.add (((differentiable_const _).mul (correlation_differentiable_J G h β _)).mul
      (correlation_differentiable_J G h β _) |>.mul
      (correlation_differentiable_J G h β _))

/-- **truncated4 Differentiable in J** (Step 211). -/
theorem truncated4_differentiable_J (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h β : ℝ) (i j k l : ι) :
    Differentiable ℝ (fun J' => truncated4 G (⟨J', h, β⟩ : IsingParams ℝ) i j k l) := by
  unfold truncated4
  exact (((correlation_differentiable_J G h β _).sub
    ((correlation_differentiable_J G h β _).mul (correlation_differentiable_J G h β _))).sub
    ((correlation_differentiable_J G h β _).mul (correlation_differentiable_J G h β _))).sub
    ((correlation_differentiable_J G h β _).mul (correlation_differentiable_J G h β _))


end IsingModel
