import IsingModel.Inequalities.GHS.GHSInequality
import IsingModel.Inequalities.GKS
import IsingModel.InfiniteVolume.Boundedness

/-!
# Truncated 3-point contraction into two-point functions (finite volume)

Brick 1 toward the external-field derivative `∂/∂h` of the connected
two-point function (issue #4413).

For a ferromagnetic Ising model with `h ≥ 0` (folded into `Ferromagnetic p`)
on a general finite graph, the Ursell (truncated 3-point) function is
contracted by two-point functions:
`|⟨σ_i; σ_j; σ_k⟩| ≤ ⟨σ_i⟩·⟨σ_j; σ_k⟩ + ⟨σ_j⟩·⟨σ_i; σ_k⟩`
(weighted form) and, since `0 ≤ ⟨σ_·⟩ ≤ 1` at `h ≥ 0` with `⟨σ_·; σ_·⟩ ≥ 0`,
`|⟨σ_i; σ_j; σ_k⟩| ≤ ⟨σ_i; σ_k⟩ + ⟨σ_j; σ_k⟩` (constant `C = 1`).

This is the finite-volume correlation-inequality content of the
Griffiths–Hurst–Sherman bound used in the proof of GJ Theorem 17.6.1
(*Quantum Physics* 2nd ed., p. 313). It combines:
* the GHS inequality (GJ Cor 4.3.4, p. 62) `⟨σ_i; σ_j; σ_k⟩ ≤ 0`, and
* GKS-II (second Griffiths inequality, GJ Thm 4.1.3, (4.1.11), p. 57)
  `⟨σ_iσ_j⟩·⟨σ_k⟩ ≤ ⟨σ_iσ_jσ_k⟩` regrouped against the pair `{i,j}` vs `{k}`.

No Lebowitz inductive bound (GJ Cor 4.3.5, p. 63) is needed here: that
provides only the wrong-sign upper bound `⟨σ_i;σ_j;σ_k⟩ ≤ 2⟨σ_i⟩⟨σ_j⟩⟨σ_k⟩`,
whereas GHS gives the required `|·| = −⟨σ_i;σ_j;σ_k⟩`.

Pure finite volume: no limit, exhaustion, or equicontinuity is involved, so
this is book-faithful and independently valuable even if the full
infinite-volume `∂/∂h` chain stalls at the equicontinuity wall.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Regrouping identity for the Ursell function against the pair `{i,j}` vs
`{k}`: the truncated 3-point function plus the two weighted two-point terms
equals `⟨σ_iσ_jσ_k⟩ − ⟨σ_iσ_j⟩⟨σ_k⟩`. Proved by unfolding the definitions and
`ring`. -/
private lemma truncated3_add_weighted_two_point_eq
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (i j k : ι) :
    truncated3 G p i j k
        + correlation G p {i} * truncated2 G p j k
        + correlation G p {j} * truncated2 G p i k
      = correlation G p {i, j, k}
        - correlation G p {i, j} * correlation G p {k} := by
  unfold truncated3 truncated2
  ring

/-- **Weighted truncated 3-point contraction** (finite volume, ferromagnetic,
`h ≥ 0`): for distinct sites `i, j, k`,
`|⟨σ_i; σ_j; σ_k⟩| ≤ ⟨σ_i⟩·⟨σ_j; σ_k⟩ + ⟨σ_j⟩·⟨σ_i; σ_k⟩`.

Proof: GHS gives `⟨σ_i; σ_j; σ_k⟩ ≤ 0`, so the absolute value is its negation;
the regrouping identity `truncated3_add_weighted_two_point_eq` together with
GKS-II (`⟨σ_iσ_j⟩⟨σ_k⟩ ≤ ⟨σ_iσ_jσ_k⟩`, via `symmDiff {i,j} {k} = {i,j,k}`)
shows the left-hand sum is non-negative, which is the claim.

Reference: Glimm–Jaffe, *Quantum Physics* 2nd ed., Thm 17.6.1 (p. 313),
Cor 4.3.4 (p. 62), Thm 4.1.3, (4.1.11) (p. 57). -/
theorem abs_truncated3_le_weighted
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) {i j k : ι}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    |truncated3 G p i j k|
      ≤ correlation G p {i} * truncated2 G p j k
        + correlation G p {j} * truncated2 G p i k := by
  have hghs := ghs_inequality G p hf i j k hij hjk hik
  have hgks := gks_second G p hf ({i, j} : Finset ι) {k}
  have hijk : symmDiff ({i, j} : Finset ι) {k} = ({i, j, k} : Finset ι) := by
    ext x
    simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (⟨h | rfl, hk⟩ | ⟨rfl, h⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    · rintro (rfl | rfl | rfl)
      · exact Or.inl ⟨Or.inl rfl, hik⟩
      · exact Or.inl ⟨Or.inr rfl, hjk⟩
      · exact Or.inr ⟨rfl, fun h => h.elim hik.symm hjk.symm⟩
  rw [hijk] at hgks
  have hkey := truncated3_add_weighted_two_point_eq G p i j k
  rw [abs_of_nonpos hghs]
  linarith

/-- **Truncated 3-point contraction, `C = 1` form** (finite volume,
ferromagnetic, `h ≥ 0`): for distinct sites `i, j, k`,
`|⟨σ_i; σ_j; σ_k⟩| ≤ ⟨σ_i; σ_k⟩ + ⟨σ_j; σ_k⟩`.

This is the constant-`C = 1` corollary of `abs_truncated3_le_weighted`,
using `0 ≤ ⟨σ_i⟩ ≤ 1` at `h ≥ 0` (GKS-I `gks_first` and
`abs_correlation_le_one`) and non-negativity of the two-point functions
(`truncated2_nonneg`). It is the pointwise brick behind bounding the
field derivative of the connected two-point function in the proof of
GJ Theorem 17.6.1 (*Quantum Physics* 2nd ed., p. 313). -/
theorem abs_truncated3_le
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) {i j k : ι}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    |truncated3 G p i j k| ≤ truncated2 G p i k + truncated2 G p j k := by
  have hw := abs_truncated3_le_weighted G p hf hij hjk hik
  have hi1 : correlation G p {i} ≤ 1 :=
    le_trans (le_abs_self _) (abs_correlation_le_one G p {i})
  have hj1 : correlation G p {j} ≤ 1 :=
    le_trans (le_abs_self _) (abs_correlation_le_one G p {j})
  have hjk0 : 0 ≤ truncated2 G p j k := truncated2_nonneg G p hf j k
  have hik0 : 0 ≤ truncated2 G p i k := truncated2_nonneg G p hf i k
  have h1 := mul_le_of_le_one_left hjk0 hi1
  have h2 := mul_le_of_le_one_left hik0 hj1
  linarith

/-! ## Semi-truncated two-block susceptibility (the `∂/∂h` brick, `|B| ≤ 2`)

For a block `B` and an extra site `l ∉ B`, the *semi-truncated two-block
susceptibility* is `⟨σ_B; σ_l⟩ := ⟨σ_B σ_l⟩ − ⟨σ_B⟩⟨σ_l⟩`, the connected
correlation whose site-sum is the field derivative `∂/∂h ⟨σ_B⟩`.  For `|B| ≤ 2`
it is squeezed between `0` (GKS-II) and the sub-additive two-point bound
`∑_{b ∈ B} τ₂(b, l)` (GHS `+` GKS-I regrouping), the head equi-Lipschitz brick of
the `∂/∂h` route of GJ Theorem 17.6.1 (*Quantum Physics* 2nd ed., p. 313). -/

/-- **Lower bound for the pair semi-truncated susceptibility (`B = {i,j}`,
GKS-II)**: for a ferromagnetic model with `h ≥ 0` and sites with `l ∉ {i, j}`,
`0 ≤ ⟨σ_iσ_j; σ_l⟩ = ⟨σ_iσ_jσ_l⟩ − ⟨σ_iσ_j⟩⟨σ_l⟩`.

Proof: GKS-II (`gks_second`) applied to `{i,j}` and `{l}` gives
`⟨σ_iσ_j⟩⟨σ_l⟩ ≤ ⟨σ^{{i,j} △ {l}}⟩ = ⟨σ_iσ_jσ_l⟩` (using `l ∉ {i,j}`, so the
symmetric difference is `{i,j,l}`).  This is the GKS-II lower half of the
semi-truncated two-block bound of GJ Theorem 17.6.1 (*Quantum Physics* 2nd ed.,
p. 313; Thm 4.1.3, (4.1.11), p. 57). -/
theorem semiTruncated_pair_nonneg (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) {i j l : ι}
    (hil : i ≠ l) (hjl : j ≠ l) :
    0 ≤ correlation G p {i, j, l}
      - correlation G p {i, j} * correlation G p {l} := by
  have hgks := gks_second G p hf ({i, j} : Finset ι) {l}
  have hijl : symmDiff ({i, j} : Finset ι) {l} = ({i, j, l} : Finset ι) := by
    ext x
    simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (⟨h | rfl, _⟩ | ⟨rfl, _⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    · rintro (rfl | rfl | rfl)
      · exact Or.inl ⟨Or.inl rfl, hil⟩
      · exact Or.inl ⟨Or.inr rfl, hjl⟩
      · exact Or.inr ⟨rfl, fun h => h.elim hil.symm hjl.symm⟩
  rw [hijl] at hgks
  linarith

/-- **Upper bound for the pair semi-truncated susceptibility (`B = {i,j}`,
GHS `+` GKS-I)**: for a ferromagnetic model with `h ≥ 0` and pairwise distinct
sites `i, j, l`,
`⟨σ_iσ_j; σ_l⟩ ≤ τ₂(i, l) + τ₂(j, l)`.

Proof: the exact regrouping identity (closed by `ring` after unfolding)
`⟨σ_iσ_j; σ_l⟩ = truncated3(i,j,l) + ⟨σ_i⟩·τ₂(j,l) + ⟨σ_j⟩·τ₂(i,l)`, together
with GHS (`ghs_inequality`, `truncated3 ≤ 0`), the magnetization bound
`⟨σ_·⟩ ≤ 1` (`abs_correlation_le_one`), and `τ₂ ≥ 0` (`truncated2_nonneg`), gives
`⟨σ_iσ_j; σ_l⟩ ≤ 0 + 1·τ₂(j,l) + 1·τ₂(i,l)`.  This is the GHS/GKS-I upper half of
the semi-truncated two-block bound of GJ Theorem 17.6.1 (*Quantum Physics* 2nd
ed., p. 313; Cor. 4.3.4, p. 62). -/
theorem semiTruncated_pair_le (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) {i j l : ι}
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    correlation G p {i, j, l} - correlation G p {i, j} * correlation G p {l}
      ≤ truncated2 G p i l + truncated2 G p j l := by
  have hid : correlation G p {i, j, l}
        - correlation G p {i, j} * correlation G p {l}
      = truncated3 G p i j l
        + correlation G p {i} * truncated2 G p j l
        + correlation G p {j} * truncated2 G p i l := by
    unfold truncated3 truncated2
    ring
  have hghs := ghs_inequality G p hf i j l hij hjl hil
  have hi1 : correlation G p {i} ≤ 1 :=
    le_trans (le_abs_self _) (abs_correlation_le_one G p {i})
  have hj1 : correlation G p {j} ≤ 1 :=
    le_trans (le_abs_self _) (abs_correlation_le_one G p {j})
  have hjl0 : 0 ≤ truncated2 G p j l := truncated2_nonneg G p hf j l
  have hil0 : 0 ≤ truncated2 G p i l := truncated2_nonneg G p hf i l
  have h1 := mul_le_of_le_one_left hjl0 hi1
  have h2 := mul_le_of_le_one_left hil0 hj1
  rw [hid]; linarith

end IsingModel
