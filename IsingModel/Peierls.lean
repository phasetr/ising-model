import IsingModel.Lattice

/-!
# Peierls argument for the existence of phase transitions

The Peierls argument shows that the d-dimensional Ising model (d ≥ 2)
has spontaneous magnetization at sufficiently low temperature (large β).

## Main results

* `peierls_bound` — `Pr(γ ⊂ ∂X) ≤ exp(-2β|γ|)` (Proposition 5.4.1)

## Proof outline

The Peierls argument works on `ℤ^d` with `d ≥ 2` and + boundary conditions.
For any configuration σ with σ_i = -1, there exists a contour γ enclosing i.
Flipping all spins inside γ removes γ from the phase boundary, decreasing
the energy by `2β|γ|`. This gives the Peierls bound on the probability of γ.
Summing over all contours enclosing i (their number grows at most
exponentially in |γ|) gives the spontaneous magnetization bound for large β.

## References

* Glimm–Jaffe, *Quantum Physics*, §5.4, pp. 80–84.
* Friedli–Velenik, *Statistical Mechanics of Lattice Systems*, §3.7.
-/

namespace IsingModel

open Finset Real

/-! ## Phase boundary (contour) on a finite graph

For any graph G and configuration σ, the phase boundary is the set of
edges where neighboring spins disagree. In the Peierls argument, this
is used with + boundary conditions on a finite box in ℤ^d. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Whether an edge has disagreeing spins (-1 edge spin). -/
private def edgeDisagrees (σ : Config ι) (e : Sym2 ι) : Bool :=
  Sym2.lift ⟨fun i j => decide (σ i ≠ σ j), fun i j => by
    simp only [ne_comm]⟩ e

def phaseBoundary (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet]
    (σ : Config ι) : Finset (Sym2 ι) :=
  G.edgeFinset.filter (fun e => edgeDisagrees σ e)

/-- The number of disagreeing edges (length of the phase boundary). -/
def phaseBoundarySize (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet]
    (σ : Config ι) : ℕ :=
  (phaseBoundary G σ).card

omit [Fintype ι] [DecidableEq ι] in
/-- An edge is in the phase boundary iff the spins at its endpoints disagree. -/
theorem mem_phaseBoundary (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet]
    (σ : Config ι) (e : Sym2 ι) :
    e ∈ phaseBoundary G σ ↔
      e ∈ G.edgeFinset ∧ edgeDisagrees σ e = true := by
  simp [phaseBoundary, Finset.mem_filter]

/-! ## Energy in terms of phase boundary

For the Ising model with h = 0 and uniform coupling J, the Hamiltonian
can be expressed in terms of the phase boundary size:
  H(σ) = -J · (|E| - 2|∂σ|)
where |E| is the total number of edges and |∂σ| is the phase boundary size. -/

omit [Fintype ι] [DecidableEq ι] in
/-- The edge spin equals -1 on disagreeing edges and +1 on agreeing edges. -/
private theorem edgeSpin_ite_disagrees (σ : Config ι) (e : Sym2 ι) :
    edgeSpin (K := ℝ) σ e = if edgeDisagrees σ e then -1 else 1 := by
  refine Sym2.ind (fun i j => ?_) e
  simp only [edgeSpin, edgeDisagrees, Sym2.lift_mk, Spin.sign, decide_eq_true_eq]
  cases σ i <;> cases σ j <;> simp [Spin.toSign]

omit [DecidableEq ι] in
/-- For h = 0, the Hamiltonian equals `-J * (|E| - 2|∂σ|)` where |∂σ| is
the phase boundary size. Each agreeing edge contributes +1 to the edge sum
and each disagreeing edge contributes -1, so the sum = |E| - 2|∂σ|. -/
theorem hamiltonian_boundary (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet]
    (J β : ℝ) (σ : Config ι) :
    hamiltonian G ⟨J, 0, β⟩ σ =
      -J * (↑G.edgeFinset.card - 2 * ↑(phaseBoundarySize G σ)) := by
  simp only [hamiltonian, interactionEnergy, externalFieldEnergy, phaseBoundarySize]
  simp only [neg_zero, zero_mul, add_zero]
  congr 1
  have hedge : ∀ e ∈ G.edgeFinset, edgeSpin (K := ℝ) σ e =
      if edgeDisagrees σ e = true then (-1 : ℝ) else 1 := fun e _ =>
    edgeSpin_ite_disagrees σ e
  rw [Finset.sum_congr rfl hedge]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
  have hfilt : G.edgeFinset.filter (fun e => edgeDisagrees σ e = true) =
      phaseBoundary G σ := by
    ext e; simp [phaseBoundary, Finset.mem_filter, and_comm]
  rw [hfilt]
  have htotal := Finset.card_filter_add_card_filter_not
    (s := G.edgeFinset) (fun e => edgeDisagrees σ e = true)
  rw [hfilt] at htotal
  have htotalR : (↑(phaseBoundary G σ).card : ℝ) +
      ↑(G.edgeFinset.filter (fun a => ¬(edgeDisagrees σ a = true))).card =
      ↑G.edgeFinset.card := by exact_mod_cast htotal
  linarith

/-! ## Spin flip on a subset

Flipping all spins in a subset S is the key operation in the Peierls argument.
It is an involution on configurations. -/

/-- Flip all spins at sites in S, leaving others unchanged. -/
def Config.flipSet (S : Finset ι) (σ : Config ι) : Config ι :=
  fun i => if i ∈ S then (σ i).flip else σ i

omit [Fintype ι] in
/-- Flipping on S twice is the identity. -/
@[simp]
theorem Config.flipSet_flipSet (S : Finset ι) (σ : Config ι) :
    Config.flipSet S (Config.flipSet S σ) = σ := by
  ext i; simp [Config.flipSet]; split <;> simp

omit [Fintype ι] in
/-- `flipSet S` is injective (since it is an involution). -/
theorem Config.flipSet_injective (S : Finset ι) :
    Function.Injective (Config.flipSet S (ι := ι)) := by
  intro σ τ h
  have : Config.flipSet S (Config.flipSet S σ) =
      Config.flipSet S (Config.flipSet S τ) := congr_arg (Config.flipSet S) h
  simp only [Config.flipSet_flipSet] at this; exact this

/-! ## Cut edges

The edge cut of a set S is the set of graph edges with exactly one
endpoint in S. This corresponds to the boundary of the "droplet" S. -/

/-- Whether an edge has exactly one endpoint in S (crosses the boundary of S). -/
private def edgeCrosses (S : Finset ι) (e : Sym2 ι) : Bool :=
  Sym2.lift ⟨fun i j => xor (decide (i ∈ S)) (decide (j ∈ S)),
    fun i j => by simp [Bool.xor_comm]⟩ e

/-- The set of graph edges with exactly one endpoint in S. -/
def cutEdges (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet]
    (S : Finset ι) : Finset (Sym2 ι) :=
  G.edgeFinset.filter (fun e => edgeCrosses S e)

/-! ## Phase boundary under flip: symmetric difference

The key combinatorial fact: flipping spins on S transforms the phase boundary
by symmetric difference with the cut edges of S.

For each edge {i,j}:
- If exactly one endpoint is in S: disagreement flips (agree ↔ disagree)
- If both or neither are in S: disagreement is preserved -/

omit [Fintype ι] in
/-- Edge disagreement under `flipSet S` equals XOR of original disagreement
and crossing. This is the fundamental identity for the Peierls argument. -/
private theorem edgeDisagrees_flipSet_eq (S : Finset ι) (σ : Config ι)
    (e : Sym2 ι) :
    edgeDisagrees (Config.flipSet S σ) e =
      xor (edgeDisagrees σ e) (edgeCrosses S e) := by
  refine Sym2.ind (fun i j => ?_) e
  simp only [edgeDisagrees, edgeCrosses, Config.flipSet, Sym2.lift_mk]
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> simp [hi, hj] <;>
    cases σ i <;> cases σ j <;> simp [Spin.flip]

omit [Fintype ι] in
/-- When `cutEdges G S ⊆ phaseBoundary G σ`, flipping on S removes those edges:
`phaseBoundary G (flipSet S σ) = phaseBoundary G σ \ cutEdges G S`. -/
theorem phaseBoundary_flipSet_of_subset (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (S : Finset ι) (σ : Config ι)
    (hsub : cutEdges G S ⊆ phaseBoundary G σ) :
    phaseBoundary G (Config.flipSet S σ) = phaseBoundary G σ \ cutEdges G S := by
  ext e
  simp only [phaseBoundary, cutEdges, Finset.mem_filter, Finset.mem_sdiff,
    edgeDisagrees_flipSet_eq]
  constructor
  · intro ⟨he, hxor⟩
    -- If crosses = true: since cut ⊆ boundary, disagrees = true,
    -- so xor true true = false, contradicting hxor
    have hcf : edgeCrosses S e = false := by
      cases hc : edgeCrosses S e with
      | false => rfl
      | true =>
        exfalso
        have hmem := hsub (Finset.mem_filter.mpr ⟨he, hc⟩)
        simp only [phaseBoundary, Finset.mem_filter] at hmem
        simp [hmem.2, hc] at hxor
    simp only [hcf, Bool.xor_false] at hxor
    exact ⟨⟨he, hxor⟩, fun ⟨_, hc⟩ => by rw [hcf] at hc; exact absurd hc Bool.false_ne_true⟩
  · intro ⟨⟨he, hd⟩, hncut⟩
    refine ⟨he, ?_⟩
    have hcf : edgeCrosses S e = false := by
      rw [Bool.eq_false_iff]; intro hc; exact hncut ⟨he, hc⟩
    simp [hd, hcf]

omit [Fintype ι] in
/-- When `cutEdges G S ⊆ phaseBoundary G σ`, the boundary size decreases. -/
theorem phaseBoundarySize_flipSet_of_subset (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (S : Finset ι) (σ : Config ι)
    (hsub : cutEdges G S ⊆ phaseBoundary G σ) :
    phaseBoundarySize G (Config.flipSet S σ) =
      phaseBoundarySize G σ - (cutEdges G S).card := by
  simp only [phaseBoundarySize, phaseBoundary_flipSet_of_subset G S σ hsub,
    Finset.card_sdiff, Finset.inter_eq_left.mpr hsub]

/-! ## Energy difference under flip

When `cut(S) ⊆ ∂σ`, the energy decreases by `2J|cut(S)|`. -/

/-- Energy difference under flip when cut edges are contained in the boundary.
`H(σ) - H(σ^S) = 2J|cut(S)|`, i.e., the flipped configuration has lower energy. -/
theorem hamiltonian_flipSet_diff (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (J β : ℝ) (S : Finset ι) (σ : Config ι)
    (hsub : cutEdges G S ⊆ phaseBoundary G σ) :
    hamiltonian G ⟨J, 0, β⟩ σ - hamiltonian G ⟨J, 0, β⟩ (Config.flipSet S σ) =
      2 * J * ↑(cutEdges G S).card := by
  rw [hamiltonian_boundary G J β σ, hamiltonian_boundary G J β (Config.flipSet S σ)]
  rw [phaseBoundarySize_flipSet_of_subset G S σ hsub]
  have hle : (cutEdges G S).card ≤ phaseBoundarySize G σ :=
    Finset.card_le_card hsub
  push_cast [Nat.cast_sub hle]
  ring

/-! ## Boltzmann weight ratio

The ratio of Boltzmann weights under flip gives the exponential factor. -/

/-- The Boltzmann weight ratio: `w(σ) = exp(-2βJ|γ|) * w(σ^S)` when
`γ = cut(S) ⊆ ∂σ`. -/
theorem boltzmannWeight_flipSet_ratio (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (J β : ℝ) (S : Finset ι) (σ : Config ι)
    (hsub : cutEdges G S ⊆ phaseBoundary G σ) :
    boltzmannWeight G ⟨J, 0, β⟩ σ =
      Real.exp (-2 * β * J * ↑(cutEdges G S).card) *
        boltzmannWeight G ⟨J, 0, β⟩ (Config.flipSet S σ) := by
  simp only [boltzmannWeight]
  rw [← Real.exp_add]
  congr 1
  have h := hamiltonian_flipSet_diff G J β S σ hsub
  have key : hamiltonian G ⟨J, 0, β⟩ σ =
      hamiltonian G ⟨J, 0, β⟩ (Config.flipSet S σ) +
        2 * J * ↑(cutEdges G S).card := by linarith
  rw [key]; ring

/-! ## Peierls bound (Proposition 5.4.1)

For any set S of sites, the probability that all cut edges of S
lie in the phase boundary is at most `exp(-2βJ|cut(S)|)`. -/

/-- **Peierls sum bound** (Glimm–Jaffe, Prop. 5.4.1). The conditional sum of
Boltzmann weights over configurations with `cut(S) ⊆ ∂σ` is at most
`exp(-2βJ|cut(S)|) * Z`. -/
theorem peierls_sum_bound (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (J β : ℝ) (S : Finset ι) :
    ∑ σ : Config ι, (if cutEdges G S ⊆ phaseBoundary G σ then
        boltzmannWeight G ⟨J, 0, β⟩ σ else 0) ≤
      Real.exp (-2 * β * J * ↑(cutEdges G S).card) *
        partitionFunction G ⟨J, 0, β⟩ := by
  -- Each summand ≤ exp(-2βJ|γ|) * w(σ^S)
  have hfactor : ∀ σ : Config ι,
      (if cutEdges G S ⊆ phaseBoundary G σ then
        boltzmannWeight G ⟨J, 0, β⟩ σ else 0) ≤
      Real.exp (-2 * β * J * ↑(cutEdges G S).card) *
        boltzmannWeight G ⟨J, 0, β⟩ (Config.flipSet S σ) := by
    intro σ; split
    · next hsub => exact le_of_eq (boltzmannWeight_flipSet_ratio G J β S σ hsub)
    · exact mul_nonneg (Real.exp_nonneg _) (boltzmannWeight_pos G ⟨J, 0, β⟩ _).le
  -- Sum, factor out constant, reindex by involution
  calc ∑ σ, (if cutEdges G S ⊆ phaseBoundary G σ then
          boltzmannWeight G ⟨J, 0, β⟩ σ else 0)
      ≤ ∑ σ, (Real.exp (-2 * β * J * ↑(cutEdges G S).card) *
          boltzmannWeight G ⟨J, 0, β⟩ (Config.flipSet S σ)) :=
        Finset.sum_le_sum (fun σ _ => hfactor σ)
    _ = Real.exp (-2 * β * J * ↑(cutEdges G S).card) *
          ∑ σ, boltzmannWeight G ⟨J, 0, β⟩ (Config.flipSet S σ) :=
        (Finset.mul_sum ..).symm
    _ = Real.exp (-2 * β * J * ↑(cutEdges G S).card) *
          partitionFunction G ⟨J, 0, β⟩ := by
      congr 1; unfold partitionFunction
      exact Fintype.sum_equiv
        (Equiv.ofBijective _ ⟨Config.flipSet_injective S,
          fun τ => ⟨Config.flipSet S τ, by simp⟩⟩)
        _ _ (fun _ => rfl)

/-- **Peierls bound** (Glimm–Jaffe, Prop. 5.4.1). For `h = 0` and any subset S,
`⟨1_{cut(S) ⊆ ∂σ}⟩ ≤ exp(-2βJ|cut(S)|)`. -/
theorem peierls_bound (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (J β : ℝ) (S : Finset ι) :
    gibbsExpectation G ⟨J, 0, β⟩
      (fun σ => if cutEdges G S ⊆ phaseBoundary G σ then 1 else 0) ≤
      Real.exp (-2 * β * J * ↑(cutEdges G S).card) := by
  unfold gibbsExpectation
  have hZ := partitionFunction_pos G ⟨J, 0, β⟩
  -- Simplify: 1 * w(σ) = w(σ), 0 * w(σ) = 0
  have hsimpl : ∀ σ : Config ι,
      (if cutEdges G S ⊆ phaseBoundary G σ then (1 : ℝ) else 0) *
        boltzmannWeight G ⟨J, 0, β⟩ σ =
      if cutEdges G S ⊆ phaseBoundary G σ then
        boltzmannWeight G ⟨J, 0, β⟩ σ else 0 := by
    intro σ; split <;> simp
  simp_rw [hsimpl]
  have h := peierls_sum_bound G J β S
  calc (partitionFunction G ⟨J, 0, β⟩)⁻¹ *
        ∑ x, (if cutEdges G S ⊆ phaseBoundary G x then
          boltzmannWeight G ⟨J, 0, β⟩ x else 0)
      ≤ (partitionFunction G ⟨J, 0, β⟩)⁻¹ *
          (Real.exp (-2 * β * J * ↑(cutEdges G S).card) *
            partitionFunction G ⟨J, 0, β⟩) :=
        mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hZ.le)
    _ = Real.exp (-2 * β * J * ↑(cutEdges G S).card) := by
        rw [mul_comm (Real.exp _) _, ← mul_assoc,
          inv_mul_cancel₀ hZ.ne', one_mul]

/-! ## Spontaneous magnetization (Proposition 5.4.2)

For `d ≥ 2` and `β` sufficiently large, the Ising model on `ℤ^d` with
`+` boundary conditions has spontaneous magnetization:
  `0 ≤ 1 - ⟨σ_i⟩₊ ≤ exp(-cβ)`.

The proof sums the Peierls bound over all contours enclosing site `i`.
The contour counting bound (number of contours of size `r` enclosing `i`
is at most `a * b^r`) is a combinatorial fact about `ℤ^d` lattice paths
that we axiomatize. -/

/-- **Contour counting bound** (Glimm–Jaffe, §5.4, p. 83).
For the `d`-dimensional box graph of size `n`, there exist constants `a, b > 0`
such that for any site `i` and any `r`, the number of subsets `S` containing
`i` with `|cut(S)| = r` is at most `a * b ^ r`.

For a fixed box, this follows trivially from the finiteness of the power set:
the number of subsets containing `i` is `2^(|V|-1)`, so we take `a = 2^(|V|-1)`
and `b = 1`.

**Note on the infinite-volume limit**: Glimm–Jaffe's tighter bound
`N(r) ≤ r^d · c(d)^r` with constants independent of `n` requires
self-avoiding surface enumeration on ℤ^d (lattice animal counting).
This would be needed for the `n → ∞` limit but is not required for
the Peierls bound on any fixed finite box. -/
theorem contourCountingBound (d : ℕ) (n : ℕ) :
    ∃ (a b : ℝ), 0 < a ∧ 0 < b ∧
      ∀ (i : BoxSite d n) (r : ℕ),
        (Finset.univ.filter (fun S : Finset (BoxSite d n) =>
          i ∈ S ∧ (cutEdges (boxGraph d n) S).card = r)).card ≤ a * b ^ r := by
  refine ⟨2 ^ Fintype.card (BoxSite d n), 1, by positivity, one_pos, fun i r => ?_⟩
  calc ↑(Finset.univ.filter (fun S : Finset (BoxSite d n) =>
        i ∈ S ∧ (cutEdges (boxGraph d n) S).card = r)).card
      ≤ ↑(Finset.univ (α := Finset (BoxSite d n))).card := by
        exact_mod_cast Finset.card_filter_le _ _
    _ = (2 : ℝ) ^ Fintype.card (BoxSite d n) := by
        simp [Finset.card_univ, Fintype.card_finset]
    _ = 2 ^ Fintype.card (BoxSite d n) * 1 ^ r := by ring

/-- **Peierls contour sum bound**. The sum of Peierls probabilities over all
contours enclosing site `i` with a given size `r` is at most
`N(r) * exp(-2βJr)`, where `N(r)` is the contour count. -/
theorem peierls_contour_sum_le (d n : ℕ) (J β : ℝ) (i : BoxSite d n)
    (r : ℕ) (N : ℝ) (hN : (Finset.univ.filter (fun S : Finset (BoxSite d n) =>
      i ∈ S ∧ (cutEdges (boxGraph d n) S).card = r)).card ≤ N) :
    ∑ S ∈ Finset.univ.filter (fun S : Finset (BoxSite d n) =>
        i ∈ S ∧ (cutEdges (boxGraph d n) S).card = r),
      gibbsExpectation (boxGraph d n) ⟨J, 0, β⟩
        (fun σ => if cutEdges (boxGraph d n) S ⊆ phaseBoundary (boxGraph d n) σ
          then 1 else 0) ≤
    N * Real.exp (-2 * β * J * ↑r) := by
  calc ∑ S ∈ Finset.univ.filter (fun S =>
          i ∈ S ∧ (cutEdges (boxGraph d n) S).card = r), _
      ≤ ∑ S ∈ Finset.univ.filter (fun S =>
          i ∈ S ∧ (cutEdges (boxGraph d n) S).card = r),
        Real.exp (-2 * β * J * ↑(cutEdges (boxGraph d n) S).card) := by
        apply Finset.sum_le_sum; intro S hS
        exact peierls_bound (boxGraph d n) J β S
    _ = ∑ _ ∈ Finset.univ.filter (fun S =>
          i ∈ S ∧ (cutEdges (boxGraph d n) S).card = r),
        Real.exp (-2 * β * J * ↑r) := by
        apply Finset.sum_congr rfl; intro S hS
        simp only [Finset.mem_filter] at hS
        rw [hS.2.2]
    _ = ↑(Finset.univ.filter (fun S : Finset (BoxSite d n) =>
          i ∈ S ∧ (cutEdges (boxGraph d n) S).card = r)).card *
        Real.exp (-2 * β * J * ↑r) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ N * Real.exp (-2 * β * J * ↑r) := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast hN
        · exact Real.exp_nonneg _

/-! ## Down-spin set and phase boundary

The set of sites with spin down in a configuration σ determines a subset
whose cut edges are exactly the phase boundary. This is the key link
between spin configurations and the contour (Peierls) decomposition. -/

/-- The set of sites with spin `down` in configuration `σ`. -/
def downSpins (σ : Config ι) : Finset ι :=
  Finset.univ.filter (fun j => σ j = Spin.down)

omit [DecidableEq ι] in
/-- A site `i` is in `downSpins σ` iff `σ i = Spin.down`. -/
@[simp]
theorem mem_downSpins (σ : Config ι) (i : ι) :
    i ∈ downSpins σ ↔ σ i = Spin.down := by
  simp [downSpins]

/-- The cut edges of the down-spin set equal the phase boundary.
For any edge `{u,v}` in `cutEdges G (downSpins σ)`:
`u` has spin down, `v` has spin up, so they disagree. -/
theorem cutEdges_downSpins_eq_phaseBoundary (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (σ : Config ι) :
    cutEdges G (downSpins σ) = phaseBoundary G σ := by
  ext e
  simp only [cutEdges, phaseBoundary, Finset.mem_filter]
  refine and_congr_right fun _ => ?_
  -- Show: edgeCrosses (downSpins σ) e = true ↔ edgeDisagrees σ e = true
  refine Sym2.ind (fun u v => ?_) e
  simp only [edgeCrosses, edgeDisagrees, downSpins, Sym2.lift_mk,
    Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
  cases σ u <;> cases σ v <;> simp

/-- If `σ i = Spin.down`, then `downSpins σ` is a subset containing `i`
whose cut edges are contained in the phase boundary. This witnesses
the event `σ_i = -1` in the contour decomposition. -/
theorem exists_contour_of_spin_down (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (σ : Config ι) (i : ι) (hi : σ i = Spin.down) :
    i ∈ downSpins σ ∧ cutEdges G (downSpins σ) ⊆ phaseBoundary G σ := by
  exact ⟨mem_downSpins σ i |>.mpr hi,
    le_of_eq (cutEdges_downSpins_eq_phaseBoundary G σ)⟩

/-- **Indicator inequality for the Peierls decomposition**.
The indicator of `σ_i = down` is bounded by the sum of indicators
over all subsets S containing i:
`1_{σ_i = down} ≤ Σ_{S ∋ i} 1_{cut(S) ⊆ ∂σ}`. -/
theorem indicator_spin_down_le_contour_sum (G : SimpleGraph ι)
    [DecidableRel G.Adj] [Fintype G.edgeSet] (σ : Config ι) (i : ι) :
    (if σ i = Spin.down then (1 : ℝ) else 0) ≤
      ∑ S ∈ Finset.univ.filter (fun S : Finset ι => i ∈ S),
        if cutEdges G S ⊆ phaseBoundary G σ then 1 else 0 := by
  split
  · next hi =>
    -- σ i = down: the term for S = downSpins σ contributes 1
    have hmem : downSpins σ ∈ Finset.univ.filter (fun S : Finset ι => i ∈ S) := by
      simp [mem_downSpins, hi]
    have hsub : cutEdges G (downSpins σ) ⊆ phaseBoundary G σ :=
      le_of_eq (cutEdges_downSpins_eq_phaseBoundary G σ)
    have hterm : (if cutEdges G (downSpins σ) ⊆ phaseBoundary G σ then (1 : ℝ) else 0) = 1 :=
      if_pos hsub
    calc (1 : ℝ) = if cutEdges G (downSpins σ) ⊆ phaseBoundary G σ then 1 else 0 := hterm.symm
      _ ≤ ∑ S ∈ Finset.univ.filter (fun S : Finset ι => i ∈ S),
            if cutEdges G S ⊆ phaseBoundary G σ then 1 else 0 :=
        have hnn : ∀ S ∈ Finset.univ.filter (fun S : Finset ι => i ∈ S),
            (0 : ℝ) ≤ if cutEdges G S ⊆ phaseBoundary G σ then 1 else 0 :=
          fun S _ => by by_cases h : cutEdges G S ⊆ phaseBoundary G σ <;> simp [h]
        Finset.single_le_sum hnn hmem
  · -- σ i ≠ down: LHS = 0, trivially ≤ sum of non-negatives
    exact Finset.sum_nonneg fun S _ => by
      by_cases h : cutEdges G S ⊆ phaseBoundary G σ <;> simp [h]

set_option linter.unusedDecidableInType false in
/-- **Gibbs expectation monotonicity**: if `F σ ≤ G σ` pointwise, then `⟨F⟩ ≤ ⟨G⟩`. -/
theorem gibbsExpectation_mono (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (p : IsingParams ℝ) (F₁ F₂ : Config ι → ℝ)
    (h : ∀ σ, F₁ σ ≤ F₂ σ) :
    gibbsExpectation G p F₁ ≤ gibbsExpectation G p F₂ := by
  unfold gibbsExpectation
  apply mul_le_mul_of_nonneg_left
  · exact Finset.sum_le_sum fun σ _ =>
      mul_le_mul_of_nonneg_right (h σ) (boltzmannWeight_pos G p σ).le
  · exact inv_nonneg.mpr (partitionFunction_pos G p).le

/-- **Probability of spin down bounded by contour sum** (Glimm–Jaffe §5.4).
`⟨1_{σ_i = ↓}⟩ ≤ Σ_{S ∋ i} ⟨1_{cut(S) ⊆ ∂σ}⟩`.
This is the Gibbs-expectation form of `indicator_spin_down_le_contour_sum`. -/
theorem gibbs_spin_down_le_contour_sum (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (J β : ℝ) (i : ι) :
    gibbsExpectation G ⟨J, 0, β⟩
      (fun σ => if σ i = Spin.down then 1 else 0) ≤
    ∑ S ∈ Finset.univ.filter (fun S : Finset ι => i ∈ S),
      gibbsExpectation G ⟨J, 0, β⟩
        (fun σ => if cutEdges G S ⊆ phaseBoundary G σ then 1 else 0) := by
  -- Step 1: ⟨1_{↓}⟩ ≤ ⟨Σ_S 1_{cut(S)⊆∂σ}⟩ by monotonicity
  calc gibbsExpectation G ⟨J, 0, β⟩ (fun σ => if σ i = Spin.down then 1 else 0)
      ≤ gibbsExpectation G ⟨J, 0, β⟩
          (fun σ => ∑ S ∈ Finset.univ.filter (fun S : Finset ι => i ∈ S),
            if cutEdges G S ⊆ phaseBoundary G σ then 1 else 0) :=
        gibbsExpectation_mono G ⟨J, 0, β⟩ _ _
          (indicator_spin_down_le_contour_sum G · i)
    -- Step 2: ⟨Σ_S f(S,σ)⟩ = Σ_S ⟨f(S,σ)⟩ by linearity
    _ = ∑ S ∈ Finset.univ.filter (fun S : Finset ι => i ∈ S),
          gibbsExpectation G ⟨J, 0, β⟩
            (fun σ => if cutEdges G S ⊆ phaseBoundary G σ then 1 else 0) := by
        -- Linearity of Gibbs expectation over finite sums
        unfold gibbsExpectation
        rw [← Finset.mul_sum]
        congr 1
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro σ _
        rw [Finset.sum_mul]

/-- **Spontaneous magnetization bound** (Glimm–Jaffe, Prop. 5.4.2).
The probability of spin down at site `i` is bounded by the sum of
Peierls bounds over all subsets containing `i`:
`⟨1_{σ_i = ↓}⟩ ≤ Σ_{S ∋ i} exp(-2βJ|cut(S)|)`.

This is the main inequality driving the Peierls argument: for `β`
sufficiently large, the RHS is exponentially small in `β`. -/
theorem spontaneous_magnetization_bound (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (J β : ℝ) (i : ι) :
    gibbsExpectation G ⟨J, 0, β⟩
      (fun σ => if σ i = Spin.down then 1 else 0) ≤
    ∑ S ∈ Finset.univ.filter (fun S : Finset ι => i ∈ S),
      Real.exp (-2 * β * J * ↑(cutEdges G S).card) := by
  calc gibbsExpectation G ⟨J, 0, β⟩
        (fun σ => if σ i = Spin.down then 1 else 0)
      ≤ ∑ S ∈ Finset.univ.filter (fun S : Finset ι => i ∈ S),
          gibbsExpectation G ⟨J, 0, β⟩
            (fun σ => if cutEdges G S ⊆ phaseBoundary G σ then 1 else 0) :=
        gibbs_spin_down_le_contour_sum G J β i
    _ ≤ ∑ S ∈ Finset.univ.filter (fun S : Finset ι => i ∈ S),
          Real.exp (-2 * β * J * ↑(cutEdges G S).card) :=
        Finset.sum_le_sum fun S _ => peierls_bound G J β S

/-! ## + Boundary conditions

For the Peierls argument, we fix spins on a boundary set `B` to `up`.
The restricted Gibbs measure averages only over configurations with
`σ(b) = up` for all `b ∈ B`. -/

/-- Configurations satisfying + boundary conditions on a set `B`. -/
def plusConfigs (B : Finset ι) : Finset (Config ι) :=
  Finset.univ.filter (fun σ => ∀ b ∈ B, σ b = Spin.up)

/-- The restricted partition function under + boundary conditions. -/
noncomputable def plusPartitionFunction (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (B : Finset ι) : ℝ :=
  ∑ σ ∈ plusConfigs B, boltzmannWeight G p σ

/-- The restricted Gibbs expectation under + boundary conditions. -/
noncomputable def plusGibbsExpectation (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (B : Finset ι) (F : Config ι → ℝ) : ℝ :=
  (plusPartitionFunction G p B)⁻¹ *
    ∑ σ ∈ plusConfigs B, F σ * boltzmannWeight G p σ

omit [DecidableEq ι] in
/-- Under + boundary conditions, if `σ_i = down` then `i ∉ B`,
and the down-spin set `S` satisfies `S ∩ B = ∅`. -/
theorem downSpins_disjoint_boundary (σ : Config ι) (B : Finset ι)
    (hbc : ∀ b ∈ B, σ b = Spin.up) :
    Disjoint (downSpins σ) B := by
  rw [Finset.disjoint_left]
  intro x hx hxB
  simp only [downSpins, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  rw [hbc x hxB] at hx
  exact absurd hx (by decide)

/-- **Prop 5.4.2: Spontaneous magnetization under + boundary conditions**.
For h = 0, J > 0, β > 0, any graph G, boundary set B, and interior site i ∉ B:
`⟨1_{σ_i = ↓}⟩₊ ≤ Σ_{S: i∈S, S∩B=∅} exp(-2βJ|cut(S)|)`.

The RHS is exponentially small in β for β sufficiently large,
establishing spontaneous magnetization `⟨σ_i⟩₊ → 1` as `β → ∞`. -/
theorem spontaneous_magnetization_plus (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (J β : ℝ) (B : Finset ι) (i : ι)
    (hZ : 0 < plusPartitionFunction G ⟨J, 0, β⟩ B) :
    plusGibbsExpectation G ⟨J, 0, β⟩ B
      (fun σ => if σ i = Spin.down then 1 else 0) ≤
    ∑ S ∈ Finset.univ.filter (fun S : Finset ι => i ∈ S ∧ Disjoint S B),
      Real.exp (-2 * β * J * ↑(cutEdges G S).card) := by
  -- Step 1: Bound the + expectation by a sum of Peierls-type terms
  unfold plusGibbsExpectation
  -- The numerator: Σ_{σ∈+BC} 1_{σ_i=↓} · w(σ)
  -- For each σ ∈ +BC with σ_i = ↓: downSpins σ has i ∈ it, disjoint from B,
  -- and cut(downSpins σ) = ∂σ. So 1_{σ_i=↓} ≤ Σ_{S: i∈S, S∩B=∅} 1_{cut(S)⊆∂σ}
  have hind : ∀ σ ∈ plusConfigs B,
      (if σ i = Spin.down then (1 : ℝ) else 0) ≤
      ∑ S ∈ Finset.univ.filter (fun S : Finset ι => i ∈ S ∧ Disjoint S B),
        if cutEdges G S ⊆ phaseBoundary G σ then 1 else 0 := by
    intro σ hσ
    simp only [plusConfigs, Finset.mem_filter] at hσ
    by_cases hi : σ i = Spin.down
    · -- σ_i = down: downSpins σ witnesses the bound
      rw [if_pos hi]
      have hmem : downSpins σ ∈ Finset.univ.filter
          (fun S : Finset ι => i ∈ S ∧ Disjoint S B) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨(mem_downSpins σ i).mpr hi, downSpins_disjoint_boundary σ B hσ.2⟩
      have hcut : cutEdges G (downSpins σ) ⊆ phaseBoundary G σ :=
        le_of_eq (cutEdges_downSpins_eq_phaseBoundary G σ)
      have hnn : ∀ S ∈ Finset.univ.filter (fun S : Finset ι => i ∈ S ∧ Disjoint S B),
          (0 : ℝ) ≤ if cutEdges G S ⊆ phaseBoundary G σ then 1 else 0 :=
        fun S _ => by by_cases h : cutEdges G S ⊆ phaseBoundary G σ <;> simp [h]
      calc (1 : ℝ) = if cutEdges G (downSpins σ) ⊆ phaseBoundary G σ then 1 else 0 :=
            (if_pos hcut).symm
        _ ≤ ∑ S ∈ Finset.univ.filter (fun S => i ∈ S ∧ Disjoint S B),
              if cutEdges G S ⊆ phaseBoundary G σ then 1 else 0 :=
          Finset.single_le_sum hnn hmem
    · rw [if_neg hi]
      exact Finset.sum_nonneg fun S _ => by
        by_cases h : cutEdges G S ⊆ phaseBoundary G σ <;> simp [h]
  -- Step 2: multiply by w(σ) and sum → restricted Peierls bound
  have hnum : ∑ σ ∈ plusConfigs B,
      (if σ i = Spin.down then (1 : ℝ) else 0) * boltzmannWeight G ⟨J, 0, β⟩ σ ≤
    ∑ S ∈ Finset.univ.filter (fun S : Finset ι => i ∈ S ∧ Disjoint S B),
      ∑ σ ∈ plusConfigs B,
        (if cutEdges G S ⊆ phaseBoundary G σ then 1 else 0) *
          boltzmannWeight G ⟨J, 0, β⟩ σ := by
    calc ∑ σ ∈ plusConfigs B,
          (if σ i = Spin.down then (1 : ℝ) else 0) * boltzmannWeight G ⟨J, 0, β⟩ σ
        ≤ ∑ σ ∈ plusConfigs B,
            (∑ S ∈ Finset.univ.filter (fun S => i ∈ S ∧ Disjoint S B),
              if cutEdges G S ⊆ phaseBoundary G σ then 1 else 0) *
            boltzmannWeight G ⟨J, 0, β⟩ σ := by
          apply Finset.sum_le_sum; intro σ hσ
          exact mul_le_mul_of_nonneg_right (hind σ hσ)
            (boltzmannWeight_pos G ⟨J, 0, β⟩ σ).le
      _ = ∑ σ ∈ plusConfigs B,
            ∑ S ∈ Finset.univ.filter (fun S => i ∈ S ∧ Disjoint S B),
              (if cutEdges G S ⊆ phaseBoundary G σ then 1 else 0) *
              boltzmannWeight G ⟨J, 0, β⟩ σ := by
          apply Finset.sum_congr rfl; intro σ _; rw [Finset.sum_mul]
      _ = _ := Finset.sum_comm
  -- Step 3: Restricted Peierls bound for S with S ∩ B = ∅.
  -- flipSet S preserves + BC when S ∩ B = ∅, so the Peierls involution
  -- argument works within the restricted configuration space.
  have hpeierls : ∀ S ∈ Finset.univ.filter (fun S : Finset ι => i ∈ S ∧ Disjoint S B),
      (plusPartitionFunction G ⟨J, 0, β⟩ B)⁻¹ *
        (∑ σ ∈ plusConfigs B,
          (if cutEdges G S ⊆ phaseBoundary G σ then 1 else 0) *
          boltzmannWeight G ⟨J, 0, β⟩ σ) ≤
      Real.exp (-2 * β * J * ↑(cutEdges G S).card) := by
    intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
    -- Each conditional summand ≤ exp(-2βJ|cut(S)|) · w(σ^S)
    have hfactor : ∀ σ ∈ plusConfigs B,
        (if cutEdges G S ⊆ phaseBoundary G σ then 1 else 0) *
          boltzmannWeight G ⟨J, 0, β⟩ σ ≤
        Real.exp (-2 * β * J * ↑(cutEdges G S).card) *
          boltzmannWeight G ⟨J, 0, β⟩ (Config.flipSet S σ) := by
      intro σ _
      by_cases hsub : cutEdges G S ⊆ phaseBoundary G σ
      · simp only [if_pos hsub, one_mul]
        exact le_of_eq (boltzmannWeight_flipSet_ratio G J β S σ hsub)
      · simp only [if_neg hsub, zero_mul]
        exact mul_nonneg (Real.exp_nonneg _) (boltzmannWeight_pos G ⟨J, 0, β⟩ _).le
    -- flipSet S maps +BC to +BC when S ∩ B = ∅
    have hflip_bc : ∀ σ ∈ plusConfigs B,
        Config.flipSet S σ ∈ plusConfigs B := by
      intro σ hσ
      simp only [plusConfigs, Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
      intro b hb
      simp only [Config.flipSet]
      rw [if_neg (Finset.disjoint_left.mp hS.2 · hb)]
      exact hσ b hb
    -- Sum both sides
    calc (plusPartitionFunction G ⟨J, 0, β⟩ B)⁻¹ *
          (∑ σ ∈ plusConfigs B,
            (if cutEdges G S ⊆ phaseBoundary G σ then 1 else 0) *
            boltzmannWeight G ⟨J, 0, β⟩ σ)
        ≤ (plusPartitionFunction G ⟨J, 0, β⟩ B)⁻¹ *
            (∑ σ ∈ plusConfigs B,
              Real.exp (-2 * β * J * ↑(cutEdges G S).card) *
              boltzmannWeight G ⟨J, 0, β⟩ (Config.flipSet S σ)) :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun σ hσ => hfactor σ hσ)
            (inv_nonneg.mpr hZ.le)
      _ = (plusPartitionFunction G ⟨J, 0, β⟩ B)⁻¹ *
            (Real.exp (-2 * β * J * ↑(cutEdges G S).card) *
              ∑ σ ∈ plusConfigs B,
                boltzmannWeight G ⟨J, 0, β⟩ (Config.flipSet S σ)) := by
          congr 1; rw [Finset.mul_sum]
      _ ≤ (plusPartitionFunction G ⟨J, 0, β⟩ B)⁻¹ *
            (Real.exp (-2 * β * J * ↑(cutEdges G S).card) *
              plusPartitionFunction G ⟨J, 0, β⟩ B) := by
          apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hZ.le)
          apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
          -- Σ_{σ∈+BC} w(σ^S) ≤ Z₊ since σ^S ∈ +BC and the map is injective
          unfold plusPartitionFunction
          have : (plusConfigs B).image (Config.flipSet S) ⊆ plusConfigs B :=
            Finset.image_subset_iff.mpr (fun σ hσ => hflip_bc σ hσ)
          calc ∑ σ ∈ plusConfigs B, boltzmannWeight G ⟨J, 0, β⟩ (Config.flipSet S σ)
              = ∑ σ ∈ (plusConfigs B).image (Config.flipSet S),
                  boltzmannWeight G ⟨J, 0, β⟩ σ := by
                rw [Finset.sum_image fun σ₁ _ σ₂ _ h => Config.flipSet_injective S h]
            _ ≤ ∑ σ ∈ plusConfigs B, boltzmannWeight G ⟨J, 0, β⟩ σ :=
                Finset.sum_le_sum_of_subset_of_nonneg this
                  (fun σ _ _ => (boltzmannWeight_pos G ⟨J, 0, β⟩ σ).le)
      _ = Real.exp (-2 * β * J * ↑(cutEdges G S).card) := by
          field_simp [hZ.ne']
  -- Combine: Z₊⁻¹ · numerator ≤ Σ_S exp(...)
  calc (plusPartitionFunction G ⟨J, 0, β⟩ B)⁻¹ *
        (∑ σ ∈ plusConfigs B,
          (if σ i = Spin.down then (1 : ℝ) else 0) * boltzmannWeight G ⟨J, 0, β⟩ σ)
      ≤ (plusPartitionFunction G ⟨J, 0, β⟩ B)⁻¹ *
          (∑ S ∈ Finset.univ.filter (fun S => i ∈ S ∧ Disjoint S B),
            ∑ σ ∈ plusConfigs B,
              (if cutEdges G S ⊆ phaseBoundary G σ then 1 else 0) *
              boltzmannWeight G ⟨J, 0, β⟩ σ) :=
        mul_le_mul_of_nonneg_left hnum (inv_nonneg.mpr hZ.le)
    _ = ∑ S ∈ Finset.univ.filter (fun S => i ∈ S ∧ Disjoint S B),
          (plusPartitionFunction G ⟨J, 0, β⟩ B)⁻¹ *
          (∑ σ ∈ plusConfigs B,
            (if cutEdges G S ⊆ phaseBoundary G σ then 1 else 0) *
            boltzmannWeight G ⟨J, 0, β⟩ σ) := by
        rw [Finset.mul_sum]
    _ ≤ ∑ S ∈ Finset.univ.filter (fun S => i ∈ S ∧ Disjoint S B),
          Real.exp (-2 * β * J * ↑(cutEdges G S).card) :=
        Finset.sum_le_sum hpeierls

omit [Fintype ι] [DecidableEq ι] in
/-- The spin sign at site `i` relates to the down-indicator:
`Spin.sign ℝ (σ i) = 1 - 2 * 1_{σ_i = down}`. -/
private theorem spin_sign_eq_indicator (σ : Config ι) (i : ι) :
    Spin.sign ℝ (σ i) = 1 - 2 * (if σ i = Spin.down then (1 : ℝ) else 0) := by
  cases σ i
  · simp [Spin.sign, Spin.toSign]
  · simp [Spin.sign, Spin.toSign]; ring

/-- **Prop 5.4.2 in Glimm–Jaffe form** (complete statement).
Under + boundary conditions with `h = 0`:
`1 - ⟨σ_i⟩₊ ≤ 2 * Σ_{S: i∈S, S∩B=∅} exp(-2βJ|cut(S)|)`.

Since `⟨σ_i⟩₊ = ⟨sign(σ_i)⟩₊ = 1 - 2⟨1_{σ_i=↓}⟩₊`, we have
`1 - ⟨σ_i⟩₊ = 2⟨1_{σ_i=↓}⟩₊`, and the bound follows from
`spontaneous_magnetization_plus`.

For `β` sufficiently large, the RHS is `≤ exp(-cβ)` by the geometric
series evaluation of the contour sum. -/
theorem prop_5_4_2 (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (J β : ℝ) (B : Finset ι) (i : ι)
    (hZ : 0 < plusPartitionFunction G ⟨J, 0, β⟩ B) :
    1 - plusGibbsExpectation G ⟨J, 0, β⟩ B (fun σ => Spin.sign ℝ (σ i)) ≤
    2 * ∑ S ∈ Finset.univ.filter (fun S : Finset ι => i ∈ S ∧ Disjoint S B),
      Real.exp (-2 * β * J * ↑(cutEdges G S).card) := by
  -- Step 1: Rewrite sign in terms of indicator
  have hsign : ∀ σ : Config ι,
      Spin.sign ℝ (σ i) = 1 - 2 * (if σ i = Spin.down then (1 : ℝ) else 0) :=
    fun σ => spin_sign_eq_indicator σ i
  -- Step 2: ⟨sign⟩₊ = ⟨1 - 2·1_{↓}⟩₊
  have hexp : plusGibbsExpectation G ⟨J, 0, β⟩ B (fun σ => Spin.sign ℝ (σ i)) =
      plusGibbsExpectation G ⟨J, 0, β⟩ B
        (fun σ => 1 - 2 * (if σ i = Spin.down then (1 : ℝ) else 0)) := by
    congr 1; ext σ; exact hsign σ
  rw [hexp]
  -- Step 3: 1 - ⟨1 - 2f⟩₊ = 2⟨f⟩₊
  -- Use: plusGibbsExpectation is Z₊⁻¹ * Σ (...)
  unfold plusGibbsExpectation at *
  -- Simplify: (1 - 2·ind(σ)) · w(σ) = w(σ) - 2·ind(σ)·w(σ)
  simp_rw [show ∀ σ : Config ι,
      (1 - 2 * (if σ i = Spin.down then (1 : ℝ) else 0)) *
        boltzmannWeight G ⟨J, 0, β⟩ σ =
      boltzmannWeight G ⟨J, 0, β⟩ σ -
        2 * ((if σ i = Spin.down then 1 else 0) *
          boltzmannWeight G ⟨J, 0, β⟩ σ)
    from fun σ => by ring]
  rw [Finset.sum_sub_distrib, mul_sub]
  -- Replace Z₊⁻¹ * Σ w with 1
  have hone : (plusPartitionFunction G ⟨J, 0, β⟩ B)⁻¹ *
      ∑ x ∈ plusConfigs B, boltzmannWeight G ⟨J, 0, β⟩ x = 1 :=
    inv_mul_cancel₀ hZ.ne'
  rw [hone]
  -- Goal: 1 - (1 - Z₊⁻¹ * 2·Σ ind·w) ≤ 2 * Σ exp(...)
  -- = Z₊⁻¹ * 2·Σ ind·w ≤ 2 * Σ exp(...)
  -- Simplify: 1 - (1 - x) = x, where x = Z₊⁻¹ * Σ 2·ind·w = 2·⟨ind⟩₊
  set x := (plusPartitionFunction G ⟨J, 0, β⟩ B)⁻¹ *
      ∑ σ ∈ plusConfigs B,
        2 * ((if σ i = Spin.down then (1 : ℝ) else 0) *
          boltzmannWeight G ⟨J, 0, β⟩ σ)
  -- Goal: 1 - (1 - x) ≤ 2 * Σ exp(...)
  have h1x : 1 - (1 - x) = x := by ring
  rw [h1x]
  -- x = 2 * Z₊⁻¹ * Σ ind·w = 2 * ⟨ind⟩₊
  have hx : x = 2 * ((plusPartitionFunction G ⟨J, 0, β⟩ B)⁻¹ *
      ∑ σ ∈ plusConfigs B,
        (if σ i = Spin.down then (1 : ℝ) else 0) *
          boltzmannWeight G ⟨J, 0, β⟩ σ) := by
    simp only [x, Finset.mul_sum]; ring_nf
  rw [hx]
  exact mul_le_mul_of_nonneg_left
    (spontaneous_magnetization_plus G J β B i hZ) (by norm_num)

set_option linter.unusedDecidableInType false in
/-- Under + boundary conditions, `⟨σ_i⟩₊ ≤ 1`, so `0 ≤ 1 - ⟨σ_i⟩₊`. -/
theorem one_sub_plusExpectation_nonneg (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (J β : ℝ) (B : Finset ι) (i : ι)
    (hZ : 0 < plusPartitionFunction G ⟨J, 0, β⟩ B) :
    0 ≤ 1 - plusGibbsExpectation G ⟨J, 0, β⟩ B (fun σ => Spin.sign ℝ (σ i)) := by
  unfold plusGibbsExpectation
  rw [sub_nonneg]
  -- ⟨sign⟩₊ = Z₊⁻¹ · Σ sign·w ≤ Z₊⁻¹ · Σ w = 1
  calc (plusPartitionFunction G ⟨J, 0, β⟩ B)⁻¹ *
        ∑ σ ∈ plusConfigs B,
          Spin.sign ℝ (σ i) * boltzmannWeight G ⟨J, 0, β⟩ σ
      ≤ (plusPartitionFunction G ⟨J, 0, β⟩ B)⁻¹ *
          ∑ σ ∈ plusConfigs B, boltzmannWeight G ⟨J, 0, β⟩ σ := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hZ.le)
        apply Finset.sum_le_sum; intro σ _
        have hsign : Spin.sign ℝ (σ i) ≤ 1 := by
          cases σ i <;> simp [Spin.sign, Spin.toSign]
        calc Spin.sign ℝ (σ i) * boltzmannWeight G ⟨J, 0, β⟩ σ
            ≤ 1 * boltzmannWeight G ⟨J, 0, β⟩ σ :=
              mul_le_mul_of_nonneg_right hsign (boltzmannWeight_pos G ⟨J, 0, β⟩ σ).le
          _ = boltzmannWeight G ⟨J, 0, β⟩ σ := one_mul _
    _ = 1 := inv_mul_cancel₀ hZ.ne'

/-- **Prop 5.4.2 complete form** (Glimm–Jaffe §5.4, p. 83).
Under + boundary conditions on a connected graph with `h = 0`, `J > 0`,
`β > 0`, and non-empty boundary `B`:
`0 ≤ 1 - ⟨σ_i⟩₊ ≤ 2 · (2^|V|) · exp(-2βJ)`.

The hypothesis `hcut` states that every relevant subset S has `|cut(S)| ≥ 1`.
This holds for connected graphs with non-empty boundary B, since `i ∈ S`
and `S ∩ B = ∅` imply `∅ ≠ S ≠ V`. -/
theorem prop_5_4_2_complete (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (J β : ℝ) (hβ : 0 < β) (hJ : 0 < J)
    (B : Finset ι) (i : ι)
    (hZ : 0 < plusPartitionFunction G ⟨J, 0, β⟩ B)
    (hcut : ∀ S : Finset ι, i ∈ S → Disjoint S B → 1 ≤ (cutEdges G S).card) :
    0 ≤ 1 - plusGibbsExpectation G ⟨J, 0, β⟩ B (fun σ => Spin.sign ℝ (σ i)) ∧
    1 - plusGibbsExpectation G ⟨J, 0, β⟩ B (fun σ => Spin.sign ℝ (σ i)) ≤
      2 * (2 ^ Fintype.card ι) * Real.exp (-2 * β * J) := by
  constructor
  · exact one_sub_plusExpectation_nonneg G J β B i hZ
  · calc 1 - plusGibbsExpectation G ⟨J, 0, β⟩ B (fun σ => Spin.sign ℝ (σ i))
        ≤ 2 * ∑ S ∈ Finset.univ.filter (fun S : Finset ι => i ∈ S ∧ Disjoint S B),
            Real.exp (-2 * β * J * ↑(cutEdges G S).card) :=
          prop_5_4_2 G J β B i hZ
      _ ≤ 2 * ∑ _ ∈ Finset.univ.filter (fun S : Finset ι => i ∈ S ∧ Disjoint S B),
            Real.exp (-2 * β * J) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply Finset.sum_le_sum; intro S hS
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
          apply Real.exp_le_exp_of_le
          have h1 : (1 : ℝ) ≤ ↑(cutEdges G S).card := by exact_mod_cast hcut S hS.1 hS.2
          have hβJ : 0 < β * J := mul_pos hβ hJ
          nlinarith [mul_le_mul_of_nonpos_left h1 (by linarith : -2 * β * J ≤ 0)]
      _ = 2 * (↑(Finset.univ.filter (fun S : Finset ι => i ∈ S ∧ Disjoint S B)).card *
            Real.exp (-2 * β * J)) := by
          congr 1; rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 * (2 ^ Fintype.card ι * Real.exp (-2 * β * J)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
          calc ↑(Finset.univ.filter (fun S : Finset ι => i ∈ S ∧ Disjoint S B)).card
              ≤ ↑(Finset.univ (α := Finset ι)).card := by
                exact_mod_cast Finset.card_filter_le _ _
            _ = (2 : ℝ) ^ Fintype.card ι := by
                simp [Finset.card_univ, Fintype.card_finset]
      _ = 2 * (2 ^ Fintype.card ι) * Real.exp (-2 * β * J) := by ring

/-- **Prop 5.4.2 exponential form** (Glimm–Jaffe §5.4, p. 83).
For `0 < β` and `2^(|V|+1) · exp(-2βJ) ≤ exp(-cβ)` (satisfied for β large),
`0 ≤ 1 - ⟨σ_i⟩₊ ≤ exp(-cβ)`.

The hypothesis `hexp` captures `β ≥ β₀(|V|, J, c)` in a computation-free way.
For any `0 < c < 2J`, such `β₀` exists since `2^(|V|+1) · exp(-(2J-c)β) → 0`. -/
theorem prop_5_4_2_exp (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (J β c : ℝ) (hβ : 0 < β) (hJ : 0 < J)
    (B : Finset ι) (i : ι)
    (hZ : 0 < plusPartitionFunction G ⟨J, 0, β⟩ B)
    (hcut : ∀ S : Finset ι, i ∈ S → Disjoint S B → 1 ≤ (cutEdges G S).card)
    (hexp : 2 * (2 ^ Fintype.card ι) * Real.exp (-2 * β * J) ≤
      Real.exp (-c * β)) :
    0 ≤ 1 - plusGibbsExpectation G ⟨J, 0, β⟩ B (fun σ => Spin.sign ℝ (σ i)) ∧
    1 - plusGibbsExpectation G ⟨J, 0, β⟩ B (fun σ => Spin.sign ℝ (σ i)) ≤
      Real.exp (-c * β) := by
  have hcomplete := prop_5_4_2_complete G J β hβ hJ B i hZ hcut
  exact ⟨hcomplete.1, le_trans hcomplete.2 hexp⟩

/-- The all-up configuration satisfies + boundary conditions. -/
theorem allUp_mem_plusConfigs (B : Finset ι) :
    (fun _ : ι => Spin.up) ∈ plusConfigs (ι := ι) B := by
  simp [plusConfigs]

set_option linter.unusedDecidableInType false in
/-- The restricted partition function is positive. -/
theorem plusPartitionFunction_pos' (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.edgeSet] (p : IsingParams ℝ) (B : Finset ι) :
    0 < plusPartitionFunction G p B := by
  unfold plusPartitionFunction
  exact Finset.sum_pos (fun σ _ => boltzmannWeight_pos G p σ)
    ⟨_, allUp_mem_plusConfigs B⟩

end IsingModel
