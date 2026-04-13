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

end IsingModel
