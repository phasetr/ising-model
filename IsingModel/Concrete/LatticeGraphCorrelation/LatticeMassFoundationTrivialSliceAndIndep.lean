import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassFoundation

/-!
# `latticeMass` trivial-slice and exhaustion-independence wrappers at ℤ^d

Narrow child module for four `latticeMass` theorems extracted from
`LatticeMassFoundation.lean`:

* `latticeMass_top_of_beta_zero` and `latticeMass_top_of_J_zero`
  (trivial slices have lattice mass `⊤`),
* `latticeMass_indep_exhaustion` and `latticeMass_indep_cubicExhaustion`
  (the lattice mass is independent of the chosen exhaustion in the
  ferromagnetic regime).
-/

namespace IsingModel
namespace Ambient

/-- **Lattice mass at `β = 0` trivial slice is `⊤`**.
At infinite temperature, `HasExponentialDecay` holds at every
rate `α` (by `HasExponentialDecay_beta_zero`). For any candidate
upper bound `b ≠ ⊤` of the supremand, pick the witness
`α := b.toNNReal + 1`; then `(α : ENNReal) = b + 1 > b`, but the
upper-bound hypothesis would force `(α : ENNReal) ≤ b`. -/
theorem latticeMass_top_of_beta_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J h : ℝ) :
    latticeMass d Λ (⟨J, h, 0⟩ : IsingParams ℝ) = ⊤ := by
  refine eq_top_iff.mpr ?_
  refine le_sSup_iff.mpr ?_
  intro b hb
  by_contra hb_ne
  rw [not_le] at hb_ne
  -- pick α : NNReal with (α : ENNReal) > b: take b.toNNReal + 1.
  set α : NNReal := b.toNNReal + 1
  have hαmem : (α : ENNReal) ∈ (fun α : NNReal => (α : ENNReal)) ''
      {α : NNReal | HasExponentialDecay d Λ
        (⟨J, h, 0⟩ : IsingParams ℝ) (α : ℝ)} :=
    ⟨α, HasExponentialDecay_beta_zero d Λ J h (α : ℝ), rfl⟩
  have hα_le_b : (α : ENNReal) ≤ b := hb hαmem
  have hb_ne_top : b ≠ ⊤ := ne_of_lt hb_ne
  have hb_toNN : ((b.toNNReal : ENNReal) : ENNReal) = b :=
    ENNReal.coe_toNNReal hb_ne_top
  have hα_eq : (α : ENNReal) = b + 1 := by
    simp only [α, ENNReal.coe_add, ENNReal.coe_one, hb_toNN]
  rw [hα_eq] at hα_le_b
  have hlt : b < b + 1 := ENNReal.lt_add_right hb_ne_top one_ne_zero
  exact absurd hα_le_b (not_le.mpr hlt)

/-- **Lattice mass at `J = 0` ferromagnetic trivial slice is `⊤`**.
Same argument as `latticeMass_top_of_beta_zero` using
`HasExponentialDecay_J_zero`. -/
theorem latticeMass_top_of_J_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ)) :
    latticeMass d Λ (⟨0, h, β⟩ : IsingParams ℝ) = ⊤ := by
  refine eq_top_iff.mpr ?_
  refine le_sSup_iff.mpr ?_
  intro b hb
  by_contra hb_ne
  rw [not_le] at hb_ne
  set α : NNReal := b.toNNReal + 1
  have hαmem : (α : ENNReal) ∈ (fun α : NNReal => (α : ENNReal)) ''
      {α : NNReal | HasExponentialDecay d Λ
        (⟨0, h, β⟩ : IsingParams ℝ) (α : ℝ)} :=
    ⟨α, HasExponentialDecay_J_zero d Λ h β (α : ℝ) hf, rfl⟩
  have hα_le_b : (α : ENNReal) ≤ b := hb hαmem
  have hb_ne_top : b ≠ ⊤ := ne_of_lt hb_ne
  have hb_toNN : ((b.toNNReal : ENNReal) : ENNReal) = b :=
    ENNReal.coe_toNNReal hb_ne_top
  have hα_eq : (α : ENNReal) = b + 1 := by
    simp only [α, ENNReal.coe_add, ENNReal.coe_one, hb_toNN]
  rw [hα_eq] at hα_le_b
  have hlt : b < b + 1 := ENNReal.lt_add_right hb_ne_top one_ne_zero
  exact absurd hα_le_b (not_le.mpr hlt)

/-- **Lattice mass is independent of exhaustion** for ferromagnetic parameters:
`latticeMass d Λ p = latticeMass d Λ' p` for any two exhaustions `Λ, Λ'` when `p` is
ferromagnetic.

Proof: `truncated2Infinite_indep_exhaustion` gives `truncated2Infinite G Λ p i j =
truncated2Infinite G Λ' p i j` for all `i, j`. Hence `HasExponentialDecay d Λ p α ↔
HasExponentialDecay d Λ' p α`, so the defining supremand sets are equal and the sSup
values agree.

**Consequence**: for ferromagnetic `p` (i.e. `J ≥ 0`, `β > 0`), the value of
`latticeMass` — and hence the set of valid exponential decay rates — does not depend
on the choice of exhaustion. This relies on `correlationInfinite_indep_exhaustion`
(which itself requires `Ferromagnetic p`). -/
theorem latticeMass_indep_exhaustion
    {d : ℕ} (Λ Λ' : Ambient.Exhaustion (Fin d → ℤ))
    {p : IsingParams ℝ} (hf : Ferromagnetic p) :
    latticeMass d Λ p = latticeMass d Λ' p := by
  unfold latticeMass
  have h_sets : {α : NNReal | HasExponentialDecay d Λ p (α : ℝ)} =
                {α : NNReal | HasExponentialDecay d Λ' p (α : ℝ)} := by
    ext α
    constructor
    · rintro ⟨C, hC, hbound⟩
      exact ⟨C, hC, fun i j hij => by
        rw [← truncated2Infinite_indep_exhaustion (IsingModel.latticeGraph d) Λ Λ' p hf i j]
        exact hbound i j hij⟩
    · rintro ⟨C, hC, hbound⟩
      exact ⟨C, hC, fun i j hij => by
        rw [truncated2Infinite_indep_exhaustion (IsingModel.latticeGraph d) Λ Λ' p hf i j]
        exact hbound i j hij⟩
  rw [h_sets]

/-- **Lattice mass via `cubicExhaustion`** equals lattice mass via any exhaustion
for ferromagnetic parameters. Corollary of `latticeMass_indep_exhaustion`. -/
theorem latticeMass_indep_cubicExhaustion
    {d : ℕ} (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {p : IsingParams ℝ} (hf : Ferromagnetic p) :
    latticeMass d Λ p = latticeMass d (Ambient.cubicExhaustion d) p :=
  latticeMass_indep_exhaustion Λ (Ambient.cubicExhaustion d) hf

end Ambient
end IsingModel
