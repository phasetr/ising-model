import IsingModel.BallBoundarySimonLieb
import IsingModel.Concrete.LatticeGraphCorrelation.LatticeMassFoundation
import IsingModel.Peierls
import IsingModel.Concrete.CubicExhaustion

/-!
# Theorem eta-le-1 split — Phase 1 disconnection of scaled correlation at s=0

Part of the split eta<=1 polynomial-to-exponential decay layer (Issue #1850).
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Phase 1: Disconnection at s = 0 -/

omit [Fintype ι] in
/-- **edgeSpin invariance under flipSet for non-crossing edges** (auxiliary):
For an edge `e = s(u, v)` that does not cross the cut `(C, Cᶜ)` (i.e., both endpoints
are on the same side of `C`), the edge spin is unchanged under `flipSet C`.

If `u, v ∈ C`: both spins flip; the product of two negatives is unchanged.
If `u, v ∉ C`: neither spin flips; the product is unchanged. -/
private theorem edgeSpin_flipSet_of_not_crosses (C : Finset ι) (σ : Config ι)
    (u v : ι) (hnotcross : ¬(u ∈ C ∧ v ∉ C) ∧ ¬(u ∉ C ∧ v ∈ C)) :
    edgeSpin (K := ℝ) (Config.flipSet C σ) s(u, v) =
    edgeSpin (K := ℝ) σ s(u, v) := by
  simp only [edgeSpin, Sym2.lift_mk, Config.flipSet]
  push Not at hnotcross
  obtain ⟨h1, h2⟩ := hnotcross
  by_cases hu : u ∈ C
  · have hv : v ∈ C := h1 hu
    simp only [hu, hv, ite_true, Spin.sign_flip]; ring
  · have hv : v ∉ C := h2 hu
    simp only [hu, hv, ite_false]

/-- **scaledBoltzmannWeight at s=0 depends only on G\E₀ edges** (auxiliary):
At `s = 0` and `h = 0`, the scaled Boltzmann weight equals
`exp(β·J · Σ_{G\E₀} edgeSpin σ e)`.
This is the key identity showing that E₀ edges cancel out at `s = 0`. -/
private theorem scaledBoltzmannWeight_zero_sdiff (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (hE₀_sub : E₀ ⊆ G.edgeFinset)
    (p : IsingParams ℝ) (hh : p.h = 0) (σ : Config ι) :
    scaledBoltzmannWeight G E₀ p 0 σ =
    Real.exp (p.β * p.J * ∑ e ∈ G.edgeFinset \ E₀, edgeSpin (K := ℝ) σ e) := by
  simp only [scaledBoltzmannWeight, boltzmannWeight, hamiltonian, interactionEnergy,
    externalFieldEnergy, hh, neg_zero, zero_mul, add_zero]
  rw [← Real.exp_add]
  congr 1
  rw [← Finset.sum_sdiff hE₀_sub]
  ring

/-- **scaledBoltzmannWeight invariance under flipSet at s=0** (auxiliary):
At `s = 0` and `h = 0`, when no edge in `G.edgeFinset \ E₀` crosses the cut `(C, Cᶜ)`,
the partial flip `flipSet C` preserves the scaled Boltzmann weight. -/
private theorem scaledBoltzmannWeight_flipSet_of_sep (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (hE₀_sub : E₀ ⊆ G.edgeFinset)
    (p : IsingParams ℝ) (hh : p.h = 0)
    (C : Finset ι)
    (hcut : ∀ v ∈ C, ∀ w ∉ C, ∀ (e : Sym2 ι), e = s(v, w) → e ∉ E₀ → ¬G.Adj v w)
    (σ : Config ι) :
    scaledBoltzmannWeight G E₀ p 0 (Config.flipSet C σ) =
    scaledBoltzmannWeight G E₀ p 0 σ := by
  rw [scaledBoltzmannWeight_zero_sdiff G E₀ hE₀_sub p hh,
      scaledBoltzmannWeight_zero_sdiff G E₀ hE₀_sub p hh]
  -- Goal: exp(β*J*Σ_{G\E₀} edgeSpin (flipSet C σ) e) = exp(β*J*Σ_{G\E₀} edgeSpin σ e)
  congr 1; congr 1
  -- Goal: Σ_{G\E₀} edgeSpin (flipSet C σ) e = Σ_{G\E₀} edgeSpin σ e
  apply Finset.sum_congr rfl
  intro e he
  -- e ∈ G.edgeFinset \ E₀; write e = s(u, v) and show edgeSpin is preserved.
  obtain ⟨hemem, heE₀⟩ := Finset.mem_sdiff.mp he
  -- Induct on e as s(u,v); after induction, hemem and heE₀ are rewritten.
  induction e using Sym2.ind with
  | h u v =>
  apply edgeSpin_flipSet_of_not_crosses
  -- Show neither direction of crossing can occur.
  refine ⟨fun ⟨hu, hv⟩ => ?_, fun ⟨hu, hv⟩ => ?_⟩
  · -- ¬(u ∈ C ∧ v ∉ C): if u ∈ C and v ∉ C, then G.Adj u v by hemem, contradiction.
    have hnadj : ¬G.Adj u v := hcut u hu v hv s(u, v) rfl heE₀
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hemem
    exact hnadj hemem
  · -- ¬(u ∉ C ∧ v ∈ C): symmetric.
    have heE₀' : s(v, u) ∉ E₀ := by rwa [Sym2.eq_swap]
    have hnadj : ¬G.Adj v u := hcut v hv u hu s(v, u) rfl heE₀'
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hemem
    exact hnadj hemem.symm

set_option linter.unusedVariables false in
/-- **Disconnection theorem for the scaled model at `s = 0`** (GJ §17.8 p. 316):
If `C` separates `r` from `s` in the sense that every edge `e ∈ G.edgeFinset ∖ E₀`
that would cross the cut `(C, Cᶜ)` is absent from `G`, then
`scaledCorrelation G E₀ p 0 {r, s} = 0`.

At `s = 0` the scaled Boltzmann weight retains only edges in `G.edgeFinset ∖ E₀`.
Since no such edge crosses the cut `(C, Cᶜ)`, the partial flip `flipSet C` is a
measure-preserving involution that negates `spinProduct {r, s}` (because `r ∈ C`
and `s ∉ C`). A standard pairing argument then shows the numerator sum is zero.

## Proof sketch

1. **flipSet C preserves scaledBoltzmannWeight G E₀ p 0**: at `s = 0` and `h = 0`,
   `scaledBoltzmannWeight G E₀ p 0 σ = exp(β·J · Σ_{G\E₀} edgeSpin σ e)`.
   Each edge `e = ⟨u, v⟩ ∈ G\E₀` does not cross `(C, Cᶜ)` by `hcut`,
   so both endpoints are on the same side; `edgeSpin (flipSet C σ) e = edgeSpin σ e`.

2. **flipSet C negates spinProduct {r, s}**: `r ∈ C` is flipped, `s ∉ C` is not,
   so `sign((flipSet C σ) r) = -sign(σ r)` while `sign((flipSet C σ) s) = sign(σ s)`.

3. **Pairing argument**: `Σ f(σ) = Σ f(flipSet C σ) = -Σ f(σ)`, hence 0.

Note: the hypothesis `hf : Ferromagnetic p` is retained in the signature for
uniformity with the rest of the API, even though this particular proof does not
use it directly (the spin-flip argument at `h = 0` does not require ferromagneticity).

Reference: Glimm–Jaffe §17.8 p. 316. -/
theorem scaledCorrelation_at_zero_of_sep (G : SimpleGraph ι) [Fintype G.edgeSet]
    (E₀ : Finset (Sym2 ι)) (hE₀_sub : E₀ ⊆ G.edgeFinset)
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (r s : ι) (hrs : r ≠ s)
    (C : Finset ι) (hrC : r ∈ C) (hsC : s ∉ C)
    (hcut : ∀ v ∈ C, ∀ w ∉ C, ∀ (e : Sym2 ι), e = s(v, w) → e ∉ E₀ → ¬G.Adj v w) :
    scaledCorrelation G E₀ p 0 {r, s} = 0 := by
  simp only [scaledCorrelation, scaledGibbsExpectation]
  -- Reduce to showing the numerator sum is zero.
  suffices hsum : ∑ σ : Config ι,
      spinProduct {r, s} σ * scaledBoltzmannWeight G E₀ p 0 σ = 0 by
    rw [hsum, mul_zero]
  -- Step B: spinProduct {r,s} (flipSet C σ) = -spinProduct {r,s} σ
  -- since r ∈ C (so sign flips) and s ∉ C (so sign unchanged).
  have hsp : ∀ σ : Config ι,
      spinProduct {r, s} (Config.flipSet C σ) = -spinProduct {r, s} σ := by
    intro σ
    -- {r, s} has r ≠ s, so the two-element product expands.
    rw [spinProduct, spinProduct]
    simp only [Finset.prod_pair hrs, Config.flipSet]
    simp only [hrC, hsC, ite_true, ite_false, Spin.toSign_flip, Int.cast_neg]
    ring
  -- Step A: scaledBoltzmannWeight is invariant under flipSet C (by hcut and h=0).
  have hbw : ∀ σ : Config ι,
      scaledBoltzmannWeight G E₀ p 0 (Config.flipSet C σ) =
      scaledBoltzmannWeight G E₀ p 0 σ :=
    scaledBoltzmannWeight_flipSet_of_sep G E₀ hE₀_sub p hh C hcut
  -- Step C: combining, the summand negates under flipSet C.
  have hflip : ∀ σ : Config ι,
      spinProduct {r, s} (Config.flipSet C σ) *
        scaledBoltzmannWeight G E₀ p 0 (Config.flipSet C σ) =
      -(spinProduct {r, s} σ * scaledBoltzmannWeight G E₀ p 0 σ) := by
    intro σ; rw [hsp, hbw]; ring
  -- Step D: pairing argument — Σ f(σ) = Σ f(flipSet C σ) = -Σ f(σ), so Σ f(σ) = 0.
  let flipSetEquiv : Equiv.Perm (Config ι) :=
    ⟨Config.flipSet C, Config.flipSet C,
      Config.flipSet_flipSet C, Config.flipSet_flipSet C⟩
  have hreindex : ∑ σ : Config ι,
        spinProduct {r, s} σ * scaledBoltzmannWeight G E₀ p 0 σ =
      ∑ σ : Config ι,
        spinProduct {r, s} (Config.flipSet C σ) *
          scaledBoltzmannWeight G E₀ p 0 (Config.flipSet C σ) :=
    (Equiv.sum_comp flipSetEquiv _).symm
  have hneq : ∑ σ : Config ι,
        spinProduct {r, s} σ * scaledBoltzmannWeight G E₀ p 0 σ =
      -(∑ σ : Config ι, spinProduct {r, s} σ * scaledBoltzmannWeight G E₀ p 0 σ) :=
    calc ∑ σ : Config ι, spinProduct {r, s} σ * scaledBoltzmannWeight G E₀ p 0 σ
        = ∑ σ : Config ι,
            spinProduct {r, s} (Config.flipSet C σ) *
              scaledBoltzmannWeight G E₀ p 0 (Config.flipSet C σ) := hreindex
      _ = ∑ σ : Config ι,
            -(spinProduct {r, s} σ * scaledBoltzmannWeight G E₀ p 0 σ) :=
            Finset.sum_congr rfl (fun σ _ => hflip σ)
      _ = -(∑ σ : Config ι, spinProduct {r, s} σ * scaledBoltzmannWeight G E₀ p 0 σ) := by
            rw [← Finset.sum_neg_distrib]
  linarith


end Ambient
end IsingModel
