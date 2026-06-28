import IsingModel.Inequalities.GKS
import IsingModel.Concrete.CubicBoxConnectivity
import IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBoundsCorrelationPairCorollaries
import IsingModel.AmbientLattice.Defs.Correlation
import IsingModel.AmbientLattice.Exhaustion

/-!
# GJ §17.5 Theorem 17.5.1 — PR-FV0: finite-volume non-adjacent pair active range

The finite-volume two-point function `⟨φ(x)φ(z)⟩_{σ,A} = correlationΛ (latticeGraph d) A` is
strictly positive (hence in the active range `Ioo 0 2`) for **every** distinct pair `x ≠ z` in a
cubic box, not just adjacent ones.  This is the prerequisite for the finite-volume per-pair
pseudo-mass (the Step-1 finite-volume redesign of GJ §17.5, cf. #4320): GJ uses the finite-volume
expectation `⟨·⟩_{σ,A}` (where the binding pair's mass equals `m⁻(σ,A)` *exactly*, so `hbind` is
free).

Strict positivity for a general pair comes from a walk inside the box (the cubic box induced graph
is connected, `inducedGraph_cubicBox_reachable`) and the second Griffiths inequality
(`gks_second`): `⟨σ^{a}σ^{c}⟩·⟨σ^{c}σ^{b}⟩ ≤ ⟨σ^{a}σ^{b}⟩` (since `{a,c} ∆ {c,b} = {a,b}`), with the
adjacent factors positive (`correlationΛ_…_pos_of_latticeAdj`).  Induction along the walk gives
`0 < ⟨σ^{a}σ^{b}⟩`.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1 proof, p.~311.
-/

namespace IsingModel
namespace Ambient

open scoped symmDiff

/-- **Pair correlation positivity from a walk via GKS-II** (graph-agnostic): for a ferromagnetic
Ising model on any finite graph `G`, if every adjacent pair has positive two-point correlation and
`a, b` are joined by a walk, then `0 < ⟨σ^{a}σ^{b}⟩` for `a ≠ b`.

Induction on the walk: at `cons (h : Adj a c) w'`, if `c = b` use the adjacent base case; else
`gks_second` gives `⟨σ^{a}σ^{c}⟩·⟨σ^{c}σ^{b}⟩ ≤ ⟨σ^{a}σ^{b}⟩` (as `{a,c} ∆ {c,b} = {a,b}`), the
first factor positive by the edge hypothesis and the second by induction. -/
theorem correlation_pair_pos_of_walk {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] {p : IsingParams ℝ} (hf : Ferromagnetic p)
    (hedge : ∀ {u v : ι}, G.Adj u v → 0 < IsingModel.correlation G p {u, v})
    {a b : ι} (w : G.Walk a b) (hab : a ≠ b) :
    0 < IsingModel.correlation G p {a, b} := by
  classical
  induction w with
  | nil => exact absurd rfl hab
  | @cons a c b h w' ih =>
    by_cases hcb : c = b
    · subst hcb; exact hedge h
    · have hac : a ≠ c := h.ne
      have hac_pos : 0 < IsingModel.correlation G p {a, c} := hedge h
      have hcb_pos : 0 < IsingModel.correlation G p {c, b} := ih hcb
      have hsdiff : ({a, c} : Finset ι) ∆ {c, b} = {a, b} := by
        ext x
        simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro (⟨rfl | rfl, h2⟩ | ⟨rfl | rfl, h2⟩)
          · exact Or.inl rfl
          · exact absurd (Or.inl rfl) h2
          · exact absurd (Or.inr rfl) h2
          · exact Or.inr rfl
        · rintro (rfl | rfl)
          · exact Or.inl ⟨Or.inl rfl, by simp only [not_or]; exact ⟨hac, hab⟩⟩
          · exact Or.inr ⟨Or.inr rfl, by simp only [not_or]; exact ⟨Ne.symm hab, Ne.symm hcb⟩⟩
      have hgks := IsingModel.gks_second G p hf ({a, c} : Finset ι) ({c, b} : Finset ι)
      rw [hsdiff] at hgks
      exact lt_of_lt_of_le (mul_pos hac_pos hcb_pos) hgks

/-- **Finite-volume cubic-box pair correlation positivity** (any distinct in-box pair): for `0 < J`,
`0 < β`, `0 < correlationΛ (latticeGraph d) (cubicBox d n) ⟨J,0,β⟩ {a, b}` for distinct box sites
`a ≠ b`.  The box induced graph is connected (`inducedGraph_cubicBox_reachable`), so a walk joins
`a, b`; the adjacent factors are positive (`correlationΛ_…_pos_of_latticeAdj`); GKS-II induction
(`correlation_pair_pos_of_walk`) closes it. -/
theorem correlationΛ_cubicBox_pair_pos {d n : ℕ} {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β)
    {a b : ↑(cubicBox d n)} (hab : a ≠ b) :
    0 < correlationΛ (IsingModel.latticeGraph d) (cubicBox d n) (⟨J, 0, β⟩ : IsingParams ℝ)
      ({a, b} : Finset ↑(cubicBox d n)) := by
  have hf : Ferromagnetic (⟨J, 0, β⟩ : IsingParams ℝ) := ⟨hJ.le, le_refl 0, hβ⟩
  obtain ⟨w⟩ := inducedGraph_cubicBox_reachable d n a b
  refine correlation_pair_pos_of_walk
    (inducedGraph (IsingModel.latticeGraph d) (cubicBox d n)) hf ?_ w hab
  intro u v huv
  exact correlationΛ_latticeGraph_high_temp_h_zero_at_pair_pos_of_latticeAdj
    d (cubicBox d n) J β (mul_pos hβ hJ) u v huv

/-- **Finite-volume non-adjacent pair active range** (GJ §17.5, p.311): for `0 < J`, `0 < β`, a
distinct pair `x ≠ z` with `{x, z} ⊆ volume n`, the finite-volume two-point function
`correlationAlongExhaustion (latticeGraph d) (cubicExhaustion d) ⟨J,0,β⟩ {x,z} n` lies in the active
range `Ioo 0 2`.  Lower from `correlationΛ_cubicBox_pair_pos`; upper from `correlationΛ_le_one`.
This is the finite-volume analogue of `correlationInfinite_pair_active_of_betaJ_pos`, used to define
the finite-volume per-pair pseudo-mass (`pseudoMassExt`). -/
theorem correlationAlongExhaustion_cubicExhaustion_pair_active {d : ℕ} {J β : ℝ}
    (hJ : 0 < J) (hβ : 0 < β) {x z : Fin d → ℤ} (hxz : x ≠ z) {n : ℕ}
    (hsub : ({x, z} : Finset (Fin d → ℤ)) ⊆ (cubicExhaustion d).volume n) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) (cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) ({x, z} : Finset (Fin d → ℤ)) n ∈ Set.Ioo (0 : ℝ) 2 := by
  have hx : x ∈ (cubicExhaustion d).volume n := hsub (Finset.mem_insert_self x {z})
  have hz : z ∈ (cubicExhaustion d).volume n :=
    hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self z))
  have hne : (⟨x, hx⟩ : ↑(cubicBox d n)) ≠ ⟨z, hz⟩ :=
    fun h => hxz (congrArg Subtype.val h)
  rw [correlationAlongExhaustion, dif_pos hsub, correlationΛ, liftFinset_pair hsub hx hz]
  refine ⟨?_, ?_⟩
  · exact correlationΛ_cubicBox_pair_pos hJ hβ hne
  · have h := correlationΛ_le_one (IsingModel.latticeGraph d) ((cubicExhaustion d).volume n)
      (⟨J, 0, β⟩ : IsingParams ℝ) ({⟨x, hx⟩, ⟨z, hz⟩} : Finset ↑((cubicExhaustion d).volume n))
    rw [correlationΛ] at h
    linarith

end Ambient
end IsingModel
