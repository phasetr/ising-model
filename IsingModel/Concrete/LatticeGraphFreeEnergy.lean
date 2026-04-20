import IsingModel.Concrete.LatticeGraphBED

/-!
# Concrete free-energy sandwich bound for the `ℤ^d` Ising model

Capstone combining the three concrete ingredients developed in
`IsingModel/Concrete/`:

* `isTranslationInvariant_latticeGraph` — translation invariance of
  the `ℓ¹`-distance-1 lattice graph on `Fin d → ℤ`;
* `cubicExhaustion d` — the concrete two-sided cubic
  `Ambient.Exhaustion (Fin d → ℤ)`;
* `boundedEdgeDensity_latticeGraph_cubicExhaustion` — bounded edge
  density with constant `c = d`.

Together with the general-framework lower bound
`freeEnergyAlongExhaustion_ge_log_two` (ferromagnetic, nonempty stage)
and upper bound `freeEnergyAlongExhaustion_le_uniform_upper_bound`
(BED), we obtain a concrete sandwich
`log 2 ≤ f_n ≤ log 2 + |β|(|J|·d + |h|)` on every nonempty stage
of the `d`-dimensional cubic Ising exhaustion.

## Main theorem

* `freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_bounds`
  — the two-sided explicit bound on the `d`-dimensional concrete
  lattice.

## References

* Glimm–Jaffe, *Quantum Physics* 2nd ed., §4.6, p. 67.
-/

namespace IsingModel

namespace Ambient

/-- **Concrete two-sided sandwich bound for the `d`-dimensional
cubic Ising free energy**: for ferromagnetic parameters
`0 ≤ J`, `0 ≤ h`, `0 < β` and any stage `n` with nonempty
`cubicBox d n`,
`log 2 ≤ freeEnergyAlongExhaustion (latticeGraph d) (cubicExhaustion d)
⟨J, h, β⟩ n ≤ log 2 + |β|·(|J|·d + |h|)`.

Composition of:
- lower bound `freeEnergyAlongExhaustion_ge_log_two` (general
  ferromagnetic `0 ≤ J, 0 ≤ h, 0 < β`, nonempty stage);
- upper bound `freeEnergyAlongExhaustion_le_uniform_upper_bound`
  (general `BoundedEdgeDensity`), applied with the concrete instance
  `boundedEdgeDensity_latticeGraph_cubicExhaustion` whose constant is
  `c = d`.

Capstone theorem for the concrete `ℤ^d` infrastructure developed in
PRs #244–#246. Note: the full Fekete convergence `f_n → f_∞` is not
delivered here — it requires a compatible `TranslationInvariantExhaustion`
on `Fin d → ℤ`, which the current single-block-shift structure does not
admit on the two-sided cubic exhaustion (design note in
`Concrete/IntLattice.lean`). -/
theorem freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_bounds
    (d : ℕ) {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β)
    (n : ℕ) (hne : ((Ambient.cubicExhaustion d).volume n).Nonempty) :
    Real.log 2
      ≤ freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) ⟨J, h, β⟩ n
    ∧ freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) ⟨J, h, β⟩ n
      ≤ Real.log 2 + |β| * (|J| * d + |h|) := by
  refine ⟨?_, ?_⟩
  · -- Lower bound.
    exact freeEnergyAlongExhaustion_ge_log_two
      (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) hJ hh hβ n hne
  · -- Upper bound from BED with explicit `c = d`.
    have hc : ∀ n, ((Ambient.cubicExhaustion d).volume n).Nonempty →
        ((Ambient.inducedGraph (IsingModel.latticeGraph d)
          ((Ambient.cubicExhaustion d).volume n)).edgeFinset.card : ℝ)
          ≤ (d : ℝ) * Fintype.card
              (↑((Ambient.cubicExhaustion d).volume n) : Type _) := by
      intro n _
      exact inducedLatticeGraph_card_edgeFinset_le d
        ((Ambient.cubicExhaustion d).volume n)
    exact freeEnergyAlongExhaustion_le_uniform_upper_bound
      (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) ⟨J, h, β⟩ hc n hne

end Ambient

end IsingModel
