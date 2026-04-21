import IsingModel.AmbientLattice
import IsingModel.Inequalities.FKG

/-!
# Ambient-layer Gibbs expectation along an exhaustion + per-stage FKG

`Ambient.gibbsExpectationAlongExhaustion` packages a per-stage family
`F : (n : ℕ) → Config (↑(Λ.volume n)) → ℝ` into a sequence
`n ↦ gibbsExpectation (inducedGraph G (Λ.volume n)) p (F n)`. This is
the natural ambient-layer companion to
`Ambient.partitionFunctionAlongExhaustion` /
`Ambient.freeEnergyAlongExhaustion`, extending the along-exhaustion API
beyond the `correlation`/`partitionFunction`/`freeEnergy` family to
arbitrary configuration-level observables.

The main result is a per-stage FKG inequality
`fkg_ising_along_exhaustion`: a direct pass-through of
`IsingModel.fkg_ising` at each stage, valid for per-stage families of
nonneg monotone functions.

## References

* Glimm–Jaffe, *Quantum Physics* 2nd ed., §4.4 (FKG inequality), p. 65.
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Ambient-layer Gibbs expectation along an exhaustion**:
stagewise `n ↦ gibbsExpectation (inducedGraph G (Λ.volume n)) p (F n)`,
for a per-stage family `F n : Config (↑(Λ.volume n)) → ℝ`.

Companion to `partitionFunctionAlongExhaustion` and
`freeEnergyAlongExhaustion`, used to formulate along-exhaustion
theorems (e.g., FKG) for general observables. -/
noncomputable def gibbsExpectationAlongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (F : (n : ℕ) → Config (↑(Λ.volume n) : Type _) → ℝ) : ℕ → ℝ :=
  fun n => gibbsExpectation (inducedGraph G (Λ.volume n)) p (F n)

/-- **Unfolding of `gibbsExpectationAlongExhaustion`**:
by construction equal to `gibbsExpectation` on the `n`-th volume with
the `n`-th family member. -/
@[simp]
theorem gibbsExpectationAlongExhaustion_apply
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (F : (n : ℕ) → Config (↑(Λ.volume n) : Type _) → ℝ) (n : ℕ) :
    gibbsExpectationAlongExhaustion G Λ p F n
      = gibbsExpectation (inducedGraph G (Λ.volume n)) p (F n) :=
  rfl

/-- **Per-stage FKG along an exhaustion** (GJ §4.4).
For a ferromagnetic Ising model on `inducedGraph G (Λ.volume n)`, and
per-stage nonneg monotone families `F n, G_fn n : Config (↑Λ_n) → ℝ`,
the FKG inequality
`⟨F n⟩ₙ · ⟨G_fn n⟩ₙ ≤ ⟨(F n) · (G_fn n)⟩ₙ`
holds at every stage `n`. Thin per-stage pass-through of
`IsingModel.fkg_ising`. -/
theorem fkg_ising_along_exhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (F G_fn : (n : ℕ) → Config (↑(Λ.volume n) : Type _) → ℝ)
    (hF_nn : ∀ n, 0 ≤ F n) (hG_nn : ∀ n, 0 ≤ G_fn n)
    (hF_mono : ∀ n, Monotone (F n)) (hG_mono : ∀ n, Monotone (G_fn n))
    (n : ℕ) :
    gibbsExpectationAlongExhaustion G Λ p F n
        * gibbsExpectationAlongExhaustion G Λ p G_fn n
      ≤ gibbsExpectationAlongExhaustion G Λ p (fun k => F k * G_fn k) n :=
  IsingModel.fkg_ising (inducedGraph G (Λ.volume n)) p hf
    (F n) (G_fn n) (hF_nn n) (hG_nn n) (hF_mono n) (hG_mono n)

end Ambient

end IsingModel
