import IsingModel.AmbientLattice.Exhaustion

/-!
# Ferromagnetic lower bounds on the partition function and on its logarithm

`partitionFunctionΛ G Λ p` is the partition function of the subgraph that a finite volume
`Λ : Finset V` induces in an arbitrary ambient graph `G : SimpleGraph V`, and
`partitionFunctionAlongExhaustion G Λ p` reads it at the stage volume `Λ.volume n` of an
exhaustion. Every statement here assumes `Ferromagnetic p` — that is `0 ≤ p.J`, `0 ≤ p.h` and
`0 < p.β` — and nothing further; in particular no volume is required to be nonempty, and the
only instance binders are `[DecidableEq V]` and a `Fintype` instance on the induced edge set,
taken on the volume itself at the finite-volume layer and stagewise at the exhaustion layer.

Three lower bounds occur, each in a multiplicative and a logarithmic form: `1` and `0`; the
vertex-count power `2 ^ Λ.card` and `↑Λ.card * log 2`; and the refinement
`(2 * cosh (p.β * p.h)) ^ Λ.card` and `↑Λ.card * log (2 * cosh (p.β * p.h))`, which
`Real.one_le_cosh` makes at least as strong as the second. Each of the six appears twice,
once at the finite-volume layer and once at the exhaustion layer, the latter being the same
inequality with `Λ` replaced by `Λ.volume n` and the stage index quantified inside the
statement.
-/

namespace IsingModel

open Finset
open Ambient

variable {V : Type*} [DecidableEq V]

/-- **`partitionFunctionΛ ≥ 1`** for ferromagnetic parameters:
lifts `partitionFunction_ge_one_of_ferromagnetic` to the
`partitionFunctionΛ` API level. -/
theorem partitionFunctionΛ_ge_one_of_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    1 ≤ partitionFunctionΛ G Λ p :=
  IsingModel.partitionFunction_ge_one_of_ferromagnetic _ p hf

/-- **`log Z_Λ ≥ 0`** for ferromagnetic parameters: immediate from
`partitionFunctionΛ_ge_one_of_ferromagnetic` via `Real.log_nonneg`. -/
theorem log_partitionFunctionΛ_nonneg_of_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    0 ≤ Real.log (partitionFunctionΛ G Λ p) :=
  Real.log_nonneg (partitionFunctionΛ_ge_one_of_ferromagnetic G Λ p hf)

/-- **`partitionFunctionAlongExhaustion ≥ 1`** for ferromagnetic
parameters: pointwise lift of
`partitionFunction_ge_one_of_ferromagnetic`. -/
theorem partitionFunctionAlongExhaustion_ge_one_of_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    1 ≤ partitionFunctionAlongExhaustion G Λ p n :=
  partitionFunctionΛ_ge_one_of_ferromagnetic G (Λ.volume n) p hf

/-- Log form: `log Z ≥ 0` along any exhaustion under ferromagnetic `p`. -/
theorem log_partitionFunctionAlongExhaustion_nonneg_of_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    0 ≤ Real.log (partitionFunctionAlongExhaustion G Λ p n) :=
  IsingModel.log_partitionFunction_nonneg_of_ferromagnetic _ p hf

/-- **`partitionFunctionΛ ≥ 2^|Λ|`** for ferromagnetic parameters:
lifts `partitionFunction_ge_two_pow_card_of_ferromagnetic`
to the `partitionFunctionΛ` API level.

Strictly sharper than `partitionFunctionΛ_ge_one_of_ferromagnetic`
for nonempty `Λ`. -/
theorem partitionFunctionΛ_ge_two_pow_card_of_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    (2 : ℝ) ^ Λ.card ≤ partitionFunctionΛ G Λ p := by
  have h := IsingModel.partitionFunction_ge_two_pow_card_of_ferromagnetic
    (inducedGraph G Λ) p hf
  rwa [Fintype.card_coe] at h

/-- Log form at `Λ` level: `|Λ| · log 2 ≤ log (partitionFunctionΛ G Λ p)`
for ferromagnetic. -/
theorem log_partitionFunctionΛ_ge_card_mul_log_two_of_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    (Λ.card : ℝ) * Real.log 2 ≤ Real.log (partitionFunctionΛ G Λ p) := by
  have h := IsingModel.log_partitionFunction_ge_card_mul_log_two_of_ferromagnetic
    (inducedGraph G Λ) p hf
  rwa [Fintype.card_coe] at h

/-- **`partitionFunctionAlongExhaustion ≥ 2^|Λ.volume n|`** for
ferromagnetic parameters: pointwise lift. -/
theorem partitionFunctionAlongExhaustion_ge_two_pow_card_of_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    (2 : ℝ) ^ (Λ.volume n).card ≤ partitionFunctionAlongExhaustion G Λ p n :=
  partitionFunctionΛ_ge_two_pow_card_of_ferromagnetic G (Λ.volume n) p hf

/-- **Sharp form at `Λ` level**: `(2·cosh(βh))^|Λ| ≤ partitionFunctionΛ G Λ p`
for ferromagnetic. Thin wrapper of
`IsingModel.partitionFunction_ge_two_cosh_pow_card_of_ferromagnetic`. -/
theorem partitionFunctionΛ_ge_two_cosh_pow_card_of_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    (2 * Real.cosh (p.β * p.h)) ^ Λ.card ≤ partitionFunctionΛ G Λ p := by
  have h := IsingModel.partitionFunction_ge_two_cosh_pow_card_of_ferromagnetic
    (inducedGraph G Λ) p hf
  rwa [Fintype.card_coe] at h

/-- **Sharp form along exhaustion**:
`(2·cosh(βh))^|Λ.volume n| ≤ partitionFunctionAlongExhaustion G Λ p n`
for ferromagnetic. Pointwise lift. -/
theorem partitionFunctionAlongExhaustion_ge_two_cosh_pow_card_of_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    (2 * Real.cosh (p.β * p.h)) ^ (Λ.volume n).card
      ≤ partitionFunctionAlongExhaustion G Λ p n :=
  partitionFunctionΛ_ge_two_cosh_pow_card_of_ferromagnetic G (Λ.volume n) p hf

/-- Log form along exhaustion: `|Λ.volume n| · log 2 ≤ log Z_n`. -/
theorem log_partitionFunctionAlongExhaustion_ge_card_mul_log_two_of_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    ((Λ.volume n).card : ℝ) * Real.log 2
      ≤ Real.log (partitionFunctionAlongExhaustion G Λ p n) := by
  have h := IsingModel.log_partitionFunction_ge_card_mul_log_two_of_ferromagnetic
    (inducedGraph G (Λ.volume n)) p hf
  rwa [Fintype.card_coe] at h

/-- Sharp form at `Λ` level: `|Λ| · log(2·cosh(βh)) ≤ log (partitionFunctionΛ G Λ p)`
for ferromagnetic. Thin wrapper of
`log_partitionFunction_ge_card_mul_log_two_cosh_of_ferromagnetic`. -/
theorem log_partitionFunctionΛ_ge_card_mul_log_two_cosh_of_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    (Λ.card : ℝ) * Real.log (2 * Real.cosh (p.β * p.h))
      ≤ Real.log (partitionFunctionΛ G Λ p) := by
  have h := IsingModel.log_partitionFunction_ge_card_mul_log_two_cosh_of_ferromagnetic
    (inducedGraph G Λ) p hf
  rwa [Fintype.card_coe] at h

/-- Sharp form along exhaustion:
`|Λ.volume n| · log(2·cosh(βh)) ≤ log Z_n`. Pointwise lift. -/
theorem log_partitionFunctionAlongExhaustion_ge_card_mul_log_two_cosh_of_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    ((Λ.volume n).card : ℝ) * Real.log (2 * Real.cosh (p.β * p.h))
      ≤ Real.log (partitionFunctionAlongExhaustion G Λ p n) :=
  log_partitionFunctionΛ_ge_card_mul_log_two_cosh_of_ferromagnetic G (Λ.volume n) p hf

end IsingModel
