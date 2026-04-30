import IsingModel.AmbientLattice.SpontaneousMono

/-!
# Special-case closed forms, h-symmetry, and critical exponents

Uniform upper bounds (BoundedEdgeDensity), closed forms for special
parameter slices (β=0, J=h=0, J=0), h-symmetry / |h|-monotonicity
along an exhaustion, and the critical exponent bounds η≥0, ζ≥0
at infinite volume (GJ §17.7 Thm 17.7.1).

## References

* Glimm–Jaffe, *Quantum Physics*, §4.6, §17.7.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-! ## Uniform upper bound under bounded edge density

The per-stage upper bound `freeEnergyAlongExhaustion_upper_bound` depends
on `|E_n| / |Λ_n|`; this ratio can diverge for an arbitrary exhaustion.
Under the natural hypothesis `BoundedEdgeDensity`, the sequence is
uniformly bounded above — a step toward Glimm–Jaffe §4.6 Prop 4.6.1
convergence (which still needs super-additivity + Fekete). -/

/-- **Bounded edge density along an exhaustion**: there is `c : ℝ` such
that for every `n` with `Λ.volume n` nonempty,
`|E(G[Λ_n])| ≤ c · |Λ_n|`.

Example: bounded-degree ambient graphs with max degree `Δ` satisfy
this with `c = Δ / 2`. -/
def BoundedEdgeDensity (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] : Prop :=
  ∃ c : ℝ, ∀ n, (Λ.volume n).Nonempty →
    ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) ≤
      c * Fintype.card (↑(Λ.volume n) : Type _)

/-- **Uniform upper bound on `freeEnergyAlongExhaustion` under bounded
edge density**: if `BoundedEdgeDensity G Λ` with constant `c`, then for
every `n` with `Λ.volume n` nonempty and any Ising parameters `p`,
`freeEnergyAlongExhaustion G Λ p n ≤ log 2 + |β|·(|J|·c + |h|)`.

Direct consequence of `freeEnergyAlongExhaustion_upper_bound` (PR #122)
and the edge-density bound `|E_n|/|Λ_n| ≤ c`. -/
theorem freeEnergyAlongExhaustion_le_uniform_upper_bound
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) ≤
        c * Fintype.card (↑(Λ.volume n) : Type _))
    (n : ℕ) (hne : (Λ.volume n).Nonempty) :
    freeEnergyAlongExhaustion G Λ p n ≤
      Real.log 2 + |p.β| * (|p.J| * c + |p.h|) := by
  have hcard_pos : (0 : ℝ) < Fintype.card (↑(Λ.volume n) : Type _) := by
    rw [Fintype.card_coe]; exact_mod_cast Finset.card_pos.mpr hne
  have hratio :
      ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) /
        Fintype.card (↑(Λ.volume n) : Type _) ≤ c :=
    (div_le_iff₀ hcard_pos).mpr (hc n hne)
  calc freeEnergyAlongExhaustion G Λ p n
      ≤ Real.log 2 +
          |p.β| * (|p.J| * (inducedGraph G (Λ.volume n)).edgeFinset.card +
              |p.h| * Fintype.card (↑(Λ.volume n) : Type _))
            / Fintype.card (↑(Λ.volume n) : Type _) :=
        freeEnergyAlongExhaustion_upper_bound G Λ p n hne
    _ = Real.log 2 +
          |p.β| * (|p.J| *
              ((inducedGraph G (Λ.volume n)).edgeFinset.card /
                Fintype.card (↑(Λ.volume n) : Type _)) + |p.h|) := by
          field_simp
    _ ≤ Real.log 2 + |p.β| * (|p.J| * c + |p.h|) := by
          gcongr

/-! ## β = 0 closed form along exhaustion -/

/-- **Along-exhaustion β=0 closed form**:
for nonempty `Λ.volume n` and any ambient graph `G, Λ, J, h`,
`freeEnergyAlongExhaustion G Λ ⟨J, h, 0⟩ n = log 2`.

Specialization of `IsingModel.freeEnergy_beta_zero` (PR #131) via
`change` + definitional unfolding of `freeEnergyAlongExhaustion`
through `freeEnergyΛ` to `IsingModel.freeEnergy (inducedGraph …)`. -/
theorem freeEnergyAlongExhaustion_beta_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (n : ℕ) (hne : (Λ.volume n).Nonempty) :
    freeEnergyAlongExhaustion G Λ (⟨J, h, 0⟩ : IsingParams ℝ) n
      = Real.log 2 := by
  change IsingModel.freeEnergy (inducedGraph G (Λ.volume n))
      (⟨J, h, 0⟩ : IsingParams ℝ) = Real.log 2
  exact IsingModel.freeEnergy_beta_zero _ J h (Finset.Nonempty.fintype_card_coe_pos hne)

/-- **Infinite-volume β=0 closed form**:
under `∀ n, (Λ.volume n).Nonempty`, `freeEnergyInfinite G Λ ⟨J, h, 0⟩ = log 2`
for any `J, h, G, Λ`.

The sequence `n ↦ freeEnergyAlongExhaustion G Λ ⟨J, h, 0⟩ n` is constantly
`log 2` by `freeEnergyAlongExhaustion_beta_zero`, so its `limsup` on
`atTop` is `log 2` by `Filter.limsup_const`.

Sanity check: the β = 0 slice of the §4.6 Prop 4.6.1 infinite-volume
free energy is trivially the maximum-entropy value.

A weakened version requiring only `∀ᶠ n in atTop, (Λ.volume n).Nonempty`
is provided as `freeEnergyInfinite_beta_zero_of_eventually_nonempty`
in `AmbientLatticeSum.lean`. -/
theorem freeEnergyInfinite_beta_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (hne : ∀ n, (Λ.volume n).Nonempty) :
    freeEnergyInfinite G Λ (⟨J, h, 0⟩ : IsingParams ℝ) = Real.log 2 := by
  unfold freeEnergyInfinite
  have hconst : freeEnergyAlongExhaustion G Λ (⟨J, h, 0⟩ : IsingParams ℝ)
      = fun _ : ℕ => Real.log 2 := by
    funext n
    exact freeEnergyAlongExhaustion_beta_zero G Λ J h n (hne n)
  rw [hconst]
  exact Filter.limsup_const (Real.log 2)

/-! ## J = h = 0 closed form along exhaustion -/

/-- **Along-exhaustion J=h=0 closed form**:
for nonempty `Λ.volume n` and any ambient graph `G, Λ` and any `β`,
`freeEnergyAlongExhaustion G Λ ⟨0, 0, β⟩ n = log 2`.

Specialization of `IsingModel.freeEnergy_zero_params` via `change` +
definitional unfolding of `freeEnergyAlongExhaustion` through
`freeEnergyΛ` to `IsingModel.freeEnergy (inducedGraph …)`. -/
theorem freeEnergyAlongExhaustion_zero_params
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) (n : ℕ) (hne : (Λ.volume n).Nonempty) :
    freeEnergyAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) n
      = Real.log 2 := by
  change IsingModel.freeEnergy (inducedGraph G (Λ.volume n))
      (⟨0, 0, β⟩ : IsingParams ℝ) = Real.log 2
  exact IsingModel.freeEnergy_zero_params _ β (Finset.Nonempty.fintype_card_coe_pos hne)

/-- **Infinite-volume J=h=0 closed form**:
under `∀ n, (Λ.volume n).Nonempty`, `freeEnergyInfinite G Λ ⟨0, 0, β⟩ = log 2`
for any `β, G, Λ`.

The sequence `n ↦ freeEnergyAlongExhaustion G Λ ⟨0, 0, β⟩ n` is constantly
`log 2` by `freeEnergyAlongExhaustion_zero_params`, so its `limsup` on
`atTop` is `log 2` by `Filter.limsup_const`.

Companion to `freeEnergyInfinite_beta_zero`: both give the
maximum-entropy value `log 2` from orthogonal degeneracies
(β=0 vs. H ≡ 0).

A weakened version requiring only `∀ᶠ n in atTop, (Λ.volume n).Nonempty`
is provided as `freeEnergyInfinite_zero_params_of_eventually_nonempty`
in `AmbientLatticeSum.lean`. -/
theorem freeEnergyInfinite_zero_params
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) (hne : ∀ n, (Λ.volume n).Nonempty) :
    freeEnergyInfinite G Λ (⟨0, 0, β⟩ : IsingParams ℝ) = Real.log 2 := by
  unfold freeEnergyInfinite
  have hconst : freeEnergyAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ)
      = fun _ : ℕ => Real.log 2 := by
    funext n
    exact freeEnergyAlongExhaustion_zero_params G Λ β n (hne n)
  rw [hconst]
  exact Filter.limsup_const (Real.log 2)

/-! ## J = 0 closed form along exhaustion (graph-independent) -/

/-- **Along-exhaustion J=0 graph-independence**:
`freeEnergyAlongExhaustion G Λ ⟨0, h, β⟩ n
  = freeEnergyAlongExhaustion ⊥ Λ ⟨0, h, β⟩ n`
for any `n`, any `G, Λ`, any `h, β` (no nonempty hypothesis).

Lift of `IsingModel.freeEnergy_eq_bot_at_J_zero` (PR #175) through
the definitional unfolding
`freeEnergyAlongExhaustion = freeEnergy (inducedGraph …)`:
apply the base identity on both sides to reduce to the same
`freeEnergy_bot` expression. -/
theorem freeEnergyAlongExhaustion_eq_bot_at_J_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Fintype (inducedGraph (⊥ : SimpleGraph V) (Λ.volume n)).edgeSet]
    (h β : ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion G Λ (⟨0, h, β⟩ : IsingParams ℝ) n
      = freeEnergyAlongExhaustion (⊥ : SimpleGraph V) Λ
          (⟨0, h, β⟩ : IsingParams ℝ) n := by
  change IsingModel.freeEnergy (inducedGraph G (Λ.volume n))
      (⟨0, h, β⟩ : IsingParams ℝ)
    = IsingModel.freeEnergy (inducedGraph (⊥ : SimpleGraph V) (Λ.volume n))
          (⟨0, h, β⟩ : IsingParams ℝ)
  rw [IsingModel.freeEnergy_eq_bot_at_J_zero (inducedGraph G (Λ.volume n)),
      IsingModel.freeEnergy_eq_bot_at_J_zero
        (inducedGraph (⊥ : SimpleGraph V) (Λ.volume n))]

/-- **Along-exhaustion J=0 closed form (graph-independent)**:
for nonempty `Λ.volume n` and any ambient graph `G, Λ` and any `h, β`,
`freeEnergyAlongExhaustion G Λ ⟨0, h, β⟩ n = log (2·cosh(β·h))`.

Specialization of `IsingModel.freeEnergy_J_zero` via `change` +
definitional unfolding. -/
theorem freeEnergyAlongExhaustion_J_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ) (n : ℕ) (hne : (Λ.volume n).Nonempty) :
    freeEnergyAlongExhaustion G Λ (⟨0, h, β⟩ : IsingParams ℝ) n
      = Real.log (2 * Real.cosh (β * h)) := by
  change IsingModel.freeEnergy (inducedGraph G (Λ.volume n))
      (⟨0, h, β⟩ : IsingParams ℝ) = _
  exact IsingModel.freeEnergy_J_zero _ h β (Finset.Nonempty.fintype_card_coe_pos hne)

/-! ## β = 0 closed form for `partitionFunctionAlongExhaustion` -/

/-- **Along-exhaustion β=0 partition function closed form**:
`partitionFunctionAlongExhaustion G Λ ⟨J, h, 0⟩ n = 2 ^ |Λ.volume n|`
for any `J, h` and any ambient graph `G, Λ`.

Specialization of `IsingModel.partitionFunction_beta_zero` (every
Boltzmann weight collapses to `exp 0 = 1`) with
`card_config_eq_two_pow` and `Fintype.card_coe`. -/
theorem partitionFunctionAlongExhaustion_beta_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ (⟨J, h, 0⟩ : IsingParams ℝ) n
      = (2 : ℝ) ^ (Λ.volume n).card := by
  change partitionFunction (inducedGraph G (Λ.volume n))
      (⟨J, h, 0⟩ : IsingParams ℝ) = (2 : ℝ) ^ (Λ.volume n).card
  rw [IsingModel.partitionFunction_beta_zero, IsingModel.card_config_eq_two_pow,
      Fintype.card_coe]
  push_cast
  rfl

/-- **Log form**: `log (partitionFunctionAlongExhaustion G Λ ⟨J, h, 0⟩ n)
= |Λ.volume n| · log 2`. Follows from
`partitionFunctionAlongExhaustion_beta_zero` via `Real.log_pow`. -/
theorem log_partitionFunctionAlongExhaustion_beta_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion G Λ
        (⟨J, h, 0⟩ : IsingParams ℝ) n)
      = ((Λ.volume n).card : ℝ) * Real.log 2 := by
  rw [partitionFunctionAlongExhaustion_beta_zero, Real.log_pow]

/-! ## J = h = 0 closed form for `partitionFunctionAlongExhaustion` -/

/-- **Along-exhaustion J=h=0 partition function closed form**:
`partitionFunctionAlongExhaustion G Λ ⟨0, 0, β⟩ n = 2 ^ |Λ.volume n|`
for any ambient graph `G, Λ` and any `β`.

Specialization of `IsingModel.partitionFunction_zero_params`
(`Z_G ⟨0,0,β⟩ = Fintype.card (Config ι)`) with `card_config_eq_two_pow`
(`|Config ι| = 2^|ι|`) and `Fintype.card_coe` (`|↑Λ| = |Λ|`). -/
theorem partitionFunctionAlongExhaustion_zero_params
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) n
      = (2 : ℝ) ^ (Λ.volume n).card := by
  change partitionFunction (inducedGraph G (Λ.volume n))
      (⟨0, 0, β⟩ : IsingParams ℝ) = (2 : ℝ) ^ (Λ.volume n).card
  rw [IsingModel.partitionFunction_zero_params, IsingModel.card_config_eq_two_pow,
      Fintype.card_coe]
  push_cast
  rfl

/-- **Log form**: `log (partitionFunctionAlongExhaustion G Λ ⟨0, 0, β⟩ n)
= |Λ.volume n| · log 2`. Follows from
`partitionFunctionAlongExhaustion_zero_params` via `Real.log_pow`. -/
theorem log_partitionFunctionAlongExhaustion_zero_params
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion G Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) n)
      = ((Λ.volume n).card : ℝ) * Real.log 2 := by
  rw [partitionFunctionAlongExhaustion_zero_params, Real.log_pow]

/-! ## J = 0 closed form for `partitionFunctionAlongExhaustion` -/

/-- **Along-exhaustion J=0 partition function closed form**:
`partitionFunctionAlongExhaustion G Λ ⟨0, h, β⟩ n = (2·cosh(β·h))^|Λ.volume n|`
for any `h, β` and any ambient graph `G, Λ`.

Specialization of `IsingModel.partitionFunction_J_zero`
(`Z_G ⟨0, h, β⟩ = (2·cosh(β·h))^|ι|`, graph-independent) with
`Fintype.card_coe` (`|↑Λ| = |Λ|`). -/
theorem partitionFunctionAlongExhaustion_J_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ (⟨0, h, β⟩ : IsingParams ℝ) n
      = (2 * Real.cosh (β * h)) ^ (Λ.volume n).card := by
  change partitionFunction (inducedGraph G (Λ.volume n))
      (⟨0, h, β⟩ : IsingParams ℝ) = _
  rw [IsingModel.partitionFunction_J_zero, Fintype.card_coe]

/-- **Log form**: `log (partitionFunctionAlongExhaustion G Λ ⟨0, h, β⟩ n)
= |Λ.volume n| · log (2·cosh(β·h))`. Follows from
`partitionFunctionAlongExhaustion_J_zero` via `Real.log_pow`
(`2·cosh(β·h) > 0`). -/
theorem log_partitionFunctionAlongExhaustion_J_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion G Λ
        (⟨0, h, β⟩ : IsingParams ℝ) n)
      = ((Λ.volume n).card : ℝ) * Real.log (2 * Real.cosh (β * h)) := by
  rw [partitionFunctionAlongExhaustion_J_zero, Real.log_pow]

/-! ## Along-exhaustion high-temperature lower bounds (GJ §18.3) -/

/-- **Along-exhaustion partition function high-temperature lower bound**:
under `0 ≤ β * J`, at every stage `n`,
`partitionFunctionAlongExhaustion G Λ ⟨J, 0, β⟩ n
  ≥ 2^|Λ.volume n| · (cosh(βJ))^|E_{Λ.volume n}|`.
Per-stage application of `partitionFunctionΛ_high_temp_expansion_h_zero_lower_bound`
(Step 287). -/
theorem partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_lower_bound
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) :
    (2 : ℝ) ^ (Λ.volume n).card *
        Real.cosh (β * J) ^
          (inducedGraph G (Λ.volume n)).edgeFinset.card
      ≤ partitionFunctionAlongExhaustion G Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n := by
  change _ ≤ partitionFunctionΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)
  exact partitionFunctionΛ_high_temp_expansion_h_zero_lower_bound
    G (Λ.volume n) J β hβJ

/-- **Along-exhaustion free-energy high-temperature lower bound**:
under `0 ≤ β * J` and `0 < |Λ.volume n|`,
`freeEnergyAlongExhaustion G Λ ⟨J, 0, β⟩ n
  ≥ log 2 + (|E_{Λ.volume n}|/|Λ.volume n|) · log(cosh(β·J))`.
Per-stage application of `freeEnergyΛ_high_temp_h_zero_lower_bound`
(Step 289). -/
theorem freeEnergyAlongExhaustion_high_temp_h_zero_lower_bound
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    Real.log 2 +
        ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) /
          (Λ.volume n).card * Real.log (Real.cosh (β * J))
      ≤ freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n := by
  change _ ≤ freeEnergyΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ)
  exact freeEnergyΛ_high_temp_h_zero_lower_bound
    G (Λ.volume n) J β hβJ hne

/-- **Along-exhaustion high-temperature even-subgraph sum is `≥ 1`**:
under `0 ≤ β * J`, at every stage `n`,
`∑_{X ⊆ E_{Λ.volume n}, even-degree} tanh(β J)^|X| ≥ 1`.
Per-stage application of `one_le_sum_pow_tanh_even_subgraph_Λ`
(Step 296). -/
theorem one_le_sum_pow_tanh_even_subgraph_alongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) :
    (1 : ℝ) ≤ ∑ X ∈
        (inducedGraph G (Λ.volume n)).edgeFinset.powerset.filter
          (fun X : Finset (Sym2 ↑(Λ.volume n)) =>
            ∀ v : ↑(Λ.volume n), Even ((X.filter (v ∈ ·)).card)),
        Real.tanh (β * J) ^ X.card :=
  one_le_sum_pow_tanh_even_subgraph_Λ G (Λ.volume n) J β hβJ

/-- **Along-exhaustion partition function high-temperature closed form (FV §3.7.3 eq. (3.45))**:
at every stage `n`,
`partitionFunctionAlongExhaustion G Λ ⟨J, 0, β⟩ n = 2^|Λ.volume n| · cosh(βJ)^|E_{Λ.volume n}| · ∑_{X ⊆ E_{Λ.volume n}, even-degree} tanh(βJ)^|X|`.
Per-stage application of `partitionFunctionΛ_high_temp_expansion_h_zero_closed`
(Step 285). -/
theorem partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_closed
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n
      = (2 : ℝ) ^ (Λ.volume n).card *
        Real.cosh (β * J) ^
          (inducedGraph G (Λ.volume n)).edgeFinset.card *
        ∑ X ∈ (inducedGraph G (Λ.volume n)).edgeFinset.powerset.filter
          (fun X => ∀ v : ↑(Λ.volume n),
            Even ((X.filter (v ∈ ·)).card)),
          Real.tanh (β * J) ^ X.card := by
  change partitionFunctionΛ G (Λ.volume n) (⟨J, 0, β⟩ : IsingParams ℝ) = _
  exact partitionFunctionΛ_high_temp_expansion_h_zero_closed
    G (Λ.volume n) J β

/-- **Along-exhaustion correlation nonnegativity from FV (3.46)**:
under `0 ≤ β * J`, at every stage `n`,
`0 ≤ correlationAlongExhaustion G Λ ⟨J, 0, β⟩ A n`.
When `A ⊄ Λ.volume n`, equals `0` by definition. When `A ⊆`, lifts via
`liftFinset` and applies `correlationΛ_high_temp_h_zero_nonneg` (Step 294). -/
theorem correlationAlongExhaustion_high_temp_h_zero_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (A : Finset V) (n : ℕ) :
    0 ≤ correlationAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) A n := by
  unfold correlationAlongExhaustion
  by_cases hAn : A ⊆ Λ.volume n
  · rw [dif_pos hAn]
    exact correlationΛ_high_temp_h_zero_nonneg G (Λ.volume n) J β hβJ
      (liftFinset A hAn)
  · rw [dif_neg hAn]

/-- **Along-exhaustion correlation high-temperature closed form (FV §3.7.3 eq. (3.46))**:
at every stage `n` with `A ⊆ Λ.volume n`, the per-stage correlation
admits the FV (3.46) ratio form. When `A ⊄ Λ.volume n`, the
along-exhaustion correlation is `0` by definition.

For the `A ⊆` case, lifts via `liftFinset` and applies
`correlationΛ_high_temp_expansion_h_zero_closed` (Step 285). -/
theorem correlationAlongExhaustion_high_temp_expansion_h_zero_closed
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (A : Finset V) (n : ℕ) (hAn : A ⊆ Λ.volume n) :
    correlationAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) A n =
      (∑ X ∈ (inducedGraph G (Λ.volume n)).edgeFinset.powerset.filter
          (fun X : Finset (Sym2 ↑(Λ.volume n)) => ∀ v : ↑(Λ.volume n),
            Even ((if v ∈ liftFinset A hAn then (1 : ℕ) else 0)
                  + (X.filter (v ∈ ·)).card)),
          Real.tanh (β * J) ^ X.card) /
      (∑ X ∈ (inducedGraph G (Λ.volume n)).edgeFinset.powerset.filter
          (fun X : Finset (Sym2 ↑(Λ.volume n)) =>
            ∀ v : ↑(Λ.volume n), Even ((X.filter (v ∈ ·)).card)),
          Real.tanh (β * J) ^ X.card) := by
  unfold correlationAlongExhaustion
  rw [dif_pos hAn]
  exact correlationΛ_high_temp_expansion_h_zero_closed G (Λ.volume n) J β
    (liftFinset A hAn)

/-- **Along-exhaustion correlation Z₂ symmetry at h = 0 (GJ §18.3)**:
for any ambient `A : Finset V` with odd cardinality, at every stage `n`
where `A ⊆ Λ.volume n`, the per-stage correlation
`correlationAlongExhaustion G Λ ⟨J, 0, β⟩ A n = 0`.

When `A ⊄ Λ.volume n`, `correlationAlongExhaustion` is `0` by definition,
trivially satisfying the equation. When `A ⊆ Λ.volume n`, lift via
`liftFinset` (preserves cardinality) and apply
`correlationΛ_high_temp_h_zero_odd_card_eq_zero` (Step 299). -/
theorem correlationAlongExhaustion_high_temp_h_zero_odd_card_eq_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (A : Finset V) (hA_odd : Odd A.card) (n : ℕ) :
    correlationAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) A n = 0 := by
  unfold correlationAlongExhaustion
  by_cases hAn : A ⊆ Λ.volume n
  · simp only [dif_pos hAn]
    have hcard : (liftFinset A hAn).card = A.card := liftFinset_card hAn
    refine correlationΛ_high_temp_h_zero_odd_card_eq_zero G (Λ.volume n) J β
      (liftFinset A hAn) ?_
    rw [hcard]; exact hA_odd
  · simp only [dif_neg hAn]

omit [DecidableEq V] in
/-- **Induced subgraph of the empty graph is empty**:
`inducedGraph (⊥ : SimpleGraph V) Λ = ⊥`.

`inducedGraph = induce = comap` and `SimpleGraph.comap_bot`.
Useful rewrite when the ambient graph is `⊥` (free-spin limit). -/
@[simp]
theorem inducedGraph_bot (Λ : Finset V) :
    inducedGraph (⊥ : SimpleGraph V) Λ = (⊥ : SimpleGraph (↑Λ : Type _)) :=
  SimpleGraph.comap_bot _

/-! ## h-symmetry / `|h|`-monotonicity along exhaustion

Specializations of `IsingModel.freeEnergy_neg_h`, `freeEnergy_eq_abs_h`,
and `freeEnergy_monotone_abs_h` (PRs #126–#127) to each stage of the
exhaustion, via the `change` + definitional-unfolding pattern already
used in this file. -/

/-- **Along-exhaustion partition-function h-evenness**:
`partitionFunctionAlongExhaustion G Λ ⟨J, -h, β⟩ n =
partitionFunctionAlongExhaustion G Λ ⟨J, h, β⟩ n`. Per-stage lift of
`IsingModel.partitionFunction_neg_h` via the flip involution. -/
theorem partitionFunctionAlongExhaustion_neg_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ (⟨J, -h, β⟩ : IsingParams ℝ) n
      = partitionFunctionAlongExhaustion G Λ (⟨J, h, β⟩ : IsingParams ℝ) n :=
  partitionFunctionΛ_neg_h G (Λ.volume n) J h β

/-- **Along-exhaustion partition-function `|h|`-rewrite**:
`partitionFunctionAlongExhaustion G Λ ⟨J, h, β⟩ n =
partitionFunctionAlongExhaustion G Λ ⟨J, |h|, β⟩ n`. Per-stage lift of
`partitionFunctionΛ_eq_abs_h`. -/
theorem partitionFunctionAlongExhaustion_eq_abs_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ (⟨J, h, β⟩ : IsingParams ℝ) n
      = partitionFunctionAlongExhaustion G Λ (⟨J, |h|, β⟩ : IsingParams ℝ) n :=
  partitionFunctionΛ_eq_abs_h G (Λ.volume n) J h β

/-- **Along-exhaustion ferromagnetic `|h|`-monotonicity of partition
function**: for `J ≥ 0`, `β > 0`, `|h₁| ≤ |h₂|`,
`partitionFunctionAlongExhaustion G Λ ⟨J, h₁, β⟩ n ≤
partitionFunctionAlongExhaustion G Λ ⟨J, h₂, β⟩ n`. Per-stage lift of
`partitionFunctionΛ_monotone_abs_h`. -/
theorem partitionFunctionAlongExhaustion_monotone_abs_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {h₁ h₂ : ℝ} (hh : |h₁| ≤ |h₂|) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ (⟨J, h₁, β⟩ : IsingParams ℝ) n
      ≤ partitionFunctionAlongExhaustion G Λ (⟨J, h₂, β⟩ : IsingParams ℝ) n :=
  partitionFunctionΛ_monotone_abs_h G (Λ.volume n) J β hJ hβ hh

/-- **Along-exhaustion h-evenness**:
`freeEnergyAlongExhaustion G Λ ⟨J, -h, β⟩ n = freeEnergyAlongExhaustion G Λ ⟨J, h, β⟩ n`. -/
theorem freeEnergyAlongExhaustion_neg_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion G Λ (⟨J, -h, β⟩ : IsingParams ℝ) n
      = freeEnergyAlongExhaustion G Λ (⟨J, h, β⟩ : IsingParams ℝ) n := by
  change IsingModel.freeEnergy (inducedGraph G (Λ.volume n))
      (⟨J, -h, β⟩ : IsingParams ℝ)
    = IsingModel.freeEnergy (inducedGraph G (Λ.volume n))
        (⟨J, h, β⟩ : IsingParams ℝ)
  exact IsingModel.freeEnergy_neg_h _ J h β

/-- **Along-exhaustion `|h|`-rewrite**:
`freeEnergyAlongExhaustion G Λ ⟨J, h, β⟩ n = freeEnergyAlongExhaustion G Λ ⟨J, |h|, β⟩ n`. -/
theorem freeEnergyAlongExhaustion_eq_abs_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion G Λ (⟨J, h, β⟩ : IsingParams ℝ) n
      = freeEnergyAlongExhaustion G Λ (⟨J, |h|, β⟩ : IsingParams ℝ) n := by
  change IsingModel.freeEnergy (inducedGraph G (Λ.volume n))
      (⟨J, h, β⟩ : IsingParams ℝ)
    = IsingModel.freeEnergy (inducedGraph G (Λ.volume n))
        (⟨J, |h|, β⟩ : IsingParams ℝ)
  exact IsingModel.freeEnergy_eq_abs_h _ J h β

/-- **Along-exhaustion ferromagnetic `|h|`-monotonicity**:
for `J ≥ 0`, `β > 0` and any real `h₁, h₂` with `|h₁| ≤ |h₂|`,
`freeEnergyAlongExhaustion G Λ ⟨J, h₁, β⟩ n ≤ freeEnergyAlongExhaustion G Λ ⟨J, h₂, β⟩ n`. -/
theorem freeEnergyAlongExhaustion_monotone_abs_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {h₁ h₂ : ℝ} (hh : |h₁| ≤ |h₂|) (n : ℕ) :
    freeEnergyAlongExhaustion G Λ (⟨J, h₁, β⟩ : IsingParams ℝ) n
      ≤ freeEnergyAlongExhaustion G Λ (⟨J, h₂, β⟩ : IsingParams ℝ) n := by
  change IsingModel.freeEnergy (inducedGraph G (Λ.volume n))
      (⟨J, h₁, β⟩ : IsingParams ℝ)
    ≤ IsingModel.freeEnergy (inducedGraph G (Λ.volume n))
        (⟨J, h₂, β⟩ : IsingParams ℝ)
  exact IsingModel.freeEnergy_monotone_abs_h _ J β hJ hβ hh

/-- **BddAbove for `freeEnergyAlongExhaustion` under bounded edge density**:
assuming `BoundedEdgeDensity G Λ`, the range of the exhaustion free energy
is bounded above.

For nonempty stages the bound is `log 2 + |β|·(|J|·c + |h|)` by the
uniform upper bound above; for empty stages the value is
`(Fintype.card ∅)⁻¹ · log 1 = 0`, which is at most the same constant
(after taking its `max` with `0`). -/
theorem BddAbove_freeEnergyAlongExhaustion_range
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hBED : BoundedEdgeDensity G Λ) :
    BddAbove (Set.range (freeEnergyAlongExhaustion G Λ p)) := by
  obtain ⟨c, hc⟩ := hBED
  refine ⟨max 0 (Real.log 2 + |p.β| * (|p.J| * c + |p.h|)), ?_⟩
  rintro y ⟨n, rfl⟩
  by_cases hne : (Λ.volume n).Nonempty
  · exact le_max_of_le_right
      (freeEnergyAlongExhaustion_le_uniform_upper_bound G Λ p hc n hne)
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    have hcard : Fintype.card (↑(Λ.volume n) : Type _) = 0 := by
      rw [Fintype.card_coe, hne]; rfl
    have hfe : freeEnergyAlongExhaustion G Λ p n = 0 := by
      change IsingModel.freeEnergy (inducedGraph G (Λ.volume n)) p = 0
      unfold IsingModel.freeEnergy
      rw [hcard, Nat.cast_zero, inv_zero, zero_mul]
    rw [hfe]; exact le_max_left _ _

/-! ## Critical exponents at ∞-volume (GJ §17.7 Thm 17.7.1)

Explicit ∞-vol named aliases for the critical-exponent bounds
`η ≥ 0` and `ζ ≥ 0`, matching the finite-volume
`IsingModel.eta_nonneg_finite_vol` / `zeta_nonneg_finite_vol`
pattern. Direct pass-throughs of `truncated2Infinite_nonneg` (GKS-II
at ∞-vol) and `truncated4Infinite_nonpos_h_zero` (Cor 4.3.3 at ∞-vol). -/

/-- **η ≥ 0 at ∞-volume** (GJ §17.7 Thm 17.7.1, ∞-vol lattice version).
Explicit alias of `truncated2Infinite_nonneg` matching the
`eta_nonneg_finite_vol` naming convention. -/
theorem eta_nonneg_infinite_vol
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (i j : V) :
    0 ≤ truncated2Infinite G Λ p i j :=
  truncated2Infinite_nonneg G Λ p hf i j

/-- **ζ ≥ 0 at ∞-volume** (GJ §17.7 Thm 17.7.1, ∞-vol lattice version,
at `h = 0`). Explicit alias of `truncated4Infinite_nonpos_h_zero` —
`U₄^∞ ≤ 0` for pairwise-distinct sites at `h = 0`. -/
theorem zeta_nonneg_infinite_vol
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hf : Ferromagnetic ⟨J, (0 : ℝ), β⟩)
    {i j k l : V}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    truncated4Infinite G Λ ⟨J, 0, β⟩ i j k l ≤ 0 :=
  truncated4Infinite_nonpos_h_zero G Λ J β hf hij hik hil hjk hjl hkl

/-- **Absence of even bound states — ∞-volume lattice** (Glimm–Jaffe
§17.2, pp. 311–313). ∞-vol version of
`IsingModel.absence_of_even_bound_states_finite_vol`:
`U₄^∞(i,j,k,l) ≤ 0` for ferromagnetic `⟨J, 0, β⟩` and pairwise-distinct
sites. Explicit alias of `truncated4Infinite_nonpos_h_zero`. -/
theorem absence_of_even_bound_states_infinite_vol
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hf : Ferromagnetic ⟨J, (0 : ℝ), β⟩)
    {i j k l : V}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    truncated4Infinite G Λ ⟨J, 0, β⟩ i j k l ≤ 0 :=
  truncated4Infinite_nonpos_h_zero G Λ J β hf hij hik hil hjk hjl hkl

end Ambient
end IsingModel
