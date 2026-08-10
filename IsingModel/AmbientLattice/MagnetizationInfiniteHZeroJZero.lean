import IsingModel.AmbientLattice.MagnetizationAlongExhaustion
import IsingModel.AmbientLattice.MagnetizationInfiniteLambdaHSymmetry
import IsingModel.AmbientLattice.MagnetizationInfiniteExhaustionHSymmetry

/-!
# Zero-field vanishing and the noninteracting closed form for the correlation

Statements for an ambient graph `G : SimpleGraph V`, about the correlation at the stage and
infinite-volume layers along an exhaustion `Λ` of `V`, and about the single-site magnetization
read off it at the finite-volume and stage layers.

Instance binders follow the layer. The statement about `magnetizationΛ` takes `DecidableEq V`
and `Fintype` on the edge set of the induced subgraph of its own `Λ : Finset V`; every other
declaration takes `DecidableEq V` and the stagewise `Fintype` family indexed by the stage. The
Prop-valued hypotheses are exactly these: the infinite-volume zero-field statement assumes
`Odd A.card`; the on-stage closed form assumes `A ⊆ Λ.volume n`; the infinite-volume closed
form assumes `Ferromagnetic ⟨0, h, β⟩`, whose content on that slice is `0 ≤ h` and `0 < β`;
the vanishing statement at zero coupling and zero field assumes `0 < β` together with
`A.Nonempty`; the lower bound assumes `0 ≤ J`, `0 ≤ h` and `0 < β`; and the remaining
statements assume nothing.

At zero field the infinite-volume correlation of an odd test set vanishes, and the single-site
magnetization vanishes at the finite-volume and stage layers, the singleton being one such
test set.

On the noninteracting slice the stage correlation equals `Real.tanh (β * h) ^ A.card` as soon
as the test set is covered by the stage volume; since an exhaustion covers every finite set
eventually, the stage sequence is eventually equal to that value, and passing to the supremum
under `0 ≤ h` and `0 < β` gives the same closed form for the infinite-volume correlation.

Under those two hypotheses `Real.tanh (β * h)` lies in `Set.Ico 0 1`, so the closed form
vanishes exactly when the test set is nonempty and `h = 0`, is strictly positive when the test
set is nonempty and `0 < h`, and equals `1` at the empty test set for every field. Reading it
at `h = 0` with a nonempty test set recovers the vanishing statement at zero coupling and zero
field. Raising the coupling from `0` while keeping `0 ≤ h` and `0 < β` turns the closed form
into a lower bound for the infinite-volume correlation at an arbitrary nonnegative coupling.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Z₂ symmetry at `h = 0` for `correlationInfinite`**: vanishes
for odd-cardinality sets.  Supremum of a constantly-zero sequence. -/
theorem correlationInfinite_h_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (A : Finset V) (hodd : Odd A.card) :
    correlationInfinite G Λ ⟨J, 0, β⟩ A = 0 := by
  simp only [correlationInfinite,
    correlationAlongExhaustion_h_zero G Λ J β A hodd, ciSup_const]

/-- **Z₂ symmetry at `h = 0` for `magnetizationΛ`**: for any `J, β` and
any site `i : ↑Λ`, `magnetizationΛ G Λ ⟨J, 0, β⟩ i = 0`. Specialization
of `correlationΛ_odd_vanish_h_zero` at `A = {i}` using `Odd 1`. -/
theorem magnetizationΛ_h_zero (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (J β : ℝ) (i : ↑Λ) :
    magnetizationΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) i = 0 :=
  correlationΛ_odd_vanish_h_zero G Λ J β {i}
    (by simp [Finset.card_singleton])

/-- **Z₂ symmetry at `h = 0` for `magnetizationAlongExhaustion`**
per stage: for any `J, β`, any site `i : V`, and any `n`,
`magnetizationAlongExhaustion G Λ ⟨J, 0, β⟩ i n = 0`.
Specialization of `correlationAlongExhaustion_h_zero` at `A = {i}`. -/
theorem magnetizationAlongExhaustion_h_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (i : V) (n : ℕ) :
    magnetizationAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) i n = 0 :=
  correlationAlongExhaustion_h_zero G Λ J β {i}
    (by simp [Finset.card_singleton]) n


/-- **`correlationAlongExhaustion` at `J = 0` (on-stage closed form)**:
whenever the test set `A` is contained in `Λ.volume n`,
`correlationAlongExhaustion G Λ ⟨0, h, β⟩ A n = tanh(β·h)^A.card`.

Specialization of `IsingModel.correlation_J_zero`
(`⟨σ^A⟩ = tanh(β·h)^{|A|}`) along the induced-subgraph coercion.
Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §4.1
(infinite-temperature slice of the correlation function). -/
theorem correlationAlongExhaustion_J_zero_of_subset
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ) {A : Finset V} {n : ℕ} (hAn : A ⊆ Λ.volume n) :
    correlationAlongExhaustion G Λ (⟨0, h, β⟩ : IsingParams ℝ) A n
      = Real.tanh (β * h) ^ A.card := by
  rw [correlationAlongExhaustion_of_subset G Λ (⟨0, h, β⟩ : IsingParams ℝ)
        hAn]
  change IsingModel.correlation (inducedGraph G (Λ.volume n))
      (⟨0, h, β⟩ : IsingParams ℝ) (liftFinset A hAn) = _
  rw [IsingModel.correlation_J_zero, liftFinset_card hAn]

/-- **`correlationAlongExhaustion` at `J = 0` is eventually constant**
at `tanh(β·h)^A.card`. Immediate consequence of `Exhaustion.exhaust`
(any finite `A` is eventually covered by `Λ.volume n`) and
`correlationAlongExhaustion_J_zero_of_subset`. -/
theorem correlationAlongExhaustion_J_zero_eventually_eq
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ) (A : Finset V) :
    ∀ᶠ n in Filter.atTop,
      correlationAlongExhaustion G Λ (⟨0, h, β⟩ : IsingParams ℝ) A n
        = Real.tanh (β * h) ^ A.card := by
  obtain ⟨N, hN⟩ := Λ.exhaust A
  refine Filter.eventually_atTop.mpr ⟨N, ?_⟩
  intro n hn
  exact correlationAlongExhaustion_J_zero_of_subset G Λ h β (hN n hn)

/-- **∞-volume correlation at `J = 0`** (ferromagnetic): for
`⟨0, h, β⟩` ferromagnetic (i.e. `h ≥ 0`, `0 < β`; the strict-`β`
condition comes from `Ferromagnetic.hβ`),
`correlationInfinite G Λ ⟨0, h, β⟩ A = tanh(β·h)^A.card`.

Proof: `correlationAlongExhaustion` at `J = 0` is eventually
constant at `tanh(β·h)^A.card`, so it tends to that value; by
`correlationAlongExhaustion_tendsto_ciSup` it also tends to
`correlationInfinite`, so the two limits coincide.

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §4.1 / §5.1
infinite-temperature slice. -/
theorem correlationInfinite_J_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    (A : Finset V) :
    correlationInfinite G Λ (⟨0, h, β⟩ : IsingParams ℝ) A
      = Real.tanh (β * h) ^ A.card := by
  have h_tendsto_ciSup := correlationAlongExhaustion_tendsto_ciSup G Λ
    (⟨0, h, β⟩ : IsingParams ℝ) hf A
  have h_event := correlationAlongExhaustion_J_zero_eventually_eq G Λ h β A
  have h_tendsto_const :
      Filter.Tendsto
        (correlationAlongExhaustion G Λ (⟨0, h, β⟩ : IsingParams ℝ) A)
        Filter.atTop (nhds (Real.tanh (β * h) ^ A.card)) :=
    tendsto_const_nhds.congr' (h_event.mono (fun _ heq => heq.symm))
  have h_unique :
      (⨆ n, correlationAlongExhaustion G Λ
          (⟨0, h, β⟩ : IsingParams ℝ) A n) = Real.tanh (β * h) ^ A.card :=
    tendsto_nhds_unique h_tendsto_ciSup h_tendsto_const
  simp only [correlationInfinite, h_unique]

/-- **`correlationInfinite` at J = h = 0 vanishes for nonempty A** (Step 279, GJ §4.1):
At zero coupling and zero field, the system is uniformly distributed; for nonempty A
the spin product averages to zero by Z₂ symmetry.

Specialization of `correlationInfinite_J_zero` at `h = 0` (where `tanh(β·0) = 0` and
`0^|A| = 0` for `|A| ≥ 1`). -/
theorem correlationInfinite_zero_params_vanish_of_nonempty_A
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β : ℝ} (hβ : 0 < β) {A : Finset V} (hA : A.Nonempty) :
    correlationInfinite G Λ (⟨0, 0, β⟩ : IsingParams ℝ) A = 0 := by
  have hf : Ferromagnetic (⟨(0 : ℝ), 0, β⟩ : IsingParams ℝ) :=
    ⟨le_refl 0, le_refl 0, hβ⟩
  rw [correlationInfinite_J_zero G Λ 0 β hf A]
  have h_card_pos : 0 < A.card := Finset.card_pos.mpr hA
  rw [mul_zero, Real.tanh_zero, zero_pow h_card_pos.ne']

/-- **∞-volume lower bound `correlationInfinite ≥ tanh(β·h)^|A|`**
(ferromagnetic): by J-monotonicity from `J = 0` where
`correlationInfinite = tanh(β·h)^|A|` (via `correlationInfinite_J_zero`). -/
theorem correlationInfinite_ge_tanh_pow_card
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β)
    (A : Finset V) :
    Real.tanh (β * h) ^ A.card
      ≤ correlationInfinite G Λ (⟨J, h, β⟩ : IsingParams ℝ) A := by
  have hf0 : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ) :=
    ⟨le_rfl, hh, hβ⟩
  have h_zero := correlationInfinite_J_zero G Λ h β hf0 A
  rw [← h_zero]
  exact correlationInfinite_monotone_J G Λ hh hβ A
    (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hJ) hJ

end Ambient

end IsingModel
