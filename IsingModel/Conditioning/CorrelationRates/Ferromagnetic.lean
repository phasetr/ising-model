import IsingModel.Conditioning.CorrelationRates.TanhBounds

/-!
# Correlation rates split — ferromagnetic bounds and pair/singleton bundles

Part of the split high-temperature correlation-rates layer (Issue #1850).
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Pair correlation under `Ferromagnetic` at h = 0**: under ferromagnetic
parameters `⟨J, 0, β⟩` (i.e. `0 ≤ J, 0 < β`),
`0 ≤ ⟨σ_i σ_j⟩ ≤ 1`. Bridges the `Ferromagnetic` typeclass and FV (3.46)
nonneg/upper-bound. -/
theorem correlation_high_temp_h_zero_at_pair_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (i j : ι) :
    0 ≤ correlation G ⟨J, 0, β⟩ ({i, j} : Finset ι) ∧
      correlation G ⟨J, 0, β⟩ ({i, j} : Finset ι) ≤ 1 :=
  correlation_high_temp_h_zero_at_pair_sandwich G J β
    (mul_nonneg hβ.le hJ) i j

/-- **Pair correlation high-temp closed form (FV (3.46) at A = {i,j})**:
for `i ≠ j` and at `h = 0`,
`⟨σ_i σ_j⟩_{β,0} = (∑_{X : ∂X = {i,j}} tanh^|X|) / (∑_{X : ∂X = ∅} tanh^|X|)`.

Direct instantiation of `correlation_high_temp_expansion_h_zero_closed`
(Step 284) at `A = {i, j}`. Useful concrete case of the
two-point function formula. -/
theorem correlation_high_temp_h_zero_at_pair
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (i j : ι) :
    correlation G ⟨J, 0, β⟩ ({i, j} : Finset ι) =
      (∑ X ∈ G.edgeFinset.powerset.filter
          (fun X : Finset (Sym2 ι) => ∀ v : ι,
            Even ((if v ∈ ({i, j} : Finset ι) then (1 : ℕ) else 0)
                  + (X.filter (v ∈ ·)).card)),
          Real.tanh (β * J) ^ X.card) /
      (∑ X ∈ G.edgeFinset.powerset.filter
          (fun X : Finset (Sym2 ι) => ∀ v : ι, Even ((X.filter (v ∈ ·)).card)),
          Real.tanh (β * J) ^ X.card) :=
  correlation_high_temp_expansion_h_zero_closed G J β {i, j}

/-- **Magnetization at h = 0 vanishes via FV (3.46) handshake**:
specialization of `correlation_high_temp_h_zero_odd_card_eq_zero` (Step 298)
at `A = {i}`. Since `|{i}| = 1` is odd, the FV (3.46) numerator filter
is empty by handshake, so `⟨σ_i⟩ = 0`. -/
theorem correlation_high_temp_h_zero_at_singleton
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℝ) (i : ι) :
    correlation G ⟨J, 0, β⟩ ({i} : Finset ι) = 0 := by
  refine correlation_high_temp_h_zero_odd_card_eq_zero G J β {i} ?_
  rw [Finset.card_singleton]
  exact ⟨0, rfl⟩

/-- **Singleton vanish + ≤ 1 sandwich at h = 0**: trivial since the
correlation is exactly 0 at h = 0 (Z₂ symmetry). -/
theorem correlation_high_temp_h_zero_at_singleton_eq_zero_le_one
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (i : ι) :
    correlation G ⟨J, 0, β⟩ ({i} : Finset ι) = 0 ∧
      correlation G ⟨J, 0, β⟩ ({i} : Finset ι) ≤ 1 :=
  ⟨correlation_high_temp_h_zero_at_singleton G J β i,
   (correlation_high_temp_h_zero_at_singleton G J β i).symm ▸ zero_le_one⟩

/-- **Singleton magnetization under ferromagnetic at h = 0**:
under `0 ≤ J, 0 < β`, `⟨σ_i⟩_{β,0} = 0`. Trivial wrap of Step 331. -/
theorem correlation_high_temp_h_zero_at_singleton_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (_hJ : 0 ≤ J) (_hβ : 0 < β) (i : ι) :
    correlation G ⟨J, 0, β⟩ ({i} : Finset ι) = 0 :=
  correlation_high_temp_h_zero_at_singleton G J β i

/-- **Pair + singleton bundle at h = 0**: combines pair sandwich with
singleton vanishing in a single statement. -/
theorem correlation_high_temp_h_zero_at_pair_singleton_bundle
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (i j : ι) :
    correlation G ⟨J, 0, β⟩ ({i} : Finset ι) = 0 ∧
      0 ≤ correlation G ⟨J, 0, β⟩ ({i, j} : Finset ι) ∧
      correlation G ⟨J, 0, β⟩ ({i, j} : Finset ι) ≤ 1 :=
  ⟨correlation_high_temp_h_zero_at_singleton G J β i,
   correlation_high_temp_h_zero_at_pair_nonneg G J β hβJ i j,
   correlation_high_temp_h_zero_at_pair_le_one G J β i j⟩

/-- **Pair + singleton trivial-slices full bundle at h = 0**: at
`J = 0` and at `β = 0`, both pair and singleton correlations vanish.
Combines the pair and singleton trivial-slices facts. -/
theorem correlation_high_temp_h_zero_at_pair_singleton_trivial_slices_bundle
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (i j : ι) :
    correlation G ⟨0, 0, β⟩ ({i} : Finset ι) = 0 ∧
      correlation G ⟨J, 0, 0⟩ ({i} : Finset ι) = 0 ∧
      correlation G ⟨0, 0, β⟩ ({i, j} : Finset ι) = 0 ∧
      correlation G ⟨J, 0, 0⟩ ({i, j} : Finset ι) = 0 :=
  ⟨correlation_high_temp_h_zero_at_singleton_J_zero G β i,
   correlation_high_temp_h_zero_at_singleton_beta_zero G J i,
   correlation_high_temp_h_zero_at_pair_J_zero G β i j,
   correlation_high_temp_h_zero_at_pair_beta_zero G J i j⟩

/-- **Pair + singleton bundle under ferromagnetic at h = 0**: under
ferromagnetic parameters `⟨J, 0, β⟩` (i.e. `0 ≤ J, 0 < β`), packages
`⟨σ_i⟩ = 0`, `0 ≤ ⟨σ_iσ_j⟩`, and `⟨σ_iσ_j⟩ ≤ 1` into a single triple.
Bridges the `Ferromagnetic` typeclass and the bundle of Step 339 via
`mul_nonneg hβ.le hJ`. -/
theorem correlation_high_temp_h_zero_at_pair_singleton_bundle_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (i j : ι) :
    correlation G ⟨J, 0, β⟩ ({i} : Finset ι) = 0 ∧
      0 ≤ correlation G ⟨J, 0, β⟩ ({i, j} : Finset ι) ∧
      correlation G ⟨J, 0, β⟩ ({i, j} : Finset ι) ≤ 1 :=
  correlation_high_temp_h_zero_at_pair_singleton_bundle G J β
    (mul_nonneg hβ.le hJ) i j

/-- **Pair + singleton complete-summary bundle at h = 0**: a single
statement bundling all known §18.3 properties at `A ∈ {{i}, {i, j}}`:
  1. `⟨σ_iσ_j⟩ ≤ 1` (unconditional upper bound),
  2. `0 ≤ ⟨σ_iσ_j⟩` (sandwich lower under `0 ≤ β·J`),
  3. `⟨σ_i⟩ = 0` (singleton vanishing, unconditional via Z₂ symmetry),
  4. `⟨σ_iσ_j⟩^{⟨0,0,β⟩} = 0` (pair vanishing at trivial slice `J = 0`),
  5. `⟨σ_iσ_j⟩^{⟨J,0,0⟩} = 0` (pair vanishing at trivial slice `β = 0`).
Useful for downstream applications that want a single import for the
qualitative behaviour of pair / singleton correlations at `h = 0`. -/
theorem correlation_high_temp_h_zero_at_pair_singleton_complete_summary
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (i j : ι) :
    correlation G ⟨J, 0, β⟩ ({i, j} : Finset ι) ≤ 1 ∧
      0 ≤ correlation G ⟨J, 0, β⟩ ({i, j} : Finset ι) ∧
      correlation G ⟨J, 0, β⟩ ({i} : Finset ι) = 0 ∧
      correlation G ⟨0, 0, β⟩ ({i, j} : Finset ι) = 0 ∧
      correlation G ⟨J, 0, 0⟩ ({i, j} : Finset ι) = 0 :=
  ⟨correlation_high_temp_h_zero_at_pair_le_one G J β i j,
   correlation_high_temp_h_zero_at_pair_nonneg G J β hβJ i j,
   correlation_high_temp_h_zero_at_singleton G J β i,
   correlation_high_temp_h_zero_at_pair_J_zero G β i j,
   correlation_high_temp_h_zero_at_pair_beta_zero G J i j⟩


end IsingModel
