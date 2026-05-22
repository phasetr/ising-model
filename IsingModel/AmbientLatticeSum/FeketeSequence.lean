import IsingModel.AmbientLatticeSum.TendstoAtTop

namespace IsingModel

open Ambient

namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ## Fekete convergence from a `Finset V`-sequence (no `Exhaustion` required)

Drop the `Exhaustion V` requirement of `freeEnergyAlongExhaustion_tendsto_of_superadditive`.
Given only a sequence `B : ℕ → Finset V` with linear-growth cardinality
and `log Z` super-additivity, the free-energy-density sequence converges
via Fekete.

This unblocks concrete ℤ^d Prop 4.6.1 completion for "brick" /
"stripe" / "half-line" exhaustions that satisfy the linear-growth
hypotheses despite not covering all of `V` (so not an
`Exhaustion V` in the strict sense).

Reference: Glimm–Jaffe, *Quantum Physics* 2nd ed., §4.6 Prop 4.6.1,
p. 68 (Fekete step, generalised to arbitrary Finset sequences). -/

/-- **Fekete convergence for a general `Finset V`-sequence** (no
`Exhaustion` required). Given `B : ℕ → Finset V` with
`|B(m+n)| = |B m| + |B n|`, super-additivity of `log Z_{B n}`, a
finite-edge-set `Fintype` instance per stage, and uniform upper bound
on `freeEnergy (inducedGraph G (B n)) p`, the sequence
`n ↦ freeEnergy (inducedGraph G (B n)) p` converges.

Same proof skeleton as
`freeEnergyAlongExhaustion_tendsto_of_superadditive`, but factored
through a general sequence. -/
theorem freeEnergy_of_finset_sequence_tendsto_of_superadditive
    (G : SimpleGraph V) (B : ℕ → Finset V)
    [∀ n, Fintype (inducedGraph G (B n)).edgeSet]
    (p : IsingParams ℝ)
    (hcard_add : ∀ m n, (B (m + n)).card = (B m).card + (B n).card)
    (hsuper : ∀ m n, Real.log (partitionFunction (inducedGraph G (B m)) p)
                      + Real.log (partitionFunction (inducedGraph G (B n)) p)
                      ≤ Real.log (partitionFunction
                          (inducedGraph G (B (m + n))) p))
    (hbdd : BddAbove (Set.range
              (fun n => IsingModel.freeEnergy (inducedGraph G (B n)) p)))
    (hcard_one : (B 1).card ≠ 0) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n => IsingModel.freeEnergy (inducedGraph G (B n)) p)
      Filter.atTop (nhds L) := by
  set u : ℕ → ℝ :=
    fun n => -Real.log (partitionFunction (inducedGraph G (B n)) p) with hu_def
  have hsub : Subadditive u := by
    intro m n
    have := hsuper m n
    simp only [hu_def]
    linarith
  have hcard0 : (B 0).card = 0 := by
    have h : (B 0).card = (B 0).card + (B 0).card := by
      have := hcard_add 0 0; simpa using this
    omega
  have hcard_mul : ∀ n, (B n).card = n * (B 1).card := by
    intro n
    induction n with
    | zero => rw [hcard0, Nat.zero_mul]
    | succ n ih =>
      calc (B (n + 1)).card
          = (B n).card + (B 1).card := hcard_add n 1
        _ = n * (B 1).card + (B 1).card := by rw [ih]
        _ = (n + 1) * (B 1).card := by ring
  have hcard1_pos : (0 : ℝ) < ((B 1).card : ℝ) := by
    have : 0 < (B 1).card := Nat.pos_of_ne_zero hcard_one
    exact_mod_cast this
  have hcard1_ne : ((B 1).card : ℝ) ≠ 0 := hcard1_pos.ne'
  obtain ⟨C, hC⟩ := hbdd
  have hbdd_below : BddBelow (Set.range fun n : ℕ => u n / (n : ℝ)) := by
    refine ⟨-((B 1).card : ℝ) * max C 0, ?_⟩
    rintro _ ⟨n, rfl⟩
    change -((B 1).card : ℝ) * max C 0 ≤ u n / (n : ℝ)
    by_cases hn : n = 0
    · subst hn
      rw [Nat.cast_zero, div_zero]
      have hm : 0 ≤ max C 0 := le_max_right _ _
      have hc : 0 ≤ ((B 1).card : ℝ) := Nat.cast_nonneg _
      nlinarith
    · have hn' : 0 < n := Nat.pos_of_ne_zero hn
      have hn_real : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn'
      have hn_ne : (n : ℝ) ≠ 0 := hn_real.ne'
      have hcardn : ((B n).card : ℝ) = (n : ℝ) * ((B 1).card : ℝ) := by
        exact_mod_cast hcard_mul n
      have hfe_unfold :
          IsingModel.freeEnergy (inducedGraph G (B n)) p
            = (((B n).card : ℝ))⁻¹
              * Real.log (partitionFunction (inducedGraph G (B n)) p) := by
        unfold IsingModel.freeEnergy
        rw [Fintype.card_coe]
      have hfe_val : IsingModel.freeEnergy (inducedGraph G (B n)) p ≤ C :=
        hC ⟨n, rfl⟩
      have hrel : u n / (n : ℝ)
          = -((B 1).card : ℝ)
            * IsingModel.freeEnergy (inducedGraph G (B n)) p := by
        rw [hfe_unfold, hcardn]
        change -Real.log (partitionFunction (inducedGraph G (B n)) p)
            / (n : ℝ)
          = -((B 1).card : ℝ)
            * (((n : ℝ) * ((B 1).card : ℝ))⁻¹
              * Real.log (partitionFunction (inducedGraph G (B n)) p))
        field_simp
      rw [hrel]
      have hmax : IsingModel.freeEnergy (inducedGraph G (B n)) p ≤ max C 0 :=
        hfe_val.trans (le_max_left _ _)
      nlinarith
  have htendsto_quot : Filter.Tendsto (fun n => u n / (n : ℝ)) Filter.atTop
      (nhds hsub.lim) :=
    hsub.tendsto_lim hbdd_below
  set L : ℝ := -hsub.lim / ((B 1).card : ℝ) with hL_def
  refine ⟨L, ?_⟩
  have htendsto_target : Filter.Tendsto
      (fun n => -(u n / (n : ℝ)) / ((B 1).card : ℝ))
      Filter.atTop (nhds L) := by
    rw [hL_def]
    exact (htendsto_quot.neg).div_const _
  refine htendsto_target.congr' ?_
  refine (Filter.eventually_ge_atTop 1).mono ?_
  intro n hn
  have hn_pos : 0 < n := hn
  have hn_real : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
  have hn_ne : (n : ℝ) ≠ 0 := hn_real.ne'
  have hcardn : ((B n).card : ℝ) = (n : ℝ) * ((B 1).card : ℝ) := by
    exact_mod_cast hcard_mul n
  have hfe_unfold :
      IsingModel.freeEnergy (inducedGraph G (B n)) p
        = (((B n).card : ℝ))⁻¹
          * Real.log (partitionFunction (inducedGraph G (B n)) p) := by
    unfold IsingModel.freeEnergy
    rw [Fintype.card_coe]
  change -(u n / (n : ℝ)) / ((B 1).card : ℝ)
      = IsingModel.freeEnergy (inducedGraph G (B n)) p
  rw [hfe_unfold, hcardn]
  simp only [hu_def]
  field_simp

end Ambient

end IsingModel
