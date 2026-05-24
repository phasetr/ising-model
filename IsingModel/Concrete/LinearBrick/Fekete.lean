import IsingModel.Concrete.LinearBrick.Geometry

namespace IsingModel

namespace Concrete

/-! ## Super-additivity, `BddAbove`, and Fekete convergence on the 1D brick

With the combinatorial foundation above, apply the generic-Finset
Fekete theorem
`Ambient.freeEnergy_of_finset_sequence_tendsto_of_superadditive`
(PR #638) to conclude concrete Prop 4.6.1 convergence on the 1D
linear brick. -/

-- A `Fintype ((Ambient.inducedGraph (latticeGraph 1) Λ).edgeSet)` instance is
-- already available via the auto-derived `Ambient.instFintype...` (see
-- `Ambient.inducedLatticeGraph_card_edgeFinset_le`), so no local instance is
-- introduced here.

/-- **Super-additivity of `log Z` on the 1D brick** (ferromagnetic): for
every `m n : ℕ`,
`log Z_{linearBox m} + log Z_{linearBox n} ≤ log Z_{linearBox (m + n)}`.

Combines `log_partitionFunction_inducedGraph_disjUnion_super_additive`
(on the disjoint union `linearBox m` + `m`-shift of `linearBox n`)
with translation invariance (`partitionFunctionΛ_vaddFinset_eq` on the
shifted brick) and `linearBox_union_shift` (identifying the union with
`linearBox (m + n)`). -/
theorem log_partitionFunctionΛ_linearBox_super_additive
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (m n : ℕ) :
    Real.log (Ambient.partitionFunctionΛ
              (IsingModel.latticeGraph 1) (linearBox m) p)
        + Real.log (Ambient.partitionFunctionΛ
              (IsingModel.latticeGraph 1) (linearBox n) p)
      ≤ Real.log (Ambient.partitionFunctionΛ
              (IsingModel.latticeGraph 1) (linearBox (m + n)) p) := by
  -- Identify `log Z_{m-shifted linearBox n}` with `log Z_{linearBox n}` via
  -- translation invariance.
  set shift_m : Fin 1 → ℤ := fun _ => (m : ℤ) with hshift
  have hTI : Ambient.partitionFunctionΛ (IsingModel.latticeGraph 1)
      (Ambient.vaddFinset shift_m (linearBox n)) p
        = Ambient.partitionFunctionΛ (IsingModel.latticeGraph 1)
              (linearBox n) p :=
    Ambient.partitionFunctionΛ_vaddFinset_eq (IsingModel.latticeGraph 1)
      shift_m (linearBox n) p
  -- Apply disjoint-union super-additivity on `linearBox m` and the shifted brick.
  have hunion := linearBox_union_shift m n
  have hdisj := linearBox_disjoint_shift m n
  have hsup := Ambient.log_partitionFunctionΛ_disjUnion_super_additive
    (IsingModel.latticeGraph 1) (Λ₁ := linearBox m)
    (Λ₂ := Ambient.vaddFinset shift_m (linearBox n)) hdisj p hf
  -- Bridge `log Z(union)` to `log Z(linearBox (m + n))` via the
  -- subsingleton-congruence lemma, then combine numerically with `linarith`.
  have hlog_shift : Real.log (Ambient.partitionFunctionΛ
        (IsingModel.latticeGraph 1)
        (Ambient.vaddFinset shift_m (linearBox n)) p)
      = Real.log (Ambient.partitionFunctionΛ
        (IsingModel.latticeGraph 1) (linearBox n) p) :=
    congrArg Real.log hTI
  have hlog_union : Real.log (Ambient.partitionFunctionΛ
        (IsingModel.latticeGraph 1)
        (linearBox m ∪ Ambient.vaddFinset shift_m (linearBox n)) p)
      = Real.log (Ambient.partitionFunctionΛ
        (IsingModel.latticeGraph 1) (linearBox (m + n)) p) :=
    congrArg Real.log (Ambient.partitionFunctionΛ_congr_finset
      (IsingModel.latticeGraph 1) hunion p)
  linarith [hsup, hlog_shift, hlog_union]

/-- **Per-stage uniform free-energy upper bound** on the 1D brick
(ferromagnetic): for every `n : ℕ`,
`freeEnergy (inducedGraph (latticeGraph 1) (linearBox n)) p ≤
 log 2 + |β|·(|J| + |h|)`.

Via `freeEnergy_upper_bound` applied per stage, combined with the
edge-count bound `Ambient.inducedLatticeGraph_card_edgeFinset_le` at `d = 1`
(= `|E| ≤ 1 · |Λ|`). -/
theorem linearBox_freeEnergy_le (n : ℕ) (p : IsingParams ℝ) :
    IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph 1) (linearBox n)) p
      ≤ Real.log 2 + |p.β| * (|p.J| + |p.h|) := by
  by_cases hn : n = 0
  · subst hn
    -- At `n = 0`, `linearBox 0 = ∅`, so `Fintype.card = 0` and `freeEnergy = 0`.
    have hcard : Fintype.card (↑(linearBox 0) : Type _) = 0 := by
      rw [Fintype.card_coe, linearBox_card]
    have hfe : IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph 1) (linearBox 0)) p = 0 := by
      unfold IsingModel.freeEnergy
      rw [hcard, Nat.cast_zero, inv_zero, zero_mul]
    rw [hfe]
    have h1 : (0 : ℝ) ≤ |p.β| * (|p.J| + |p.h|) := by positivity
    have h2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    linarith
  · have hn' : 0 < n := Nat.pos_of_ne_zero hn
    have hcardpos : 0 < Fintype.card (↑(linearBox n) : Type _) := by
      rw [Fintype.card_coe, linearBox_card]; exact hn'
    have hub := IsingModel.freeEnergy_upper_bound
      (Ambient.inducedGraph (IsingModel.latticeGraph 1) (linearBox n)) p hcardpos
    have hE := Ambient.inducedLatticeGraph_card_edgeFinset_le 1 (linearBox n)
    have hN_pos : (0 : ℝ) < (Fintype.card (↑(linearBox n) : Type _) : ℝ) := by
      exact_mod_cast hcardpos
    have hone : ((1 : ℕ) : ℝ) = (1 : ℝ) := by norm_cast
    rw [hone, one_mul] at hE
    -- Abbreviations: `N := vertex count`, `E := edge count` (as reals).
    -- Inline arithmetic: bound numerator, then fraction, then use `hub`.
    have hJabs_nn : (0 : ℝ) ≤ |p.J| := abs_nonneg _
    have hbeta_nn : (0 : ℝ) ≤ |p.β| := abs_nonneg _
    have hJE : |p.J| *
        ((Ambient.inducedGraph (IsingModel.latticeGraph 1)
          (linearBox n)).edgeFinset.card : ℝ)
        ≤ |p.J| * (Fintype.card (↑(linearBox n) : Type _) : ℝ) :=
      mul_le_mul_of_nonneg_left hE hJabs_nn
    have hnum : |p.J| *
        ((Ambient.inducedGraph (IsingModel.latticeGraph 1)
          (linearBox n)).edgeFinset.card : ℝ)
        + |p.h| * (Fintype.card (↑(linearBox n) : Type _) : ℝ)
        ≤ (|p.J| + |p.h|) * (Fintype.card (↑(linearBox n) : Type _) : ℝ) := by
      nlinarith [hJE]
    have hfrac : |p.β| *
        (|p.J| *
          ((Ambient.inducedGraph (IsingModel.latticeGraph 1)
            (linearBox n)).edgeFinset.card : ℝ)
          + |p.h| * (Fintype.card (↑(linearBox n) : Type _) : ℝ))
        / (Fintype.card (↑(linearBox n) : Type _) : ℝ)
          ≤ |p.β| * (|p.J| + |p.h|) := by
      rw [div_le_iff₀ hN_pos]
      calc |p.β| *
            (|p.J| *
              ((Ambient.inducedGraph (IsingModel.latticeGraph 1)
                (linearBox n)).edgeFinset.card : ℝ)
              + |p.h| * (Fintype.card (↑(linearBox n) : Type _) : ℝ))
          ≤ |p.β| *
              ((|p.J| + |p.h|) *
                (Fintype.card (↑(linearBox n) : Type _) : ℝ)) :=
            mul_le_mul_of_nonneg_left hnum hbeta_nn
        _ = |p.β| * (|p.J| + |p.h|)
              * (Fintype.card (↑(linearBox n) : Type _) : ℝ) := by ring
    linarith [hub, hfrac]

/-- **`BddAbove` of `freeEnergy` on the 1D brick** (ferromagnetic):
the free-energy-density sequence `n ↦ freeEnergy_{linearBox n}` is
bounded above by `log 2 + |β|·(|J| + |h|)`, independent of `n`.

Wrapper around `linearBox_freeEnergy_le`. -/
theorem freeEnergy_linearBox_bddAbove (p : IsingParams ℝ) :
    BddAbove (Set.range
      (fun n => IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph 1) (linearBox n)) p)) := by
  refine ⟨Real.log 2 + |p.β| * (|p.J| + |p.h|), ?_⟩
  rintro _ ⟨n, rfl⟩
  exact linearBox_freeEnergy_le n p

/-- **Concrete ℤ 1D Ising free-energy-density Fekete convergence**
(GJ §4.6 Prop 4.6.1 at general ferromagnetic parameters): for any
ferromagnetic `p`, the sequence
`n ↦ freeEnergy (inducedGraph (latticeGraph 1) (linearBox n)) p`
converges.

Apply `Ambient.freeEnergy_of_finset_sequence_tendsto_of_superadditive`
(PR #638) with the combinatorial inputs
`linearBox_card_add`, `log_partitionFunctionΛ_linearBox_super_additive`,
`freeEnergy_linearBox_bddAbove`, and `linearBox_one_card_ne_zero`. -/
theorem freeEnergy_linearBox_tendsto
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n => IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph 1) (linearBox n)) p)
      Filter.atTop (nhds L) :=
  Ambient.freeEnergy_of_finset_sequence_tendsto_of_superadditive
    (IsingModel.latticeGraph 1) linearBox p
    linearBox_card_add
    (log_partitionFunctionΛ_linearBox_super_additive p hf)
    (freeEnergy_linearBox_bddAbove p)
    linearBox_one_card_ne_zero


end Concrete

end IsingModel
