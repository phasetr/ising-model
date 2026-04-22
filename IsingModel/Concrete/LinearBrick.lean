import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Concrete.IntLattice
import IsingModel.TranslationInvariance
import IsingModel.AmbientLatticeSum

/-!
# 1D linear brick on `latticeGraph 1` (§4.6 Prop 4.6.1 concrete ℤ instance)

Concrete application of
`freeEnergy_of_finset_sequence_tendsto_of_superadditive` (PR #638) to
the 1D linear-brick exhaustion of `latticeGraph 1 : SimpleGraph (Fin 1 → ℤ)`.
Provides the first concrete ℤ^d Ising Prop 4.6.1 convergence at general
ferromagnetic parameters (beyond the J = 0 / β = 0 trivial slices).

## Main definitions

* `linearBox (n : ℕ) : Finset (Fin 1 → ℤ)` — a 1D-line block of `n`
  points along coordinate 0. Cardinality is `n`.

## Main results

* `linearBox_card`, `linearBox_card_add` — cardinality is linear.
* `linearBox_disjoint_shift`, `linearBox_union_shift` — the union
  decomposition `linearBox (m + n) = linearBox m ∪ (shift_m +ᵥ linearBox n)`.

## References

* Glimm–Jaffe, *Quantum Physics* 2nd ed., §4.6 Prop 4.6.1, p. 68.
-/

namespace IsingModel

namespace Concrete

/-- **Linear brick** on `Fin 1 → ℤ`: the Finset of `n` points
`{fun _ => k | k ∈ Finset.Ico 0 n}`. Contiguous 1D line of length `n`
starting at the origin. -/
noncomputable def linearBox (n : ℕ) : Finset (Fin 1 → ℤ) :=
  Fintype.piFinset (fun _ : Fin 1 => Finset.Ico (0 : ℤ) (n : ℤ))

/-- **Cardinality of `linearBox n`** equals `n`. -/
theorem linearBox_card (n : ℕ) : (linearBox n).card = n := by
  unfold linearBox
  rw [Fintype.card_piFinset]
  simp [Int.card_Ico]

/-- **Additive cardinality**: `|linearBox (m + n)| = |linearBox m| + |linearBox n|`.
Foundation for the `hcard_add` hypothesis of
`freeEnergy_of_finset_sequence_tendsto_of_superadditive`. -/
theorem linearBox_card_add (m n : ℕ) :
    (linearBox (m + n)).card = (linearBox m).card + (linearBox n).card := by
  rw [linearBox_card, linearBox_card, linearBox_card]

/-- **Non-degeneracy of the base step**: `|linearBox 1| = 1 ≠ 0`. -/
theorem linearBox_one_card_ne_zero : (linearBox 1).card ≠ 0 := by
  rw [linearBox_card]; decide

/-- **Membership characterisation**: `v ∈ linearBox n ↔ 0 ≤ v 0 ∧ v 0 < n`. -/
theorem mem_linearBox {n : ℕ} {v : Fin 1 → ℤ} :
    v ∈ linearBox n ↔ 0 ≤ v 0 ∧ v 0 < (n : ℤ) := by
  unfold linearBox
  rw [Fintype.mem_piFinset]
  constructor
  · intro h
    have := h 0
    rw [Finset.mem_Ico] at this
    exact this
  · intro ⟨h1, h2⟩ i
    fin_cases i
    rw [Finset.mem_Ico]
    exact ⟨h1, h2⟩

/-- **Disjointness of shifted linear bricks**: `linearBox m` and the
`m`-shift of `linearBox n` (along direction 0) are disjoint. -/
theorem linearBox_disjoint_shift (m n : ℕ) :
    Disjoint (linearBox m)
      (Ambient.vaddFinset ((fun _ : Fin 1 => (m : ℤ)) : Fin 1 → ℤ) (linearBox n)) := by
  rw [Finset.disjoint_left]
  intro v hvm hvs
  rw [Ambient.mem_vaddFinset] at hvs
  obtain ⟨w, hw, hwv⟩ := hvs
  rw [mem_linearBox] at hvm
  rw [mem_linearBox] at hw
  -- hwv : (fun _ => (m : ℤ)) +ᵥ w = v, i.e., v 0 = m + w 0
  have hv0 : v 0 = (m : ℤ) + w 0 := by
    have : ((fun _ : Fin 1 => (m : ℤ)) +ᵥ w) 0 = v 0 := congrArg (· 0) hwv
    simp [vadd_eq_add] at this
    linarith
  omega

/-- **Union decomposition**:
`linearBox m ∪ (shift_m +ᵥ linearBox n) = linearBox (m + n)`. -/
theorem linearBox_union_shift (m n : ℕ) :
    linearBox m ∪
        Ambient.vaddFinset ((fun _ : Fin 1 => (m : ℤ)) : Fin 1 → ℤ) (linearBox n)
      = linearBox (m + n) := by
  ext v
  simp only [Finset.mem_union, Ambient.mem_vaddFinset, mem_linearBox]
  constructor
  · rintro (hleft | ⟨w, hw, hwv⟩)
    · refine ⟨hleft.1, ?_⟩
      have hmn : (m : ℤ) ≤ (m + n : ℕ) := by push_cast; linarith
      exact lt_of_lt_of_le hleft.2 hmn
    · have hv0 : v 0 = (m : ℤ) + w 0 := by
        have : ((fun _ : Fin 1 => (m : ℤ)) +ᵥ w) 0 = v 0 := congrArg (· 0) hwv
        simp [vadd_eq_add] at this
        linarith
      refine ⟨?_, ?_⟩
      · rw [hv0]; linarith [hw.1]
      · rw [hv0]; push_cast; linarith [hw.2]
  · rintro ⟨h1, h2⟩
    by_cases hcase : v 0 < (m : ℤ)
    · left; exact ⟨h1, hcase⟩
    · right
      push Not at hcase
      refine ⟨fun _ : Fin 1 => v 0 - (m : ℤ), ⟨?_, ?_⟩, ?_⟩
      · linarith
      · push_cast at h2; linarith
      · funext i
        fin_cases i
        simp [vadd_eq_add]

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

/-! ## Named infinite-volume limit and J=0 closed form -/

/-- **Infinite-volume free-energy density along the 1D linearBox
sequence**. The `Classical.choose` witness of
`freeEnergy_linearBox_tendsto`, pinning down the Fekete limit value. -/
noncomputable def freeEnergyInfinite_linearBox
    (p : IsingParams ℝ) (hf : Ferromagnetic p) : ℝ :=
  Classical.choose (freeEnergy_linearBox_tendsto p hf)

/-- **Convergence to the named limit**: the 1D linearBox
free-energy-density sequence converges to `freeEnergyInfinite_linearBox p hf`. -/
theorem freeEnergy_linearBox_tendsto_freeEnergyInfinite
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    Filter.Tendsto
      (fun n => IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph 1) (linearBox n)) p)
      Filter.atTop (nhds (freeEnergyInfinite_linearBox p hf)) :=
  Classical.choose_spec (freeEnergy_linearBox_tendsto p hf)

/-- **`linearBox n` is nonempty** when `n ≥ 1`. Derived from
`linearBox_card = n`. -/
theorem linearBox_nonempty {n : ℕ} (hn : 1 ≤ n) : (linearBox n).Nonempty := by
  rw [← Finset.card_pos, linearBox_card]; exact hn

/-- **J=0 closed form for the 1D linearBox infinite-volume free-energy
density**: `freeEnergyInfinite_linearBox ⟨0, h, β⟩ hf = log(2·cosh(β·h))`
under ferromagnetic `0 ≤ h, 0 < β`. Parallel to PR #647. -/
theorem freeEnergyInfinite_linearBox_J_zero
    {h β : ℝ} (hh : 0 ≤ h) (hβ : 0 < β) :
    freeEnergyInfinite_linearBox
        (⟨0, h, β⟩ : IsingParams ℝ) ⟨le_refl 0, hh, hβ⟩
      = Real.log (2 * Real.cosh (β * h)) := by
  have hconst : Filter.Tendsto
      (fun n => IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph 1) (linearBox n))
          (⟨0, h, β⟩ : IsingParams ℝ))
      Filter.atTop (nhds (Real.log (2 * Real.cosh (β * h)))) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hne : (linearBox n).Nonempty := linearBox_nonempty hn
    have hpos : 0 < Fintype.card (↑(linearBox n) : Type _) := by
      rw [Fintype.card_coe]; exact Finset.card_pos.mpr hne
    exact (IsingModel.freeEnergy_J_zero _ h β hpos).symm
  exact tendsto_nhds_unique
    (freeEnergy_linearBox_tendsto_freeEnergyInfinite _ _) hconst

/-- **Infinite-volume lower bound** `log 2 ≤ freeEnergyInfinite_linearBox`
for ferromagnetic `0 ≤ J, 0 ≤ h, 0 < β`. Transports the per-stage
`freeEnergy_ge_log_two_of_ferromagnetic` through the Fekete limit. -/
theorem freeEnergyInfinite_linearBox_ge_log_two
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) :
    Real.log 2
      ≤ freeEnergyInfinite_linearBox (⟨J, h, β⟩ : IsingParams ℝ) ⟨hJ, hh, hβ⟩ := by
  refine ge_of_tendsto (freeEnergy_linearBox_tendsto_freeEnergyInfinite _ _) ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hne : (linearBox n).Nonempty := linearBox_nonempty hn
  have hpos : 0 < Fintype.card (↑(linearBox n) : Type _) := by
    rw [Fintype.card_coe]; exact Finset.card_pos.mpr hne
  exact IsingModel.freeEnergy_ge_log_two_of_ferromagnetic _ _ ⟨hJ, hh, hβ⟩ hpos

/-- **Infinite-volume upper bound**
`freeEnergyInfinite_linearBox ≤ log 2 + |β|·(|J| + |h|)`. Transports
the per-stage `linearBox_freeEnergy_le` through the Fekete limit. -/
theorem freeEnergyInfinite_linearBox_le
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    freeEnergyInfinite_linearBox p hf
      ≤ Real.log 2 + |p.β| * (|p.J| + |p.h|) := by
  refine le_of_tendsto (freeEnergy_linearBox_tendsto_freeEnergyInfinite p hf) ?_
  filter_upwards with n
  exact linearBox_freeEnergy_le n p

/-- **Infinite-volume sandwich** on the 1D linearBox (ferromagnetic):
`log 2 ≤ freeEnergyInfinite_linearBox ≤ log 2 + |β|·(|J| + |h|)`. -/
theorem freeEnergyInfinite_linearBox_sandwich
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) :
    Real.log 2
        ≤ freeEnergyInfinite_linearBox
            (⟨J, h, β⟩ : IsingParams ℝ) ⟨hJ, hh, hβ⟩
    ∧ freeEnergyInfinite_linearBox
            (⟨J, h, β⟩ : IsingParams ℝ) ⟨hJ, hh, hβ⟩
        ≤ Real.log 2 + |β| * (|J| + |h|) :=
  ⟨freeEnergyInfinite_linearBox_ge_log_two hJ hh hβ,
   freeEnergyInfinite_linearBox_le _ ⟨hJ, hh, hβ⟩⟩

/-- **Translation-invariance of the Fekete limit** on the 1D
linearBox: any coord-shift of the linearBox sequence converges to the
same `freeEnergyInfinite_linearBox p hf`. -/
theorem freeEnergyInfinite_linearBox_tendsto_shift
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (t : Fin 1 → ℤ) :
    Filter.Tendsto
      (fun n => IsingModel.freeEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph 1)
          (Ambient.vaddFinset t (linearBox n))) p)
      Filter.atTop (nhds (freeEnergyInfinite_linearBox p hf)) := by
  refine (freeEnergy_linearBox_tendsto_freeEnergyInfinite p hf).congr ?_
  intro n
  exact (Ambient.freeEnergyΛ_vaddFinset_eq
    (IsingModel.latticeGraph 1) t (linearBox n) p).symm

/-- **Nonnegativity** of `freeEnergyInfinite_linearBox` under
ferromagnetic parameters. Transport per-stage
`freeEnergy_nonneg_of_ferromagnetic` through the Fekete limit. -/
theorem freeEnergyInfinite_linearBox_nonneg
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    0 ≤ freeEnergyInfinite_linearBox p hf := by
  refine ge_of_tendsto (freeEnergy_linearBox_tendsto_freeEnergyInfinite p hf) ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hne : (linearBox n).Nonempty := linearBox_nonempty hn
  have hpos : 0 < Fintype.card (↑(linearBox n) : Type _) := by
    rw [Fintype.card_coe]; exact Finset.card_pos.mpr hne
  exact IsingModel.freeEnergy_nonneg_of_ferromagnetic _ p hf hpos

/-- **Tighter lower bound** `log(2·cosh(β·h)) ≤ freeEnergyInfinite_linearBox`
under ferromagnetic `0 ≤ J, 0 ≤ h, 0 < β`. Sharper than
`freeEnergyInfinite_linearBox_ge_log_two` (PR #650) when `h > 0`. -/
theorem freeEnergyInfinite_linearBox_ge_log_two_cosh
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) :
    Real.log (2 * Real.cosh (β * h))
      ≤ freeEnergyInfinite_linearBox
          (⟨J, h, β⟩ : IsingParams ℝ) ⟨hJ, hh, hβ⟩ := by
  refine ge_of_tendsto
    (freeEnergy_linearBox_tendsto_freeEnergyInfinite _ ⟨hJ, hh, hβ⟩) ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hne : (linearBox n).Nonempty := linearBox_nonempty hn
  have hpos : 0 < Fintype.card (↑(linearBox n) : Type _) := by
    rw [Fintype.card_coe]; exact Finset.card_pos.mpr hne
  exact IsingModel.freeEnergy_ge_log_two_cosh _ hJ hh hβ hpos

/-- **Cosh-form sandwich** on the 1D linearBox: combines the tighter
`log(2·cosh(β·h))` lower bound with the upper bound `log 2 + |β|·(|J| + |h|)`. -/
theorem freeEnergyInfinite_linearBox_sandwich_cosh
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) :
    Real.log (2 * Real.cosh (β * h))
        ≤ freeEnergyInfinite_linearBox
            (⟨J, h, β⟩ : IsingParams ℝ) ⟨hJ, hh, hβ⟩
    ∧ freeEnergyInfinite_linearBox
            (⟨J, h, β⟩ : IsingParams ℝ) ⟨hJ, hh, hβ⟩
        ≤ Real.log 2 + |β| * (|J| + |h|) :=
  ⟨freeEnergyInfinite_linearBox_ge_log_two_cosh hJ hh hβ,
   freeEnergyInfinite_linearBox_le _ ⟨hJ, hh, hβ⟩⟩

end Concrete

end IsingModel
