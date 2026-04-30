import IsingModel.AmbientLattice.MagnetizationInfinite

/-!
# Spontaneous magnetization and spontaneous correlation

Definitions and properties of the spontaneous magnetization
`spontaneousMagnetization` (infimum of `magnetizationInfinite` as `h → 0⁺`)
and the spontaneous correlation function `spontaneousCorrelation`.

## References

* Glimm–Jaffe, *Quantum Physics*, §5.1–5.4.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-! ## Spontaneous magnetization

Define the spontaneous magnetization
$m^*(G, \Lambda; J, \beta; i) := \lim_{h \to 0^+} M^{\mathrm{FM}}(J, h, \beta; i)$
as the infimum over `h > 0` of `magnetizationInfinite`.  Since
`magnetizationInfinite` is monotone in `h` on `Set.Ici 0` (PR #95) and
bounded below by `0` (ferromagnetic, PR #98), the right-limit at `h = 0`
equals this infimum.

Reference: Glimm–Jaffe §5.1 p. 77. Friedli–Velenik §3.10 (self-consistent
magnetization). -/

/-! ## Spontaneous correlation function (general `A`)

Generalize `spontaneousMagnetization` (single-site, `A = {i}`) to an
arbitrary finite set `A : Finset V`.  Same infimum-form over `h > 0`,
derived from PR #91–#100's `correlationInfinite` API. -/

/-- **Spontaneous correlation function** (infimum form):
`spontaneousCorrelation G Λ J β A := ⨅ h : ↥(Set.Ioi 0), correlationInfinite G Λ ⟨J, h, β⟩ A`.

Generalization of `spontaneousMagnetization` to arbitrary `A : Finset V`.
For $A = \{i\}$, coincides with `spontaneousMagnetization` by definition. -/
noncomputable def spontaneousCorrelation
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (A : Finset V) : ℝ :=
  ⨅ h : ↥(Set.Ioi (0 : ℝ)), correlationInfinite G Λ ⟨J, h.val, β⟩ A

/-- **Unfolding of `spontaneousCorrelation`** as a named identity:
`spontaneousCorrelation G Λ J β A = ⨅ h ∈ Ioi 0, correlationInfinite G Λ ⟨J, h, β⟩ A`. -/
theorem spontaneousCorrelation_apply
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (A : Finset V) :
    spontaneousCorrelation G Λ J β A
      = ⨅ h : ↥(Set.Ioi (0 : ℝ)), correlationInfinite G Λ ⟨J, h.val, β⟩ A :=
  rfl

/-- **Bounded-below witness** for `spontaneousCorrelation`: the family
`h ↦ correlationInfinite G Λ ⟨J, h, β⟩ A` over `Set.Ioi 0` is bounded
below by `0` (ferromagnetic). -/
theorem correlationInfinite_bddBelow_on_Ioi
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (A : Finset V) :
    BddBelow (Set.range
      (fun h : ↥(Set.Ioi (0 : ℝ)) =>
        correlationInfinite G Λ ⟨J, h.val, β⟩ A)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨h, rfl⟩
  exact correlationInfinite_nonneg G Λ ⟨J, h.val, β⟩
    ⟨hJ, le_of_lt h.property, hβ⟩ A

/-- **Nonnegativity** (ferromagnetic): $\langle \sigma^A \rangle^* \ge 0$. -/
theorem spontaneousCorrelation_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (A : Finset V) :
    0 ≤ spontaneousCorrelation G Λ J β A := by
  refine le_ciInf ?_
  rintro h
  exact correlationInfinite_nonneg G Λ ⟨J, h.val, β⟩
    ⟨hJ, le_of_lt h.property, hβ⟩ A

/-- **Upper bound**: $\langle \sigma^A \rangle^* \le 1$. -/
theorem spontaneousCorrelation_le_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (A : Finset V) :
    spontaneousCorrelation G Λ J β A ≤ 1 := by
  refine ciInf_le_of_le
    (correlationInfinite_bddBelow_on_Ioi G Λ hJ hβ A)
    ⟨1, by norm_num⟩ ?_
  exact correlationInfinite_le_one G Λ ⟨J, 1, β⟩ A

/-- **`-1 ≤ spontaneousCorrelation`** (ferromagnetic). Follows from
`spontaneousCorrelation_nonneg`. -/
theorem neg_one_le_spontaneousCorrelation
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (A : Finset V) :
    -1 ≤ spontaneousCorrelation G Λ J β A := by
  have := spontaneousCorrelation_nonneg G Λ hJ hβ A
  linarith

/-- **`|spontaneousCorrelation| ≤ 1`** (ferromagnetic). -/
theorem abs_spontaneousCorrelation_le_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (A : Finset V) :
    |spontaneousCorrelation G Λ J β A| ≤ 1 :=
  abs_le.mpr ⟨neg_one_le_spontaneousCorrelation G Λ hJ hβ A,
    spontaneousCorrelation_le_one G Λ hJ hβ A⟩

/-- **`spontaneousCorrelation² ≤ 1`** (ferromagnetic). -/
theorem spontaneousCorrelation_sq_le_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (A : Finset V) :
    spontaneousCorrelation G Λ J β A ^ 2 ≤ 1 := by
  have h := abs_spontaneousCorrelation_le_one G Λ hJ hβ A
  have : |spontaneousCorrelation G Λ J β A| ^ 2 ≤ 1 ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) h 2
  simpa [sq_abs] using this

/-- **Lower bound by `correlationInfinite` at positive `h`**: for any
`h > 0`, $\langle \sigma^A \rangle^* \le \langle \sigma^A \rangle(h)$. -/
theorem spontaneousCorrelation_le_correlationInfinite
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β)
    {h : ℝ} (hh : 0 < h) (A : Finset V) :
    spontaneousCorrelation G Λ J β A
      ≤ correlationInfinite G Λ ⟨J, h, β⟩ A :=
  ciInf_le
    (correlationInfinite_bddBelow_on_Ioi G Λ hJ hβ A)
    ⟨h, hh⟩

/-- **Exhaustion-independence**: $\langle \sigma^A \rangle^*$ does not
depend on the choice of exhaustion. -/
theorem spontaneousCorrelation_indep_exhaustion
    (G : SimpleGraph V) (Λ Λ' : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Fintype (inducedGraph G (Λ'.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (A : Finset V) :
    spontaneousCorrelation G Λ J β A
      = spontaneousCorrelation G Λ' J β A := by
  unfold spontaneousCorrelation
  congr 1
  funext h
  exact correlationInfinite_indep_exhaustion G Λ Λ' ⟨J, h.val, β⟩
    ⟨hJ, le_of_lt h.property, hβ⟩ A

/-- **Right-limit Tendsto**: for ferromagnetic Ising, the general-`A`
`correlationInfinite ⟨J, h, β⟩ A` tends to `spontaneousCorrelation` as
`h → 0⁺`. Analogous to
`tendsto_magnetizationInfinite_spontaneousMagnetization_nhdsGT`. -/
theorem tendsto_correlationInfinite_spontaneousCorrelation_nhdsGT
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (A : Finset V) :
    Filter.Tendsto
      (fun h : ℝ => correlationInfinite G Λ ⟨J, h, β⟩ A)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (spontaneousCorrelation G Λ J β A)) := by
  set f : ℝ → ℝ := fun h => correlationInfinite G Λ ⟨J, h, β⟩ A with hf_def
  have hmono : MonotoneOn f (Set.Ioi 0) := by
    have hmono_Ici : MonotoneOn f (Set.Ici 0) :=
      correlationInfinite_monotone_h G Λ hJ hβ A
    exact hmono_Ici.mono Set.Ioi_subset_Ici_self
  have hbdd : BddBelow (f '' Set.Ioi 0) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨h, hh, rfl⟩
    exact correlationInfinite_nonneg G Λ ⟨J, h, β⟩
      ⟨hJ, le_of_lt hh, hβ⟩ A
  have htendsto := hmono.tendsto_nhdsGT hbdd
  have hsInf : sInf (f '' Set.Ioi 0) = spontaneousCorrelation G Λ J β A := by
    unfold spontaneousCorrelation
    rw [← sInf_range, ← Set.image_univ]
    congr 1
    ext y
    simp [hf_def, Set.image_univ, Set.mem_image, Set.mem_Ioi, Subtype.exists]
  rw [← hsInf]
  exact htendsto

/-! ## Spontaneous magnetization (single-site specialization)

`spontaneousMagnetization` is the single-site case `A = {i}` of
`spontaneousCorrelation`.  All basic properties are one-line
specializations.

Reference: Glimm–Jaffe §5.1 p. 77 (the order parameter $m^*$
distinguishing ordered/disordered phases). -/

/-- **Spontaneous magnetization at infinite volume** (*infimum form*):
for ferromagnetic Ising on an ambient type `V`, exhaustion `Λ`, and
fixed `J, β`,
`spontaneousMagnetization G Λ J β i := spontaneousCorrelation G Λ J β {i}`.

This is the order parameter $m^*$.  Since `magnetizationInfinite` is
monotone in `h` on `Set.Ici 0` and bounded in `[0, 1]`, this infimum
coincides with $\lim_{h \to 0^+} M(h)$
(`tendsto_magnetizationInfinite_spontaneousMagnetization_nhdsGT`). -/
noncomputable def spontaneousMagnetization
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (i : V) : ℝ :=
  spontaneousCorrelation G Λ J β {i}

/-- **Unfolding of `spontaneousMagnetization`**:
`spontaneousMagnetization G Λ J β i = spontaneousCorrelation G Λ J β {i}`. -/
theorem spontaneousMagnetization_apply
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (i : V) :
    spontaneousMagnetization G Λ J β i = spontaneousCorrelation G Λ J β {i} :=
  rfl

/-- **Agreement at singletons**: `spontaneousCorrelation` on `{i}`
equals `spontaneousMagnetization`. Holds by definition. -/
theorem spontaneousCorrelation_singleton_eq_spontaneousMagnetization
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (i : V) :
    spontaneousCorrelation G Λ J β {i}
      = spontaneousMagnetization G Λ J β i :=
  rfl

/-- **Nonnegativity of `spontaneousMagnetization`** (ferromagnetic):
$m^* \ge 0$.  Specialization of `spontaneousCorrelation_nonneg` at
`A = {i}`. -/
theorem spontaneousMagnetization_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (i : V) :
    0 ≤ spontaneousMagnetization G Λ J β i :=
  spontaneousCorrelation_nonneg G Λ hJ hβ {i}

/-- **Upper bound**: $m^* \le 1$.  Specialization of
`spontaneousCorrelation_le_one` at `A = {i}`. -/
theorem spontaneousMagnetization_le_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (i : V) :
    spontaneousMagnetization G Λ J β i ≤ 1 :=
  spontaneousCorrelation_le_one G Λ hJ hβ {i}


/-- **`-1 ≤ spontaneousMagnetization`** (ferromagnetic).
Direct from `spontaneousMagnetization_nonneg`. -/
theorem neg_one_le_spontaneousMagnetization
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (i : V) :
    -1 ≤ spontaneousMagnetization G Λ J β i := by
  have := spontaneousMagnetization_nonneg G Λ hJ hβ i
  linarith

/-- **`|spontaneousMagnetization| ≤ 1`** (ferromagnetic). -/
theorem abs_spontaneousMagnetization_le_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (i : V) :
    |spontaneousMagnetization G Λ J β i| ≤ 1 :=
  abs_le.mpr ⟨neg_one_le_spontaneousMagnetization G Λ hJ hβ i,
    spontaneousMagnetization_le_one G Λ hJ hβ i⟩

/-- **`spontaneousMagnetization² ≤ 1`** (ferromagnetic). -/
theorem spontaneousMagnetization_sq_le_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (i : V) :
    spontaneousMagnetization G Λ J β i ^ 2 ≤ 1 := by
  have h := abs_spontaneousMagnetization_le_one G Λ hJ hβ i
  have : |spontaneousMagnetization G Λ J β i| ^ 2 ≤ 1 ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) h 2
  simpa [sq_abs] using this

/-- **Lower bound for `magnetizationInfinite` at positive `h`**:
$m^* \le M(h)$ for $h > 0$. Specialization of
`spontaneousCorrelation_le_correlationInfinite` at `A = {i}` (noting
`magnetizationInfinite = correlationInfinite ... {i}`). -/
theorem spontaneousMagnetization_le_magnetizationInfinite
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β)
    {h : ℝ} (hh : 0 < h) (i : V) :
    spontaneousMagnetization G Λ J β i
      ≤ magnetizationInfinite G Λ ⟨J, h, β⟩ i :=
  spontaneousCorrelation_le_correlationInfinite G Λ hJ hβ hh {i}

/-- **Exhaustion-independence of `spontaneousMagnetization`**:
the value does not depend on the choice of exhaustion.  Specialization
of `spontaneousCorrelation_indep_exhaustion` at `A = {i}`. -/
theorem spontaneousMagnetization_indep_exhaustion
    (G : SimpleGraph V) (Λ Λ' : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Fintype (inducedGraph G (Λ'.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (i : V) :
    spontaneousMagnetization G Λ J β i
      = spontaneousMagnetization G Λ' J β i :=
  spontaneousCorrelation_indep_exhaustion G Λ Λ' hJ hβ {i}

/-- **Right-limit Tendsto**: for ferromagnetic Ising,
`magnetizationInfinite` tends to `spontaneousMagnetization` as
`h → 0⁺`.  Specialization of
`tendsto_correlationInfinite_spontaneousCorrelation_nhdsGT` at
`A = {i}` (noting `magnetizationInfinite = correlationInfinite ... {i}`). -/
theorem tendsto_magnetizationInfinite_spontaneousMagnetization_nhdsGT
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (i : V) :
    Filter.Tendsto
      (fun h : ℝ => magnetizationInfinite G Λ ⟨J, h, β⟩ i)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (spontaneousMagnetization G Λ J β i)) :=
  tendsto_correlationInfinite_spontaneousCorrelation_nhdsGT G Λ hJ hβ {i}

/-- **`spontaneousMagnetization` at J = 0 vanishes** (Step 268, GJ §5.1):
At zero coupling, no spontaneous symmetry breaking — `m^* := lim_{h → 0⁺} M(h) = 0`.

**Proof**: at J = 0, `magnetizationInfinite G Λ ⟨0, h, β⟩ i = tanh(β·h)` (Step 233's
`magnetizationInfinite_J_zero`) for `h ≥ 0`. The function `h ↦ tanh(β·h)` is continuous
with `tanh(β·0) = 0`. By `tendsto_magnetizationInfinite_spontaneousMagnetization_nhdsGT`,
spontaneousMagnetization = lim_{h → 0⁺} M(h) = lim_{h → 0⁺} tanh(βh) = 0.

Reference: Glimm–Jaffe §5.1 p. 77 (no spontaneous symmetry breaking at J = 0). -/
theorem spontaneousMagnetization_J_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β : ℝ} (hβ : 0 < β) (i : V) :
    spontaneousMagnetization G Λ 0 β i = 0 := by
  -- Use that lim_{h → 0⁺} M(h) = spontaneousMagnetization
  have h_tend := tendsto_magnetizationInfinite_spontaneousMagnetization_nhdsGT
    G Λ (le_refl 0) hβ i
  -- M(h) at J = 0 equals tanh(βh) for h ≥ 0 (and the limit takes h ∈ Ioi 0 where h > 0)
  have h_eq : ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      magnetizationInfinite G Λ ⟨0, h, β⟩ i = Real.tanh (β * h) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh_pos : 0 < h := hh
    have hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ) :=
      ⟨le_refl 0, hh_pos.le, hβ⟩
    exact magnetizationInfinite_J_zero G Λ h β hf i
  have h_tend' := h_tend.congr' h_eq
  -- tanh(β·h) → tanh(0) = 0 as h → 0⁺
  have h_tanh_cont : Continuous (Real.tanh : ℝ → ℝ) := by
    rw [show (Real.tanh : ℝ → ℝ) = (fun x => Real.sinh x / Real.cosh x) from
        funext fun x => Real.tanh_eq_sinh_div_cosh x]
    exact Real.continuous_sinh.div Real.continuous_cosh (fun x => (Real.cosh_pos x).ne')
  have h_tanh_zero : Real.tanh (β * 0) = 0 := by
    rw [mul_zero]; exact Real.tanh_zero
  have h_tend_zero : Filter.Tendsto (fun h : ℝ => Real.tanh (β * h))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have h_cont : Continuous (fun h : ℝ => Real.tanh (β * h)) :=
      h_tanh_cont.comp (continuous_const.mul continuous_id)
    have h_at_zero : Filter.Tendsto (fun h : ℝ => Real.tanh (β * h))
        (nhds (0 : ℝ)) (nhds (Real.tanh (β * 0))) := h_cont.tendsto 0
    rw [h_tanh_zero] at h_at_zero
    exact h_at_zero.mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique h_tend' h_tend_zero

/-- **`spontaneousCorrelation` at J = 0 vanishes for nonempty A** (Step 270, GJ §5.1):
At zero coupling, all infinite-volume correlations factorise as `tanh(βh)^|A|` (Step 233's
`correlationInfinite_J_zero`); the infimum over `h ∈ Ioi 0` equals 0 for `A.Nonempty`
since `tanh(βh) → 0` as `h → 0⁺`.

Generalizes `spontaneousMagnetization_J_zero` (Step 268) from `A = {i}` to arbitrary
nonempty `A`. -/
theorem spontaneousCorrelation_J_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β : ℝ} (hβ : 0 < β) (A : Finset V) (hA : A.Nonempty) :
    spontaneousCorrelation G Λ 0 β A = 0 := by
  have h_tend := tendsto_correlationInfinite_spontaneousCorrelation_nhdsGT
    G Λ (le_refl 0) hβ A
  have h_eq : ∀ᶠ h in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      correlationInfinite G Λ (⟨0, h, β⟩ : IsingParams ℝ) A = Real.tanh (β * h) ^ A.card := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh_pos : 0 < h := hh
    have hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ) :=
      ⟨le_refl 0, hh_pos.le, hβ⟩
    exact correlationInfinite_J_zero G Λ h β hf A
  have h_tend' := h_tend.congr' h_eq
  -- tanh(βh)^|A| → 0 as h → 0⁺ (for A nonempty, |A| ≥ 1)
  have h_tanh_cont : Continuous (Real.tanh : ℝ → ℝ) := by
    rw [show (Real.tanh : ℝ → ℝ) = (fun x => Real.sinh x / Real.cosh x) from
        funext fun x => Real.tanh_eq_sinh_div_cosh x]
    exact Real.continuous_sinh.div Real.continuous_cosh (fun x => (Real.cosh_pos x).ne')
  have h_card_pos : 0 < A.card := Finset.card_pos.mpr hA
  have h_pow_zero : (0 : ℝ) ^ A.card = 0 := zero_pow h_card_pos.ne'
  have h_tend_zero : Filter.Tendsto (fun h : ℝ => Real.tanh (β * h) ^ A.card)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have h_inner : Continuous (fun h : ℝ => Real.tanh (β * h) ^ A.card) :=
      (h_tanh_cont.comp (continuous_const.mul continuous_id)).pow _
    have h_at_zero := h_inner.tendsto 0
    rw [show Real.tanh (β * 0) ^ A.card = 0 by rw [mul_zero, Real.tanh_zero, h_pow_zero]]
      at h_at_zero
    exact h_at_zero.mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique h_tend' h_tend_zero

/-- **`spontaneousMagnetization` at β = 0 vanishes** (Step 269, GJ §5.1):
At infinite temperature, every magnetizationInfinite at β = 0 vanishes
(`magnetizationInfinite_beta_zero`), so the infimum over h ∈ Ioi 0 is 0.

**Proof**: spontaneousMagnetization = ⨅ h, correlationInfinite ⟨J, h, 0⟩ {i};
each value = 0 (β=0 vanishing); infimum of constant 0 = 0. -/
theorem spontaneousMagnetization_beta_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J : ℝ) (i : V) :
    spontaneousMagnetization G Λ J 0 i = 0 := by
  unfold spontaneousMagnetization spontaneousCorrelation
  have h_eq : ∀ h : ↥(Set.Ioi (0 : ℝ)),
      correlationInfinite G Λ (⟨J, h.val, 0⟩ : IsingParams ℝ) {i} = 0 := by
    intro h
    -- magnetizationInfinite_beta_zero gives 0 for {i} singleton
    have := magnetizationInfinite_beta_zero G Λ J h.val i
    unfold magnetizationInfinite at this
    exact this
  simp [h_eq]


end Ambient
end IsingModel
