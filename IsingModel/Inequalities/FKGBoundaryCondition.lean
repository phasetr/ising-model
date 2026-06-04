import IsingModel.Inequalities.FKGInhomogeneous

/-!
# FKG inequality with arbitrary boundary conditions (FV Thm 3.21, full form)

Friedli–Velenik Theorem 3.21 states the FKG inequality for a finite volume `Λ`
with an **arbitrary boundary condition** `#`: the spins outside `Λ` are frozen to
a fixed external configuration, and the spins inside `Λ` fluctuate, interacting
with each other and with the frozen boundary spins.

The boundary-condition Gibbs measure is obtained from the (inhomogeneous-coupling)
Boltzmann weight of `FKGInhomogeneous.lean` by **conditioning**: only
configurations agreeing with the boundary condition `η` outside `Λ` are retained.
Crucially, this conditioning preserves the FKG lattice structure — the set of
configurations agreeing with `η` off `Λ` is a **sublattice** (if `σ, σ'` agree
with `η` off `Λ`, so do `σ ⊔ σ'` and `σ ⊓ σ'`), so the conditioned weight, the
indicator of that sublattice times the log-supermodular Boltzmann weight, is again
log-supermodular.  No new Hamiltonian is needed: the boundary interactions are
already present in `boltzmannWeightJ`, and the conditioning simply restricts the
sum.

* `agreesOff` — the boundary-agreement predicate; `agreesOff_sup` / `agreesOff_inf`
  give the sublattice closure.
* `boltzmannWeightBC` — the conditioned (boundary-condition) Boltzmann weight, and
  `boltzmannWeightBC_log_supermodular`.
* `gibbsExpectationBC` + linearity, then `fkg_isingBC` (nonnegative observables)
  and `fkg_isingBC_of_monotone` (arbitrary monotone observables).

This completes FV Theorem 3.21 in full generality (nonnegative inhomogeneous
couplings, arbitrary field, arbitrary boundary condition).  Part of Issue #3558.

Reference: Friedli–Velenik, *Statistical Mechanics of Lattice Systems* (2017),
Theorem 3.21, p. 98.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Boundary-agreement predicate and its sublattice closure -/

/-- **Boundary agreement**: `σ` agrees with the external configuration `η` outside
the volume `Λ` (the boundary condition fixes the spins off `Λ`). -/
def agreesOff (Λ : Finset ι) (η σ : Config ι) : Prop :=
  ∀ i, i ∉ Λ → σ i = η i

omit [Fintype ι] [DecidableEq ι] in
/-- The boundary condition itself agrees with `η` off `Λ` (so the conditioned set
is nonempty). -/
theorem agreesOff_self (Λ : Finset ι) (η : Config ι) : agreesOff Λ η η :=
  fun _ _ => rfl

omit [Fintype ι] [DecidableEq ι] in
/-- **Sublattice closure under `⊔`**: if `σ` and `σ'` agree with `η` off `Λ`, so
does `σ ⊔ σ'` (off `Λ`, both equal `η i`, so their join is `η i`). -/
theorem agreesOff_sup {Λ : Finset ι} {η σ σ' : Config ι}
    (hσ : agreesOff Λ η σ) (hσ' : agreesOff Λ η σ') : agreesOff Λ η (σ ⊔ σ') := by
  intro i hi
  rw [Pi.sup_apply, hσ i hi, hσ' i hi, sup_idem]

omit [Fintype ι] [DecidableEq ι] in
/-- **Sublattice closure under `⊓`**: if `σ` and `σ'` agree with `η` off `Λ`, so
does `σ ⊓ σ'`. -/
theorem agreesOff_inf {Λ : Finset ι} {η σ σ' : Config ι}
    (hσ : agreesOff Λ η σ) (hσ' : agreesOff Λ η σ') : agreesOff Λ η (σ ⊓ σ') := by
  intro i hi
  rw [Pi.inf_apply, hσ i hi, hσ' i hi, inf_idem]

/-! ## Boundary-condition Boltzmann weight -/

open Classical in
/-- **Boundary-condition Boltzmann weight**: the inhomogeneous Boltzmann weight
restricted to configurations agreeing with the boundary condition `η` off `Λ`
(others get weight `0`). -/
noncomputable def boltzmannWeightBC (G : SimpleGraph ι) [Fintype G.edgeSet]
    (β : ℝ) (J : Sym2 ι → ℝ) (h : ℝ) (Λ : Finset ι) (η : Config ι) (σ : Config ι) : ℝ :=
  Set.indicator {σ | agreesOff Λ η σ} (boltzmannWeightJ G β J h) σ

omit [DecidableEq ι] in
/-- The boundary-condition Boltzmann weight is nonnegative. -/
theorem boltzmannWeightBC_nonneg (G : SimpleGraph ι) [Fintype G.edgeSet]
    (β : ℝ) (J : Sym2 ι → ℝ) (h : ℝ) (Λ : Finset ι) (η : Config ι) (σ : Config ι) :
    0 ≤ boltzmannWeightBC G β J h Λ η σ := by
  unfold boltzmannWeightBC
  exact Set.indicator_nonneg (fun s _ => (boltzmannWeightJ_pos G β J h s).le) σ

omit [DecidableEq ι] in
/-- The boundary-condition Boltzmann weight equals the inhomogeneous weight on
configurations agreeing with `η` off `Λ`. -/
theorem boltzmannWeightBC_of_agrees (G : SimpleGraph ι) [Fintype G.edgeSet]
    (β : ℝ) (J : Sym2 ι → ℝ) (h : ℝ) {Λ : Finset ι} {η σ : Config ι}
    (hσ : agreesOff Λ η σ) :
    boltzmannWeightBC G β J h Λ η σ = boltzmannWeightJ G β J h σ := by
  unfold boltzmannWeightBC
  exact Set.indicator_of_mem hσ _

omit [DecidableEq ι] in
/-- The boundary-condition Boltzmann weight is `0` on configurations disagreeing
with `η` off `Λ`. -/
theorem boltzmannWeightBC_of_not_agrees (G : SimpleGraph ι) [Fintype G.edgeSet]
    (β : ℝ) (J : Sym2 ι → ℝ) (h : ℝ) {Λ : Finset ι} {η σ : Config ι}
    (hσ : ¬ agreesOff Λ η σ) :
    boltzmannWeightBC G β J h Λ η σ = 0 := by
  unfold boltzmannWeightBC
  exact Set.indicator_of_notMem hσ _

omit [DecidableEq ι] in
/-- **Log-supermodularity of the boundary-condition Boltzmann weight** (the FKG
lattice condition under conditioning): for `β ≥ 0` and `J(e) ≥ 0`,

`w(σ)·w(σ') ≤ w(σ ⊔ σ')·w(σ ⊓ σ')`.

If both `σ, σ'` agree with `η` off `Λ`, this is the inhomogeneous
log-supermodularity (and `σ ⊔ σ'`, `σ ⊓ σ'` again agree, by the sublattice
closure).  If either disagrees, the left side is `0 ≤` the (nonnegative) right
side. -/
theorem boltzmannWeightBC_log_supermodular (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β : ℝ} {J : Sym2 ι → ℝ} {h : ℝ} (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (Λ : Finset ι) (η : Config ι) (σ σ' : Config ι) :
    boltzmannWeightBC G β J h Λ η σ * boltzmannWeightBC G β J h Λ η σ' ≤
    boltzmannWeightBC G β J h Λ η (σ ⊔ σ') * boltzmannWeightBC G β J h Λ η (σ ⊓ σ') := by
  by_cases hσ : agreesOff Λ η σ
  · by_cases hσ' : agreesOff Λ η σ'
    · rw [boltzmannWeightBC_of_agrees G β J h hσ, boltzmannWeightBC_of_agrees G β J h hσ',
        boltzmannWeightBC_of_agrees G β J h (agreesOff_sup hσ hσ'),
        boltzmannWeightBC_of_agrees G β J h (agreesOff_inf hσ hσ')]
      exact boltzmannWeightJ_log_supermodular (h := h) G hβ hJ σ σ'
    · rw [boltzmannWeightBC_of_not_agrees G β J h hσ', mul_zero]
      exact mul_nonneg (boltzmannWeightBC_nonneg G β J h Λ η _)
        (boltzmannWeightBC_nonneg G β J h Λ η _)
  · rw [boltzmannWeightBC_of_not_agrees G β J h hσ, zero_mul]
    exact mul_nonneg (boltzmannWeightBC_nonneg G β J h Λ η _)
      (boltzmannWeightBC_nonneg G β J h Λ η _)

/-! ## Boundary-condition partition function and Gibbs expectation -/

/-- **Boundary-condition partition function**: `Z = ∑_σ w(σ)` (only configurations
agreeing with `η` off `Λ` contribute). -/
noncomputable def partitionFunctionBC (G : SimpleGraph ι) [Fintype G.edgeSet]
    (β : ℝ) (J : Sym2 ι → ℝ) (h : ℝ) (Λ : Finset ι) (η : Config ι) : ℝ :=
  ∑ σ : Config ι, boltzmannWeightBC G β J h Λ η σ

/-- The boundary-condition partition function is strictly positive: the boundary
condition `η` itself contributes a strictly positive weight. -/
theorem partitionFunctionBC_pos (G : SimpleGraph ι) [Fintype G.edgeSet]
    (β : ℝ) (J : Sym2 ι → ℝ) (h : ℝ) (Λ : Finset ι) (η : Config ι) :
    0 < partitionFunctionBC G β J h Λ η := by
  refine Finset.sum_pos' (fun σ _ => boltzmannWeightBC_nonneg G β J h Λ η σ) ⟨η, mem_univ η, ?_⟩
  rw [boltzmannWeightBC_of_agrees G β J h (agreesOff_self Λ η)]
  exact boltzmannWeightJ_pos G β J h η

/-- The boundary-condition partition function is nonzero. -/
theorem partitionFunctionBC_ne_zero (G : SimpleGraph ι) [Fintype G.edgeSet]
    (β : ℝ) (J : Sym2 ι → ℝ) (h : ℝ) (Λ : Finset ι) (η : Config ι) :
    partitionFunctionBC G β J h Λ η ≠ 0 :=
  ne_of_gt (partitionFunctionBC_pos G β J h Λ η)

/-- **Boundary-condition Gibbs expectation**: `⟨F⟩^η_Λ = Z⁻¹ ∑_σ F(σ) w(σ)`. -/
noncomputable def gibbsExpectationBC (G : SimpleGraph ι) [Fintype G.edgeSet]
    (β : ℝ) (J : Sym2 ι → ℝ) (h : ℝ) (Λ : Finset ι) (η : Config ι) (F : Config ι → ℝ) : ℝ :=
  (partitionFunctionBC G β J h Λ η)⁻¹ *
    ∑ σ : Config ι, F σ * boltzmannWeightBC G β J h Λ η σ

/-- **Gibbs expectation of a constant**: `⟨c⟩ = c`. -/
theorem gibbsExpectationBC_const (G : SimpleGraph ι) [Fintype G.edgeSet]
    (β : ℝ) (J : Sym2 ι → ℝ) (h : ℝ) (Λ : Finset ι) (η : Config ι) (c : ℝ) :
    gibbsExpectationBC G β J h Λ η (fun _ => c) = c := by
  unfold gibbsExpectationBC
  have hZ : partitionFunctionBC G β J h Λ η ≠ 0 := partitionFunctionBC_ne_zero G β J h Λ η
  rw [← Finset.mul_sum]
  rw [show (∑ σ : Config ι, boltzmannWeightBC G β J h Λ η σ)
        = partitionFunctionBC G β J h Λ η from rfl]
  rw [← mul_assoc, mul_comm (partitionFunctionBC G β J h Λ η)⁻¹ c, mul_assoc,
    inv_mul_cancel₀ hZ, mul_one]

/-- **Additivity of the Gibbs expectation**: `⟨F + H⟩ = ⟨F⟩ + ⟨H⟩`. -/
theorem gibbsExpectationBC_add (G : SimpleGraph ι) [Fintype G.edgeSet]
    (β : ℝ) (J : Sym2 ι → ℝ) (h : ℝ) (Λ : Finset ι) (η : Config ι) (F H : Config ι → ℝ) :
    gibbsExpectationBC G β J h Λ η (F + H)
      = gibbsExpectationBC G β J h Λ η F + gibbsExpectationBC G β J h Λ η H := by
  unfold gibbsExpectationBC
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  simp only [Pi.add_apply]
  ring

/-- **Scalar homogeneity of the Gibbs expectation**: `⟨c · F⟩ = c · ⟨F⟩`. -/
theorem gibbsExpectationBC_const_mul (G : SimpleGraph ι) [Fintype G.edgeSet]
    (β : ℝ) (J : Sym2 ι → ℝ) (h : ℝ) (Λ : Finset ι) (η : Config ι) (c : ℝ) (F : Config ι → ℝ) :
    gibbsExpectationBC G β J h Λ η (fun σ => c * F σ)
      = c * gibbsExpectationBC G β J h Λ η F := by
  unfold gibbsExpectationBC
  rw [show (∑ σ : Config ι, (c * F σ) * boltzmannWeightBC G β J h Λ η σ)
        = c * ∑ σ : Config ι, F σ * boltzmannWeightBC G β J h Λ η σ from by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    ring]
  ring

/-! ## FKG inequality with boundary conditions -/

/-- **Boundary-condition FKG inequality** (nonnegative observables): for
nonnegative couplings `J(e) ≥ 0`, `β ≥ 0`, arbitrary field `h`, an arbitrary
boundary condition `η` outside `Λ`, and monotone nondecreasing nonnegative
`f, g`, `⟨f⟩^η_Λ ⟨g⟩^η_Λ ≤ ⟨fg⟩^η_Λ`.

Applies Mathlib's `fkg` to the conditioned Boltzmann weight, whose
log-supermodularity is `boltzmannWeightBC_log_supermodular`. -/
theorem fkg_isingBC (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β : ℝ} {J : Sym2 ι → ℝ} {h : ℝ} (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (Λ : Finset ι) (η : Config ι) (f g : Config ι → ℝ)
    (hf_nn : 0 ≤ f) (hg_nn : 0 ≤ g)
    (hf_mono : Monotone f) (hg_mono : Monotone g) :
    gibbsExpectationBC G β J h Λ η f * gibbsExpectationBC G β J h Λ η g ≤
    gibbsExpectationBC G β J h Λ η (f * g) := by
  have hZ := partitionFunctionBC_pos G β J h Λ η
  have hw_nn : 0 ≤ boltzmannWeightBC G β J h Λ η := fun σ => boltzmannWeightBC_nonneg G β J h Λ η σ
  have hw_sm : ∀ a b : Config ι,
      boltzmannWeightBC G β J h Λ η a * boltzmannWeightBC G β J h Λ η b ≤
      boltzmannWeightBC G β J h Λ η (a ⊓ b) * boltzmannWeightBC G β J h Λ η (a ⊔ b) := by
    intro a b
    have hlsm := boltzmannWeightBC_log_supermodular (h := h) G hβ hJ Λ η a b
    linarith [mul_comm (boltzmannWeightBC G β J h Λ η (a ⊔ b))
      (boltzmannWeightBC G β J h Λ η (a ⊓ b))]
  have hfkg := fkg (μ := boltzmannWeightBC G β J h Λ η) (f := f) (g := g)
    hw_nn hf_nn hg_nn hf_mono hg_mono hw_sm
  simp only [gibbsExpectationBC, partitionFunctionBC]
  have hZinv := inv_pos.mpr hZ
  simp_rw [show ∀ σ : Config ι, f σ * boltzmannWeightBC G β J h Λ η σ =
    boltzmannWeightBC G β J h Λ η σ * f σ from fun σ => mul_comm _ _,
    show ∀ σ : Config ι, g σ * boltzmannWeightBC G β J h Λ η σ =
    boltzmannWeightBC G β J h Λ η σ * g σ from fun σ => mul_comm _ _,
    show ∀ σ : Config ι, (f * g) σ * boltzmannWeightBC G β J h Λ η σ =
    boltzmannWeightBC G β J h Λ η σ * (f σ * g σ) from fun σ => by simp [Pi.mul_apply]; ring]
  set Z := ∑ σ : Config ι, boltzmannWeightBC G β J h Λ η σ with hZdef
  have hZ' : (0 : ℝ) < Z := hZ
  have hZne := ne_of_gt hZ'
  rw [show ((Z⁻¹ * ∑ x, boltzmannWeightBC G β J h Λ η x * f x) *
      (Z⁻¹ * ∑ x, boltzmannWeightBC G β J h Λ η x * g x)) =
    Z⁻¹ * Z⁻¹ * ((∑ x, boltzmannWeightBC G β J h Λ η x * f x) *
      (∑ x, boltzmannWeightBC G β J h Λ η x * g x)) from by ring]
  rw [show Z⁻¹ * Z⁻¹ = (Z * Z)⁻¹ from by rw [mul_inv_rev]]
  rw [show Z⁻¹ * ∑ σ, boltzmannWeightBC G β J h Λ η σ * (f σ * g σ) =
    (Z * Z)⁻¹ * (Z * ∑ σ, boltzmannWeightBC G β J h Λ η σ * (f σ * g σ)) from by
      field_simp]
  exact mul_le_mul_of_nonneg_left hfkg (by positivity)

/-- **General boundary-condition FKG inequality** (FV Thm 3.21, full form): for
nonnegative couplings `J(e) ≥ 0`, `β ≥ 0`, arbitrary field `h`, an arbitrary
boundary condition `η` outside `Λ`, and **arbitrary** monotone nondecreasing
`f, g` (of any sign), `⟨f⟩^η_Λ ⟨g⟩^η_Λ ≤ ⟨fg⟩^η_Λ`.

Drops the nonnegativity hypothesis of `fkg_isingBC` by the covariance
shift-invariance argument (as in `fkg_ising_of_monotone`). -/
theorem fkg_isingBC_of_monotone (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β : ℝ} {J : Sym2 ι → ℝ} {h : ℝ} (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (Λ : Finset ι) (η : Config ι) (f g : Config ι → ℝ)
    (hf_mono : Monotone f) (hg_mono : Monotone g) :
    gibbsExpectationBC G β J h Λ η f * gibbsExpectationBC G β J h Λ η g ≤
    gibbsExpectationBC G β J h Λ η (f * g) := by
  classical
  have huniv : (Finset.univ : Finset (Config ι)).Nonempty := Finset.univ_nonempty
  set a : ℝ := Finset.univ.inf' huniv f with ha_def
  set b : ℝ := Finset.univ.inf' huniv g with hb_def
  have ha : ∀ σ : Config ι, a ≤ f σ := fun σ => Finset.inf'_le f (Finset.mem_univ σ)
  have hb : ∀ σ : Config ι, b ≤ g σ := fun σ => Finset.inf'_le g (Finset.mem_univ σ)
  set f' : Config ι → ℝ := fun σ => f σ - a with hf'_def
  set g' : Config ι → ℝ := fun σ => g σ - b with hg'_def
  have hf'_nn : 0 ≤ f' := fun σ => sub_nonneg.mpr (ha σ)
  have hg'_nn : 0 ≤ g' := fun σ => sub_nonneg.mpr (hb σ)
  have hf'_mono : Monotone f' := fun x y hxy => sub_le_sub_right (hf_mono hxy) a
  have hg'_mono : Monotone g' := fun x y hxy => sub_le_sub_right (hg_mono hxy) b
  have hEf' : gibbsExpectationBC G β J h Λ η f' = gibbsExpectationBC G β J h Λ η f - a := by
    have hrw : f' = f + (fun _ => -a) := by funext σ; simp [hf'_def, Pi.add_apply]; ring
    rw [hrw, gibbsExpectationBC_add, gibbsExpectationBC_const]; ring
  have hEg' : gibbsExpectationBC G β J h Λ η g' = gibbsExpectationBC G β J h Λ η g - b := by
    have hrw : g' = g + (fun _ => -b) := by funext σ; simp [hg'_def, Pi.add_apply]; ring
    rw [hrw, gibbsExpectationBC_add, gibbsExpectationBC_const]; ring
  have hEf'g' : gibbsExpectationBC G β J h Λ η (f' * g')
      = gibbsExpectationBC G β J h Λ η (f * g)
        - a * gibbsExpectationBC G β J h Λ η g - b * gibbsExpectationBC G β J h Λ η f + a * b := by
    have hrw : f' * g'
        = (f * g) + ((fun σ => (-a) * g σ)
            + ((fun σ => (-b) * f σ) + (fun _ => a * b))) := by
      funext σ
      simp only [hf'_def, hg'_def, Pi.mul_apply, Pi.add_apply]
      ring
    rw [hrw, gibbsExpectationBC_add, gibbsExpectationBC_add, gibbsExpectationBC_add,
      gibbsExpectationBC_const_mul, gibbsExpectationBC_const_mul, gibbsExpectationBC_const]
    ring
  have hfkg := fkg_isingBC (h := h) G hβ hJ Λ η f' g' hf'_nn hg'_nn hf'_mono hg'_mono
  rw [hEf', hEg', hEf'g'] at hfkg
  nlinarith [hfkg]

end IsingModel
