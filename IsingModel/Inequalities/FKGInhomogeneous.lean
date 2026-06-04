import IsingModel.Inequalities.FKG
import IsingModel.Inequalities.FKGGeneral
import IsingModel.Inequalities.WeightedExpectation

/-!
# FKG inequality with inhomogeneous per-edge couplings (FV Thm 3.21, free boundary)

Friedli–Velenik Theorem 3.21 states the FKG inequality for a **collection of
nonnegative couplings** `J = (J_{ij})` (one per edge), not just a single uniform
coupling.  The existing `fkg_ising` / `fkg_ising_of_monotone` treat only the
uniform scalar coupling `IsingParams.J`.  This file builds the inhomogeneous
per-edge coupling Gibbs stack and proves the FKG inequality for it (free boundary),
for **arbitrary** monotone observables.

* `interactionEnergyJ` / `hamiltonianJ` / `boltzmannWeightJ` — the inhomogeneous
  coupling energy `-∑_e J(e)·s(σ_i)s(σ_j)`, Hamiltonian, and Boltzmann weight
  `exp(-β H)`.
* `boltzmannWeightJ_log_supermodular` — the FKG lattice condition, valid as soon
  as every coupling `J(e) ≥ 0` (and `β, h ≥ 0`): the per-edge supermodularity is
  summed with the nonnegative weights `J(e)`.
* `gibbsExpectationJ` + linearity lemmas, then `fkg_isingJ` (nonnegative
  observables) and `fkg_isingJ_of_monotone` (arbitrary monotone observables, via
  the same covariance shift as `fkg_ising_of_monotone`).

This is Part of the FV 3.21 programme (Issue #3558): it removes the *uniform
coupling* restriction; arbitrary boundary conditions remain follow-up.

Reference: Friedli–Velenik, *Statistical Mechanics of Lattice Systems* (2017),
Theorem 3.21, p. 98.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Per-edge spin supermodularity** for ±1 spins (companion of the private
`spin_edge_supermodular` in `FKG.lean`):
`s(a)s(b) + s(c)s(d) ≤ s(a⊔c)s(b⊔d) + s(a⊓c)s(b⊓d)`.  Verified by exhausting the
16 cases. -/
private theorem spin_edge_supermodularJ (a b c d : Spin) :
    Spin.sign ℝ a * Spin.sign ℝ b + Spin.sign ℝ c * Spin.sign ℝ d ≤
    Spin.sign ℝ (a ⊔ c) * Spin.sign ℝ (b ⊔ d) +
    Spin.sign ℝ (a ⊓ c) * Spin.sign ℝ (b ⊓ d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> norm_num [Spin.sign, Spin.toSign]

/-! ## Inhomogeneous-coupling energy and Boltzmann weight -/

/-- **Inhomogeneous interaction energy**: `-∑_{e ∈ edges} J(e)·s(σ_i)s(σ_j)` for a
per-edge coupling function `J : Sym2 ι → ℝ`. -/
noncomputable def interactionEnergyJ (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J : Sym2 ι → ℝ) (σ : Config ι) : ℝ :=
  -∑ e ∈ G.edgeFinset, J e * edgeSpin σ e

/-- **Inhomogeneous Hamiltonian**: `interactionEnergyJ + externalFieldEnergy`,
with per-edge couplings `J` and scalar field `h`. -/
noncomputable def hamiltonianJ (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J : Sym2 ι → ℝ) (h : ℝ) (σ : Config ι) : ℝ :=
  interactionEnergyJ G J σ + externalFieldEnergy h σ

/-- **Inhomogeneous Boltzmann weight**: `exp(-β·H(σ))` for the inhomogeneous
Hamiltonian. -/
noncomputable def boltzmannWeightJ (G : SimpleGraph ι) [Fintype G.edgeSet]
    (β : ℝ) (J : Sym2 ι → ℝ) (h : ℝ) (σ : Config ι) : ℝ :=
  Real.exp (-β * hamiltonianJ G J h σ)

omit [DecidableEq ι] in
/-- The inhomogeneous Boltzmann weight is strictly positive. -/
theorem boltzmannWeightJ_pos (G : SimpleGraph ι) [Fintype G.edgeSet]
    (β : ℝ) (J : Sym2 ι → ℝ) (h : ℝ) (σ : Config ι) :
    0 < boltzmannWeightJ G β J h σ :=
  Real.exp_pos _

/-! ## Log-supermodularity (the FKG lattice condition) -/

omit [DecidableEq ι] in
/-- **Log-supermodularity of the inhomogeneous Boltzmann weight** (the FKG lattice
condition): for `β ≥ 0` and every coupling `J(e) ≥ 0` (the field `h` may have
any sign — its term is modular),

`w(σ)·w(σ') ≤ w(σ ⊔ σ')·w(σ ⊓ σ')`.

Each edge term is supermodular (`edgeSpin σ + edgeSpin σ' ≤ edgeSpin (σ⊔σ') +
edgeSpin (σ⊓σ')`); the nonnegative weights `J(e)` preserve the inequality under
summation, and the field term is modular (equality). -/
theorem boltzmannWeightJ_log_supermodular (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β : ℝ} {J : Sym2 ι → ℝ} {h : ℝ} (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (σ σ' : Config ι) :
    boltzmannWeightJ G β J h σ * boltzmannWeightJ G β J h σ' ≤
    boltzmannWeightJ G β J h (σ ⊔ σ') * boltzmannWeightJ G β J h (σ ⊓ σ') := by
  unfold boltzmannWeightJ
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp_of_le
  unfold hamiltonianJ interactionEnergyJ externalFieldEnergy
  -- Site terms: modular (equality).
  have hsite : ∀ i, Spin.sign ℝ (σ i) + Spin.sign ℝ (σ' i) =
      Spin.sign ℝ ((σ ⊔ σ') i) + Spin.sign ℝ ((σ ⊓ σ') i) := by
    intro i; simp only [Pi.sup_apply, Pi.inf_apply]
    cases σ i <;> cases σ' i <;> simp [Spin.sign, Spin.toSign]
  -- Per-edge supermodularity weighted by the nonnegative coupling J(e).
  have hedge : ∀ e ∈ G.edgeFinset,
      J e * edgeSpin (K := ℝ) σ e + J e * edgeSpin (K := ℝ) σ' e ≤
      J e * edgeSpin (K := ℝ) (σ ⊔ σ') e + J e * edgeSpin (K := ℝ) (σ ⊓ σ') e := by
    intro e _
    have hsm : edgeSpin (K := ℝ) σ e + edgeSpin (K := ℝ) σ' e ≤
        edgeSpin (K := ℝ) (σ ⊔ σ') e + edgeSpin (K := ℝ) (σ ⊓ σ') e := by
      refine Sym2.ind (fun i j => ?_) e
      simp only [edgeSpin, Sym2.lift_mk, Spin.sign]
      exact spin_edge_supermodularJ (σ i) (σ j) (σ' i) (σ' j)
    rw [← mul_add, ← mul_add]
    exact mul_le_mul_of_nonneg_left hsm (hJ e)
  have hedge_sum : ∑ e ∈ G.edgeFinset, J e * edgeSpin (K := ℝ) σ e +
      ∑ e ∈ G.edgeFinset, J e * edgeSpin (K := ℝ) σ' e ≤
      ∑ e ∈ G.edgeFinset, J e * edgeSpin (K := ℝ) (σ ⊔ σ') e +
      ∑ e ∈ G.edgeFinset, J e * edgeSpin (K := ℝ) (σ ⊓ σ') e := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun e he => hedge e he
  have hsite_sum : ∑ i : ι, Spin.sign ℝ (σ i) + ∑ i, Spin.sign ℝ (σ' i) =
      ∑ i, Spin.sign ℝ ((σ ⊔ σ') i) + ∑ i, Spin.sign ℝ ((σ ⊓ σ') i) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => hsite i
  -- β·(edge sum) supermodular, β·h·(site sum) modular.
  have h1 := mul_le_mul_of_nonneg_left hedge_sum hβ
  linarith [h1, congrArg (β * h * ·) hsite_sum]

/-! ## Partition function and Gibbs expectation -/

/-- **Inhomogeneous partition function**: `Z = ∑_σ w(σ)`. -/
noncomputable def partitionFunctionJ (G : SimpleGraph ι) [Fintype G.edgeSet]
    (β : ℝ) (J : Sym2 ι → ℝ) (h : ℝ) : ℝ :=
  ∑ σ : Config ι, boltzmannWeightJ G β J h σ

/-- The inhomogeneous partition function is strictly positive. -/
theorem partitionFunctionJ_pos (G : SimpleGraph ι) [Fintype G.edgeSet]
    (β : ℝ) (J : Sym2 ι → ℝ) (h : ℝ) :
    0 < partitionFunctionJ G β J h :=
  Finset.sum_pos (fun σ _ => boltzmannWeightJ_pos G β J h σ) ⟨Classical.arbitrary _, mem_univ _⟩

/-- The inhomogeneous partition function is nonzero. -/
theorem partitionFunctionJ_ne_zero (G : SimpleGraph ι) [Fintype G.edgeSet]
    (β : ℝ) (J : Sym2 ι → ℝ) (h : ℝ) :
    partitionFunctionJ G β J h ≠ 0 :=
  ne_of_gt (partitionFunctionJ_pos G β J h)

/-- **Inhomogeneous Gibbs expectation**: `⟨F⟩ = Z⁻¹ ∑_σ F(σ) w(σ)`. -/
noncomputable def gibbsExpectationJ (G : SimpleGraph ι) [Fintype G.edgeSet]
    (β : ℝ) (J : Sym2 ι → ℝ) (h : ℝ) (F : Config ι → ℝ) : ℝ :=
  (partitionFunctionJ G β J h)⁻¹ * ∑ σ : Config ι, F σ * boltzmannWeightJ G β J h σ

/-- **Gibbs expectation of a constant**: `⟨c⟩ = c`. -/
theorem gibbsExpectationJ_const (G : SimpleGraph ι) [Fintype G.edgeSet]
    (β : ℝ) (J : Sym2 ι → ℝ) (h : ℝ) (c : ℝ) :
    gibbsExpectationJ G β J h (fun _ => c) = c := by
  unfold gibbsExpectationJ
  exact weightedExpectation_const (partitionFunctionJ G β J h) (boltzmannWeightJ G β J h) rfl
    (partitionFunctionJ_ne_zero G β J h) c

/-- **Additivity of the Gibbs expectation**: `⟨F + H⟩ = ⟨F⟩ + ⟨H⟩`. -/
theorem gibbsExpectationJ_add (G : SimpleGraph ι) [Fintype G.edgeSet]
    (β : ℝ) (J : Sym2 ι → ℝ) (h : ℝ) (F H : Config ι → ℝ) :
    gibbsExpectationJ G β J h (F + H)
      = gibbsExpectationJ G β J h F + gibbsExpectationJ G β J h H := by
  unfold gibbsExpectationJ
  exact weightedExpectation_add (partitionFunctionJ G β J h) (boltzmannWeightJ G β J h) F H

/-- **Scalar homogeneity of the Gibbs expectation**: `⟨c · F⟩ = c · ⟨F⟩`. -/
theorem gibbsExpectationJ_const_mul (G : SimpleGraph ι) [Fintype G.edgeSet]
    (β : ℝ) (J : Sym2 ι → ℝ) (h : ℝ) (c : ℝ) (F : Config ι → ℝ) :
    gibbsExpectationJ G β J h (fun σ => c * F σ) = c * gibbsExpectationJ G β J h F := by
  unfold gibbsExpectationJ
  exact weightedExpectation_const_mul (partitionFunctionJ G β J h) (boltzmannWeightJ G β J h) c F

/-! ## FKG inequality with inhomogeneous couplings -/

/-- **Inhomogeneous-coupling FKG inequality** (nonnegative observables): for
nonnegative couplings `J(e) ≥ 0`, `β ≥ 0` (arbitrary field `h`), and monotone
nondecreasing nonnegative `f, g`, `⟨f⟩⟨g⟩ ≤ ⟨fg⟩`.

Applies Mathlib's `fkg` to the inhomogeneous Boltzmann weight, whose
log-supermodularity is `boltzmannWeightJ_log_supermodular`. -/
theorem fkg_isingJ (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β : ℝ} {J : Sym2 ι → ℝ} {h : ℝ} (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (f g : Config ι → ℝ)
    (hf_nn : 0 ≤ f) (hg_nn : 0 ≤ g)
    (hf_mono : Monotone f) (hg_mono : Monotone g) :
    gibbsExpectationJ G β J h f * gibbsExpectationJ G β J h g ≤
    gibbsExpectationJ G β J h (f * g) := by
  have hZ := partitionFunctionJ_pos G β J h
  have hw_nn : 0 ≤ boltzmannWeightJ G β J h := fun σ => (boltzmannWeightJ_pos G β J h σ).le
  have hw_sm : ∀ a b : Config ι,
      boltzmannWeightJ G β J h a * boltzmannWeightJ G β J h b ≤
      boltzmannWeightJ G β J h (a ⊓ b) * boltzmannWeightJ G β J h (a ⊔ b) := by
    intro a b
    have hlsm := boltzmannWeightJ_log_supermodular (h := h) G hβ hJ a b
    linarith [mul_comm (boltzmannWeightJ G β J h (a ⊔ b)) (boltzmannWeightJ G β J h (a ⊓ b))]
  have hfkg := fkg (μ := boltzmannWeightJ G β J h) (f := f) (g := g)
    hw_nn hf_nn hg_nn hf_mono hg_mono hw_sm
  simp only [gibbsExpectationJ, partitionFunctionJ]
  have hZinv := inv_pos.mpr hZ
  simp_rw [show ∀ σ : Config ι, f σ * boltzmannWeightJ G β J h σ =
    boltzmannWeightJ G β J h σ * f σ from fun σ => mul_comm _ _,
    show ∀ σ : Config ι, g σ * boltzmannWeightJ G β J h σ =
    boltzmannWeightJ G β J h σ * g σ from fun σ => mul_comm _ _,
    show ∀ σ : Config ι, (f * g) σ * boltzmannWeightJ G β J h σ =
    boltzmannWeightJ G β J h σ * (f σ * g σ) from fun σ => by simp [Pi.mul_apply]; ring]
  set Z := ∑ σ : Config ι, boltzmannWeightJ G β J h σ with hZdef
  have hZ' : (0 : ℝ) < Z := hZ
  have hZne := ne_of_gt hZ'
  -- hfkg: (Σ w*f)(Σ w*g) ≤ Z * Σ w*(f*g); divide by Z².
  rw [show ((Z⁻¹ * ∑ x, boltzmannWeightJ G β J h x * f x) *
      (Z⁻¹ * ∑ x, boltzmannWeightJ G β J h x * g x)) =
    Z⁻¹ * Z⁻¹ * ((∑ x, boltzmannWeightJ G β J h x * f x) *
      (∑ x, boltzmannWeightJ G β J h x * g x)) from by ring]
  rw [show Z⁻¹ * Z⁻¹ = (Z * Z)⁻¹ from by rw [mul_inv_rev]]
  rw [show Z⁻¹ * ∑ σ, boltzmannWeightJ G β J h σ * (f σ * g σ) =
    (Z * Z)⁻¹ * (Z * ∑ σ, boltzmannWeightJ G β J h σ * (f σ * g σ)) from by
      field_simp]
  exact mul_le_mul_of_nonneg_left hfkg (by positivity)

/-- **General inhomogeneous-coupling FKG inequality** (FV Thm 3.21, free boundary):
for nonnegative couplings `J(e) ≥ 0`, `β ≥ 0`, **arbitrary** field `h`, and
**arbitrary** monotone nondecreasing `f, g` (of any sign), `⟨f⟩⟨g⟩ ≤ ⟨fg⟩`.

Drops the nonnegativity hypothesis of `fkg_isingJ` by the covariance
shift-invariance argument (as in `fkg_ising_of_monotone`): shift `f, g` by their
finite minima to nonnegative monotone observables with the same covariance. -/
theorem fkg_isingJ_of_monotone (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β : ℝ} {J : Sym2 ι → ℝ} {h : ℝ} (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (f g : Config ι → ℝ)
    (hf_mono : Monotone f) (hg_mono : Monotone g) :
    gibbsExpectationJ G β J h f * gibbsExpectationJ G β J h g ≤
    gibbsExpectationJ G β J h (f * g) := by
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
  have hEf' : gibbsExpectationJ G β J h f' = gibbsExpectationJ G β J h f - a := by
    have hrw : f' = f + (fun _ => -a) := by funext σ; simp [hf'_def, Pi.add_apply]; ring
    rw [hrw, gibbsExpectationJ_add, gibbsExpectationJ_const]; ring
  have hEg' : gibbsExpectationJ G β J h g' = gibbsExpectationJ G β J h g - b := by
    have hrw : g' = g + (fun _ => -b) := by funext σ; simp [hg'_def, Pi.add_apply]; ring
    rw [hrw, gibbsExpectationJ_add, gibbsExpectationJ_const]; ring
  have hEf'g' : gibbsExpectationJ G β J h (f' * g')
      = gibbsExpectationJ G β J h (f * g)
        - a * gibbsExpectationJ G β J h g - b * gibbsExpectationJ G β J h f + a * b := by
    have hrw : f' * g'
        = (f * g) + ((fun σ => (-a) * g σ)
            + ((fun σ => (-b) * f σ) + (fun _ => a * b))) := by
      funext σ
      simp only [hf'_def, hg'_def, Pi.mul_apply, Pi.add_apply]
      ring
    rw [hrw, gibbsExpectationJ_add, gibbsExpectationJ_add, gibbsExpectationJ_add,
      gibbsExpectationJ_const_mul, gibbsExpectationJ_const_mul, gibbsExpectationJ_const]
    ring
  have hfkg := fkg_isingJ (h := h) G hβ hJ f' g' hf'_nn hg'_nn hf'_mono hg'_mono
  rw [hEf', hEg', hEf'g'] at hfkg
  nlinarith [hfkg]

end IsingModel
