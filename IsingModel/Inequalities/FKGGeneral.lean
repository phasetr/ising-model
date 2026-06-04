import IsingModel.Inequalities.FKG

/-!
# General FKG inequality for arbitrary monotone observables (FV Thm 3.21)

`fkg_ising` proves the FKG inequality `⟨f⟩⟨g⟩ ≤ ⟨fg⟩` for ferromagnetic Ising
models, but — inheriting the interface of Mathlib's `fkg` — it additionally
requires the observables to be **nonnegative** (`0 ≤ f`, `0 ≤ g`).  The genuine
Friedli–Velenik Theorem 3.21 holds for **any** monotone (nondecreasing) `f, g`,
of arbitrary sign.

The nonnegativity hypothesis is removed here by the standard covariance
shift-invariance argument.  The Gibbs covariance
`Cov(f, g) = ⟨fg⟩ − ⟨f⟩⟨g⟩` is invariant under adding constants to `f` and `g`
(the constant terms cancel by linearity and normalisation `⟨1⟩ = 1`).  Since the
configuration space `Config ι` is finite, each monotone observable is bounded
below, so subtracting its minimum yields a nonnegative monotone observable
`f' = f − min f ≥ 0` with the same covariance.  Applying `fkg_ising` to `f', g'`
gives `Cov(f, g) = Cov(f', g') ≥ 0`, i.e. `⟨f⟩⟨g⟩ ≤ ⟨fg⟩`.

The Gibbs-expectation linearity lemmas (`gibbsExpectation_const`,
`gibbsExpectation_add`, `gibbsExpectation_const_mul`) are proved here as well;
they are the algebraic backbone of the shift argument.

Reference: Friedli–Velenik, *Statistical Mechanics of Lattice Systems* (2017),
Theorem 3.21, p. 98.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Linearity of the Gibbs expectation -/

/-- **Gibbs expectation of a constant**: `⟨c⟩ = c` (normalisation `⟨1⟩ = 1`).
`⟨c⟩ = Z⁻¹ ∑_σ c · w(σ) = c · Z⁻¹ · Z = c`. -/
theorem gibbsExpectation_const (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (c : ℝ) :
    gibbsExpectation G p (fun _ => c) = c := by
  unfold gibbsExpectation
  have hZ : partitionFunction G p ≠ 0 := partitionFunction_ne_zero G p
  rw [← Finset.mul_sum]
  rw [show (∑ σ : Config ι, boltzmannWeight G p σ) = partitionFunction G p from rfl]
  rw [← mul_assoc, mul_comm (partitionFunction G p)⁻¹ c, mul_assoc,
    inv_mul_cancel₀ hZ, mul_one]

/-- **Additivity of the Gibbs expectation**: `⟨F + H⟩ = ⟨F⟩ + ⟨H⟩`.
Distribute `Z⁻¹` over the split sum `∑_σ (F + H)(σ) w(σ) = ∑ F w + ∑ H w`. -/
theorem gibbsExpectation_add (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (F H : Config ι → ℝ) :
    gibbsExpectation G p (F + H)
      = gibbsExpectation G p F + gibbsExpectation G p H := by
  unfold gibbsExpectation
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  simp only [Pi.add_apply]
  ring

/-- **Scalar homogeneity of the Gibbs expectation**: `⟨c · F⟩ = c · ⟨F⟩`. -/
theorem gibbsExpectation_const_mul (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (c : ℝ) (F : Config ι → ℝ) :
    gibbsExpectation G p (fun σ => c * F σ) = c * gibbsExpectation G p F := by
  unfold gibbsExpectation
  rw [show (∑ σ : Config ι, (c * F σ) * boltzmannWeight G p σ)
        = c * ∑ σ : Config ι, F σ * boltzmannWeight G p σ from by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    ring]
  ring

/-! ## General FKG inequality -/

/-- **General FKG inequality for the Ising model** (Friedli–Velenik Thm 3.21):
for a ferromagnetic Ising model and **arbitrary** monotone nondecreasing
observables `f, g` (of any sign), `⟨f⟩⟨g⟩ ≤ ⟨fg⟩`.

This strengthens `fkg_ising` by dropping its nonnegativity hypotheses
`0 ≤ f`, `0 ≤ g`.  The Gibbs covariance is invariant under shifting `f, g` by
constants, so subtracting the (finite) minima `a = min f`, `b = min g` produces
nonnegative monotone observables `f' = f − a`, `g' = g − b` with the same
covariance; `fkg_ising` applied to `f', g'` then yields the result. -/
theorem fkg_ising_of_monotone (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (f g : Config ι → ℝ)
    (hf_mono : Monotone f) (hg_mono : Monotone g) :
    gibbsExpectation G p f * gibbsExpectation G p g ≤
    gibbsExpectation G p (f * g) := by
  classical
  -- The configuration space is finite and nonempty.
  have huniv : (Finset.univ : Finset (Config ι)).Nonempty :=
    Finset.univ_nonempty
  -- Lower bounds: minima of f and g over the configuration space.
  set a : ℝ := Finset.univ.inf' huniv f with ha_def
  set b : ℝ := Finset.univ.inf' huniv g with hb_def
  have ha : ∀ σ : Config ι, a ≤ f σ := fun σ =>
    Finset.inf'_le f (Finset.mem_univ σ)
  have hb : ∀ σ : Config ι, b ≤ g σ := fun σ =>
    Finset.inf'_le g (Finset.mem_univ σ)
  -- Shifted nonnegative monotone observables.
  set f' : Config ι → ℝ := fun σ => f σ - a with hf'_def
  set g' : Config ι → ℝ := fun σ => g σ - b with hg'_def
  have hf'_nn : 0 ≤ f' := fun σ => sub_nonneg.mpr (ha σ)
  have hg'_nn : 0 ≤ g' := fun σ => sub_nonneg.mpr (hb σ)
  have hf'_mono : Monotone f' := fun x y hxy => sub_le_sub_right (hf_mono hxy) a
  have hg'_mono : Monotone g' := fun x y hxy => sub_le_sub_right (hg_mono hxy) b
  -- Gibbs expectations of the shifted observables.
  have hEf' : gibbsExpectation G p f' = gibbsExpectation G p f - a := by
    have hrw : f' = f + (fun _ => -a) := by funext σ; simp [hf'_def, Pi.add_apply]; ring
    rw [hrw, gibbsExpectation_add, gibbsExpectation_const]; ring
  have hEg' : gibbsExpectation G p g' = gibbsExpectation G p g - b := by
    have hrw : g' = g + (fun _ => -b) := by funext σ; simp [hg'_def, Pi.add_apply]; ring
    rw [hrw, gibbsExpectation_add, gibbsExpectation_const]; ring
  -- Gibbs expectation of the shifted product, via the covariance expansion.
  have hEf'g' : gibbsExpectation G p (f' * g')
      = gibbsExpectation G p (f * g)
        - a * gibbsExpectation G p g - b * gibbsExpectation G p f + a * b := by
    have hrw : f' * g'
        = (f * g) + ((fun σ => (-a) * g σ)
            + ((fun σ => (-b) * f σ) + (fun _ => a * b))) := by
      funext σ
      simp only [hf'_def, hg'_def, Pi.mul_apply, Pi.add_apply]
      ring
    rw [hrw, gibbsExpectation_add, gibbsExpectation_add, gibbsExpectation_add,
      gibbsExpectation_const_mul, gibbsExpectation_const_mul, gibbsExpectation_const]
    ring
  -- Apply the nonnegative FKG inequality to f', g'.
  have hfkg := fkg_ising G p hf f' g' hf'_nn hg'_nn hf'_mono hg'_mono
  rw [hEf', hEg', hEf'g'] at hfkg
  nlinarith [hfkg]

end IsingModel
