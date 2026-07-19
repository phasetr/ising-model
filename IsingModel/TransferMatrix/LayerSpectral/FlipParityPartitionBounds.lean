import IsingModel.TransferMatrix.LayerSpectral.HermitianBridge
import IsingModel.TransferMatrix.LayerSpectral.FlipParitySpectralSum

/-!
# Flip-parity partition and marked-sum bounds (GJ §17.1)

Partition lower bounds and marked-sum spectral-prefactor upper bounds derived
from spectral dominance and flip-parity channel cancellation.  Child module of
the `LayerSpectral.FlipParity` scaffold.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §17.1, pp. 304--306.
-/

namespace IsingModel

namespace TransferMatrix

open Matrix

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

namespace RealOrthogonalSpectralData

/-- The finite open-boundary spectral denominator prefactor attached to a
boundary vector and a chosen dominant channel. -/
noncomputable def boundarySpectralPartitionPrefactor {M : Matrix Ω Ω ℝ}
  (E : RealOrthogonalSpectralData M) (v : Ω → ℝ) (top : Ω) (theta : ℝ) : ℝ :=
  (E.boundaryCoordinates v top) ^ 2 -
    (∑ i ∈ Finset.univ.erase top, (E.boundaryCoordinates v i) ^ 2) * theta

/-- Boundary-vector spectral dominance gives a lower bound for a finite
boundary-power denominator. -/
theorem boundary_partition_lower_of_dominant_bounds {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (v : Ω → ℝ)
    (top : Ω) (scale theta : ℝ)
    (scale_pos : 0 < scale)
    (theta_nonneg : 0 ≤ theta)
    (theta_le_one : theta ≤ 1)
    (dominant_eigenvalue : E.eigenvalue top = scale)
    (subdominant_abs_le : ∀ i, i ≠ top → |E.eigenvalue i| ≤ theta * scale)
    (n : ℕ) :
    E.boundarySpectralPartitionPrefactor v top theta * scale ^ n ≤
      ∑ i, (E.boundaryCoordinates v i) ^ 2 * E.eigenvalue i ^ n := by
  let b : Ω → ℝ := E.boundaryCoordinates v
  let rest : Finset Ω := Finset.univ.erase top
  have hscale_nonneg : 0 ≤ scale := scale_pos.le
  have htheta_scale_nonneg : 0 ≤ theta * scale :=
    mul_nonneg theta_nonneg hscale_nonneg
  have hrest_coeff_nonneg :
      0 ≤ ∑ i ∈ rest, b i ^ 2 := by
    exact Finset.sum_nonneg fun i _ => sq_nonneg (b i)
  by_cases hn : n = 0
  · subst n
    have hpref_le_top :
        E.boundarySpectralPartitionPrefactor v top theta ≤ b top ^ 2 := by
      dsimp [boundarySpectralPartitionPrefactor, b, rest]
      exact sub_le_self _ (mul_nonneg hrest_coeff_nonneg theta_nonneg)
    have htop_le_sum :
        b top ^ 2 ≤ ∑ i, b i ^ 2 := by
      exact Finset.single_le_sum
        (fun i _ => sq_nonneg (b i)) (Finset.mem_univ top)
    calc
      E.boundarySpectralPartitionPrefactor v top theta * scale ^ 0
          = E.boundarySpectralPartitionPrefactor v top theta := by simp
      _ ≤ b top ^ 2 := hpref_le_top
      _ ≤ ∑ i, b i ^ 2 := htop_le_sum
      _ = ∑ i, b i ^ 2 * E.eigenvalue i ^ 0 := by simp
  · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
    have htheta_pow_le : theta ^ n ≤ theta := by
      simpa using pow_le_pow_of_le_one theta_nonneg theta_le_one hn_pos
    have hscale_pow_nonneg : 0 ≤ scale ^ n := pow_nonneg hscale_nonneg n
    have hrest_term :
        ∀ i ∈ rest,
          -(b i ^ 2 * (theta * scale) ^ n) ≤ b i ^ 2 * E.eigenvalue i ^ n := by
      intro i hi
      have hitop : i ≠ top := (Finset.mem_erase.mp hi).1
      have hpow_abs : |E.eigenvalue i ^ n| ≤ (theta * scale) ^ n := by
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (subdominant_abs_le i hitop) n
      have hneg := neg_le_of_abs_le hpow_abs
      simpa [mul_assoc] using
        mul_le_mul_of_nonneg_left hneg (sq_nonneg (b i))
    have hrest_sum :
        ∑ i ∈ rest, -(b i ^ 2 * (theta * scale) ^ n)
          ≤ ∑ i ∈ rest, b i ^ 2 * E.eigenvalue i ^ n :=
      Finset.sum_le_sum hrest_term
    have hrest_sum' :
        -((∑ i ∈ rest, b i ^ 2) * (theta * scale) ^ n)
          ≤ ∑ i ∈ rest, b i ^ 2 * E.eigenvalue i ^ n := by
      simpa [Finset.sum_neg_distrib, Finset.sum_mul, mul_assoc] using hrest_sum
    have hrest_pow_le :
        (∑ i ∈ rest, b i ^ 2) * (theta * scale) ^ n
          ≤ (∑ i ∈ rest, b i ^ 2) * theta * scale ^ n := by
      rw [mul_pow]
      calc
        (∑ i ∈ rest, b i ^ 2) * (theta ^ n * scale ^ n)
            ≤ (∑ i ∈ rest, b i ^ 2) * (theta * scale ^ n) := by
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right htheta_pow_le hscale_pow_nonneg)
                hrest_coeff_nonneg
        _ = (∑ i ∈ rest, b i ^ 2) * theta * scale ^ n := by ring
    have htop_rest_lower :
        b top ^ 2 * scale ^ n -
            (∑ i ∈ rest, b i ^ 2) * (theta * scale) ^ n
          ≤ b top ^ 2 * scale ^ n +
              ∑ i ∈ rest, b i ^ 2 * E.eigenvalue i ^ n := by
      linarith
    have hpref_le :
        E.boundarySpectralPartitionPrefactor v top theta * scale ^ n
          ≤ b top ^ 2 * scale ^ n -
              (∑ i ∈ rest, b i ^ 2) * (theta * scale) ^ n := by
      dsimp [boundarySpectralPartitionPrefactor, b, rest]
      nlinarith
    calc
      E.boundarySpectralPartitionPrefactor v top theta * scale ^ n
          ≤ b top ^ 2 * scale ^ n -
              (∑ i ∈ rest, b i ^ 2) * (theta * scale) ^ n := hpref_le
      _ ≤ b top ^ 2 * scale ^ n +
              ∑ i ∈ rest, b i ^ 2 * E.eigenvalue i ^ n := htop_rest_lower
      _ = (∑ i ∈ rest, b i ^ 2 * E.eigenvalue i ^ n) +
              b top ^ 2 * scale ^ n := by ring
      _ = ∑ i, b i ^ 2 * E.eigenvalue i ^ n := by
        rw [← Finset.sum_erase_add (Finset.univ)
          (fun i => b i ^ 2 * E.eigenvalue i ^ n) (Finset.mem_univ top)]
        simp [rest, dominant_eigenvalue]

/-- The balanced marked trace written in explicit orthogonal spectral data. -/
theorem marked_trace_eq_sum {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (f : Ω → ℝ) (a b : ℕ) :
    (Matrix.diagonal f * M ^ a * Matrix.diagonal f * M ^ b).trace
      = ∑ i, ∑ j,
          E.markedMatrix f i j * E.markedMatrix f j i
            * E.eigenvalue j ^ a * E.eigenvalue i ^ b := by
  rw [E.pow_eq a, E.pow_eq b]
  rw [show
      Matrix.diagonal f
          * (E.changeOfBasis * Matrix.diagonal (fun i => E.eigenvalue i ^ a)
              * E.changeOfBasisᵀ)
          * Matrix.diagonal f
          * (E.changeOfBasis * Matrix.diagonal (fun i => E.eigenvalue i ^ b)
              * E.changeOfBasisᵀ)
        =
          (Matrix.diagonal f * E.changeOfBasis
            * Matrix.diagonal (fun i => E.eigenvalue i ^ a)
            * E.changeOfBasisᵀ * Matrix.diagonal f * E.changeOfBasis
            * Matrix.diagonal (fun i => E.eigenvalue i ^ b))
            * E.changeOfBasisᵀ by
        noncomm_ring]
  rw [Matrix.trace_mul_comm]
  simp [markedMatrix, Matrix.mul_assoc]
  simpa [markedMatrix, Matrix.mul_assoc] using
    trace_marked_diagonal_pow_eq_sum (E.markedMatrix f) E.eigenvalue a b

/-- A nonnegative dominant spectral term gives a lower bound on the partition
spectral sum. -/
theorem partition_sum_lower_of_eigenvalue_nonnegative {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (top : Ω) (scale : ℝ)
    (dominant_eigenvalue : E.eigenvalue top = scale)
    (eigenvalue_nonnegative : ∀ i, 0 ≤ E.eigenvalue i)
    {N : ℕ} (_hN : 0 < N) :
    scale ^ N ≤ ∑ i, E.eigenvalue i ^ N := by
  have hterms : ∀ i ∈ (Finset.univ : Finset Ω), 0 ≤ E.eigenvalue i ^ N := by
    intro i _
    exact pow_nonneg (eigenvalue_nonnegative i) N
  have htop :=
    Finset.single_le_sum hterms (Finset.mem_univ top)
  simpa [dominant_eigenvalue] using htop

/-- A dominant index and a subdominant absolute bound imply the global
absolute eigenvalue bound. -/
theorem eigenvalue_abs_le_scale_of_dominant_bounds {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (top : Ω) (scale theta : ℝ)
    (scale_pos : 0 < scale)
    (theta_le_one : theta ≤ 1)
    (dominant_eigenvalue : E.eigenvalue top = scale)
    (subdominant_abs_le : ∀ i, i ≠ top → |E.eigenvalue i| ≤ theta * scale) :
    ∀ i, |E.eigenvalue i| ≤ scale := by
  intro i
  by_cases hitop : i = top
  · subst i
    simp [dominant_eigenvalue, abs_of_pos scale_pos]
  · calc
      |E.eigenvalue i| ≤ theta * scale := subdominant_abs_le i hitop
      _ ≤ scale := by
        exact (mul_le_iff_le_one_left scale_pos).2 theta_le_one

/-- A dominant eigenvalue and a uniform subdominant absolute bound give a finite
lower bound for the partition spectral sum. -/
theorem partition_sum_lower_of_dominant_bounds {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (top : Ω) (scale theta : ℝ)
    (scale_pos : 0 < scale)
    (theta_nonneg : 0 ≤ theta)
    (dominant_eigenvalue : E.eigenvalue top = scale)
    (subdominant_abs_le : ∀ i, i ≠ top → |E.eigenvalue i| ≤ theta * scale)
    {N : ℕ} (_hN : 0 < N) :
    scale ^ N - (((Fintype.card Ω - 1 : ℕ) : ℝ) * (theta * scale) ^ N)
      ≤ ∑ i, E.eigenvalue i ^ N := by
  let rest : Finset Ω := Finset.univ.erase top
  have htheta_scale_nonneg : 0 ≤ theta * scale :=
    mul_nonneg theta_nonneg scale_pos.le
  have hrest_term :
      ∀ i ∈ rest, -((theta * scale) ^ N) ≤ E.eigenvalue i ^ N := by
    intro i hi
    have hitop : i ≠ top := (Finset.mem_erase.mp hi).1
    have hpow_abs : |E.eigenvalue i ^ N| ≤ (theta * scale) ^ N := by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (subdominant_abs_le i hitop) N
    exact neg_le_of_abs_le hpow_abs
  have hrest_sum :
      ∑ i ∈ rest, -((theta * scale) ^ N)
        ≤ ∑ i ∈ rest, E.eigenvalue i ^ N :=
    Finset.sum_le_sum hrest_term
  have hrest_sum' :
      -(((Fintype.card Ω - 1 : ℕ) : ℝ) * (theta * scale) ^ N)
        ≤ ∑ i ∈ rest, E.eigenvalue i ^ N := by
    simpa [rest, Finset.sum_const, nsmul_eq_mul,
      Finset.card_erase_of_mem (Finset.mem_univ top)] using hrest_sum
  have hadd := add_le_add_left hrest_sum' (scale ^ N)
  calc
    scale ^ N - (((Fintype.card Ω - 1 : ℕ) : ℝ) * (theta * scale) ^ N)
        = scale ^ N
          + -(((Fintype.card Ω - 1 : ℕ) : ℝ) * (theta * scale) ^ N) := by ring
    _ ≤ scale ^ N + ∑ i ∈ rest, E.eigenvalue i ^ N := by
      simpa [add_comm, add_left_comm, add_assoc] using hadd
    _ = (∑ i ∈ rest, E.eigenvalue i ^ N) + scale ^ N := by ring
    _ = ∑ i, E.eigenvalue i ^ N := by
      rw [← Finset.sum_erase_add (Finset.univ) (fun i => E.eigenvalue i ^ N)
        (Finset.mem_univ top)]
      simp [rest, dominant_eigenvalue]

/-- The finite-cardinality dominant-bound partition estimate in certificate
prefactor form. -/
theorem partition_lower_of_dominant_bounds {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (top : Ω) (scale theta : ℝ)
    (scale_pos : 0 < scale)
    (theta_nonneg : 0 ≤ theta)
    (theta_le_one : theta ≤ 1)
    (dominant_eigenvalue : E.eigenvalue top = scale)
    (subdominant_abs_le : ∀ i, i ≠ top → |E.eigenvalue i| ≤ theta * scale)
    {N : ℕ} (hN : 0 < N) :
    finiteSpectralPartitionPrefactor Ω theta * scale ^ N
      ≤ ∑ i, E.eigenvalue i ^ N := by
  have hN_one : 1 ≤ N := hN
  have htheta_pow_le : theta ^ N ≤ theta := by
    simpa using pow_le_pow_of_le_one theta_nonneg theta_le_one hN_one
  have hscale_pow_nonneg : 0 ≤ scale ^ N := pow_nonneg scale_pos.le N
  have hcard_mul :
      (((Fintype.card Ω - 1 : ℕ) : ℝ) * (theta * scale) ^ N)
        ≤ (((Fintype.card Ω - 1 : ℕ) : ℝ) * theta) * scale ^ N := by
    rw [mul_pow]
    calc
      (((Fintype.card Ω - 1 : ℕ) : ℝ) * (theta ^ N * scale ^ N))
          ≤ ((Fintype.card Ω - 1 : ℕ) : ℝ) * (theta * scale ^ N) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right htheta_pow_le hscale_pow_nonneg)
              (Nat.cast_nonneg _)
      _ = (((Fintype.card Ω - 1 : ℕ) : ℝ) * theta) * scale ^ N := by ring
  have hprefactor_le :
      finiteSpectralPartitionPrefactor Ω theta * scale ^ N
        ≤ scale ^ N - (((Fintype.card Ω - 1 : ℕ) : ℝ) * (theta * scale) ^ N) := by
    calc
      finiteSpectralPartitionPrefactor Ω theta * scale ^ N
          = scale ^ N
            - (((Fintype.card Ω - 1 : ℕ) : ℝ) * theta) * scale ^ N := by
              rw [finiteSpectralPartitionPrefactor]
              ring
      _ ≤ scale ^ N - (((Fintype.card Ω - 1 : ℕ) : ℝ) * (theta * scale) ^ N) :=
            sub_le_sub_left hcard_mul (scale ^ N)
  exact hprefactor_le.trans
    (partition_sum_lower_of_dominant_bounds E top scale theta scale_pos
      theta_nonneg dominant_eigenvalue subdominant_abs_le hN)

/-- Spectral dominance and cancellation of the dominant marked column give the
one-sided marked-trace bound in the separation exponent. -/
theorem marked_sum_abs_le_spectralPrefactor {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (f : Ω → ℝ) (top : Ω)
    (scale theta : ℝ)
    (scale_pos : 0 < scale)
    (theta_nonneg : 0 ≤ theta)
    (eigenvalue_abs_le_scale : ∀ i, |E.eigenvalue i| ≤ scale)
    (subdominant_abs_le : ∀ i, i ≠ top → |E.eigenvalue i| ≤ theta * scale)
    (dominant_markedColumn_zero :
      ∀ i, E.markedMatrix f i top * E.markedMatrix f top i = 0)
    {a b : ℕ} (_ha : 0 < a) :
    |∑ i, ∑ j,
        E.markedMatrix f i j * E.markedMatrix f j i
          * E.eigenvalue j ^ a * E.eigenvalue i ^ b|
      ≤ E.markedSpectralPrefactor f * scale ^ (a + b) * theta ^ a := by
  let coeff : Ω → Ω → ℝ :=
    fun i j => E.markedMatrix f i j * E.markedMatrix f j i
  let term : Ω → Ω → ℝ :=
    fun i j => coeff i j * E.eigenvalue j ^ a * E.eigenvalue i ^ b
  have hscale_nonneg : 0 ≤ scale := scale_pos.le
  have htheta_scale_nonneg : 0 ≤ theta * scale :=
    mul_nonneg theta_nonneg hscale_nonneg
  have hsum :
      |∑ i, ∑ j, term i j| ≤ ∑ i, ∑ j, |term i j| := by
    calc
      |∑ i, ∑ j, term i j| ≤ ∑ i, |∑ j, term i j| :=
        Finset.abs_sum_le_sum_abs (fun i => ∑ j, term i j) Finset.univ
      _ ≤ ∑ i, ∑ j, |term i j| := by
        exact Finset.sum_le_sum fun i _ =>
          Finset.abs_sum_le_sum_abs (fun j => term i j) Finset.univ
  have hterm : ∀ i j, |term i j| ≤
      |coeff i j| * (scale ^ (a + b) * theta ^ a) := by
    intro i j
    by_cases hj : j = top
    · subst j
      have hcoeff : coeff i top = 0 := dominant_markedColumn_zero i
      simp [term, coeff, hcoeff]
    · have hjpow : |E.eigenvalue j| ^ a ≤ (theta * scale) ^ a :=
        pow_le_pow_left₀ (abs_nonneg _) (subdominant_abs_le j hj) a
      have hipow : |E.eigenvalue i| ^ b ≤ scale ^ b :=
        pow_le_pow_left₀ (abs_nonneg _) (eigenvalue_abs_le_scale i) b
      have hpow_mul :
          |E.eigenvalue j| ^ a * |E.eigenvalue i| ^ b
            ≤ (theta * scale) ^ a * scale ^ b :=
        mul_le_mul hjpow hipow (pow_nonneg (abs_nonneg _) b)
          (pow_nonneg htheta_scale_nonneg a)
      have hpow_eq :
          (theta * scale) ^ a * scale ^ b = scale ^ (a + b) * theta ^ a := by
        rw [mul_pow, pow_add]
        ring
      calc
        |term i j|
            = |coeff i j| * (|E.eigenvalue j| ^ a * |E.eigenvalue i| ^ b) := by
              simp [term, abs_mul, abs_pow, mul_assoc]
        _ ≤ |coeff i j| * ((theta * scale) ^ a * scale ^ b) :=
              mul_le_mul_of_nonneg_left hpow_mul (abs_nonneg _)
        _ = |coeff i j| * (scale ^ (a + b) * theta ^ a) := by
              rw [hpow_eq]
  calc
    |∑ i, ∑ j,
        E.markedMatrix f i j * E.markedMatrix f j i
          * E.eigenvalue j ^ a * E.eigenvalue i ^ b|
        = |∑ i, ∑ j, term i j| := rfl
    _ ≤ ∑ i, ∑ j, |term i j| := hsum
    _ ≤ ∑ i, ∑ j, |coeff i j| * (scale ^ (a + b) * theta ^ a) := by
      exact Finset.sum_le_sum fun i _ =>
        Finset.sum_le_sum fun j _ => hterm i j
    _ = E.markedSpectralPrefactor f * scale ^ (a + b) * theta ^ a := by
      simp [markedSpectralPrefactor, coeff, Finset.sum_mul, mul_assoc]

/-- Spectral dominance and cancellation of only the dominant-dominant marked
entry give a two-sided cyclic marked-trace bound.  This is the natural finite
cycle estimate: after the non-decaying `(top, top)` channel is removed, each
remaining spectral term has a subdominant eigenvalue on at least one arc. -/
theorem marked_sum_abs_le_spectralPrefactor_min {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (f : Ω → ℝ) (top : Ω)
    (scale theta : ℝ)
    (scale_pos : 0 < scale)
    (theta_nonneg : 0 ≤ theta)
    (theta_le_one : theta ≤ 1)
    (eigenvalue_abs_le_scale : ∀ i, |E.eigenvalue i| ≤ scale)
    (subdominant_abs_le : ∀ i, i ≠ top → |E.eigenvalue i| ≤ theta * scale)
    (dominant_markedDiagonal_zero : E.markedMatrix f top top = 0)
    {a b : ℕ} :
    |∑ i, ∑ j,
        E.markedMatrix f i j * E.markedMatrix f j i
          * E.eigenvalue j ^ a * E.eigenvalue i ^ b|
      ≤ E.markedSpectralPrefactor f * scale ^ (a + b) * theta ^ min a b := by
  let coeff : Ω → Ω → ℝ :=
    fun i j => E.markedMatrix f i j * E.markedMatrix f j i
  let term : Ω → Ω → ℝ :=
    fun i j => coeff i j * E.eigenvalue j ^ a * E.eigenvalue i ^ b
  have hscale_nonneg : 0 ≤ scale := scale_pos.le
  have htheta_scale_nonneg : 0 ≤ theta * scale :=
    mul_nonneg theta_nonneg hscale_nonneg
  have htheta_min_nonneg : 0 ≤ theta ^ min a b :=
    pow_nonneg theta_nonneg _
  have hsum :
      |∑ i, ∑ j, term i j| ≤ ∑ i, ∑ j, |term i j| := by
    calc
      |∑ i, ∑ j, term i j| ≤ ∑ i, |∑ j, term i j| :=
        Finset.abs_sum_le_sum_abs (fun i => ∑ j, term i j) Finset.univ
      _ ≤ ∑ i, ∑ j, |term i j| := by
        exact Finset.sum_le_sum fun i _ =>
          Finset.abs_sum_le_sum_abs (fun j => term i j) Finset.univ
  have hterm : ∀ i j, |term i j| ≤
      |coeff i j| * (scale ^ (a + b) * theta ^ min a b) := by
    intro i j
    by_cases hj : j = top
    · subst j
      by_cases hi : i = top
      · subst i
        have hcoeff : coeff top top = 0 := by
          simp [coeff, dominant_markedDiagonal_zero]
        simp [term, hcoeff]
      · have hjpow : |E.eigenvalue top| ^ a ≤ scale ^ a :=
          pow_le_pow_left₀ (abs_nonneg _) (eigenvalue_abs_le_scale top) a
        have hipow : |E.eigenvalue i| ^ b ≤ (theta * scale) ^ b :=
          pow_le_pow_left₀ (abs_nonneg _) (subdominant_abs_le i hi) b
        have hpow_mul :
            |E.eigenvalue top| ^ a * |E.eigenvalue i| ^ b
              ≤ scale ^ a * (theta * scale) ^ b :=
          mul_le_mul hjpow hipow (pow_nonneg (abs_nonneg _) b)
            (pow_nonneg hscale_nonneg a)
        have htheta_pow_le_min : theta ^ b ≤ theta ^ min a b :=
          pow_le_pow_of_le_one theta_nonneg theta_le_one (Nat.min_le_right a b)
        have hpow_eq :
            scale ^ a * (theta * scale) ^ b = scale ^ (a + b) * theta ^ b := by
          rw [mul_pow, pow_add]
          ring
        have hpow_target :
            scale ^ a * (theta * scale) ^ b
              ≤ scale ^ (a + b) * theta ^ min a b := by
          rw [hpow_eq]
          exact mul_le_mul_of_nonneg_left htheta_pow_le_min
            (pow_nonneg hscale_nonneg (a + b))
        calc
          |term i top|
              = |coeff i top| * (|E.eigenvalue top| ^ a * |E.eigenvalue i| ^ b) := by
                simp [term, abs_mul, abs_pow, mul_assoc]
          _ ≤ |coeff i top| * (scale ^ a * (theta * scale) ^ b) :=
                mul_le_mul_of_nonneg_left hpow_mul (abs_nonneg _)
          _ ≤ |coeff i top| * (scale ^ (a + b) * theta ^ min a b) :=
                mul_le_mul_of_nonneg_left hpow_target (abs_nonneg _)
    · have hjpow : |E.eigenvalue j| ^ a ≤ (theta * scale) ^ a :=
        pow_le_pow_left₀ (abs_nonneg _) (subdominant_abs_le j hj) a
      have hipow : |E.eigenvalue i| ^ b ≤ scale ^ b :=
        pow_le_pow_left₀ (abs_nonneg _) (eigenvalue_abs_le_scale i) b
      have hpow_mul :
          |E.eigenvalue j| ^ a * |E.eigenvalue i| ^ b
            ≤ (theta * scale) ^ a * scale ^ b :=
        mul_le_mul hjpow hipow (pow_nonneg (abs_nonneg _) b)
          (pow_nonneg htheta_scale_nonneg a)
      have htheta_pow_le_min : theta ^ a ≤ theta ^ min a b :=
        pow_le_pow_of_le_one theta_nonneg theta_le_one (Nat.min_le_left a b)
      have hpow_eq :
          (theta * scale) ^ a * scale ^ b = scale ^ (a + b) * theta ^ a := by
        rw [mul_pow, pow_add]
        ring
      have hpow_target :
          (theta * scale) ^ a * scale ^ b
            ≤ scale ^ (a + b) * theta ^ min a b := by
        rw [hpow_eq]
        exact mul_le_mul_of_nonneg_left htheta_pow_le_min
          (pow_nonneg hscale_nonneg (a + b))
      calc
        |term i j|
            = |coeff i j| * (|E.eigenvalue j| ^ a * |E.eigenvalue i| ^ b) := by
              simp [term, abs_mul, abs_pow, mul_assoc]
        _ ≤ |coeff i j| * ((theta * scale) ^ a * scale ^ b) :=
              mul_le_mul_of_nonneg_left hpow_mul (abs_nonneg _)
        _ ≤ |coeff i j| * (scale ^ (a + b) * theta ^ min a b) :=
              mul_le_mul_of_nonneg_left hpow_target (abs_nonneg _)
  calc
    |∑ i, ∑ j,
        E.markedMatrix f i j * E.markedMatrix f j i
          * E.eigenvalue j ^ a * E.eigenvalue i ^ b|
        = |∑ i, ∑ j, term i j| := rfl
    _ ≤ ∑ i, ∑ j, |term i j| := hsum
    _ ≤ ∑ i, ∑ j, |coeff i j| * (scale ^ (a + b) * theta ^ min a b) := by
      exact Finset.sum_le_sum fun i _ =>
        Finset.sum_le_sum fun j _ => hterm i j
    _ = E.markedSpectralPrefactor f * scale ^ (a + b) * theta ^ min a b := by
      simp [markedSpectralPrefactor, coeff, Finset.sum_mul, mul_assoc]

/-- A top-supported pair of boundary vectors and a zero dominant marked diagonal
give the central-channel cancellation needed for open boundary-vector marked
products. -/
theorem boundaryMarkedCentral_zero_of_topBoundary {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (f vL vR : Ω → ℝ) (top : Ω)
    (hL : ∀ i, i ≠ top → E.boundaryCoordinates vL i = 0)
    (hR : ∀ i, i ≠ top → E.boundaryCoordinates vR i = 0)
    (hG : E.markedMatrix f top top = 0) :
    ∀ i l,
      E.boundaryCoordinates vL i * E.markedMatrix f i top *
        E.markedMatrix f top l * E.boundaryCoordinates vR l = 0 := by
  intro i l
  by_cases hi : i = top
  · subst i
    by_cases hl : l = top
    · subst l
      simp [hG]
    · simp [hR l hl]
  · simp [hL i hi]

/-- Spectral dominance and central-channel cancellation give an open
boundary-vector marked numerator bound in the separation exponent. -/
theorem boundaryMarkedSpectralSum_abs_le_spectralPrefactor {M : Matrix Ω Ω ℝ}
    (E : RealOrthogonalSpectralData M) (f vL vR : Ω → ℝ)
    (top : Ω) (scale theta : ℝ)
    (scale_pos : 0 < scale)
    (theta_nonneg : 0 ≤ theta)
    (eigenvalue_abs_le_scale : ∀ i, |E.eigenvalue i| ≤ scale)
    (subdominant_abs_le : ∀ i, i ≠ top → |E.eigenvalue i| ≤ theta * scale)
    (central_dominant_channel_zero : ∀ i l,
      E.boundaryCoordinates vL i * E.markedMatrix f i top *
        E.markedMatrix f top l * E.boundaryCoordinates vR l = 0)
    (left sep right : ℕ) :
    |∑ i, ∑ j, ∑ l,
        E.boundaryCoordinates vL i * E.eigenvalue i ^ left *
        E.markedMatrix f i j * E.eigenvalue j ^ sep *
        E.markedMatrix f j l * E.eigenvalue l ^ right *
        E.boundaryCoordinates vR l|
      ≤ E.boundaryMarkedSpectralPrefactor f vL vR *
          scale ^ (left + sep + right) * theta ^ sep := by
  let coeff : Ω → Ω → Ω → ℝ :=
    fun i j l =>
      E.boundaryCoordinates vL i * E.markedMatrix f i j *
        E.markedMatrix f j l * E.boundaryCoordinates vR l
  let term : Ω → Ω → Ω → ℝ :=
    fun i j l =>
      coeff i j l * E.eigenvalue i ^ left * E.eigenvalue j ^ sep *
        E.eigenvalue l ^ right
  have hscale_nonneg : 0 ≤ scale := scale_pos.le
  have htheta_scale_nonneg : 0 ≤ theta * scale :=
    mul_nonneg theta_nonneg hscale_nonneg
  have hsum :
      |∑ i, ∑ j, ∑ l, term i j l| ≤ ∑ i, ∑ j, ∑ l, |term i j l| := by
    calc
      |∑ i, ∑ j, ∑ l, term i j l|
          ≤ ∑ i, |∑ j, ∑ l, term i j l| :=
            Finset.abs_sum_le_sum_abs (fun i => ∑ j, ∑ l, term i j l) Finset.univ
      _ ≤ ∑ i, ∑ j, |∑ l, term i j l| := by
            exact Finset.sum_le_sum fun i _ =>
              Finset.abs_sum_le_sum_abs (fun j => ∑ l, term i j l) Finset.univ
      _ ≤ ∑ i, ∑ j, ∑ l, |term i j l| := by
            exact Finset.sum_le_sum fun i _ =>
              Finset.sum_le_sum fun j _ =>
                Finset.abs_sum_le_sum_abs (fun l => term i j l) Finset.univ
  have hterm : ∀ i j l, |term i j l| ≤
      |coeff i j l| * (scale ^ (left + sep + right) * theta ^ sep) := by
    intro i j l
    by_cases hj : j = top
    · subst j
      have hcoeff : coeff i top l = 0 := central_dominant_channel_zero i l
      simp [term, hcoeff]
    · have hipow : |E.eigenvalue i| ^ left ≤ scale ^ left :=
        pow_le_pow_left₀ (abs_nonneg _) (eigenvalue_abs_le_scale i) left
      have hjpow : |E.eigenvalue j| ^ sep ≤ (theta * scale) ^ sep :=
        pow_le_pow_left₀ (abs_nonneg _) (subdominant_abs_le j hj) sep
      have hlpow : |E.eigenvalue l| ^ right ≤ scale ^ right :=
        pow_le_pow_left₀ (abs_nonneg _) (eigenvalue_abs_le_scale l) right
      have hpow_mul :
          |E.eigenvalue i| ^ left * |E.eigenvalue j| ^ sep *
              |E.eigenvalue l| ^ right
            ≤ scale ^ left * (theta * scale) ^ sep * scale ^ right := by
        exact mul_le_mul
          (mul_le_mul hipow hjpow (pow_nonneg (abs_nonneg _) sep)
            (pow_nonneg hscale_nonneg left))
          hlpow (pow_nonneg (abs_nonneg _) right)
          (mul_nonneg (pow_nonneg hscale_nonneg left)
            (pow_nonneg htheta_scale_nonneg sep))
      have hpow_eq :
          scale ^ left * (theta * scale) ^ sep * scale ^ right =
            scale ^ (left + sep + right) * theta ^ sep := by
        rw [mul_pow, pow_add, pow_add]
        ring
      calc
        |term i j l|
            = |coeff i j l| *
                (|E.eigenvalue i| ^ left * |E.eigenvalue j| ^ sep *
                  |E.eigenvalue l| ^ right) := by
              simp [term, abs_mul, abs_pow, mul_assoc]
        _ ≤ |coeff i j l| *
              (scale ^ left * (theta * scale) ^ sep * scale ^ right) :=
                mul_le_mul_of_nonneg_left hpow_mul (abs_nonneg _)
        _ = |coeff i j l| * (scale ^ (left + sep + right) * theta ^ sep) := by
              rw [hpow_eq]
  calc
    |∑ i, ∑ j, ∑ l,
        E.boundaryCoordinates vL i * E.eigenvalue i ^ left *
        E.markedMatrix f i j * E.eigenvalue j ^ sep *
        E.markedMatrix f j l * E.eigenvalue l ^ right *
        E.boundaryCoordinates vR l|
        = |∑ i, ∑ j, ∑ l, term i j l| := by
            congr 1
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            apply Finset.sum_congr rfl
            intro l _
            simp [term, coeff]
            ring
    _ ≤ ∑ i, ∑ j, ∑ l, |term i j l| := hsum
    _ ≤ ∑ i, ∑ j, ∑ l,
          |coeff i j l| * (scale ^ (left + sep + right) * theta ^ sep) := by
            exact Finset.sum_le_sum fun i _ =>
              Finset.sum_le_sum fun j _ =>
                Finset.sum_le_sum fun l _ => hterm i j l
    _ = E.boundaryMarkedSpectralPrefactor f vL vR *
          scale ^ (left + sep + right) * theta ^ sep := by
            simp [boundaryMarkedSpectralPrefactor, coeff, Finset.sum_mul, mul_assoc]

end RealOrthogonalSpectralData

end TransferMatrix

end IsingModel
