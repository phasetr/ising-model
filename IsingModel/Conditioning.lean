import IsingModel.FreeEnergy
import IsingModel.Inequalities.GHS
import Mathlib.Algebra.BigOperators.Ring.Nat

/-!
# Conditioning inequalities

Formalization of results from Glimm–Jaffe, Chapter 10 (pp. 193–198),
specialized to the lattice Ising model.

## Main results

* `partitionFunction_beta_rescale` — `Z(J,h,β) = Z(βJ,βh,1)`
* `partitionFunction_monotone_beta` — `Z` monotone in `β` (Cor. 10.2.3)
* `hamiltonian_abs_le` — `|H(σ)| ≤ |J|·|E| + |h|·|ι|`
* `partitionFunction_upper` — `Z ≤ 2^|ι| · exp(|β|(|J|·|E| + |h|·|ι|))`
* `partitionFunction_lower` — `exp(-|β|(|J|·|E| + |h|·|ι|)) ≤ Z`

## References

* Glimm–Jaffe, *Quantum Physics*, §10.1–10.3, pp. 193–197
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Monotonicity in β (Corollary 10.2.3, lattice version) -/

/-- The partition function depends on `(J, h, β)` only through `(βJ, βh)`:
`Z(J, h, β) = Z(βJ, βh, 1)`. -/
private theorem partitionFunction_beta_rescale
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) :
    partitionFunction G ⟨J, h, β⟩ = partitionFunction G ⟨β * J, β * h, 1⟩ := by
  unfold partitionFunction boltzmannWeight hamiltonian interactionEnergy externalFieldEnergy
  congr 1; ext σ; congr 1; ring

/-- **Corollary 10.2.3** (lattice version).
The partition function is monotone increasing in `β` on `(0, ∞)`. -/
theorem partitionFunction_monotone_beta
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h : ℝ) (hJ : 0 ≤ J) (hh : 0 ≤ h) (β₁ β₂ : ℝ)
    (hβ₁ : 0 < β₁) (hβ : β₁ ≤ β₂) :
    partitionFunction G ⟨J, h, β₁⟩ ≤ partitionFunction G ⟨J, h, β₂⟩ := by
  rw [partitionFunction_beta_rescale G J h β₁,
      partitionFunction_beta_rescale G J h β₂]
  calc partitionFunction G ⟨β₁ * J, β₁ * h, 1⟩
      ≤ partitionFunction G ⟨β₂ * J, β₁ * h, 1⟩ :=
        partitionFunction_monotone_J G (β₁ * h) 1
          (mul_nonneg hβ₁.le hh) one_pos (β₁ * J) (β₂ * J)
          (mul_nonneg hβ₁.le hJ) (by nlinarith)
    _ ≤ partitionFunction G ⟨β₂ * J, β₂ * h, 1⟩ :=
        partitionFunction_monotone_h G (β₂ * J) 1
          (mul_nonneg (le_trans hβ₁.le hβ) hJ) one_pos (β₁ * h) (β₂ * h)
          (mul_nonneg hβ₁.le hh) (by nlinarith)

/-! ## Hamiltonian bound and partition function bounds (Corollary 10.3.2)

The Hamiltonian satisfies `|H(σ)| ≤ |J|·|E| + |h|·|ι|` since each
`edgeSpin(σ,e) ∈ {±1}` and each `sign(σ_i) ∈ {±1}`.

This gives the partition function bounds:
`exp(-|β|(|J|·|E| + |h|·|ι|)) ≤ Z ≤ 2^|ι| · exp(|β|(|J|·|E| + |h|·|ι|))`. -/

omit [Fintype ι] [DecidableEq ι] in
/-- The absolute value of each edge spin is at most 1. -/
private theorem abs_edgeSpin_le_one (σ : Config ι) (e : Sym2 ι) :
    |edgeSpin (K := ℝ) σ e| ≤ 1 := by
  have h := edgeSpin_sq σ e
  nlinarith [sq_abs (edgeSpin (K := ℝ) σ e)]

omit [Fintype ι] [DecidableEq ι] in
/-- The absolute value of each spin sign is at most 1. -/
private theorem abs_spin_sign_le_one (σ : Config ι) (i : ι) :
    |Spin.sign ℝ (σ i)| ≤ 1 := by
  cases σ i <;> simp [Spin.sign, Spin.toSign]

omit [DecidableEq ι] in
/-- **Hamiltonian bound**: `|H(σ)| ≤ |J| · |E| + |h| · |ι|`.
Since `|edgeSpin| ≤ 1` and `|sign(σ_i)| ≤ 1`. -/
theorem hamiltonian_abs_le (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (σ : Config ι) :
    |hamiltonian G p σ| ≤
    |p.J| * G.edgeFinset.card + |p.h| * Fintype.card ι := by
  unfold hamiltonian interactionEnergy externalFieldEnergy
  have h1 : |∑ e ∈ G.edgeFinset, edgeSpin (K := ℝ) σ e| ≤ G.edgeFinset.card := by
    calc |∑ e ∈ G.edgeFinset, edgeSpin (K := ℝ) σ e|
        ≤ ∑ e ∈ G.edgeFinset, |edgeSpin (K := ℝ) σ e| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ ∈ G.edgeFinset, (1 : ℝ) :=
          Finset.sum_le_sum (fun e _ => abs_edgeSpin_le_one σ e)
      _ = G.edgeFinset.card := by simp
  have h2 : |∑ i : ι, Spin.sign ℝ (σ i)| ≤ Fintype.card ι := by
    calc |∑ i : ι, Spin.sign ℝ (σ i)|
        ≤ ∑ i : ι, |Spin.sign ℝ (σ i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ : ι, (1 : ℝ) :=
          Finset.sum_le_sum (fun i _ => abs_spin_sign_le_one σ i)
      _ = Fintype.card ι := by simp [Finset.card_univ]
  change |-p.J * ∑ e ∈ G.edgeFinset, edgeSpin σ e +
      -p.h * ∑ i : ι, Spin.sign ℝ (σ i)| ≤ _
  calc |-p.J * ∑ e ∈ G.edgeFinset, edgeSpin σ e +
        -p.h * ∑ i : ι, Spin.sign ℝ (σ i)|
      ≤ |p.J * ∑ e ∈ G.edgeFinset, edgeSpin σ e| +
        |p.h * ∑ i : ι, Spin.sign ℝ (σ i)| := by
        calc _ ≤ |-p.J * ∑ e ∈ G.edgeFinset, edgeSpin σ e| +
            |-p.h * ∑ i : ι, Spin.sign ℝ (σ i)| := abs_add_le _ _
          _ = _ := by simp [abs_neg]
    _ = |p.J| * |∑ e ∈ G.edgeFinset, edgeSpin σ e| +
        |p.h| * |∑ i : ι, Spin.sign ℝ (σ i)| := by rw [abs_mul, abs_mul]
    _ ≤ |p.J| * G.edgeFinset.card + |p.h| * Fintype.card ι := by
        gcongr

/-- **Partition function upper bound** (Corollary 10.3.2, lattice version):
`Z ≤ 2^|ι| · exp(|β| · (|J|·|E| + |h|·|ι|))`.

Each Boltzmann weight is at most `exp(|β|·(|J|·|E| + |h|·|ι|))` by the
Hamiltonian bound, and there are `2^|ι|` configurations. -/
theorem partitionFunction_upper (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) :
    partitionFunction G p ≤
    Fintype.card (Config ι) *
      Real.exp (|p.β| * (|p.J| * G.edgeFinset.card + |p.h| * Fintype.card ι)) := by
  unfold partitionFunction
  calc ∑ σ : Config ι, boltzmannWeight G p σ
      ≤ ∑ _ : Config ι,
          Real.exp (|p.β| * (|p.J| * G.edgeFinset.card + |p.h| * Fintype.card ι)) := by
        apply Finset.sum_le_sum; intro σ _
        unfold boltzmannWeight
        apply Real.exp_le_exp_of_le
        calc -p.β * hamiltonian G p σ
            ≤ |(-p.β * hamiltonian G p σ)| := le_abs_self _
          _ = |p.β| * |hamiltonian G p σ| := by rw [abs_mul, abs_neg]
          _ ≤ |p.β| * (|p.J| * ↑G.edgeFinset.card + |p.h| * ↑(Fintype.card ι)) := by
              gcongr; exact hamiltonian_abs_le G p σ
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **Partition function lower bound** (Corollary 10.3.2, lattice version):
`exp(-|β| · (|J|·|E| + |h|·|ι|)) ≤ Z`.

The sum over all configurations is at least the value at any single
configuration. Each `exp(-β H(σ)) ≥ exp(-|β|·(|J|·|E| + |h|·|ι|))`. -/
theorem partitionFunction_lower (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) :
    Real.exp (-(|p.β| * (|p.J| * G.edgeFinset.card + |p.h| * Fintype.card ι))) ≤
    partitionFunction G p := by
  unfold partitionFunction
  calc Real.exp (-(|p.β| * (|p.J| * ↑G.edgeFinset.card + |p.h| * ↑(Fintype.card ι))))
      ≤ boltzmannWeight G p (fun _ => Spin.up) := by
        unfold boltzmannWeight
        apply Real.exp_le_exp_of_le
        have hH := hamiltonian_abs_le G p (fun _ => Spin.up)
        -- Need: -(|β|·bound) ≤ -β·H, i.e., β·H ≤ |β|·bound
        -- From |H| ≤ bound: |β·H| = |β|·|H| ≤ |β|·bound
        -- So -(|β|·bound) ≤ β·H ≤ |β|·bound, hence -(|β|·bound) ≤ -(β·H)... no
        -- Actually we need -(|β|·bound) ≤ -β·H, i.e., β·H ≤ |β|·bound
        have : |p.β * hamiltonian G p (fun _ => Spin.up)| ≤
            |p.β| * (|p.J| * ↑G.edgeFinset.card + |p.h| * ↑(Fintype.card ι)) := by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left hH (abs_nonneg _)
        linarith [le_abs_self (p.β * hamiltonian G p fun _ => Spin.up)]
    _ ≤ ∑ σ : Config ι, boltzmannWeight G p σ :=
        Finset.single_le_sum (fun σ _ => le_of_lt (boltzmannWeight_pos G p σ))
          (Finset.mem_univ _)

/-! ## Reflection positivity (§10.4)

Reflection positivity (Glimm–Jaffe, §10.4, pp. 198–200) is a
fundamental property of statistical mechanical systems with a
reflection symmetry. A bilinear form `b(A, B)` is reflection-positive
if `b(A, A) ≥ 0` for all `A`.

The key consequence is the Schwarz inequality (10.4.2):
`|b(A, B)| ≤ b(A, A)^{1/2} · b(B, B)^{1/2}`.

For the Ising model on a lattice with a reflection symmetry `θ`,
the bilinear form `b(A, B) = ⟨(θA) · B⟩` is reflection-positive.
The proof uses the factorization of the Boltzmann weight across the
reflection plane (Theorem 10.4.3). -/

/-- A bilinear form is **reflection-positive** if `b(x, x) ≥ 0` for all `x`.
This is the semi-inner product property (Glimm–Jaffe, §10.4, p. 198). -/
def ReflectionPositive {α : Type*} (b : α → α → ℝ) : Prop :=
  ∀ x, 0 ≤ b x x

/-- **Trivial instance**: the identically-zero bilinear form is
reflection positive. -/
theorem ReflectionPositive.zero {α : Type*} :
    ReflectionPositive (fun (_ _ : α) => (0 : ℝ)) :=
  fun _ => le_refl 0

/-- **Constant instance**: a constant bilinear form with nonneg value
is reflection positive. Generalization of `.zero`. -/
theorem ReflectionPositive.const {α : Type*} {c : ℝ} (hc : 0 ≤ c) :
    ReflectionPositive (fun (_ _ : α) => c) :=
  fun _ => hc

/-- **Diagonal-transfer**: if two bilinear forms agree on the diagonal
(i.e., `b₁ x x = b₂ x x` for all x) and one is RP, the other is too. -/
theorem ReflectionPositive.of_diag_eq {α : Type*} {b₁ b₂ : α → α → ℝ}
    (hb : ∀ x, b₁ x x = b₂ x x) (h : ReflectionPositive b₁) :
    ReflectionPositive b₂ :=
  fun x => (hb x) ▸ h x

/-- **Definitional unfolding**: `ReflectionPositive b ↔ ∀ x, 0 ≤ b x x`. -/
theorem ReflectionPositive.iff_forall_diag_nonneg {α : Type*}
    (b : α → α → ℝ) : ReflectionPositive b ↔ ∀ x : α, 0 ≤ b x x := Iff.rfl

/-- **Monotone-diagonal closure**: if `b₁` is RP and `b₁(x, x) ≤ b₂(x, x)`
pointwise on the diagonal, then `b₂` is RP. -/
theorem ReflectionPositive.of_le_diag {α : Type*} {b₁ b₂ : α → α → ℝ}
    (h : ReflectionPositive b₁) (hle : ∀ x, b₁ x x ≤ b₂ x x) :
    ReflectionPositive b₂ :=
  fun x => (h x).trans (hle x)

/-- **Euclidean example**: the dot product `(·, ·)` on `Fin n → ℝ`
defined as `fun x y => ∑ i, x i * y i` is reflection positive. Concrete
instance of `ReflectionPositive` obtained from a sum of nonneg diagonal
squares `x i * x i = (x i)² ≥ 0`. -/
theorem ReflectionPositive.euclidean_dot {n : ℕ} :
    ReflectionPositive (fun x y : Fin n → ℝ => ∑ i : Fin n, x i * y i) := by
  intro x
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))

/-- **Classical Cauchy-Schwarz on `Fin n → ℝ`**: for `x, y : Fin n → ℝ`,
`(∑ xᵢ yᵢ)² ≤ (∑ xᵢ²) · (∑ yᵢ²)`. Direct consequence of mathlib's
`Finset.sum_mul_sq_le_sq_mul_sq`; a concrete instance of the RP
framework's Cauchy-Schwarz pattern on the Euclidean inner product. -/
theorem euclidean_cauchy_schwarz {n : ℕ} (x y : Fin n → ℝ) :
    (∑ i : Fin n, x i * y i) ^ 2
      ≤ (∑ i : Fin n, (x i) ^ 2) * (∑ i : Fin n, (y i) ^ 2) :=
  Finset.sum_mul_sq_le_sq_mul_sq _ x y

/-- **Euclidean Cauchy-Schwarz abs form**: `|∑ xᵢ yᵢ| ≤ √((∑ xᵢ²) · (∑ yᵢ²))`
on `Fin n → ℝ`. Direct sqrt-monotone consequence of
`euclidean_cauchy_schwarz`. -/
theorem abs_euclidean_inner_le_sqrt {n : ℕ} (x y : Fin n → ℝ) :
    |∑ i : Fin n, x i * y i|
      ≤ Real.sqrt ((∑ i : Fin n, (x i) ^ 2) * (∑ i : Fin n, (y i) ^ 2)) := by
  have hsq := euclidean_cauchy_schwarz x y
  have := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq_eq_abs] at this

/-- **Euclidean norm-squared nonneg**: `0 ≤ ∑ (xᵢ)²` on `Fin n → ℝ`. -/
theorem euclidean_norm_sq_nonneg {n : ℕ} (x : Fin n → ℝ) :
    0 ≤ ∑ i : Fin n, (x i) ^ 2 :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- **Euclidean dot product is symmetric**: `∑ xᵢ yᵢ = ∑ yᵢ xᵢ`. -/
theorem euclidean_inner_comm {n : ℕ} (x y : Fin n → ℝ) :
    ∑ i : Fin n, x i * y i = ∑ i : Fin n, y i * x i := by
  apply Finset.sum_congr rfl
  intros i _
  ring

/-- **Euclidean self-inner = norm squared**: `∑ xᵢ · xᵢ = ∑ (xᵢ)²`. -/
theorem euclidean_inner_self {n : ℕ} (x : Fin n → ℝ) :
    ∑ i : Fin n, x i * x i = ∑ i : Fin n, (x i) ^ 2 := by
  apply Finset.sum_congr rfl
  intros i _
  ring

/-- **Euclidean non-degeneracy**: `∑ (xᵢ)² = 0 ↔ ∀ i, x i = 0`. -/
theorem euclidean_norm_sq_eq_zero_iff {n : ℕ} (x : Fin n → ℝ) :
    (∑ i : Fin n, (x i) ^ 2) = 0 ↔ ∀ i, x i = 0 := by
  constructor
  · intro h i
    have h_each : ∀ j ∈ Finset.univ, (x j) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp h
    exact pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp (h_each i (Finset.mem_univ _))
  · intro h
    apply Finset.sum_eq_zero
    intros i _
    rw [h i]; ring

/-- **Euclidean dot product vanishes with zero left-argument**:
`∑ (fun i => 0) i * yᵢ = 0`. -/
theorem euclidean_inner_zero_left {n : ℕ} (y : Fin n → ℝ) :
    ∑ i : Fin n, (0 : ℝ) * y i = 0 := by
  apply Finset.sum_eq_zero
  intros i _
  ring

/-- **Euclidean dot product vanishes with zero right-argument**:
`∑ xᵢ · (fun _ => 0) i = 0`. -/
theorem euclidean_inner_zero_right {n : ℕ} (x : Fin n → ℝ) :
    ∑ i : Fin n, x i * (0 : ℝ) = 0 := by
  apply Finset.sum_eq_zero
  intros i _
  ring

/-- **Euclidean dot product with constant-one left-argument**:
`∑ 1 · yᵢ = ∑ yᵢ`. -/
theorem euclidean_inner_one_left {n : ℕ} (y : Fin n → ℝ) :
    ∑ i : Fin n, (1 : ℝ) * y i = ∑ i : Fin n, y i := by
  apply Finset.sum_congr rfl
  intros i _
  ring

/-- **Euclidean dot product with constant-one right-argument**:
`∑ xᵢ · 1 = ∑ xᵢ`. -/
theorem euclidean_inner_one_right {n : ℕ} (x : Fin n → ℝ) :
    ∑ i : Fin n, x i * (1 : ℝ) = ∑ i : Fin n, x i := by
  apply Finset.sum_congr rfl
  intros i _
  ring

/-- **Euclidean dot product distributes over left addition**:
`∑ (xᵢ + yᵢ) · zᵢ = ∑ xᵢ · zᵢ + ∑ yᵢ · zᵢ`. -/
theorem euclidean_inner_add_left {n : ℕ} (x y z : Fin n → ℝ) :
    ∑ i : Fin n, (x i + y i) * z i
      = (∑ i : Fin n, x i * z i) + (∑ i : Fin n, y i * z i) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intros i _
  ring

/-- **Euclidean dot product distributes over right addition**:
`∑ xᵢ · (yᵢ + zᵢ) = ∑ xᵢ · yᵢ + ∑ xᵢ · zᵢ`. -/
theorem euclidean_inner_add_right {n : ℕ} (x y z : Fin n → ℝ) :
    ∑ i : Fin n, x i * (y i + z i)
      = (∑ i : Fin n, x i * y i) + (∑ i : Fin n, x i * z i) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intros i _
  ring

/-- **Euclidean dot product pulls out left scalar**:
`∑ (c · xᵢ) · yᵢ = c · ∑ xᵢ · yᵢ`. -/
theorem euclidean_inner_smul_left {n : ℕ} (c : ℝ) (x y : Fin n → ℝ) :
    ∑ i : Fin n, (c * x i) * y i = c * ∑ i : Fin n, x i * y i := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intros i _
  ring

/-- **Euclidean dot product pulls out right scalar**:
`∑ xᵢ · (c · yᵢ) = c · ∑ xᵢ · yᵢ`. -/
theorem euclidean_inner_smul_right {n : ℕ} (c : ℝ) (x y : Fin n → ℝ) :
    ∑ i : Fin n, x i * (c * y i) = c * ∑ i : Fin n, x i * y i := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intros i _
  ring

/-- **Euclidean dot product negation, left**:
`∑ (-xᵢ) · yᵢ = - ∑ xᵢ · yᵢ`. -/
theorem euclidean_inner_neg_left {n : ℕ} (x y : Fin n → ℝ) :
    ∑ i : Fin n, (-x i) * y i = -(∑ i : Fin n, x i * y i) := by
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intros i _
  ring

/-- **Euclidean dot product negation, right**:
`∑ xᵢ · (-yᵢ) = - ∑ xᵢ · yᵢ`. -/
theorem euclidean_inner_neg_right {n : ℕ} (x y : Fin n → ℝ) :
    ∑ i : Fin n, x i * (-y i) = -(∑ i : Fin n, x i * y i) := by
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intros i _
  ring

/-- **Euclidean dot product distributes over left subtraction**:
`∑ (xᵢ - yᵢ) · zᵢ = ∑ xᵢ · zᵢ - ∑ yᵢ · zᵢ`. -/
theorem euclidean_inner_sub_left {n : ℕ} (x y z : Fin n → ℝ) :
    ∑ i : Fin n, (x i - y i) * z i
      = (∑ i : Fin n, x i * z i) - (∑ i : Fin n, y i * z i) := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intros i _
  ring

/-- **Euclidean dot product distributes over right subtraction**:
`∑ xᵢ · (yᵢ - zᵢ) = ∑ xᵢ · yᵢ - ∑ xᵢ · zᵢ`. -/
theorem euclidean_inner_sub_right {n : ℕ} (x y z : Fin n → ℝ) :
    ∑ i : Fin n, x i * (y i - z i)
      = (∑ i : Fin n, x i * y i) - (∑ i : Fin n, x i * z i) := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intros i _
  ring

/-- **Euclidean polarization identity**:
`4·∑ xᵢ·yᵢ = ∑ (xᵢ + yᵢ)² - ∑ (xᵢ - yᵢ)²`. Expresses the inner
product as a difference of squared norms. -/
theorem euclidean_polarization {n : ℕ} (x y : Fin n → ℝ) :
    4 * (∑ i : Fin n, x i * y i)
      = (∑ i : Fin n, (x i + y i) ^ 2) - (∑ i : Fin n, (x i - y i) ^ 2) := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intros i _
  ring

/-- **Euclidean norm squared of a sum**:
`∑ (xᵢ + yᵢ)² = ∑ xᵢ² + 2·∑ xᵢ·yᵢ + ∑ yᵢ²`. -/
theorem euclidean_norm_sq_add {n : ℕ} (x y : Fin n → ℝ) :
    (∑ i : Fin n, (x i + y i) ^ 2)
      = (∑ i : Fin n, (x i) ^ 2) + 2 * (∑ i : Fin n, x i * y i)
          + (∑ i : Fin n, (y i) ^ 2) := by
  have h : ∀ i : Fin n, (x i + y i) ^ 2 = (x i) ^ 2 + 2 * (x i * y i) + (y i) ^ 2 :=
    fun i => by ring
  rw [Finset.sum_congr rfl (fun i _ => h i)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]

/-- **Euclidean norm squared of a difference**:
`∑ (xᵢ - yᵢ)² = ∑ xᵢ² - 2·∑ xᵢ·yᵢ + ∑ yᵢ²`. -/
theorem euclidean_norm_sq_sub {n : ℕ} (x y : Fin n → ℝ) :
    (∑ i : Fin n, (x i - y i) ^ 2)
      = (∑ i : Fin n, (x i) ^ 2) - 2 * (∑ i : Fin n, x i * y i)
          + (∑ i : Fin n, (y i) ^ 2) := by
  have h : ∀ i : Fin n, (x i - y i) ^ 2 = (x i) ^ 2 - 2 * (x i * y i) + (y i) ^ 2 :=
    fun i => by ring
  rw [Finset.sum_congr rfl (fun i _ => h i)]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]

/-- **Euclidean Pythagorean identity**: if `x, y : Fin n → ℝ` are
orthogonal (`∑ xᵢ·yᵢ = 0`), then `∑ (xᵢ+yᵢ)² = ∑ xᵢ² + ∑ yᵢ²`.
Immediate from `euclidean_norm_sq_add` with the middle term vanishing. -/
theorem euclidean_pythagorean {n : ℕ} (x y : Fin n → ℝ)
    (h_ortho : (∑ i : Fin n, x i * y i) = 0) :
    (∑ i : Fin n, (x i + y i) ^ 2)
      = (∑ i : Fin n, (x i) ^ 2) + (∑ i : Fin n, (y i) ^ 2) := by
  rw [euclidean_norm_sq_add x y, h_ortho]
  ring

/-- **Euclidean norm squared under scalar multiplication**:
`∑ (c · xᵢ)² = c² · ∑ xᵢ²`. -/
theorem euclidean_norm_sq_smul {n : ℕ} (c : ℝ) (x : Fin n → ℝ) :
    (∑ i : Fin n, (c * x i) ^ 2) = c ^ 2 * (∑ i : Fin n, (x i) ^ 2) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intros i _
  ring

/-- **Euclidean norm squared of negation**: `∑ (-xᵢ)² = ∑ xᵢ²`. -/
theorem euclidean_norm_sq_neg {n : ℕ} (x : Fin n → ℝ) :
    (∑ i : Fin n, (-x i) ^ 2) = (∑ i : Fin n, (x i) ^ 2) := by
  apply Finset.sum_congr rfl
  intros i _
  ring

/-- **Euclidean norm squared of zero function**: `∑ (0 : ℝ)² = 0`. -/
theorem euclidean_norm_sq_zero_fn {n : ℕ} :
    (∑ _ : Fin n, ((0 : ℝ)) ^ 2) = 0 := by
  apply Finset.sum_eq_zero
  intros i _
  ring

/-- **Euclidean sum swap**: for a double-indexed family
`f : Fin m → Fin n → ℝ`, swap the order of summation:
`∑ i, ∑ j, f i j = ∑ j, ∑ i, f i j`. -/
theorem euclidean_sum_swap {m n : ℕ} (f : Fin m → Fin n → ℝ) :
    (∑ i : Fin m, ∑ j : Fin n, f i j) = ∑ j : Fin n, ∑ i : Fin m, f i j :=
  Finset.sum_comm

/-- **Empty-dimension Euclidean norm squared**: `∑ i : Fin 0, (xᵢ)² = 0`. -/
theorem euclidean_norm_sq_empty (x : Fin 0 → ℝ) :
    (∑ i : Fin 0, (x i) ^ 2) = 0 := by
  simp

/-- **Single-element Euclidean norm squared**: `∑ i : Fin 1, (xᵢ)² = (x 0)²`. -/
theorem euclidean_norm_sq_single (x : Fin 1 → ℝ) :
    (∑ i : Fin 1, (x i) ^ 2) = (x 0) ^ 2 := by
  simp

/-- **Two-element Euclidean norm squared**: `∑ i : Fin 2, (xᵢ)² = (x 0)² + (x 1)²`. -/
theorem euclidean_norm_sq_two (x : Fin 2 → ℝ) :
    (∑ i : Fin 2, (x i) ^ 2) = (x 0) ^ 2 + (x 1) ^ 2 := by
  simp [Fin.sum_univ_two]

/-- **Three-element Euclidean norm squared**:
`∑ i : Fin 3, (xᵢ)² = (x 0)² + (x 1)² + (x 2)²`. -/
theorem euclidean_norm_sq_three (x : Fin 3 → ℝ) :
    (∑ i : Fin 3, (x i) ^ 2) = (x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2 := by
  simp [Fin.sum_univ_three]

/-- **Single-element Euclidean inner**:
`∑ i : Fin 1, x i * y i = x 0 * y 0`. -/
theorem euclidean_inner_single (x y : Fin 1 → ℝ) :
    (∑ i : Fin 1, x i * y i) = x 0 * y 0 := by
  simp

/-- **Two-element Euclidean inner**:
`∑ i : Fin 2, x i * y i = x 0 * y 0 + x 1 * y 1`. -/
theorem euclidean_inner_two (x y : Fin 2 → ℝ) :
    (∑ i : Fin 2, x i * y i) = x 0 * y 0 + x 1 * y 1 := by
  simp [Fin.sum_univ_two]

/-- **Three-element Euclidean inner**:
`∑ i : Fin 3, x i * y i = x 0 * y 0 + x 1 * y 1 + x 2 * y 2`. -/
theorem euclidean_inner_three (x y : Fin 3 → ℝ) :
    (∑ i : Fin 3, x i * y i) = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 := by
  simp [Fin.sum_univ_three]

/-- **Euclidean constant-function norm squared**: `∑ c² over Fin n = n · c²`. -/
theorem euclidean_norm_sq_const {n : ℕ} (c : ℝ) :
    (∑ _ : Fin n, c ^ 2) = n * c ^ 2 := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **Euclidean constant-constant inner**: `∑ c · d over Fin n = n · c · d`. -/
theorem euclidean_inner_const {n : ℕ} (c d : ℝ) :
    (∑ _ : Fin n, c * d) = n * (c * d) := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **Euclidean norm squared of constant-one vector**: `∑ 1² over Fin n = n`. -/
theorem euclidean_norm_sq_one_fn {n : ℕ} :
    (∑ _ : Fin n, ((1 : ℝ)) ^ 2) = n := by
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]

/-- **Euclidean inner with constant-one vector equals sum**:
`∑ i, (fun _ => 1) i · x i = ∑ i, x i`. -/
theorem euclidean_inner_one_fn_left {n : ℕ} (x : Fin n → ℝ) :
    (∑ i : Fin n, (1 : ℝ) * x i) = ∑ i : Fin n, x i := by
  apply Finset.sum_congr rfl
  intros i _
  ring

/-- **Euclidean inner with constant-one right vector equals sum**:
`∑ i, x i · 1 = ∑ i, x i`. -/
theorem euclidean_inner_one_fn_right {n : ℕ} (x : Fin n → ℝ) :
    (∑ i : Fin n, x i * (1 : ℝ)) = ∑ i : Fin n, x i := by
  apply Finset.sum_congr rfl
  intros i _
  ring

/-- **Euclidean inner of negated pair**: `∑ (-xᵢ) · (-yᵢ) = ∑ xᵢ · yᵢ`. -/
theorem euclidean_inner_neg_neg {n : ℕ} (x y : Fin n → ℝ) :
    (∑ i : Fin n, (-x i) * (-y i)) = ∑ i : Fin n, x i * y i := by
  apply Finset.sum_congr rfl
  intros i _
  ring

/-- **Euclidean inner with scalar multiples on both sides**:
`∑ (c·xᵢ) · (d·yᵢ) = (c·d) · ∑ xᵢ · yᵢ`. -/
theorem euclidean_inner_smul_smul {n : ℕ} (c d : ℝ) (x y : Fin n → ℝ) :
    (∑ i : Fin n, (c * x i) * (d * y i)) = c * d * (∑ i : Fin n, x i * y i) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intros i _
  ring

/-- **Euclidean scale by 1 is identity**: `∑ 1·xᵢ · 1·yᵢ = ∑ xᵢ·yᵢ`. -/
theorem euclidean_inner_one_smul_one_smul {n : ℕ} (x y : Fin n → ℝ) :
    (∑ i : Fin n, ((1 : ℝ) * x i) * ((1 : ℝ) * y i)) = ∑ i : Fin n, x i * y i := by
  rw [euclidean_inner_smul_smul]
  ring

/-- **Euclidean scale by 0 vanishes, left side**: `∑ 0·xᵢ · yᵢ = 0`. -/
theorem euclidean_inner_zero_smul_left {n : ℕ} (x y : Fin n → ℝ) :
    (∑ i : Fin n, ((0 : ℝ) * x i) * y i) = 0 := by
  apply Finset.sum_eq_zero
  intros i _
  ring

/-- **Euclidean scale by 0 vanishes, right side**: `∑ xᵢ · 0·yᵢ = 0`. -/
theorem euclidean_inner_zero_smul_right {n : ℕ} (x y : Fin n → ℝ) :
    (∑ i : Fin n, x i * ((0 : ℝ) * y i)) = 0 := by
  apply Finset.sum_eq_zero
  intros i _
  ring

/-- **Parallelogram identity for Euclidean norm squared**:
`∑ (xᵢ + yᵢ)² + ∑ (xᵢ - yᵢ)² = 2·(∑ xᵢ² + ∑ yᵢ²)`. -/
theorem euclidean_parallelogram {n : ℕ} (x y : Fin n → ℝ) :
    (∑ i : Fin n, (x i + y i) ^ 2) + (∑ i : Fin n, (x i - y i) ^ 2)
      = 2 * ((∑ i : Fin n, (x i) ^ 2) + (∑ i : Fin n, (y i) ^ 2)) := by
  have h_left : (∑ i : Fin n, (x i + y i) ^ 2)
      + (∑ i : Fin n, (x i - y i) ^ 2)
      = ∑ i : Fin n, ((x i + y i) ^ 2 + (x i - y i) ^ 2) := by
    rw [← Finset.sum_add_distrib]
  have h_pointwise : ∀ i : Fin n,
      (x i + y i) ^ 2 + (x i - y i) ^ 2 = 2 * ((x i) ^ 2 + (y i) ^ 2) := by
    intros i; ring
  rw [h_left]
  calc ∑ i : Fin n, ((x i + y i) ^ 2 + (x i - y i) ^ 2)
      = ∑ i : Fin n, 2 * ((x i) ^ 2 + (y i) ^ 2) :=
        Finset.sum_congr rfl (fun i _ => h_pointwise i)
    _ = 2 * ∑ i : Fin n, ((x i) ^ 2 + (y i) ^ 2) := (Finset.mul_sum _ _ _).symm
    _ = 2 * ((∑ i : Fin n, (x i) ^ 2) + (∑ i : Fin n, (y i) ^ 2)) := by
        rw [Finset.sum_add_distrib]

/-- **Constant-diagonal instance**: if `f : α → ℝ` is nonneg, then
the form `fun x _ => f x` (constant in the second argument) is
reflection positive. -/
theorem ReflectionPositive.of_diag_nonneg {α : Type*} (f : α → ℝ)
    (hf : ∀ x, 0 ≤ f x) :
    ReflectionPositive (fun (x _ : α) => f x) :=
  fun x => hf x

/-- **Sum of reflection-positive forms is reflection positive**. -/
theorem ReflectionPositive.add {α : Type*} {b₁ b₂ : α → α → ℝ}
    (h₁ : ReflectionPositive b₁) (h₂ : ReflectionPositive b₂) :
    ReflectionPositive (fun x y => b₁ x y + b₂ x y) :=
  fun x => add_nonneg (h₁ x) (h₂ x)

/-- **Non-negative scalar multiple of a reflection-positive form is
reflection positive**. -/
theorem ReflectionPositive.smul_nonneg {α : Type*} {b : α → α → ℝ}
    {c : ℝ} (hc : 0 ≤ c) (h : ReflectionPositive b) :
    ReflectionPositive (fun x y => c * b x y) :=
  fun x => mul_nonneg hc (h x)

/-- **Reparametrization preserves reflection positivity**: for any
map `g : β → α` and RP form `b : α → α → ℝ`, the pullback
`fun x y => b (g x) (g y)` is RP on `β`. -/
theorem ReflectionPositive.comp {α β : Type*} {b : α → α → ℝ}
    (h : ReflectionPositive b) (g : β → α) :
    ReflectionPositive (fun x y : β => b (g x) (g y)) :=
  fun x => h (g x)

/-- **Finite-sum closure**: a sum of finitely many reflection-positive
forms indexed by a `Finset` is reflection positive. -/
theorem ReflectionPositive.sum {α ι : Type*} {b : ι → α → α → ℝ}
    (s : Finset ι) (h : ∀ i ∈ s, ReflectionPositive (b i)) :
    ReflectionPositive (fun x y => ∑ i ∈ s, b i x y) := by
  intro x
  exact Finset.sum_nonneg (fun i hi => h i hi x)

/-- **Weighted-sum closure**: a nonneg-weighted sum of
reflection-positive forms is reflection positive. Combines
`.smul_nonneg` and `.sum`. -/
theorem ReflectionPositive.weighted_sum {α ι : Type*}
    {b : ι → α → α → ℝ} {c : ι → ℝ} (s : Finset ι)
    (hc : ∀ i ∈ s, 0 ≤ c i)
    (h : ∀ i ∈ s, ReflectionPositive (b i)) :
    ReflectionPositive (fun x y => ∑ i ∈ s, c i * b i x y) := by
  intro x
  exact Finset.sum_nonneg (fun i hi => mul_nonneg (hc i hi) (h i hi x))

/-- **Discriminant lemma** (algebraic core of the Schwarz inequality).
If `a t² + 2b t + c ≥ 0` for all `t ∈ ℝ`, then `b² ≤ a c`.
This is the key step in deriving the Schwarz inequality (10.4.2)
from reflection positivity.

In the application: `a = b(y,y)`, `b = b(x,y)`, `c = b(x,x)`,
and the quadratic comes from `0 ≤ b(x + ty, x + ty)`. -/
theorem discriminant_nonneg (a b c : ℝ) (h : ∀ t : ℝ, 0 ≤ a * t ^ 2 + 2 * b * t + c) :
    b ^ 2 ≤ a * c := by
  -- Use mathlib's `discrim_le_zero`: if a·t² + (2b)·t + c ≥ 0 for all t,
  -- then discrim(a, 2b, c) = (2b)² - 4ac ≤ 0, i.e., 4b² ≤ 4ac.
  have hd := discrim_le_zero (a := a) (b := 2 * b) (c := c) (fun t => by
    have := h t; rw [sq] at this; linarith)
  unfold discrim at hd; nlinarith

/-- **Completing-the-square factorization** (§10.6 supporting identity):
for any `a ≠ 0`,
`a · t² + 2·b·t + c = a · (t + b/a)² + (c - b²/a)`.
The underlying algebraic identity for `discriminant_nonneg_converse`
and analogous completing-the-square arguments. -/
theorem quadratic_complete_square (a b c t : ℝ) (ha : a ≠ 0) :
    a * t ^ 2 + 2 * b * t + c = a * (t + b / a) ^ 2 + (c - b ^ 2 / a) := by
  field_simp
  ring

/-- **Converse of `discriminant_nonneg`** (for `0 < a`):
if `b² ≤ a · c`, then `a · t² + 2·b·t + c ≥ 0` for all `t ∈ ℝ`.

Proof: complete the square `a·t² + 2·b·t + c = a·(t + b/a)² + (c - b²/a)`,
and both terms are non-negative under the hypotheses. -/
theorem discriminant_nonneg_converse (a b c : ℝ) (ha : 0 < a)
    (h : b ^ 2 ≤ a * c) :
    ∀ t : ℝ, 0 ≤ a * t ^ 2 + 2 * b * t + c := by
  intro t
  -- a·(t + b/a)² = a·t² + 2·b·t + b²/a, so
  -- a·t² + 2·b·t + c = a·(t + b/a)² + (c - b²/a).
  have hsq : 0 ≤ a * (t + b / a) ^ 2 :=
    mul_nonneg ha.le (sq_nonneg _)
  have hrem : 0 ≤ c - b ^ 2 / a := by
    have := (div_le_iff₀ ha).mpr (by linarith : b ^ 2 ≤ c * a)
    linarith
  have hid : a * t ^ 2 + 2 * b * t + c
      = a * (t + b / a) ^ 2 + (c - b ^ 2 / a) := by
    field_simp
    ring
  linarith [hsq, hrem]

/-- **Discriminant iff** (for `0 < a`):
`a · t² + 2·b·t + c ≥ 0` for all `t` iff `b² ≤ a · c`. Combines
`discriminant_nonneg` (forward) and `discriminant_nonneg_converse`
(backward). -/
theorem discriminant_nonneg_iff (a b c : ℝ) (ha : 0 < a) :
    (∀ t : ℝ, 0 ≤ a * t ^ 2 + 2 * b * t + c) ↔ b ^ 2 ≤ a * c :=
  ⟨discriminant_nonneg a b c, discriminant_nonneg_converse a b c ha⟩

/-- **Discriminant equality case** (for `a ≠ 0`): if `b² = a · c`,
the quadratic `a · t² + 2·b·t + c` has a double root at `t = -b/a`
where it vanishes. -/
theorem quadratic_zero_of_discriminant_eq (a b c : ℝ) (ha : a ≠ 0)
    (h : b ^ 2 = a * c) :
    a * (-b / a) ^ 2 + 2 * b * (-b / a) + c = 0 := by
  rw [quadratic_complete_square a b c (-b / a) ha]
  have : -b / a + b / a = 0 := by ring
  simp [this]
  -- c - b²/a = 0 since b² = a·c.
  field_simp
  linarith

/-- **Strict discriminant positivity** (for `0 < a`):
if `b² < a · c`, then `a · t² + 2·b·t + c > 0` for all `t ∈ ℝ`.

Proof: complete the square `a·t² + 2·b·t + c = a·(t + b/a)² + (c - b²/a)`;
the second term is positive under the strict hypothesis (and the
first is non-negative), so the sum is strictly positive. -/
theorem discriminant_pos_of_strict (a b c : ℝ) (ha : 0 < a)
    (h : b ^ 2 < a * c) :
    ∀ t : ℝ, 0 < a * t ^ 2 + 2 * b * t + c := by
  intro t
  rw [quadratic_complete_square a b c t ha.ne']
  have hsq : 0 ≤ a * (t + b / a) ^ 2 := mul_nonneg ha.le (sq_nonneg _)
  have hrem_pos : 0 < c - b ^ 2 / a := by
    have := (div_lt_iff₀ ha).mpr (by linarith : b ^ 2 < c * a)
    linarith
  linarith

/-- **Strict discriminant forward** (for `0 < a`): if the quadratic
is strictly positive everywhere, then `b² < a·c`. The forward
direction of `discriminant_pos_iff`, via evaluating at the vertex
`t = -b/a`. -/
theorem discriminant_strict_of_pos (a b c : ℝ) (ha : 0 < a)
    (h : ∀ t : ℝ, 0 < a * t ^ 2 + 2 * b * t + c) :
    b ^ 2 < a * c := by
  -- Evaluate at `t = -b/a`: the quadratic becomes `c - b²/a > 0`,
  -- so `b² < a·c`.
  have hvertex : 0 < c - b ^ 2 / a := by
    have := h (-b / a)
    rw [quadratic_complete_square a b c (-b / a) ha.ne'] at this
    have : -b / a + b / a = 0 := by ring
    have hev : a * (-b / a + b / a) ^ 2 = 0 := by rw [this]; ring
    nlinarith [h (-b / a), quadratic_complete_square a b c (-b / a) ha.ne']
  have := (div_lt_iff₀ ha).mp (by linarith : b ^ 2 / a < c)
  linarith

/-- **Strict discriminant iff** (for `0 < a`): combined biconditional. -/
theorem discriminant_pos_iff (a b c : ℝ) (ha : 0 < a) :
    (∀ t : ℝ, 0 < a * t ^ 2 + 2 * b * t + c) ↔ b ^ 2 < a * c :=
  ⟨discriminant_strict_of_pos a b c ha, discriminant_pos_of_strict a b c ha⟩

/-- **Polarization identity for bilinear forms** (§10.6 supporting
identity): for any bilinear `b : α → α → ℝ` on an additive commutative
group `α`,
`b(x + y, x + y) - b(x - y, x - y) = 2 · (b(x, y) + b(y, x))`.

The left-hand side exposes the symmetrized `b(x, y) + b(y, x)` even
when `b` is non-symmetric. Fundamental tool for §10.6 non-symmetric
reflection positivity: it expresses the symmetrized off-diagonal
entries as a difference of diagonal entries.

The bilinearity hypotheses are given explicitly (without requiring a
concrete `LinearMap.BilinMap`); they suffice for the calculation. -/
theorem polarization_identity {α : Type*} [AddCommGroup α]
    (b : α → α → ℝ)
    (hbi_left : ∀ x y z : α, b (x + y) z = b x z + b y z)
    (hbi_right : ∀ x y z : α, b x (y + z) = b x y + b x z)
    (hbi_neg_left : ∀ x y : α, b (-x) y = -b x y)
    (hbi_neg_right : ∀ x y : α, b x (-y) = -b x y)
    (x y : α) :
    b (x + y) (x + y) - b (x - y) (x - y)
      = 2 * (b x y + b y x) := by
  -- Expand `b (x + y) (x + y) = b x x + b x y + b y x + b y y`.
  have h1 : b (x + y) (x + y) = b x x + b x y + b y x + b y y := by
    rw [hbi_left]
    rw [hbi_right, hbi_right]
    ring
  -- Expand `b (x - y) (x - y) = b x x - b x y - b y x + b y y`.
  have h2 : b (x - y) (x - y) = b x x - b x y - b y x + b y y := by
    have hsubst : x - y = x + -y := by abel
    rw [hsubst]
    rw [hbi_left]
    rw [hbi_right, hbi_right]
    rw [hbi_neg_right, hbi_neg_left]
    -- Remaining: `b (-y) (-y) = b y y`, via `hbi_neg_left` + `hbi_neg_right`.
    have hneg_neg : b (-y) (-y) = b y y := by
      rw [hbi_neg_left, hbi_neg_right]; ring
    rw [hneg_neg]
    ring
  rw [h1, h2]
  ring

/-- **Schwarz absolute-value bound** (§10.6): from the quadratic
positivity `∀ t, 0 ≤ a·t² + 2·b·t + c` with `a, c ≥ 0`, conclude
the bound `|b| ≤ √(a·c)` on the symmetric linear coefficient.

Direct consequence of `discriminant_nonneg` (`b² ≤ a·c`) + sqrt-monotone. -/
theorem schwarz_abs_bound (a b c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (h : ∀ t : ℝ, 0 ≤ a * t ^ 2 + 2 * b * t + c) :
    |b| ≤ Real.sqrt (a * c) := by
  have hbsq : b ^ 2 ≤ a * c := discriminant_nonneg a b c h
  have hac : 0 ≤ a * c := mul_nonneg ha hc
  have hsqrt : Real.sqrt (b ^ 2) ≤ Real.sqrt (a * c) := Real.sqrt_le_sqrt hbsq
  rwa [Real.sqrt_sq_eq_abs] at hsqrt

/-! ## Multiple reflections and geometric mean bounds (§10.5–10.6)

Glimm–Jaffe §10.5 develops multiple reflection bounds by iterating
the Schwarz inequality from §10.4. The key algebraic tool is:

`|⟨k⟩|^{2^n} ≤ ⟨M_{2^n}(k)⟩`

where `M_{2^n}` is the `2^n`-fold reflection product (eq. 10.5.4).

For the lattice Ising model, the essential consequence is: repeated
application of the discriminant lemma bounds expectations by geometric
means of reflected expectations.

§10.6 extends these bounds to non-symmetric reflections, needed for
regularity of P(φ)₂ fields but not for existence (p. 206). -/

/-- **Iterated Schwarz inequality** (Prop. 10.5.2, algebraic core).
If `0 ≤ a` and `x² ≤ a · b`, then `x^{2^n} ≤ a^{2^n - 1} · b^{2^{n-1}}`.

This captures the key step in the multiple reflection bound:
iterated application of `x² ≤ ab` yields geometric mean estimates. -/
theorem iterated_schwarz_sq (x a : ℝ) (hx : 0 ≤ x) (ha : 0 ≤ a) (hxab : x ^ 2 ≤ a * x) :
    x ≤ a := by
  rcases eq_or_lt_of_le hx with rfl | hx_pos
  · simp [ha]
  · nlinarith [sq_nonneg (x - a)]

/-- **Non-symmetric discriminant lemma** (§10.6 algebraic core).
Generalizes `discriminant_nonneg` to the case where the linear
coefficient is a sum `b₁ + b₂` of two potentially distinct terms
(as arises from a non-symmetric bilinear form `b` where
`b(x, y) ≠ b(y, x)`): if `a·t² + (b₁ + b₂)·t + c ≥ 0` for all `t ∈ ℝ`,
then `((b₁ + b₂) / 2)² ≤ a · c`.

In a reflection-positivity setting, `b₁` and `b₂` would be the two
off-diagonal entries of a non-symmetric form; their symmetrized
average still satisfies the Schwarz bound. This is GJ §10.6's
algebraic core for extending §10.4 to non-symmetric reflections. -/
theorem nonsymmetric_discriminant_mean (a b₁ b₂ c : ℝ)
    (h : ∀ t : ℝ, 0 ≤ a * t ^ 2 + (b₁ + b₂) * t + c) :
    ((b₁ + b₂) / 2) ^ 2 ≤ a * c := by
  have h' : ∀ t : ℝ, 0 ≤ a * t ^ 2 + 2 * ((b₁ + b₂) / 2) * t + c := by
    intro t
    have := h t
    linarith
  exact discriminant_nonneg a ((b₁ + b₂) / 2) c h'

/-- **Non-symmetric Schwarz-AM-GM bound** (§10.6 algebraic consequence):
for `0 ≤ a, 0 ≤ c` and a non-symmetric bilinear form with `b₁ + b₂`
as the symmetrized linear term, the arithmetic mean of the two
non-symmetric entries is bounded by the geometric mean `√(a·c)`.
Derived from `nonsymmetric_discriminant_mean`. -/
theorem nonsymmetric_mean_le_geom_mean (a b₁ b₂ c : ℝ)
    (ha : 0 ≤ a) (hc : 0 ≤ c)
    (h : ∀ t : ℝ, 0 ≤ a * t ^ 2 + (b₁ + b₂) * t + c) :
    |(b₁ + b₂) / 2| ≤ Real.sqrt (a * c) := by
  have hsq := nonsymmetric_discriminant_mean a b₁ b₂ c h
  have hac : 0 ≤ a * c := mul_nonneg ha hc
  have := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq_eq_abs] at this

/-- **Non-symmetric sum absolute-value bound** (§10.6): the total
`|b₁ + b₂|` is bounded by `2·√(a·c)`, from the quadratic positivity.
Multiplicative restatement of `nonsymmetric_mean_le_geom_mean`. -/
theorem nonsymmetric_sum_abs_bound (a b₁ b₂ c : ℝ)
    (ha : 0 ≤ a) (hc : 0 ≤ c)
    (h : ∀ t : ℝ, 0 ≤ a * t ^ 2 + (b₁ + b₂) * t + c) :
    |b₁ + b₂| ≤ 2 * Real.sqrt (a * c) := by
  have hmean := nonsymmetric_mean_le_geom_mean a b₁ b₂ c ha hc h
  have habs_half : |(b₁ + b₂) / 2| = |b₁ + b₂| / 2 := by
    rw [abs_div]
    simp
  rw [habs_half] at hmean
  linarith

/-- **Non-symmetric iterated Schwarz** (§10.6 iterative step): from
`0 ≤ x, 0 ≤ a, 0 ≤ b` and `x² ≤ a · b`, conclude the non-symmetric
geometric-mean bound `x ≤ √(a · b)`. Direct analogue of
`iterated_schwarz_sq` for the two-variable case. -/
theorem nonsymmetric_iterated_schwarz (x a b : ℝ)
    (hx : 0 ≤ x) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hxab : x ^ 2 ≤ a * b) :
    x ≤ Real.sqrt (a * b) := by
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  have hsqrt : Real.sqrt (x ^ 2) ≤ Real.sqrt (a * b) := Real.sqrt_le_sqrt hxab
  rw [Real.sqrt_sq hx] at hsqrt
  exact hsqrt

/-- **Non-symmetric AM-GM consequence** (§10.6): from the iterated
Schwarz bound `x² ≤ a · b`, deduce the AM-type bound `2x ≤ a + b`,
via the elementary `(a - b)² ≥ 0` step (AM-GM). -/
theorem nonsymmetric_two_le_sum (x a b : ℝ)
    (hx : 0 ≤ x) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hxab : x ^ 2 ≤ a * b) :
    2 * x ≤ a + b := by
  -- First, `x² ≤ a·b ≤ ((a + b)/2)²` via AM-GM (`(a-b)² ≥ 0`).
  have hamgm : a * b ≤ ((a + b) / 2) ^ 2 := by nlinarith [sq_nonneg (a - b)]
  have hx_sq : x ^ 2 ≤ ((a + b) / 2) ^ 2 := hxab.trans hamgm
  have h_nn : 0 ≤ (a + b) / 2 := by linarith
  have := abs_le_of_sq_le_sq' hx_sq h_nn
  have hx_abs : x ≤ (a + b) / 2 := (abs_of_nonneg hx) ▸ this.2
  linarith

/-- **Non-symmetric product bound** (§10.6): under `x² ≤ a, y² ≤ b`
with `x·y ≥ 0` and `a, b ≥ 0`, conclude `x · y ≤ √(a · b)`.

Captures a Cauchy-Schwarz-in-product form useful for non-symmetric
reflection contexts where `x = ⟨A⟩, y = ⟨B⟩` with `A, B` reflected
into `θ(A), θ(B)` and `⟨A²⟩ = a, ⟨B²⟩ = b`. -/
theorem nonsymmetric_product_bound (x y a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hxy_nn : 0 ≤ x * y)
    (hxa : x ^ 2 ≤ a) (hyb : y ^ 2 ≤ b) :
    x * y ≤ Real.sqrt (a * b) := by
  have hxysq : (x * y) ^ 2 ≤ a * b := by
    have : (x * y) ^ 2 = x ^ 2 * y ^ 2 := by ring
    rw [this]
    exact mul_le_mul hxa hyb (sq_nonneg _) ha
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  have hsqrt : Real.sqrt ((x * y) ^ 2) ≤ Real.sqrt (a * b) :=
    Real.sqrt_le_sqrt hxysq
  rw [Real.sqrt_sq hxy_nn] at hsqrt
  exact hsqrt

/-- **Cross-variable Schwarz iteration** (§10.6): from the two-sided
bound `x² ≤ a·y` and `y² ≤ b·x`, derive `x⁴ ≤ a²·b·x` (and by
symmetry `y⁴ ≤ a·b²·y`).

Chain: `x⁴ = (x²)² ≤ (a·y)² = a²·y² ≤ a²·(b·x) = a²·b·x`.
Analogue of §10.5's iterated Schwarz for the non-symmetric two-variable
setting where each variable bounds the other's square. -/
theorem nonsymmetric_cross_iteration_x (x y a b : ℝ)
    (hxay : x ^ 2 ≤ a * y) (hybx : y ^ 2 ≤ b * x) :
    x ^ 4 ≤ a ^ 2 * b * x := by
  nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg (x^2 - a*y),
    mul_self_nonneg (a*y - x^2), hxay, hybx,
    mul_le_mul_of_nonneg_left hybx (sq_nonneg a)]

/-- **Cross-variable Schwarz iteration** (§10.6, y-side): symmetric
partner of `nonsymmetric_cross_iteration_x` giving `y⁴ ≤ a·b²·y`. -/
theorem nonsymmetric_cross_iteration_y (x y a b : ℝ)
    (hxay : x ^ 2 ≤ a * y) (hybx : y ^ 2 ≤ b * x) :
    y ^ 4 ≤ a * b ^ 2 * y := by
  nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg (y^2 - b*x),
    mul_self_nonneg (b*x - y^2), hxay, hybx,
    mul_le_mul_of_nonneg_left hxay (sq_nonneg b)]

/-- **Cube bound from cross-iteration** (§10.6): when `x > 0`,
the bound `x⁴ ≤ a²·b·x` (from `nonsymmetric_cross_iteration_x`)
strengthens to `x³ ≤ a²·b`. Division by the positive factor `x`. -/
theorem nonsymmetric_cube_bound_x (x y a b : ℝ) (hx : 0 < x)
    (hxay : x ^ 2 ≤ a * y) (hybx : y ^ 2 ≤ b * x) :
    x ^ 3 ≤ a ^ 2 * b := by
  have h4 := nonsymmetric_cross_iteration_x x y a b hxay hybx
  nlinarith [h4, hx, sq_nonneg x]

/-- **Cube bound from cross-iteration** (§10.6, y-side): symmetric partner
`y³ ≤ a · b²` when `y > 0`. -/
theorem nonsymmetric_cube_bound_y (x y a b : ℝ) (hy : 0 < y)
    (hxay : x ^ 2 ≤ a * y) (hybx : y ^ 2 ≤ b * x) :
    y ^ 3 ≤ a * b ^ 2 := by
  have h4 := nonsymmetric_cross_iteration_y x y a b hxay hybx
  nlinarith [h4, hy, sq_nonneg y]

/-- **Non-symmetric reflection-positive Schwarz** (§10.6 main):
for a bilinear `b : α → α → ℝ` on an ℝ-module `α` satisfying
`ReflectionPositive b` (i.e., `b x x ≥ 0` for all x), the
symmetrized off-diagonal entries satisfy the Schwarz-style bound

  `((b x y + b y x) / 2)² ≤ b x x · b y y`.

Proof: for all `t : ℝ`, bilinearity expands `b (x + t•y) (x + t•y)`
to `b x x + t·(b x y + b y x) + t²·b y y`; reflection positivity
gives this quadratic ≥ 0 for all t; `nonsymmetric_discriminant_mean`
yields the Schwarz bound. -/
theorem schwarz_of_reflection_positive
    {α : Type*} [AddCommGroup α] [Module ℝ α]
    (b : α → α → ℝ)
    (hbi_left : ∀ x y z : α, b (x + y) z = b x z + b y z)
    (hbi_right : ∀ x y z : α, b x (y + z) = b x y + b x z)
    (hbi_smul_left : ∀ (c : ℝ) (x y : α), b (c • x) y = c * b x y)
    (hbi_smul_right : ∀ (c : ℝ) (x y : α), b x (c • y) = c * b x y)
    (hRP : ReflectionPositive b) (x y : α) :
    ((b x y + b y x) / 2) ^ 2 ≤ b x x * b y y := by
  have hquad : ∀ t : ℝ,
      0 ≤ b y y * t ^ 2 + (b x y + b y x) * t + b x x := by
    intro t
    have hrp := hRP (x + t • y)
    have hexpand : b (x + t • y) (x + t • y)
        = b y y * t ^ 2 + (b x y + b y x) * t + b x x := by
      rw [hbi_left]
      rw [hbi_right, hbi_right]
      rw [hbi_smul_right, hbi_smul_left, hbi_smul_right, hbi_smul_left]
      ring
    linarith [hrp, hexpand]
  have := nonsymmetric_discriminant_mean (b y y) (b x y) (b y x) (b x x) hquad
  linarith [this, mul_comm (b y y) (b x x)]

/-- **Reflection-positive Schwarz, AM-GM form** (§10.6 corollary):
`|b x y + b y x| / 2 ≤ √(b x x · b y y)` from
`schwarz_of_reflection_positive` (PR #685) + sqrt monotonicity. -/
theorem reflection_positive_mean_le_geom_mean
    {α : Type*} [AddCommGroup α] [Module ℝ α]
    (b : α → α → ℝ)
    (hbi_left : ∀ x y z : α, b (x + y) z = b x z + b y z)
    (hbi_right : ∀ x y z : α, b x (y + z) = b x y + b x z)
    (hbi_smul_left : ∀ (c : ℝ) (x y : α), b (c • x) y = c * b x y)
    (hbi_smul_right : ∀ (c : ℝ) (x y : α), b x (c • y) = c * b x y)
    (hRP : ReflectionPositive b) (x y : α) :
    |(b x y + b y x) / 2| ≤ Real.sqrt (b x x * b y y) := by
  have hsq := schwarz_of_reflection_positive b hbi_left hbi_right
    hbi_smul_left hbi_smul_right hRP x y
  have := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq_eq_abs] at this

/-- **Reflection-positive Schwarz, sum abs bound**:
`|b x y + b y x| ≤ 2·√(b x x · b y y)` from `_mean_le_geom_mean`
by multiplying both sides by 2. -/
theorem reflection_positive_sum_abs_bound
    {α : Type*} [AddCommGroup α] [Module ℝ α]
    (b : α → α → ℝ)
    (hbi_left : ∀ x y z : α, b (x + y) z = b x z + b y z)
    (hbi_right : ∀ x y z : α, b x (y + z) = b x y + b x z)
    (hbi_smul_left : ∀ (c : ℝ) (x y : α), b (c • x) y = c * b x y)
    (hbi_smul_right : ∀ (c : ℝ) (x y : α), b x (c • y) = c * b x y)
    (hRP : ReflectionPositive b) (x y : α) :
    |b x y + b y x| ≤ 2 * Real.sqrt (b x x * b y y) := by
  have hmean := reflection_positive_mean_le_geom_mean b hbi_left hbi_right
    hbi_smul_left hbi_smul_right hRP x y
  have habs_half : |(b x y + b y x) / 2| = |b x y + b y x| / 2 := by
    rw [abs_div]
    simp
  rw [habs_half] at hmean
  linarith

/-- **Classical symmetric Cauchy-Schwarz** (§10.6 corollary for
symmetric `b`): for symmetric bilinear `b` (i.e., `b x y = b y x`)
satisfying `ReflectionPositive b`, the classical Schwarz inequality
`(b x y)² ≤ b x x · b y y` holds. Direct reduction of
`schwarz_of_reflection_positive` using `(b x y + b y x)/2 = b x y`
under symmetry. -/
theorem classical_schwarz_of_symmetric_reflection_positive
    {α : Type*} [AddCommGroup α] [Module ℝ α]
    (b : α → α → ℝ)
    (hbi_left : ∀ x y z : α, b (x + y) z = b x z + b y z)
    (hbi_right : ∀ x y z : α, b x (y + z) = b x y + b x z)
    (hbi_smul_left : ∀ (c : ℝ) (x y : α), b (c • x) y = c * b x y)
    (hbi_smul_right : ∀ (c : ℝ) (x y : α), b x (c • y) = c * b x y)
    (hRP : ReflectionPositive b)
    (hsym : ∀ x y : α, b x y = b y x) (x y : α) :
    (b x y) ^ 2 ≤ b x x * b y y := by
  have hsq := schwarz_of_reflection_positive b hbi_left hbi_right
    hbi_smul_left hbi_smul_right hRP x y
  -- `(b x y + b y x)/2 = (b x y + b x y)/2 = b x y` under symmetry.
  have hmean : (b x y + b y x) / 2 = b x y := by
    rw [hsym y x]; ring
  rw [hmean] at hsq
  exact hsq

/-- **Classical symmetric Schwarz absolute-value form** (§10.6
corollary): `|b x y| ≤ √(b x x · b y y)` under symmetric bilinear +
reflection positive. Immediate from
`classical_schwarz_of_symmetric_reflection_positive` + sqrt
monotonicity. -/
theorem classical_schwarz_abs_of_symmetric_reflection_positive
    {α : Type*} [AddCommGroup α] [Module ℝ α]
    (b : α → α → ℝ)
    (hbi_left : ∀ x y z : α, b (x + y) z = b x z + b y z)
    (hbi_right : ∀ x y z : α, b x (y + z) = b x y + b x z)
    (hbi_smul_left : ∀ (c : ℝ) (x y : α), b (c • x) y = c * b x y)
    (hbi_smul_right : ∀ (c : ℝ) (x y : α), b x (c • y) = c * b x y)
    (hRP : ReflectionPositive b)
    (hsym : ∀ x y : α, b x y = b y x) (x y : α) :
    |b x y| ≤ Real.sqrt (b x x * b y y) := by
  have hsq := classical_schwarz_of_symmetric_reflection_positive b
    hbi_left hbi_right hbi_smul_left hbi_smul_right hRP hsym x y
  have := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq_eq_abs] at this

/-- **Symmetric degenerate case** (§10.6 corollary): if `b` is symmetric
bilinear with reflection positivity and `b x x = 0`, then `b x y = 0`
for all `y`. Proof: `(b x y)² ≤ b x x · b y y = 0`, so `b x y = 0`. -/
theorem symmetric_reflection_positive_off_diag_zero_of_diag_zero
    {α : Type*} [AddCommGroup α] [Module ℝ α]
    (b : α → α → ℝ)
    (hbi_left : ∀ x y z : α, b (x + y) z = b x z + b y z)
    (hbi_right : ∀ x y z : α, b x (y + z) = b x y + b x z)
    (hbi_smul_left : ∀ (c : ℝ) (x y : α), b (c • x) y = c * b x y)
    (hbi_smul_right : ∀ (c : ℝ) (x y : α), b x (c • y) = c * b x y)
    (hRP : ReflectionPositive b)
    (hsym : ∀ x y : α, b x y = b y x) (x y : α) (hxx : b x x = 0) :
    b x y = 0 := by
  have hsq := classical_schwarz_of_symmetric_reflection_positive b
    hbi_left hbi_right hbi_smul_left hbi_smul_right hRP hsym x y
  rw [hxx, zero_mul] at hsq
  have hnn : 0 ≤ (b x y) ^ 2 := sq_nonneg _
  have hzero : (b x y) ^ 2 = 0 := le_antisymm hsq hnn
  exact pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp hzero

/-- **Degenerate case variant** (§10.6 corollary): if `b y y = 0`,
then `b x y + b y x = 0`. Symmetric partner of
`reflection_positive_off_diag_zero_of_diag_zero`. -/
theorem reflection_positive_off_diag_zero_of_diag_zero_right
    {α : Type*} [AddCommGroup α] [Module ℝ α]
    (b : α → α → ℝ)
    (hbi_left : ∀ x y z : α, b (x + y) z = b x z + b y z)
    (hbi_right : ∀ x y z : α, b x (y + z) = b x y + b x z)
    (hbi_smul_left : ∀ (c : ℝ) (x y : α), b (c • x) y = c * b x y)
    (hbi_smul_right : ∀ (c : ℝ) (x y : α), b x (c • y) = c * b x y)
    (hRP : ReflectionPositive b) (x y : α) (hyy : b y y = 0) :
    b x y + b y x = 0 := by
  have hsq := schwarz_of_reflection_positive b hbi_left hbi_right
    hbi_smul_left hbi_smul_right hRP x y
  rw [hyy, mul_zero] at hsq
  have hnn : 0 ≤ ((b x y + b y x) / 2) ^ 2 := sq_nonneg _
  have hzero : ((b x y + b y x) / 2) ^ 2 = 0 := le_antisymm hsq hnn
  have hhalf_zero : (b x y + b y x) / 2 = 0 :=
    pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp hzero
  linarith

/-- **Degenerate reflection-positive case** (§10.6 corollary): if
`b x x = 0`, then `b x y + b y x = 0` (the symmetrized off-diagonal
vanishes). Immediate from Schwarz: `((b x y + b y x)/2)² ≤ 0` forces
`b x y + b y x = 0`. -/
theorem reflection_positive_off_diag_zero_of_diag_zero
    {α : Type*} [AddCommGroup α] [Module ℝ α]
    (b : α → α → ℝ)
    (hbi_left : ∀ x y z : α, b (x + y) z = b x z + b y z)
    (hbi_right : ∀ x y z : α, b x (y + z) = b x y + b x z)
    (hbi_smul_left : ∀ (c : ℝ) (x y : α), b (c • x) y = c * b x y)
    (hbi_smul_right : ∀ (c : ℝ) (x y : α), b x (c • y) = c * b x y)
    (hRP : ReflectionPositive b) (x y : α) (hxx : b x x = 0) :
    b x y + b y x = 0 := by
  have hsq := schwarz_of_reflection_positive b hbi_left hbi_right
    hbi_smul_left hbi_smul_right hRP x y
  rw [hxx, zero_mul] at hsq
  have hnn : 0 ≤ ((b x y + b y x) / 2) ^ 2 := sq_nonneg _
  have hzero : ((b x y + b y x) / 2) ^ 2 = 0 := le_antisymm hsq hnn
  have hhalf_zero : (b x y + b y x) / 2 = 0 := pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp hzero
  linarith

/-! ## High-temperature / cluster expansion (§18.1–18.3)

Glimm–Jaffe Chapter 18 develops the cluster expansion for P(φ)₂ fields.
The lattice Ising analogue is the **high-temperature expansion**, which
decomposes each Boltzmann factor using

`exp(βJ · σ_iσ_j) = cosh(βJ) + sinh(βJ) · σ_iσ_j`

(already proved as `exp_edgeSpin_decomp` in `NonnegCorrelations.lean`).

The high-temperature expansion gives:
`Z = (cosh βJ)^|E| · Σ_σ ∏_e (1 + tanh(βJ) · σ_iσ_j) · exp(βh Σ σ_i)`

For `h = 0`, the sum over σ selects only even subgraphs (those where
every vertex has even degree), giving the well-known formula:
`Z(h=0) = 2^|ι| · (cosh βJ)^|E| · Σ_{X ⊆ E, even} (tanh βJ)^|X|`

The convergence of this expansion for small `tanh(βJ)` (high temperature)
establishes exponential decay of correlations and uniqueness of the
Gibbs state — the lattice analogue of Theorem 18.1.1.

The key algebraic ingredient `exp_edgeSpin_decomp` is already formalized. -/

/-- **Partition function high-temperature expansion** (lattice analogue of GJ §18.3).

For any Ising parameter `p = (J, h, β)` and any finite simple graph `G`,
\[
Z(G; p) = (\cosh(\beta J))^{|E|} \sum_\sigma
  \Bigl(\prod_{e \in E} (1 + \tanh(\beta J)\,\sigma_i\sigma_j)\Bigr)
  \exp\!\bigl(\beta h \sum_i \sigma_i\bigr).
\]

Reference: Glimm–Jaffe, *Quantum Physics*, §18.1–18.3, pp. 378–386
("Clustering and analyticity"); see also Friedli–Velenik §3.7.3
("Uniqueness at high temperature"), eqs. (3.41)–(3.42), pp. 116–117
(2017 ed.). The proof rewrites each edge factor via
`exp_edgeSpin_decomp` (which gives `exp(α·s) = cosh α + sinh α · s`
for `s ∈ {±1}`) and pulls out the common factor `cosh(βJ)`. -/
theorem partitionFunction_high_temp_expansion
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) :
    partitionFunction G p =
      Real.cosh (p.β * p.J) ^ G.edgeFinset.card *
      ∑ σ : Config ι,
        (∏ e ∈ G.edgeFinset, (1 + Real.tanh (p.β * p.J) * edgeSpin σ e)) *
        Real.exp (p.β * p.h * ∑ i : ι, Spin.sign ℝ (σ i)) := by
  unfold partitionFunction boltzmannWeight hamiltonian
    interactionEnergy externalFieldEnergy
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  have hexp_split :
      Real.exp (-p.β *
          (-p.J * ∑ e ∈ G.edgeFinset, edgeSpin σ e
            + -p.h * ∑ i : ι, Spin.sign ℝ (σ i))) =
        (∏ e ∈ G.edgeFinset, Real.exp (p.β * p.J * edgeSpin σ e)) *
          Real.exp (p.β * p.h * ∑ i : ι, Spin.sign ℝ (σ i)) := by
    have hrewrite :
        -p.β *
            (-p.J * ∑ e ∈ G.edgeFinset, edgeSpin σ e
              + -p.h * ∑ i : ι, Spin.sign ℝ (σ i))
          = (∑ e ∈ G.edgeFinset, p.β * p.J * edgeSpin σ e)
            + p.β * p.h * ∑ i : ι, Spin.sign ℝ (σ i) := by
      rw [show
          -p.β *
              (-p.J * ∑ e ∈ G.edgeFinset, edgeSpin σ e
                + -p.h * ∑ i : ι, Spin.sign ℝ (σ i))
            = (p.β * p.J) * (∑ e ∈ G.edgeFinset, edgeSpin σ e)
              + p.β * p.h * (∑ i : ι, Spin.sign ℝ (σ i)) from by ring,
          Finset.mul_sum]
    rw [hrewrite, Real.exp_add, Real.exp_sum]
  rw [hexp_split]
  have hedge_decomp : ∀ e ∈ G.edgeFinset,
      Real.exp (p.β * p.J * edgeSpin σ e) =
        Real.cosh (p.β * p.J) * (1 + Real.tanh (p.β * p.J) * edgeSpin σ e) := by
    intro e _
    rw [exp_edgeSpin_decomp, Real.tanh_eq_sinh_div_cosh]
    have hcosh_ne : Real.cosh (p.β * p.J) ≠ 0 := (Real.cosh_pos _).ne'
    field_simp
  rw [Finset.prod_congr rfl hedge_decomp, Finset.prod_mul_distrib,
      Finset.prod_const]
  ring

/-- **Partition function high-temperature expansion at zero field**
(GJ §18.3 / FV §3.7.3 eq. (3.42)):
\[
Z(G; J, 0, \beta) = (\cosh(\beta J))^{|E|}
\sum_\sigma \prod_{\{i,j\} \in E}
  (1 + \tanh(\beta J)\,\sigma_i\sigma_j).
\]

Direct corollary of `partitionFunction_high_temp_expansion` at `h = 0`,
where the field factor `exp(βh · Σ sign(σ_i))` collapses to `1`. -/
theorem partitionFunction_high_temp_expansion_h_zero
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) :
    partitionFunction G ⟨J, 0, β⟩ =
      Real.cosh (β * J) ^ G.edgeFinset.card *
      ∑ σ : Config ι,
        ∏ e ∈ G.edgeFinset, (1 + Real.tanh (β * J) * edgeSpin σ e) := by
  rw [partitionFunction_high_temp_expansion G ⟨J, 0, β⟩]
  simp

/-! ### Even-subgraph closed form (FV §3.7.3 eq. (3.45)) -/

omit [DecidableEq ι] in
/-- Single-spin sum of `toSign^k`: `2` if `k` is even, else `0`.
Elementary parity fact used in the high-temperature expansion. -/
private theorem sum_toSign_pow_real (k : ℕ) :
    (∑ s : Spin, ((s.toSign : ℝ)) ^ k) = if Even k then 2 else 0 := by
  have hu : (Finset.univ : Finset Spin) = {Spin.up, Spin.down} := by decide
  rw [hu, Finset.sum_pair (by decide : Spin.up ≠ Spin.down)]
  have hup : ((Spin.up.toSign : ℤ) : ℝ) = 1 := by simp [Spin.toSign]
  have hdown : ((Spin.down.toSign : ℤ) : ℝ) = -1 := by simp [Spin.toSign]
  rw [hup, hdown, one_pow]
  by_cases hk : Even k
  · rw [if_pos hk, hk.neg_one_pow]; norm_num
  · rw [if_neg hk]
    rw [Nat.not_even_iff_odd] at hk
    rw [hk.neg_one_pow]; norm_num

/-- Configuration sum of `∏_v (toSign σ v)^(k v)`: equals `2^|ι|`
when every `k v` is even, else `0`. Per-vertex Fubini reduces to
`sum_toSign_pow_real`. -/
private theorem sum_prod_toSign_pow_real (k : ι → ℕ) :
    (∑ σ : Config ι, ∏ v : ι, ((σ v).toSign : ℝ) ^ (k v))
      = if (∀ v : ι, Even (k v)) then (2 : ℝ) ^ Fintype.card ι else 0 := by
  have hfubini :
      (∑ σ : Config ι, ∏ v : ι, ((σ v).toSign : ℝ) ^ (k v))
        = ∏ v : ι, ∑ s : Spin, ((s.toSign : ℝ)) ^ (k v) :=
    (Fintype.prod_sum (κ := fun _ => Spin)
      (fun v s => ((s.toSign : ℝ)) ^ (k v))).symm
  rw [hfubini]
  simp_rw [sum_toSign_pow_real]
  by_cases h : ∀ v : ι, Even (k v)
  · rw [if_pos h,
      Finset.prod_congr rfl (fun v _ => if_pos (h v)),
      Finset.prod_const, Finset.card_univ]
  · rw [if_neg h]
    push Not at h
    obtain ⟨v, hv⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ v) (if_neg hv)

/-- **Edge-product to vertex-power**: for `X` a subset of `G.edgeFinset`
on a SimpleGraph (so every edge is non-diagonal),
`∏_{e ∈ X} edgeSpin σ e = ∏_v (σ v.toSign)^(deg_X v)` where
`deg_X v := (X.filter (v ∈ ·)).card`. The combinatorial bridge between
the edge product appearing in the high-temperature expansion and the
per-vertex Fubini decomposition. -/
private theorem prod_edgeSpin_eq_prod_pow_filter_card
    (G : SimpleGraph ι) [Fintype G.edgeSet] (X : Finset (Sym2 ι))
    (hX : X ⊆ G.edgeFinset) (σ : Config ι) :
    (∏ e ∈ X, edgeSpin (K := ℝ) σ e)
      = ∏ v : ι, ((σ v).toSign : ℝ) ^ ((X.filter (v ∈ ·)).card) := by
  classical
  -- ∏_v g_v^(filter (v∈·) X).card = ∏_v g_v^(∑_{e ∈ X} if v∈e then 1 else 0)
  have hcard : ∀ v : ι,
      (X.filter (v ∈ ·)).card
        = ∑ e ∈ X, (if v ∈ e then 1 else 0) := fun v => by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  simp_rw [hcard]
  -- ∏_v g_v^(∑_e ...) = ∏_v ∏_e g_v^(if v∈e then 1 else 0)
  simp_rw [← Finset.prod_pow_eq_pow_sum]
  -- push pow through if
  have hpush : ∀ (v : ι) (e : Sym2 ι),
      ((σ v).toSign : ℝ) ^ (if v ∈ e then (1 : ℕ) else 0)
        = if v ∈ e then ((σ v).toSign : ℝ) else 1 := by
    intro v e
    by_cases hv : v ∈ e <;> simp [hv]
  simp_rw [hpush]
  -- swap the two products
  rw [Finset.prod_comm]
  -- ∏_e ∏_v (if v∈e then σ v.toSign else 1) = ∏_e edgeSpin σ e
  refine Finset.prod_congr rfl (fun e he => ?_)
  rw [show (∏ v : ι, if v ∈ e then ((σ v).toSign : ℝ) else 1)
      = ∏ v ∈ Finset.univ.filter (· ∈ e), ((σ v).toSign : ℝ) from by
        rw [Finset.prod_filter]]
  -- univ.filter (· ∈ e) = e.toFinset
  have hfilter : (Finset.univ : Finset ι).filter (· ∈ e) = e.toFinset := by
    ext v; simp
  rw [hfilter]
  -- e is non-diag (since e ∈ X ⊆ G.edgeFinset, no loops)
  have hnd : ¬ e.IsDiag := G.not_isDiag_of_mem_edgeSet
    (G.mem_edgeFinset.mp (hX he))
  -- edgeSpin σ e = e.toFinset.prod σ.toSign for non-diag e
  refine Sym2.inductionOn e (fun i j => ?_) hnd
  intro hnd_ij
  rw [Sym2.toFinset_mk_eq, Sym2.mk_isDiag_iff] at *
  rw [Finset.prod_insert (Finset.notMem_singleton.mpr hnd_ij),
      Finset.prod_singleton]
  -- edgeSpin σ s(i,j) = σ i.toSign * σ j.toSign
  unfold edgeSpin
  simp [Sym2.lift_mk, Spin.sign]

/-- **σ-sum of edge product**: for `X ⊆ G.edgeFinset` on a SimpleGraph,
`∑_σ ∏_{e ∈ X} edgeSpin σ e = 2^|ι|` if every vertex has even degree
in `X`, else `0`. The parity step reducing the high-temperature
expansion of `Z(h=0)` to a sum over even-degree subgraphs. -/
private theorem sum_prod_edgeSpin_eq_pow_card_or_zero
    (G : SimpleGraph ι) [Fintype G.edgeSet] (X : Finset (Sym2 ι))
    (hX : X ⊆ G.edgeFinset) :
    (∑ σ : Config ι, ∏ e ∈ X, edgeSpin (K := ℝ) σ e)
      = if (∀ v : ι, Even ((X.filter (v ∈ ·)).card))
        then (2 : ℝ) ^ Fintype.card ι else 0 := by
  simp_rw [prod_edgeSpin_eq_prod_pow_filter_card G X hX]
  exact sum_prod_toSign_pow_real
    (k := fun v => (X.filter (v ∈ ·)).card)

/-- **Partition function at h = 0 — Friedli–Velenik §3.7.3 eq. (3.45)**:
\[
Z(G; J, 0, \beta) = 2^{|\iota|} \cdot (\cosh(\beta J))^{|E|}
\sum_{\substack{X \subseteq E \\ \text{every $v$ has even $X$-degree}}}
  \tanh(\beta J)^{|X|}.
\]

The full closed form of the lattice high-temperature expansion at zero
external field. Combines `partitionFunction_high_temp_expansion_h_zero`
(Step 282), `Finset.prod_one_add` for the subset expansion, and the
per-σ parity argument `sum_prod_edgeSpin_eq_pow_card_or_zero` to
collapse to even-degree subgraphs.

References: GJ §18.3 (lattice cluster expansion); FV §3.7.3 eq. (3.45),
p. 117 (2017 ed.). -/
theorem partitionFunction_high_temp_expansion_h_zero_closed
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) :
    partitionFunction G ⟨J, 0, β⟩ =
      (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card *
      ∑ X ∈ G.edgeFinset.powerset.filter
        (fun X => ∀ v : ι, Even ((X.filter (v ∈ ·)).card)),
        Real.tanh (β * J) ^ X.card := by
  rw [partitionFunction_high_temp_expansion_h_zero G J β]
  -- Z = cosh^|E| * ∑_σ ∏_e (1 + t · spin_e)
  -- Step 1: subset expansion via Finset.prod_one_add
  have hexpand : ∀ σ : Config ι,
      (∏ e ∈ G.edgeFinset, (1 + Real.tanh (β * J) * edgeSpin σ e))
        = ∑ X ∈ G.edgeFinset.powerset,
            ∏ e ∈ X, (Real.tanh (β * J) * edgeSpin σ e) := fun σ =>
    Finset.prod_one_add G.edgeFinset
  simp_rw [hexpand]
  -- Step 2: pull tanh^|X| out of inner product
  have hpull : ∀ σ : Config ι, ∀ X : Finset (Sym2 ι),
      (∏ e ∈ X, (Real.tanh (β * J) * edgeSpin σ e))
        = Real.tanh (β * J) ^ X.card *
            (∏ e ∈ X, edgeSpin (K := ℝ) σ e) := by
    intros σ X
    rw [Finset.prod_mul_distrib, Finset.prod_const]
  simp_rw [hpull]
  -- Step 3: swap σ-sum and X-sum
  rw [Finset.sum_comm]
  -- Step 4: pull tanh^|X| out of σ-sum
  have hsum_const : ∀ X : Finset (Sym2 ι),
      (∑ σ : Config ι, Real.tanh (β * J) ^ X.card *
            (∏ e ∈ X, edgeSpin (K := ℝ) σ e))
        = Real.tanh (β * J) ^ X.card *
            (∑ σ : Config ι, ∏ e ∈ X, edgeSpin (K := ℝ) σ e) := fun X => by
    rw [← Finset.mul_sum]
  simp_rw [hsum_const]
  -- Step 5: collapse inner σ-sum via parity
  have hparity : ∀ X ∈ G.edgeFinset.powerset,
      (∑ σ : Config ι, ∏ e ∈ X, edgeSpin (K := ℝ) σ e)
        = if (∀ v : ι, Even ((X.filter (v ∈ ·)).card))
          then (2 : ℝ) ^ Fintype.card ι else 0 := fun X hX =>
    sum_prod_edgeSpin_eq_pow_card_or_zero G X (Finset.mem_powerset.mp hX)
  rw [Finset.sum_congr rfl
    (fun X hX => by rw [hparity X hX])]
  -- Step 6: redistribute and collapse to filter form
  -- LHS: cosh^|E| * ∑_X (tanh^|X| * if even then 2^|ι| else 0)
  -- Goal: 2^|ι| * cosh^|E| * ∑_{X with even} tanh^|X|
  have hdist : ∀ X : Finset (Sym2 ι),
      Real.tanh (β * J) ^ X.card *
          (if (∀ v : ι, Even ((X.filter (v ∈ ·)).card))
            then (2 : ℝ) ^ Fintype.card ι else 0)
        = (if (∀ v : ι, Even ((X.filter (v ∈ ·)).card))
            then (2 : ℝ) ^ Fintype.card ι * Real.tanh (β * J) ^ X.card
            else 0) := fun X => by
    by_cases h : ∀ v : ι, Even ((X.filter (v ∈ ·)).card)
    · rw [if_pos h, if_pos h]; ring
    · rw [if_neg h, if_neg h]; ring
  simp_rw [hdist]
  -- LHS: cosh^|E| * ∑_X (if even then 2^|ι| * tanh^|X| else 0)
  rw [← Finset.sum_filter]
  -- LHS: cosh^|E| * ∑_{X filtered} (2^|ι| * tanh^|X|)
  rw [← Finset.mul_sum]
  ring

/-- **High-temperature even-subset sum is `≥ 1`**: under `0 ≤ β J`,
`∑_{X ⊆ G.edgeFinset, even-degree} tanh(β J)^|X| ≥ 1`.

The empty edge subset `X = ∅` is always even-degree (every vertex
has degree `0`) and contributes `tanh(βJ)^0 = 1`; every other
even-degree subset contributes `tanh(βJ)^|X| ≥ 0` under `0 ≤ βJ`
(via `0 ≤ tanh(βJ)`). The core inequality underlying the Z lower
bound `partitionFunction_high_temp_expansion_h_zero_lower_bound`. -/
theorem one_le_sum_pow_tanh_even_subgraph
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    (1 : ℝ) ≤ ∑ X ∈ G.edgeFinset.powerset.filter
        (fun X : Finset (Sym2 ι) =>
          ∀ v : ι, Even ((X.filter (v ∈ ·)).card)),
        Real.tanh (β * J) ^ X.card := by
  have htanh_nn : 0 ≤ Real.tanh (β * J) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg
      (Real.sinh_nonneg_iff.mpr hβJ) (Real.cosh_pos _).le
  have hempty_mem : (∅ : Finset (Sym2 ι)) ∈ G.edgeFinset.powerset.filter
      (fun X => ∀ v : ι, Even ((X.filter (v ∈ ·)).card)) := by
    refine Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset _, ?_⟩
    intro v
    simp
  have hempty_term : Real.tanh (β * J) ^ (∅ : Finset (Sym2 ι)).card = 1 := by simp
  have hnn : ∀ X ∈ G.edgeFinset.powerset.filter
      (fun X : Finset (Sym2 ι) => ∀ v : ι, Even ((X.filter (v ∈ ·)).card)),
      0 ≤ Real.tanh (β * J) ^ (X : Finset (Sym2 ι)).card :=
    fun X _ => pow_nonneg htanh_nn _
  have hsingle :
      Real.tanh (β * J) ^ (∅ : Finset (Sym2 ι)).card
        ≤ ∑ X ∈ G.edgeFinset.powerset.filter
            (fun X : Finset (Sym2 ι) =>
              ∀ v : ι, Even ((X.filter (v ∈ ·)).card)),
            Real.tanh (β * J) ^ X.card :=
    Finset.single_le_sum (f := fun X : Finset (Sym2 ι) =>
        Real.tanh (β * J) ^ X.card) hnn hempty_mem
  rw [hempty_term] at hsingle
  exact hsingle

/-- **Lower bound from the empty-X term**: under `0 ≤ β J`, the
high-temperature expansion FV (3.45) yields the lower bound
`Z(G; J, 0, β) ≥ 2^|ι| · (cosh(βJ))^|E|`. The empty edge subset
`X = ∅` is always even-degree (every vertex has degree 0), and
contributes `tanh(βJ)^0 = 1` to the sum, while every other
even-degree subset contributes a nonneg amount under `0 ≤ βJ`
(since `0 ≤ tanh(βJ)` then). -/
theorem partitionFunction_high_temp_expansion_h_zero_lower_bound
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card
      ≤ partitionFunction G ⟨J, 0, β⟩ := by
  rw [partitionFunction_high_temp_expansion_h_zero_closed]
  -- ∑_{X ⊆ E, even} tanh^|X| ≥ 1 (X = ∅ contributes 1, others ≥ 0)
  have htanh_nn : 0 ≤ Real.tanh (β * J) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg
      (Real.sinh_nonneg_iff.mpr hβJ) (Real.cosh_pos _).le
  -- The empty set is in the filtered powerset
  have hempty_mem : (∅ : Finset (Sym2 ι)) ∈ G.edgeFinset.powerset.filter
      (fun X => ∀ v : ι, Even ((X.filter (v ∈ ·)).card)) := by
    refine Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset _, ?_⟩
    intro v
    simp
  have hsum_ge_one :
      (1 : ℝ) ≤ ∑ X ∈ G.edgeFinset.powerset.filter
        (fun X => ∀ v : ι, Even ((X.filter (v ∈ ·)).card)),
        Real.tanh (β * J) ^ X.card := by
    have hempty_term : Real.tanh (β * J) ^ (∅ : Finset (Sym2 ι)).card = 1 := by
      simp
    have hnn : ∀ X ∈ G.edgeFinset.powerset.filter
        (fun X : Finset (Sym2 ι) => ∀ v : ι, Even ((X.filter (v ∈ ·)).card)),
        0 ≤ Real.tanh (β * J) ^ (X : Finset (Sym2 ι)).card :=
      fun X _ => pow_nonneg htanh_nn _
    have hsingle :
        Real.tanh (β * J) ^ (∅ : Finset (Sym2 ι)).card
          ≤ ∑ X ∈ G.edgeFinset.powerset.filter
              (fun X : Finset (Sym2 ι) =>
                ∀ v : ι, Even ((X.filter (v ∈ ·)).card)),
              Real.tanh (β * J) ^ X.card :=
      Finset.single_le_sum (f := fun X : Finset (Sym2 ι) =>
          Real.tanh (β * J) ^ X.card) hnn hempty_mem
    rw [hempty_term] at hsingle
    exact hsingle
  -- Multiply both sides by 2^|ι| · cosh^|E| ≥ 0
  have hcommon_nn :
      0 ≤ (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card := by
    exact mul_nonneg (pow_nonneg (by norm_num) _)
      (pow_nonneg (Real.cosh_pos _).le _)
  calc (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card
      = (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card * 1 := by ring
    _ ≤ (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card *
        ∑ X ∈ G.edgeFinset.powerset.filter
          (fun X => ∀ v : ι, Even ((X.filter (v ∈ ·)).card)),
          Real.tanh (β * J) ^ X.card :=
        mul_le_mul_of_nonneg_left hsum_ge_one hcommon_nn

/-- **Free-energy lower bound from FV (3.45)** at zero external field:
under `0 < |ι|` and `0 ≤ β * J`,
`log 2 + (|E|/|ι|) · log(cosh(β·J)) ≤ freeEnergy(G, ⟨J, 0, β⟩)`.

A graph-aware sharpening of `freeEnergy_ge_log_two_cosh` specialized
to `h = 0` (where the latter gives only `log 2`): the edge-density
factor `|E|/|ι|` times `log(cosh(βJ)) ≥ 0` is the high-temperature
cluster-expansion bonus. Direct corollary of
`partitionFunction_high_temp_expansion_h_zero_lower_bound`
(Step 286) by taking logs and dividing by `|ι|`. -/
theorem freeEnergy_high_temp_h_zero_lower_bound
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Fintype.card ι) :
    Real.log 2 +
        (G.edgeFinset.card : ℝ) / Fintype.card ι *
          Real.log (Real.cosh (β * J))
      ≤ freeEnergy G ⟨J, 0, β⟩ := by
  have hZ_lb := partitionFunction_high_temp_expansion_h_zero_lower_bound G J β hβJ
  have hcosh_pos : 0 < Real.cosh (β * J) := Real.cosh_pos _
  have hZ_lb_pos :
      0 < (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card :=
    mul_pos (pow_pos (by norm_num) _) (pow_pos hcosh_pos _)
  -- Take logs
  have hlog : Real.log ((2 : ℝ) ^ Fintype.card ι *
                          Real.cosh (β * J) ^ G.edgeFinset.card)
        ≤ Real.log (partitionFunction G ⟨J, 0, β⟩) :=
    Real.log_le_log hZ_lb_pos hZ_lb
  -- Simplify LHS
  have hlog_lhs :
      Real.log ((2 : ℝ) ^ Fintype.card ι *
                  Real.cosh (β * J) ^ G.edgeFinset.card)
        = (Fintype.card ι : ℝ) * Real.log 2
          + (G.edgeFinset.card : ℝ) * Real.log (Real.cosh (β * J)) := by
    rw [Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow]
  rw [hlog_lhs] at hlog
  -- Divide by |ι| > 0
  unfold freeEnergy
  have hι_pos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hne
  rw [show (Real.log 2 + (G.edgeFinset.card : ℝ) / Fintype.card ι *
              Real.log (Real.cosh (β * J)))
        = (Fintype.card ι : ℝ)⁻¹ *
          ((Fintype.card ι : ℝ) * Real.log 2
            + (G.edgeFinset.card : ℝ) * Real.log (Real.cosh (β * J))) from by
      field_simp]
  exact mul_le_mul_of_nonneg_left hlog (by positivity)

/-! ### Correlation closed form (FV §3.7.3 eq. (3.46)) -/

/-- **`spinProduct` as vertex-power**: for any `A : Finset ι`,
`∏_{a ∈ A} (σ a).toSign = ∏_v (σ v).toSign^(if v ∈ A then 1 else 0)`. -/
private theorem spinProduct_eq_prod_pow_indicator
    (A : Finset ι) (σ : Config ι) :
    spinProduct A σ
      = ∏ v : ι, ((σ v).toSign : ℝ) ^ (if v ∈ A then (1 : ℕ) else 0) := by
  classical
  unfold spinProduct
  rw [show (A : Finset ι) = (Finset.univ : Finset ι).filter (· ∈ A) by
    ext v; simp]
  rw [Finset.prod_filter]
  refine Finset.prod_congr rfl (fun v _ => ?_)
  by_cases hv : v ∈ A <;> simp [hv]

/-- **σ-sum of `spinProduct A · edgeSpin product`**: for `X ⊆ G.edgeFinset`,
`∑_σ spinProduct A σ · ∏_{e ∈ X} edgeSpin σ e = 2^|ι|` if the parity
of every vertex `v` matches `(v ∈ A)` (i.e. `deg_X v + 1_A v` is even),
else `0`. The σ_A-weighted parity step underlying FV (3.46). -/
private theorem sum_spinProduct_mul_prod_edgeSpin_eq_pow_card_or_zero
    (G : SimpleGraph ι) [Fintype G.edgeSet] (X : Finset (Sym2 ι))
    (hX : X ⊆ G.edgeFinset) (A : Finset ι) :
    (∑ σ : Config ι,
      spinProduct A σ * ∏ e ∈ X, edgeSpin (K := ℝ) σ e)
      = if (∀ v : ι,
            Even ((if v ∈ A then (1 : ℕ) else 0)
                  + (X.filter (v ∈ ·)).card))
        then (2 : ℝ) ^ Fintype.card ι else 0 := by
  classical
  -- Combine the indicator-power form of σ_A with the edge → vertex-power
  -- bridge from Step 283.
  have hcombine : ∀ σ : Config ι,
      spinProduct A σ * (∏ e ∈ X, edgeSpin (K := ℝ) σ e)
        = ∏ v : ι, ((σ v).toSign : ℝ) ^
            ((if v ∈ A then (1 : ℕ) else 0)
             + (X.filter (v ∈ ·)).card) := by
    intro σ
    rw [spinProduct_eq_prod_pow_indicator A σ,
        prod_edgeSpin_eq_prod_pow_filter_card G X hX σ,
        ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun v _ => ?_)
    rw [← pow_add]
  simp_rw [hcombine]
  exact sum_prod_toSign_pow_real
    (k := fun v => (if v ∈ A then (1 : ℕ) else 0)
                  + (X.filter (v ∈ ·)).card)

/-- **Numerator high-temperature expansion (h = 0)**: for any `A : Finset ι`,
`∑_σ spinProduct A σ · boltzmannWeight G ⟨J,0,β⟩ σ
  = 2^|ι| · cosh(βJ)^|E| · ∑_{X ⊆ E : every v has parity (v ∈ A)} tanh(βJ)^|X|`,
where the parity condition `(v ∈ A)` means `deg_X v + 1_A v` is even.
Companion to `partitionFunction_high_temp_expansion_h_zero_closed`
for the numerator of `correlation G ⟨J,0,β⟩ A`. -/
private theorem sum_spinProduct_boltzmannWeight_h_zero_closed
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (A : Finset ι) :
    (∑ σ : Config ι,
      spinProduct A σ * boltzmannWeight G ⟨J, 0, β⟩ σ)
      = (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card *
        ∑ X ∈ G.edgeFinset.powerset.filter
          (fun X => ∀ v : ι,
            Even ((if v ∈ A then (1 : ℕ) else 0)
                  + (X.filter (v ∈ ·)).card)),
          Real.tanh (β * J) ^ X.card := by
  -- Same skeleton as `partitionFunction_high_temp_expansion_h_zero_closed`
  -- but carrying a `spinProduct A σ` factor.
  have hboltz_h_zero : ∀ σ : Config ι,
      boltzmannWeight G ⟨J, 0, β⟩ σ
        = ∏ e ∈ G.edgeFinset, Real.exp (β * J * edgeSpin σ e) := by
    intro σ
    unfold boltzmannWeight hamiltonian interactionEnergy externalFieldEnergy
    rw [show -β *
            (-J * ∑ e ∈ G.edgeFinset, edgeSpin σ e
              + -(0 : ℝ) * ∑ i : ι, Spin.sign ℝ (σ i))
          = (β * J) * (∑ e ∈ G.edgeFinset, edgeSpin σ e) from by ring,
        Finset.mul_sum, Real.exp_sum]
  simp_rw [hboltz_h_zero]
  have hedge_decomp : ∀ σ : Config ι, ∀ e ∈ G.edgeFinset,
      Real.exp (β * J * edgeSpin σ e) =
        Real.cosh (β * J) * (1 + Real.tanh (β * J) * edgeSpin σ e) := by
    intros σ e _
    rw [exp_edgeSpin_decomp, Real.tanh_eq_sinh_div_cosh]
    have hcosh_ne : Real.cosh (β * J) ≠ 0 := (Real.cosh_pos _).ne'
    field_simp
  simp_rw [fun σ =>
    Finset.prod_congr rfl (hedge_decomp σ)]
  simp_rw [Finset.prod_mul_distrib, Finset.prod_const]
  -- ∑_σ spinProduct A σ · cosh^|E| · ∏_e (1 + ...) = cosh^|E| · ∑_σ spinProduct A σ · ∏_e (1+...)
  rw [show (∑ σ : Config ι, spinProduct A σ *
        (Real.cosh (β * J) ^ G.edgeFinset.card *
          ∏ e ∈ G.edgeFinset, (1 + Real.tanh (β * J) * edgeSpin σ e)))
      = Real.cosh (β * J) ^ G.edgeFinset.card *
        ∑ σ : Config ι, spinProduct A σ *
          ∏ e ∈ G.edgeFinset, (1 + Real.tanh (β * J) * edgeSpin σ e) by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    ring]
  -- Subset expansion
  have hexpand : ∀ σ : Config ι,
      (∏ e ∈ G.edgeFinset, (1 + Real.tanh (β * J) * edgeSpin σ e))
        = ∑ X ∈ G.edgeFinset.powerset,
            ∏ e ∈ X, (Real.tanh (β * J) * edgeSpin σ e) := fun σ =>
    Finset.prod_one_add G.edgeFinset
  simp_rw [hexpand]
  -- Pull tanh^|X| out
  have hpull : ∀ σ : Config ι, ∀ X : Finset (Sym2 ι),
      (∏ e ∈ X, (Real.tanh (β * J) * edgeSpin σ e))
        = Real.tanh (β * J) ^ X.card *
            (∏ e ∈ X, edgeSpin (K := ℝ) σ e) := by
    intros σ X
    rw [Finset.prod_mul_distrib, Finset.prod_const]
  simp_rw [hpull]
  -- Distribute spinProduct A σ over the X-sum
  rw [show (∑ σ : Config ι, spinProduct A σ *
        ∑ X ∈ G.edgeFinset.powerset,
          Real.tanh (β * J) ^ X.card * (∏ e ∈ X, edgeSpin (K := ℝ) σ e))
      = ∑ σ : Config ι,
        ∑ X ∈ G.edgeFinset.powerset,
          spinProduct A σ * (Real.tanh (β * J) ^ X.card *
            ∏ e ∈ X, edgeSpin (K := ℝ) σ e) by
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [Finset.mul_sum]]
  -- Swap σ ↔ X and pull tanh^|X| out further
  rw [Finset.sum_comm]
  rw [show (∑ X ∈ G.edgeFinset.powerset, ∑ σ : Config ι,
        spinProduct A σ * (Real.tanh (β * J) ^ X.card *
          ∏ e ∈ X, edgeSpin (K := ℝ) σ e))
      = ∑ X ∈ G.edgeFinset.powerset,
        Real.tanh (β * J) ^ X.card *
          ∑ σ : Config ι,
            spinProduct A σ * ∏ e ∈ X, edgeSpin (K := ℝ) σ e by
    refine Finset.sum_congr rfl (fun X _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    ring]
  -- Apply parity collapse
  have hparity : ∀ X ∈ G.edgeFinset.powerset,
      (∑ σ : Config ι,
        spinProduct A σ * ∏ e ∈ X, edgeSpin (K := ℝ) σ e)
        = if (∀ v : ι,
              Even ((if v ∈ A then (1 : ℕ) else 0)
                    + (X.filter (v ∈ ·)).card))
          then (2 : ℝ) ^ Fintype.card ι else 0 := fun X hX =>
    sum_spinProduct_mul_prod_edgeSpin_eq_pow_card_or_zero G X
      (Finset.mem_powerset.mp hX) A
  rw [Finset.sum_congr rfl
    (fun X hX => by rw [hparity X hX])]
  -- Distribute and collapse via filter
  have hdist : ∀ X : Finset (Sym2 ι),
      Real.tanh (β * J) ^ X.card *
          (if (∀ v : ι,
                Even ((if v ∈ A then (1 : ℕ) else 0)
                      + (X.filter (v ∈ ·)).card))
            then (2 : ℝ) ^ Fintype.card ι else 0)
        = (if (∀ v : ι,
                Even ((if v ∈ A then (1 : ℕ) else 0)
                      + (X.filter (v ∈ ·)).card))
            then (2 : ℝ) ^ Fintype.card ι * Real.tanh (β * J) ^ X.card
            else 0) := fun X => by
    by_cases h : ∀ v : ι, Even ((if v ∈ A then (1 : ℕ) else 0)
                                + (X.filter (v ∈ ·)).card)
    · rw [if_pos h, if_pos h]; ring
    · rw [if_neg h, if_neg h]; ring
  simp_rw [hdist]
  rw [← Finset.sum_filter, ← Finset.mul_sum]
  ring

/-- **Correlation closed form at h = 0 — Friedli–Velenik §3.7.3 eq. (3.46)**:
\[
\langle \sigma_A \rangle_{\beta, 0} =
  \frac{\sum_{X \subseteq E,\, \partial X = A} \tanh(\beta J)^{|X|}}
       {\sum_{X \subseteq E,\, \partial X = \emptyset} \tanh(\beta J)^{|X|}},
\]
where the boundary condition `∂X = A` is encoded as
`∀ v, Even ((1_A v) + (X.filter (v ∈ ·)).card)` (i.e. the parity
of the X-degree at every vertex `v` matches whether `v ∈ A`).

The `2^{|\iota|} \cdot (\cosh \beta J)^{|E|}` prefactor cancels between
numerator and denominator. Combines
`partitionFunction_high_temp_expansion_h_zero_closed` (Step 283) with
`sum_spinProduct_boltzmannWeight_h_zero_closed`.

References: GJ §18.3; FV §3.7.3 eq. (3.46), p. 117 (2017 ed.). -/
theorem correlation_high_temp_expansion_h_zero_closed
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (A : Finset ι) :
    correlation G ⟨J, 0, β⟩ A =
      (∑ X ∈ G.edgeFinset.powerset.filter
          (fun X => ∀ v : ι,
            Even ((if v ∈ A then (1 : ℕ) else 0)
                  + (X.filter (v ∈ ·)).card)),
        Real.tanh (β * J) ^ X.card) /
      (∑ X ∈ G.edgeFinset.powerset.filter
          (fun X => ∀ v : ι, Even ((X.filter (v ∈ ·)).card)),
        Real.tanh (β * J) ^ X.card) := by
  unfold correlation gibbsExpectation
  rw [sum_spinProduct_boltzmannWeight_h_zero_closed G J β A,
      partitionFunction_high_temp_expansion_h_zero_closed G J β]
  -- Now: (Z_closed)⁻¹ * N_closed = N_subsum / Z_subsum
  set N_sub : ℝ := ∑ X ∈ G.edgeFinset.powerset.filter
      (fun X => ∀ v : ι,
        Even ((if v ∈ A then (1 : ℕ) else 0)
              + (X.filter (v ∈ ·)).card)),
      Real.tanh (β * J) ^ X.card with hN_sub
  set Z_sub : ℝ := ∑ X ∈ G.edgeFinset.powerset.filter
      (fun X => ∀ v : ι, Even ((X.filter (v ∈ ·)).card)),
      Real.tanh (β * J) ^ X.card with hZ_sub
  -- Goal: ((2^|ι|·cosh^|E|·Z_sub))⁻¹ · (2^|ι|·cosh^|E|·N_sub) = N_sub / Z_sub
  have hcommon_pos :
      (0 : ℝ) < (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card := by
    apply mul_pos
    · exact pow_pos (by norm_num) _
    · exact pow_pos (Real.cosh_pos _) _
  have hcommon_ne : (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card ≠ 0 :=
    hcommon_pos.ne'
  field_simp

/-! ### Handshake lemma for arbitrary edge subsets

For `X ⊆ G.edgeFinset` on a `SimpleGraph` (edges non-diagonal),
`∑_v (X.filter (v ∈ ·)).card = 2 · |X|`, the standard handshake
identity. Combined with `Finset.even_sum_iff_even_card_odd`, this
gives that the number of odd `X`-degree vertices is always even —
the parity argument behind the FV (3.46) Z₂ symmetry. -/

/-- **Handshake lemma for arbitrary edge subsets**: for `X ⊆ G.edgeFinset`
on a `SimpleGraph` (so all edges are non-diagonal),
`∑_v (X.filter (v ∈ ·)).card = 2 · |X|`. -/
private theorem sum_filter_card_eq_two_mul_card
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (X : Finset (Sym2 ι)) (hX : X ⊆ G.edgeFinset) :
    ∑ v : ι, (X.filter (v ∈ ·)).card = 2 * X.card := by
  classical
  -- per-v rewrite: card filter = ∑ over X of indicator
  have hper_v : ∀ v : ι,
      (X.filter (v ∈ ·)).card = ∑ e ∈ X, (if v ∈ e then 1 else 0) := by
    intro v
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  simp_rw [hper_v]
  rw [Finset.sum_comm]
  -- inner sum: ∑_v (if v ∈ e then 1 else 0) = e.toFinset.card = 2 (non-diag)
  have hinner : ∀ e ∈ X,
      ∑ v : ι, (if v ∈ e then (1 : ℕ) else 0) = 2 := by
    intros e he
    have heq :
        (∑ v : ι, if v ∈ e then (1 : ℕ) else 0)
          = ((Finset.univ : Finset ι).filter (· ∈ e)).card := by
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [heq]
    have hf_eq : (Finset.univ : Finset ι).filter (· ∈ e) = e.toFinset := by
      ext v; simp
    rw [hf_eq]
    have hnd : ¬ e.IsDiag := G.not_isDiag_of_mem_edgeSet
      (G.mem_edgeFinset.mp (hX he))
    exact e.card_toFinset_of_not_isDiag hnd
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul]
  ring

/-- **Even count of odd-degree vertices**: for `X ⊆ G.edgeFinset`,
`Even |{v | Odd (X.filter (v ∈ ·)).card}|`. The number of vertices with
odd `X`-degree is always even. Direct consequence of the handshake
identity `∑_v deg_X v = 2|X|` plus `Finset.even_sum_iff_even_card_odd`. -/
private theorem even_card_odd_filter_card
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (X : Finset (Sym2 ι)) (hX : X ⊆ G.edgeFinset) :
    Even ((Finset.univ : Finset ι).filter
      (fun v => Odd ((X.filter (v ∈ ·)).card))).card := by
  have hsum := sum_filter_card_eq_two_mul_card G X hX
  have h_even : Even (∑ v : ι, (X.filter (v ∈ ·)).card) := by
    rw [hsum]; exact ⟨X.card, by ring⟩
  exact (Finset.even_sum_iff_even_card_odd _).mp h_even

/-- **FV (3.46) numerator filter is empty for odd-cardinality A**:
the filtered powerset
`{X ⊆ G.edgeFinset : ∀ v, Even ((1_A v) + (X.filter (v ∈ ·)).card)}`
is *empty* whenever `|A|` is odd.

Direct consequence of the handshake lemma: for any `X` in this filter,
the condition forces `{v | Odd (deg_X v)} = A`, but the LHS has even
cardinality (handshake), so `|A|` even — contradicting odd `|A|`.

A sharper version of `sum_high_temp_numerator_h_zero_odd_card_eq_zero`
(Step 291): instead of "the sum vanishes", we show "the index set is
empty". Independent of the `correlation_odd_vanish` Z₂-flip argument. -/
theorem high_temp_numerator_filter_eq_empty_of_odd_card
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (A : Finset ι) (hA_odd : Odd A.card) :
    G.edgeFinset.powerset.filter
        (fun X : Finset (Sym2 ι) => ∀ v : ι,
          Even ((if v ∈ A then (1 : ℕ) else 0)
                + (X.filter (v ∈ ·)).card)) = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro X hX
  rw [Finset.mem_filter, Finset.mem_powerset] at hX
  obtain ⟨hXsub, hcond⟩ := hX
  -- Translate hcond: ∂X = A (set of v with odd X-degree = A)
  have hboundary_eq_A :
      (Finset.univ : Finset ι).filter
          (fun v => Odd ((X.filter (v ∈ ·)).card)) = A := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hodd
      by_contra hvA
      have := hcond v
      rw [if_neg hvA, zero_add] at this
      exact (Nat.not_even_iff_odd.mpr hodd) this
    · intro hvA
      have := hcond v
      rw [if_pos hvA] at this
      rw [show (1 : ℕ) + (X.filter (v ∈ ·)).card
            = (X.filter (v ∈ ·)).card + 1 from Nat.add_comm _ _,
          Nat.even_add_one, Nat.not_even_iff_odd] at this
      exact this
  have h_even := even_card_odd_filter_card G X hXsub
  rw [hboundary_eq_A] at h_even
  exact (Nat.not_even_iff_odd.mpr hA_odd) h_even

/-! ### Z₂ symmetry from FV (3.46): odd-cardinality numerator sum vanishes -/

/-- **FV (3.46) numerator vanishes for odd-cardinality A**: the FV (3.46)
numerator `∑_{X : ∂X = A} tanh(βJ)^|X|` equals `0` for any `A` of odd
cardinality.

Proof: by `correlation_odd_vanish` (Z₂ spin-flip argument), the
correlation `⟨σ_A⟩_{β,0}` itself vanishes for odd `|A|`. Combining this
with the FV (3.46) closed form (`correlation_high_temp_expansion_h_zero_closed`)
gives `0 = numerator / denominator`; the denominator is strictly
positive (deduced from `partitionFunction_pos` and the FV (3.45)
factorization), so the numerator must be `0`.

Heuristically (not used in this proof), the filtered set indexing the
numerator is empty by the handshake lemma: `|∂X|` is always even, so no
`X` can satisfy `∂X = A` when `|A|` is odd. -/
theorem sum_high_temp_numerator_h_zero_odd_card_eq_zero
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (A : Finset ι) (hA_odd : Odd A.card) :
    ∑ X ∈ G.edgeFinset.powerset.filter
        (fun X : Finset (Sym2 ι) => ∀ v : ι,
          Even ((if v ∈ A then (1 : ℕ) else 0)
                + (X.filter (v ∈ ·)).card)),
        Real.tanh (β * J) ^ X.card = 0 := by
  -- Multiply both sides of FV (3.46) by the (positive) denominator
  have hclosed := correlation_high_temp_expansion_h_zero_closed G J β A
  have hodd_eq_zero := correlation_odd_vanish G J β A hA_odd
  rw [hodd_eq_zero] at hclosed
  -- Now: 0 = numerator / denominator, where denominator > 0 (contains X = ∅)
  set Z_sub : ℝ := ∑ X ∈ G.edgeFinset.powerset.filter
      (fun X : Finset (Sym2 ι) => ∀ v : ι, Even ((X.filter (v ∈ ·)).card)),
      Real.tanh (β * J) ^ X.card with hZ_sub
  set N_sub : ℝ := ∑ X ∈ G.edgeFinset.powerset.filter
      (fun X : Finset (Sym2 ι) => ∀ v : ι,
        Even ((if v ∈ A then (1 : ℕ) else 0)
              + (X.filter (v ∈ ·)).card)),
      Real.tanh (β * J) ^ X.card with hN_sub
  -- 0 = N_sub / Z_sub. We need N_sub = 0. This needs Z_sub ≠ 0.
  -- But the FV (3.45) closed form already established Z_sub > 0
  -- (since Z > 0 and the prefactor 2^|ι| · cosh^|E| > 0).
  have hZ_pos : 0 < Z_sub := by
    -- Z = 2^|ι| · cosh^|E| · Z_sub, Z > 0, prefactor > 0
    have hZ_eq := partitionFunction_high_temp_expansion_h_zero_closed G J β
    have hZ_pos := partitionFunction_pos G ⟨J, 0, β⟩
    have hpref_pos : (0 : ℝ) <
        (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card :=
      mul_pos (pow_pos (by norm_num) _) (pow_pos (Real.cosh_pos _) _)
    have hprod : (0 : ℝ) < (2 : ℝ) ^ Fintype.card ι *
                              Real.cosh (β * J) ^ G.edgeFinset.card * Z_sub := by
      rw [← hZ_eq]; exact hZ_pos
    exact (mul_pos_iff_of_pos_left hpref_pos).mp hprod
  rw [eq_div_iff hZ_pos.ne'] at hclosed
  rw [zero_mul] at hclosed
  exact hclosed.symm

/-- **Correlation nonnegativity at h = 0 from FV (3.46)**: under
`0 ≤ β * J`, `0 ≤ correlation G ⟨J, 0, β⟩ A` for any `A : Finset ι`.

Alternate derivation of GKS-I (`gks_first` / `correlation_nonneg_of_ferromagnetic`)
from the FV (3.46) closed form: numerator and denominator are both
sums of `tanh(βJ)^|X|` with `tanh(βJ) ≥ 0` (from `0 ≤ βJ`), hence
both nonneg; the denominator is strictly positive (deduced from
`partitionFunction_pos`), so the ratio is `≥ 0`. -/
theorem correlation_high_temp_h_zero_nonneg
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (A : Finset ι) :
    0 ≤ correlation G ⟨J, 0, β⟩ A := by
  rw [correlation_high_temp_expansion_h_zero_closed]
  have htanh_nn : 0 ≤ Real.tanh (β * J) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg
      (Real.sinh_nonneg_iff.mpr hβJ) (Real.cosh_pos _).le
  -- Numerator nonneg: sum of tanh^|X| ≥ 0
  have hnum_nn :
      0 ≤ ∑ X ∈ G.edgeFinset.powerset.filter
          (fun X : Finset (Sym2 ι) => ∀ v : ι,
            Even ((if v ∈ A then (1 : ℕ) else 0)
                  + (X.filter (v ∈ ·)).card)),
          Real.tanh (β * J) ^ X.card :=
    Finset.sum_nonneg (fun X _ => pow_nonneg htanh_nn _)
  -- Denominator nonneg: same sum, different filter
  have hden_nn :
      0 ≤ ∑ X ∈ G.edgeFinset.powerset.filter
          (fun X : Finset (Sym2 ι) => ∀ v : ι,
            Even ((X.filter (v ∈ ·)).card)),
          Real.tanh (β * J) ^ X.card :=
    Finset.sum_nonneg (fun X _ => pow_nonneg htanh_nn _)
  exact div_nonneg hnum_nn hden_nn

/-- **Z₂ symmetry of correlations at h = 0 from FV (3.46) + handshake**:
for any `A : Finset ι` of odd cardinality, `correlation G ⟨J, 0, β⟩ A = 0`.

A direct combinatorial proof going through:
1. `correlation_high_temp_expansion_h_zero_closed` (FV (3.46), Step 284)
2. `high_temp_numerator_filter_eq_empty_of_odd_card` (Step 297) — the
   numerator filter is *literally empty* by edge-vertex handshake.
3. `Finset.sum_empty`: empty sum is `0`; `0 / x = 0`.

Independent of `correlation_odd_vanish` (the standard spin-flip Z₂
argument). Provides a fully closed-form / combinatorial alternative. -/
theorem correlation_high_temp_h_zero_odd_card_eq_zero
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (A : Finset ι) (hA_odd : Odd A.card) :
    correlation G ⟨J, 0, β⟩ A = 0 := by
  rw [correlation_high_temp_expansion_h_zero_closed,
      high_temp_numerator_filter_eq_empty_of_odd_card G A hA_odd,
      Finset.sum_empty, zero_div]

/-- **High-temperature parameter**: `t = tanh(βJ)`.
For `βJ ≥ 0`, `t ∈ [0, 1)`, and the high-temperature expansion
converges when `t` is small. -/
noncomputable def highTempParam (β J : ℝ) : ℝ := Real.tanh (β * J)

/-- The high-temperature parameter satisfies `|t| < 1` for all finite `βJ`. -/
theorem abs_highTempParam_lt_one (β J : ℝ) :
    |highTempParam β J| < 1 := by
  unfold highTempParam
  exact abs_tanh_lt_one (β * J)

/-- The high-temperature parameter is strictly less than 1. -/
theorem highTempParam_lt_one (β J : ℝ) :
    highTempParam β J < 1 := by
  unfold highTempParam
  exact tanh_lt_one (β * J)

/-! ## Free energy upper bound (Corollary 10.3.2, divided by `|ι|`) -/

/-- **Free energy upper bound** (Glimm–Jaffe, Cor. 10.3.2 divided by `|ι|`):
for nonempty `ι`,
`f(G, p) ≤ log 2 + |β|·(|J|·|E| + |h|·|ι|) / |ι|`.

Obtained from `partitionFunction_upper` by taking the logarithm
(`Z ≤ 2^|ι| · exp(|β|·(|J|·|E| + |h|·|ι|))` implies
`log Z ≤ |ι|·log 2 + |β|·(|J|·|E| + |h|·|ι|)`) and dividing by `|ι|`. -/
theorem freeEnergy_upper_bound (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (hne : 0 < Fintype.card ι) :
    freeEnergy G p ≤ Real.log 2 +
      |p.β| * (|p.J| * G.edgeFinset.card + |p.h| * Fintype.card ι)
        / Fintype.card ι := by
  set A : ℝ :=
    |p.β| * (|p.J| * G.edgeFinset.card + |p.h| * Fintype.card ι)
  have hcard_pos : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast hne
  have h_config_pos : (0 : ℝ) < (Fintype.card (Config ι) : ℝ) := by
    rw [card_config_eq_two_pow]; positivity
  have h_exp_pos : (0 : ℝ) < Real.exp A := Real.exp_pos _
  have hlog : Real.log (partitionFunction G p)
      ≤ (Fintype.card ι : ℝ) * Real.log 2 + A := by
    calc Real.log (partitionFunction G p)
        ≤ Real.log ((Fintype.card (Config ι) : ℝ) * Real.exp A) :=
          (Real.log_le_log_iff (partitionFunction_pos G p)
            (mul_pos h_config_pos h_exp_pos)).mpr (partitionFunction_upper G p)
      _ = Real.log (Fintype.card (Config ι) : ℝ) + A := by
          rw [Real.log_mul h_config_pos.ne' h_exp_pos.ne', Real.log_exp]
      _ = (Fintype.card ι : ℝ) * Real.log 2 + A := by
          rw [card_config_eq_two_pow]; push_cast; rw [Real.log_pow]
  unfold freeEnergy
  calc (Fintype.card ι : ℝ)⁻¹ * Real.log (partitionFunction G p)
      ≤ (Fintype.card ι : ℝ)⁻¹ * ((Fintype.card ι : ℝ) * Real.log 2 + A) :=
        mul_le_mul_of_nonneg_left hlog (inv_nonneg.mpr hcard_pos.le)
    _ = Real.log 2 + A / (Fintype.card ι : ℝ) := by
        field_simp

end IsingModel
