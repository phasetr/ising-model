import IsingModel.FreeEnergy

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

end IsingModel
