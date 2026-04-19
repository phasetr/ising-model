import IsingModel.Hamiltonian
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric

/-!
# Gibbs measure, partition function, and expectations

Definitions for the Ising model Gibbs measure on a finite lattice.
These are specialized to `ℝ` since they require the exponential function.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Boltzmann weight and partition function -/

/-- The Boltzmann weight for a configuration: `exp(-β * H(σ))`. -/
noncomputable def boltzmannWeight (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (σ : Config ι) : ℝ :=
  Real.exp (-p.β * hamiltonian G p σ)

/-- The partition function: `Z = ∑_σ exp(-β * H(σ))`. -/
noncomputable def partitionFunction (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) : ℝ :=
  ∑ σ : Config ι, boltzmannWeight G p σ

omit [DecidableEq ι] in
/-- Each Boltzmann weight is positive. -/
theorem boltzmannWeight_pos (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (σ : Config ι) :
    0 < boltzmannWeight G p σ :=
  Real.exp_pos _

/-- The partition function is positive. -/
theorem partitionFunction_pos (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) :
    0 < partitionFunction G p := by
  unfold partitionFunction
  apply Finset.sum_pos
  · intro σ _
    exact boltzmannWeight_pos G p σ
  · exact Finset.univ_nonempty

/-- The partition function is nonzero. -/
theorem partitionFunction_ne_zero (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) :
    partitionFunction G p ≠ 0 :=
  ne_of_gt (partitionFunction_pos G p)

/-! ## Gibbs expectation -/

/-- The Gibbs expectation of an observable `F`: `⟨F⟩ = Z⁻¹ ∑_σ F(σ) exp(-β H(σ))`. -/
noncomputable def gibbsExpectation (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (F : Config ι → ℝ) : ℝ :=
  (partitionFunction G p)⁻¹ * ∑ σ : Config ι, F σ * boltzmannWeight G p σ

/-! ## Correlation function -/

/-- The spin product `σ^A = ∏_{i ∈ A} toSign(σ_i)`, as a real number. -/
noncomputable def spinProduct (A : Finset ι) (σ : Config ι) : ℝ :=
  ∏ i ∈ A, (↑(σ i).toSign : ℝ)

/-- The correlation function `⟨σ^A⟩ = ⟨∏_{i ∈ A} s(σ_i)⟩`. -/
noncomputable def correlation (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (A : Finset ι) : ℝ :=
  gibbsExpectation G p (spinProduct A)

/-! ## Spin product algebra -/

omit [Fintype ι] [DecidableEq ι] in
/-- The spin product over the empty set is `1`. -/
@[simp]
theorem spinProduct_empty (σ : Config ι) : spinProduct ∅ σ = 1 := by
  simp [spinProduct]

omit [Fintype ι] [DecidableEq ι] in
/-- The spin product over a singleton is the spin sign at that site. -/
@[simp]
theorem spinProduct_singleton (i : ι) (σ : Config ι) :
    spinProduct {i} σ = ↑(σ i).toSign := by
  simp [spinProduct]

omit [Fintype ι] in
/-- The spin product over a disjoint union factors: `σ^{A ∪ B} = σ^A · σ^B`. -/
theorem spinProduct_union {A B : Finset ι} (h : Disjoint A B) (σ : Config ι) :
    spinProduct (A ∪ B) σ = spinProduct A σ * spinProduct B σ := by
  simp [spinProduct, Finset.prod_union h]

omit [Fintype ι] [DecidableEq ι] in
/-- The square of any spin product is `1`, since each factor is `±1`. -/
theorem spinProduct_sq (A : Finset ι) (σ : Config ι) :
    spinProduct A σ ^ 2 = 1 := by
  simp only [sq, spinProduct, ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun i _ => by
    simp [← sq, ← Int.cast_pow, Spin.toSign_sq]

/-- **Correlation of the empty set is `1`**: the normalization of the
Gibbs measure. `spinProduct ∅ σ = 1` gives
`∑_σ 1 · weight = Z`, so `Z⁻¹ · Z = 1`. -/
@[simp]
theorem correlation_empty (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) :
    correlation G p ∅ = 1 := by
  unfold correlation gibbsExpectation
  have h1 : ∀ σ : Config ι,
      spinProduct ∅ σ * boltzmannWeight G p σ = boltzmannWeight G p σ := by
    intro σ; rw [spinProduct_empty, one_mul]
  rw [Finset.sum_congr rfl (fun σ _ => h1 σ)]
  change (partitionFunction G p)⁻¹ * partitionFunction G p = 1
  exact inv_mul_cancel₀ (partitionFunction_ne_zero G p)

omit [DecidableEq ι] in
/-- **Hamiltonian vanishes at zero parameters**: with `J = 0` and `h = 0`,
the Hamiltonian is identically zero (no coupling, no field). -/
theorem hamiltonian_zero_params (G : SimpleGraph ι) [Fintype G.edgeSet]
    (β : ℝ) (σ : Config ι) :
    hamiltonian G (⟨0, 0, β⟩ : IsingParams ℝ) σ = 0 := by
  unfold hamiltonian interactionEnergy externalFieldEnergy
  simp

/-- **Partition function at zero parameters**: with `J = 0` and `h = 0`,
the Hamiltonian is identically zero, so every Boltzmann weight equals 1
and the partition function counts the configurations:
`Z_G(⟨0, 0, β⟩) = Fintype.card (Config ι)`. -/
theorem partitionFunction_zero_params (G : SimpleGraph ι) [Fintype G.edgeSet]
    (β : ℝ) :
    partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ)
      = (Fintype.card (Config ι) : ℝ) := by
  unfold partitionFunction boltzmannWeight
  calc ∑ σ : Config ι,
        Real.exp (-(⟨0, 0, β⟩ : IsingParams ℝ).β *
          hamiltonian G (⟨0, 0, β⟩ : IsingParams ℝ) σ)
      = ∑ _σ : Config ι, (1 : ℝ) := by
        refine Finset.sum_congr rfl ?_
        intro σ _
        rw [hamiltonian_zero_params, mul_zero, Real.exp_zero]
    _ = (Fintype.card (Config ι) : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

/-- **Partition function at `β = 0`**: the prefactor `-β` in the
Boltzmann weight vanishes, so every weight collapses to
`exp 0 = 1` regardless of `J` and `h`, and
`Z_G(⟨J, h, 0⟩) = Fintype.card (Config ι)` for every ambient graph. -/
theorem partitionFunction_beta_zero (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h : ℝ) :
    partitionFunction G (⟨J, h, 0⟩ : IsingParams ℝ)
      = (Fintype.card (Config ι) : ℝ) := by
  unfold partitionFunction boltzmannWeight
  calc ∑ σ : Config ι,
        Real.exp (-(⟨J, h, 0⟩ : IsingParams ℝ).β *
          hamiltonian G (⟨J, h, 0⟩ : IsingParams ℝ) σ)
      = ∑ _σ : Config ι, (1 : ℝ) := by
        refine Finset.sum_congr rfl ?_
        intros σ _
        change Real.exp (-(0 : ℝ) *
          hamiltonian G (⟨J, h, 0⟩ : IsingParams ℝ) σ) = 1
        rw [neg_zero, zero_mul, Real.exp_zero]
    _ = (Fintype.card (Config ι) : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

/-- **Cardinality of `Spin` is 2**. -/
theorem card_spin : Fintype.card Spin = 2 := rfl

/-- **Cardinality of the configuration space**: `Config ι = ι → Spin`
is finite of size `2^(Fintype.card ι)`. -/
theorem card_config_eq_two_pow :
    Fintype.card (Config ι) = 2 ^ Fintype.card ι := by
  simp [Config, card_spin]

/-! ## Empty graph: free-spin / one-body limit

For the empty graph `⊥` (no edges), the `J`-term of the Hamiltonian is
the empty sum and hence vanishes, leaving only the external field term.
The partition function then factorizes over sites as
`(2 · cosh(β·h))^|ι|`. -/

omit [DecidableEq ι] in
/-- **Hamiltonian on the empty graph**: at `G = ⊥`, the interaction
energy is the empty edge sum and vanishes, leaving only the
external field term `-h · Σ sign(σ_i)`. -/
theorem hamiltonian_bot (p : IsingParams ℝ) (σ : Config ι) :
    hamiltonian (⊥ : SimpleGraph ι) p σ
      = -p.h * ∑ i : ι, Spin.sign ℝ (σ i) := by
  unfold hamiltonian interactionEnergy externalFieldEnergy
  rw [SimpleGraph.edgeFinset_bot, Finset.sum_empty, mul_zero, zero_add]

omit [DecidableEq ι] in
/-- **Hamiltonian at `J = 0`** (graph-independent): the interaction
energy has prefactor `-J = 0`, so `H_G ⟨0, h, β⟩ σ` reduces to the
external field term alone for any ambient graph `G`. -/
theorem hamiltonian_J_zero (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h β : ℝ) (σ : Config ι) :
    hamiltonian G (⟨0, h, β⟩ : IsingParams ℝ) σ
      = -h * ∑ i : ι, Spin.sign ℝ (σ i) := by
  unfold hamiltonian interactionEnergy externalFieldEnergy
  simp

omit [DecidableEq ι] in
/-- **Central identity `H_G ⟨0, h, β⟩ σ = H_⊥ ⟨0, h, β⟩ σ`**:
at `J = 0` the Hamiltonian is graph-independent.

Both sides equal `-h · ∑ sign(σ_i)` by `hamiltonian_J_zero` and
`hamiltonian_bot`. Base identity used to express the entire J=0
closed-form chain (`partitionFunction_J_zero`, `freeEnergy_J_zero`,
and their along-exhaustion / ∞-vol lifts) as corollaries of the
`⊥`-graph results. -/
theorem hamiltonian_eq_bot_at_J_zero (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h β : ℝ) (σ : Config ι) :
    hamiltonian G (⟨0, h, β⟩ : IsingParams ℝ) σ
      = hamiltonian (⊥ : SimpleGraph ι) (⟨0, h, β⟩ : IsingParams ℝ) σ := by
  rw [hamiltonian_J_zero, hamiltonian_bot]

/-- **Sum over `Spin`**: `∑ s : Spin, f s = f Spin.up + f Spin.down`.
Spin is a 2-element Fintype `{up, down}`, so the universal sum splits
into these two terms. -/
theorem sum_spin {α : Type*} [AddCommMonoid α] (f : Spin → α) :
    ∑ s : Spin, f s = f Spin.up + f Spin.down := by
  have huniv : (Finset.univ : Finset Spin) = {Spin.up, Spin.down} := by
    ext s; cases s <;> simp
  rw [huniv, Finset.sum_pair (fun h => Spin.noConfusion h)]

/-- **Single-site sum at the empty-graph site**:
`∑_{s ∈ Spin} exp(β·h · sign s) = 2 · cosh(β·h)`.

The two-element sum over `{up, down}` evaluates to `exp(β·h) + exp(-β·h)`,
which is `2 · cosh(β·h)` by `Real.cosh_eq`. -/
theorem sum_exp_spin_sign (β h : ℝ) :
    ∑ s : Spin, Real.exp (β * h * Spin.sign ℝ s)
      = 2 * Real.cosh (β * h) := by
  rw [sum_spin]
  have hup : Spin.sign ℝ Spin.up = (1 : ℝ) := by
    simp [Spin.sign, Spin.toSign]
  have hdown : Spin.sign ℝ Spin.down = (-1 : ℝ) := by
    simp [Spin.sign, Spin.toSign]
  rw [hup, hdown]
  simp only [mul_one, mul_neg_one, Real.cosh_eq]
  ring

/-- **Single-site signed sum at the empty-graph site**:
`∑_{s ∈ Spin} sign(s) · exp(β·h · sign(s)) = 2 · sinh(β·h)`.

The two-element sum over `{up, down}` evaluates to
`exp(β·h) - exp(-β·h)`, which is `2 · sinh(β·h)` by `Real.sinh_eq`.
Companion to `sum_exp_spin_sign` (unsigned, gives `2 cosh`); the signed
version powers the `⊥`-graph closed form of the correlation function. -/
theorem sum_spin_sign_exp_sign (β h : ℝ) :
    ∑ s : Spin, Spin.sign ℝ s * Real.exp (β * h * Spin.sign ℝ s)
      = 2 * Real.sinh (β * h) := by
  rw [sum_spin]
  have hup : Spin.sign ℝ Spin.up = (1 : ℝ) := by
    simp [Spin.sign, Spin.toSign]
  have hdown : Spin.sign ℝ Spin.down = (-1 : ℝ) := by
    simp [Spin.sign, Spin.toSign]
  rw [hup, hdown]
  simp only [one_mul, neg_mul, mul_one, mul_neg_one, Real.sinh_eq]
  ring

/-- **Partition function on the empty graph**: at `G = ⊥`,
`Z = (2 · cosh(β·h))^|ι|`.

Proof: use `hamiltonian_bot` to drop the `J`-term, rewrite the exponential
of a sum as a product of exponentials, then apply the finite-distributivity
`Finset.sum_prod_piFinset` (equivalent to
`∑_σ ∏_i f(σ i) = ∏_i ∑_s f(s)` when `σ : ι → Spin`), and finally evaluate
the single-site sum via `sum_exp_spin_sign`. -/
theorem partitionFunction_bot (p : IsingParams ℝ) :
    partitionFunction (⊥ : SimpleGraph ι) p
      = (2 * Real.cosh (p.β * p.h)) ^ Fintype.card ι := by
  unfold partitionFunction boltzmannWeight
  have hprod : ∀ σ : Config ι,
      Real.exp (-p.β * hamiltonian (⊥ : SimpleGraph ι) p σ)
        = ∏ i : ι, Real.exp (p.β * p.h * Spin.sign ℝ (σ i)) := by
    intro σ
    rw [hamiltonian_bot]
    have hsum : -p.β * (-p.h * ∑ i : ι, Spin.sign ℝ (σ i))
        = ∑ i : ι, p.β * p.h * Spin.sign ℝ (σ i) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [hsum, Real.exp_sum]
  calc ∑ σ : Config ι,
        Real.exp (-p.β * hamiltonian (⊥ : SimpleGraph ι) p σ)
      = ∑ σ : Config ι, ∏ i : ι,
          Real.exp (p.β * p.h * Spin.sign ℝ (σ i)) := by
        refine Finset.sum_congr rfl ?_
        intros σ _; exact hprod σ
    _ = ∑ σ ∈ Fintype.piFinset (fun _ : ι => (Finset.univ : Finset Spin)),
          ∏ i : ι, Real.exp (p.β * p.h * Spin.sign ℝ (σ i)) := by
        rw [Fintype.piFinset_univ]
    _ = ∏ i : ι, ∑ s : Spin, Real.exp (p.β * p.h * Spin.sign ℝ s) :=
        Finset.sum_prod_piFinset (Finset.univ : Finset Spin)
          (fun _ s => Real.exp (p.β * p.h * Spin.sign ℝ s))
    _ = ∏ _ : ι, 2 * Real.cosh (p.β * p.h) := by
        refine Finset.prod_congr rfl ?_
        intros i _; exact sum_exp_spin_sign p.β p.h
    _ = (2 * Real.cosh (p.β * p.h)) ^ Fintype.card ι := by
        rw [Finset.prod_const, Finset.card_univ]

/-- **Graph-independent identity at `J = 0`**:
`Z_G ⟨0, h, β⟩ = Z_⊥ ⟨0, h, β⟩` for any ambient graph `G`.

Core lemma for the J=0 closed-form chain: every downstream result
(`partitionFunction_J_zero`, `freeEnergy_J_zero`, along-exhaustion
and ∞-vol lifts) reduces to the corresponding `⊥`-graph result via
this identity. Directly via `hamiltonian_J_zero_eq_bot` pointwise. -/
theorem partitionFunction_eq_bot_at_J_zero (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h β : ℝ) :
    partitionFunction G (⟨0, h, β⟩ : IsingParams ℝ)
      = partitionFunction (⊥ : SimpleGraph ι) (⟨0, h, β⟩ : IsingParams ℝ) := by
  unfold partitionFunction boltzmannWeight
  refine Finset.sum_congr rfl ?_
  intro σ _
  rw [hamiltonian_eq_bot_at_J_zero]

/-- **Partition function at `J = 0`** (graph-independent):
`Z_G ⟨0, h, β⟩ = (2 · cosh(β·h))^|ι|` for any ambient graph `G`.

Combines `partitionFunction_eq_bot_at_J_zero` (graph independence)
with `partitionFunction_bot` (`⊥` closed form). -/
theorem partitionFunction_J_zero (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h β : ℝ) :
    partitionFunction G (⟨0, h, β⟩ : IsingParams ℝ)
      = (2 * Real.cosh (β * h)) ^ Fintype.card ι :=
  (partitionFunction_eq_bot_at_J_zero G h β).trans (partitionFunction_bot _)

/-- **Correlation at `J = 0` is graph-independent**:
`⟨σ^A⟩_{G, ⟨0,h,β⟩} = ⟨σ^A⟩_{⊥, ⟨0,h,β⟩}` for any ambient graph `G`.

Extends the `_eq_bot_at_J_zero` identity chain
(`hamiltonian_eq_bot_at_J_zero`, `partitionFunction_eq_bot_at_J_zero`,
`freeEnergy_eq_bot_at_J_zero`) to the correlation layer. Both the
Boltzmann weight in the numerator and the partition function in the
denominator are graph-independent at `J = 0`, so the ratio is. -/
theorem correlation_eq_bot_at_J_zero (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h β : ℝ) (A : Finset ι) :
    correlation G (⟨0, h, β⟩ : IsingParams ℝ) A
      = correlation (⊥ : SimpleGraph ι) (⟨0, h, β⟩ : IsingParams ℝ) A := by
  unfold correlation gibbsExpectation boltzmannWeight
  rw [partitionFunction_eq_bot_at_J_zero]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro σ _
  rw [hamiltonian_eq_bot_at_J_zero]

/-- **Correlation function on the empty graph** (closed form):
`⟨σ^A⟩_⊥ = tanh(β·h)^|A|` for any subset `A`.

Proof: at `G = ⊥` the Boltzmann weight factorises by site into
`∏ i, exp(β·h · sign(σ_i))` (`hamiltonian_bot`). The spin product
`∏_{i∈A} sign(σ_i)` becomes `∏_{i∈ι} (if i ∈ A then sign(σ_i) else 1)`
by `Finset.prod_filter` on `univ.filter (· ∈ A) = A`. The combined
per-site integrand has sum `2·sinh(β·h)` (if `i ∈ A`,
`sum_spin_sign_exp_sign`) or `2·cosh(β·h)` (else, `sum_exp_spin_sign`).
`Fintype.sum_prod_piFinset` swaps `∑_σ ∏_i` to `∏_i ∑_s`, and dividing
by `Z_⊥ = (2·cosh(β·h))^|ι|` (`partitionFunction_bot`) gives
`∏_{i∈ι} (if i ∈ A then tanh(β·h) else 1) = tanh(β·h)^|A|`. -/
theorem correlation_bot_closed (p : IsingParams ℝ) (A : Finset ι) :
    correlation (⊥ : SimpleGraph ι) p A = Real.tanh (p.β * p.h) ^ A.card := by
  have hcosh_pos : (0 : ℝ) < Real.cosh (p.β * p.h) := Real.cosh_pos _
  have h2cosh_pos : (0 : ℝ) < 2 * Real.cosh (p.β * p.h) := by linarith
  have h2cosh_ne : (2 * Real.cosh (p.β * p.h)) ≠ 0 := h2cosh_pos.ne'
  -- Boltzmann weight at ⊥ factorises over sites
  have hw : ∀ σ : Config ι,
      boltzmannWeight (⊥ : SimpleGraph ι) p σ
        = ∏ i : ι, Real.exp (p.β * p.h * Spin.sign ℝ (σ i)) := by
    intro σ
    unfold boltzmannWeight
    rw [hamiltonian_bot]
    have hsum : -p.β * (-p.h * ∑ i : ι, Spin.sign ℝ (σ i))
        = ∑ i : ι, p.β * p.h * Spin.sign ℝ (σ i) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_; ring
    rw [hsum, Real.exp_sum]
  -- spinProduct A factorises over univ with an indicator
  have hsp : ∀ σ : Config ι,
      spinProduct A σ
        = ∏ i : ι, if i ∈ A then Spin.sign ℝ (σ i) else (1 : ℝ) := by
    intro σ
    change (∏ i ∈ A, (↑(σ i).toSign : ℝ)) = _
    have hA : A = (Finset.univ : Finset ι).filter (· ∈ A) := by ext; simp
    conv_lhs => rw [hA]
    rw [Finset.prod_filter]
    refine Finset.prod_congr rfl ?_
    intro i _
    rfl
  -- per-configuration integrand = ∏ i, g i (σ i)
  have hint : ∀ σ : Config ι,
      spinProduct A σ * boltzmannWeight (⊥ : SimpleGraph ι) p σ
        = ∏ i : ι,
            (if i ∈ A then Spin.sign ℝ (σ i) else 1)
              * Real.exp (p.β * p.h * Spin.sign ℝ (σ i)) := by
    intro σ
    rw [hsp σ, hw σ, ← Finset.prod_mul_distrib]
  -- numerator: ∑_σ ∏_i (…) = ∏_i ∑_s (…) by Fintype.sum_prod_piFinset
  have hnum : ∑ σ : Config ι,
        spinProduct A σ * boltzmannWeight (⊥ : SimpleGraph ι) p σ
      = ∏ i : ι, ∑ s : Spin,
          (if i ∈ A then Spin.sign ℝ s else 1)
            * Real.exp (p.β * p.h * Spin.sign ℝ s) := by
    calc ∑ σ : Config ι,
            spinProduct A σ * boltzmannWeight (⊥ : SimpleGraph ι) p σ
        = ∑ σ : Config ι, ∏ i : ι,
              (if i ∈ A then Spin.sign ℝ (σ i) else 1)
                * Real.exp (p.β * p.h * Spin.sign ℝ (σ i)) :=
              Finset.sum_congr rfl fun σ _ => hint σ
      _ = ∑ σ ∈ Fintype.piFinset fun _ : ι => (Finset.univ : Finset Spin),
              ∏ i : ι, (if i ∈ A then Spin.sign ℝ (σ i) else 1)
                * Real.exp (p.β * p.h * Spin.sign ℝ (σ i)) := by
              rw [Fintype.piFinset_univ]
      _ = ∏ i : ι, ∑ s : Spin,
              (if i ∈ A then Spin.sign ℝ s else 1)
                * Real.exp (p.β * p.h * Spin.sign ℝ s) :=
              Finset.sum_prod_piFinset (Finset.univ : Finset Spin)
                (fun i s => (if i ∈ A then Spin.sign ℝ s else 1)
                  * Real.exp (p.β * p.h * Spin.sign ℝ s))
  -- per-site sum evaluates to 2·sinh or 2·cosh
  have hsite : ∀ i : ι,
      (∑ s : Spin, (if i ∈ A then Spin.sign ℝ s else 1)
          * Real.exp (p.β * p.h * Spin.sign ℝ s))
        = if i ∈ A then 2 * Real.sinh (p.β * p.h)
                    else 2 * Real.cosh (p.β * p.h) := by
    intro i
    by_cases hi : i ∈ A
    · simp only [if_pos hi]
      simpa using sum_spin_sign_exp_sign p.β p.h
    · simp only [if_neg hi, one_mul]
      exact sum_exp_spin_sign p.β p.h
  -- assemble the correlation
  unfold correlation gibbsExpectation
  rw [hnum, partitionFunction_bot]
  rw [show (∏ i : ι, ∑ s : Spin,
            (if i ∈ A then Spin.sign ℝ s else 1)
              * Real.exp (p.β * p.h * Spin.sign ℝ s))
        = ∏ _i : ι, (if _i ∈ A
                      then 2 * Real.sinh (p.β * p.h)
                      else 2 * Real.cosh (p.β * p.h))
      from Finset.prod_congr rfl fun i _ => hsite i]
  rw [show ((2 * Real.cosh (p.β * p.h)) ^ Fintype.card ι : ℝ)⁻¹
        = ∏ _ : ι, (2 * Real.cosh (p.β * p.h))⁻¹
      from by rw [Finset.prod_const, Finset.card_univ, inv_pow]]
  rw [← Finset.prod_mul_distrib]
  rw [show (fun i : ι => (2 * Real.cosh (p.β * p.h))⁻¹
              * (if i ∈ A then 2 * Real.sinh (p.β * p.h)
                           else 2 * Real.cosh (p.β * p.h)))
        = fun i : ι => if i ∈ A then Real.tanh (p.β * p.h) else 1
      from ?_]
  · rw [← Finset.prod_filter]
    rw [show (Finset.univ : Finset ι).filter (· ∈ A) = A from by ext; simp]
    rw [Finset.prod_const]
  · funext i
    by_cases hi : i ∈ A
    · simp only [if_pos hi, Real.tanh_eq_sinh_div_cosh]
      field_simp
    · simp only [if_neg hi]
      exact inv_mul_cancel₀ h2cosh_ne

/-- **Correlation at `J = 0`** (graph-independent closed form):
`⟨σ^A⟩_{G, ⟨0, h, β⟩} = tanh(β·h)^|A|` for any ambient graph `G` and any
subset `A`.

Composition of `correlation_eq_bot_at_J_zero` (graph-independence of
correlation at `J = 0`) with `correlation_bot_closed` (`⊥`-graph closed
form). Correlation-layer counterpart to `partitionFunction_J_zero`
(`Z = (2·cosh(β·h))^|ι|`) and `freeEnergy_J_zero` (`f = log(2·cosh(β·h))`). -/
theorem correlation_J_zero (G : SimpleGraph ι) [Fintype G.edgeSet]
    (h β : ℝ) (A : Finset ι) :
    correlation G (⟨0, h, β⟩ : IsingParams ℝ) A = Real.tanh (β * h) ^ A.card :=
  (correlation_eq_bot_at_J_zero G h β A).trans (correlation_bot_closed _ A)

/-! ## h-symmetry: `Z(-h) = Z(h)` via spin flip

From `hamiltonian_neg_h` (`H(σ; -h) = H(σ.flip; h)`) and the fact that
`σ ↦ σ.flip` is an involution of `Config ι`, the partition function is
invariant under `h ↦ -h`. -/

/-- **Partition function h-symmetry**: `Z(J, -h, β) = Z(J, h, β)`.

Proof: `exp(-β · H(σ; -h)) = exp(-β · H(σ.flip; h))` (`hamiltonian_neg_h`),
then reindex the Config-sum via the self-inverse `flipEquiv`. -/
theorem partitionFunction_neg_h (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) :
    partitionFunction G (⟨J, -h, β⟩ : IsingParams ℝ)
      = partitionFunction G (⟨J, h, β⟩ : IsingParams ℝ) := by
  unfold partitionFunction boltzmannWeight
  let flipEquiv : Equiv.Perm (Config ι) :=
    ⟨Config.flip, Config.flip, Config.flip_flip, Config.flip_flip⟩
  calc ∑ σ : Config ι,
        Real.exp (-(⟨J, -h, β⟩ : IsingParams ℝ).β *
          hamiltonian G (⟨J, -h, β⟩ : IsingParams ℝ) σ)
      = ∑ σ : Config ι,
          Real.exp (-(⟨J, h, β⟩ : IsingParams ℝ).β *
            hamiltonian G (⟨J, h, β⟩ : IsingParams ℝ) σ.flip) := by
        refine Finset.sum_congr rfl ?_
        intros σ _
        rw [hamiltonian_neg_h]
    _ = ∑ σ : Config ι,
          Real.exp (-(⟨J, h, β⟩ : IsingParams ℝ).β *
            hamiltonian G (⟨J, h, β⟩ : IsingParams ℝ) σ) :=
        (Fintype.sum_equiv flipEquiv _ _
          (fun σ => by dsimp [flipEquiv]; simp [Config.flip_flip])).symm

end IsingModel
