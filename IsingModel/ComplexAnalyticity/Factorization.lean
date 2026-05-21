import IsingModel.ComplexAnalyticity.Normalization

/-!
# Friedli-Velenik Factorization

This module is part of the split `IsingModel.ComplexAnalyticity` development.
-/

namespace IsingModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped Complex

/-- Per-site factorisation of the external-field exponential.
For `σ : Config ι` with down-spin set `X = configToFinset σ`, at each site `i`:
`exp(β·h·σ_i) = exp(β·h) · (i ∈ X ? leeYangFugacity β h : 1)`.

Case split on `σ i`: if `σ i = up` (so `i ∉ X`) then `σ_i = 1` and
the RHS is `exp(β·h)·1 = exp(β·h)`; if `σ i = down` (so `i ∈ X`) then
`σ_i = -1` and the RHS is `exp(β·h) · exp(-2β·h) = exp(-β·h)`. -/
theorem exp_beta_h_sign_eq (β : ℝ) (h : ℂ) (σ : Config ι) (i : ι) :
    Complex.exp ((β : ℂ) * h * Spin.sign ℂ (σ i))
      = Complex.exp ((β : ℂ) * h)
          * (if i ∈ configToFinset σ then
              leeYangFugacity (β : ℂ) h else 1) := by
  unfold leeYangFugacity configToFinset
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  cases hσ : σ i with
  | up =>
    simp only [Spin.sign, Spin.toSign, Int.cast_one, mul_one]
    rw [if_neg (by simp), mul_one]
  | down =>
    simp only [Spin.sign, Spin.toSign, Int.cast_neg, Int.cast_one]
    rw [if_pos (by simp)]
    rw [mul_neg_one, ← Complex.exp_add]
    congr 1; ring

/-- Per-edge factorisation of the interaction exponential.
For `σ : Config ι` with down-spin set `X = configToFinset σ`, at each
pair `(i, j)` with `i ≠ j`:
`exp(β·J·σ_i·σ_j) = exp(β·J) · edgeWeight i j (exp(-2βJ)) X`.

Case split on whether `(σ i = σ j)` (equivalently `(i∈X) = (j∈X)`). -/
theorem exp_beta_J_sign_mul_sign_eq
    (β J : ℝ) (σ : Config ι) (i j : ι) :
    Complex.exp ((β : ℂ) * (J : ℂ)
        * (Spin.sign ℂ (σ i) * Spin.sign ℂ (σ j)))
      = Complex.exp ((β : ℂ) * (J : ℂ))
          * edgeWeight i j (Real.exp (-2 * β * J)) (configToFinset σ) := by
  unfold edgeWeight configToFinset
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  cases hi : σ i with
  | up =>
    cases hj : σ j with
    | up =>
      simp [Spin.sign, Spin.toSign]
    | down =>
      rw [if_neg (by simp)]
      rw [show ((Real.exp (-2 * β * J)) : ℂ)
            = Complex.exp ((-2 * β * J : ℝ) : ℂ) from
        Complex.ofReal_exp _, ← Complex.exp_add]
      simp only [Spin.sign, Spin.toSign, Int.cast_one, Int.cast_neg,
        mul_neg_one]
      congr 1; push_cast; ring
  | down =>
    cases hj : σ j with
    | up =>
      rw [if_neg (by simp)]
      rw [show ((Real.exp (-2 * β * J)) : ℂ)
            = Complex.exp ((-2 * β * J : ℝ) : ℂ) from
        Complex.ofReal_exp _, ← Complex.exp_add]
      simp only [Spin.sign, Spin.toSign, Int.cast_neg, Int.cast_one,
        neg_mul, one_mul, mul_neg]
      congr 1; push_cast; ring
    | down =>
      simp only [Spin.sign, Spin.toSign, Int.cast_neg, Int.cast_one,
        neg_mul_neg, one_mul]
      rw [if_pos (by simp)]; ring_nf

omit [DecidableEq ι] in
/-- Product over sites of the external-field exponential factorises as
`exp(β·h·|ι|) · z^|X|` where `X = configToFinset σ` and `z = leeYangFugacity β h`. -/
theorem prod_exp_beta_h_sign_eq
    (β : ℝ) (h : ℂ) (σ : Config ι) :
    ∏ i : ι, Complex.exp ((β : ℂ) * h * Spin.sign ℂ (σ i))
      = Complex.exp ((β : ℂ) * h * (Fintype.card ι : ℂ))
          * ∏ _i ∈ configToFinset σ, leeYangFugacity (β : ℂ) h := by
  classical
  rw [show (∏ i : ι, Complex.exp ((β : ℂ) * h * Spin.sign ℂ (σ i)))
          = ∏ i : ι, (Complex.exp ((β : ℂ) * h)
              * (if i ∈ configToFinset σ then
                  leeYangFugacity (β : ℂ) h else 1))
          from Finset.prod_congr rfl fun i _ => exp_beta_h_sign_eq β h σ i]
  rw [Finset.prod_mul_distrib, Finset.prod_const,
    Finset.prod_ite_mem, Finset.univ_inter,
    Finset.card_univ, ← Complex.exp_nat_mul, Finset.prod_const]
  ring_nf

omit [Fintype ι] [DecidableEq ι] in
/-- `edgeSpinComplex` evaluated at the canonical representative
`s((Quot.out e).1, (Quot.out e).2) = e`. -/
theorem edgeSpinComplex_eq_quotOut (σ : Config ι) (e : Sym2 ι) :
    edgeSpinComplex σ e
      = Spin.sign ℂ (σ (Quot.out e).1) * Spin.sign ℂ (σ (Quot.out e).2) := by
  conv_lhs => rw [show e = s((Quot.out e).1, (Quot.out e).2) from by
    conv_lhs => rw [← Quot.out_eq e]]
  rfl

/-- Product over edges of the interaction exponential factorises as
`exp(β·J·|E|) · ∏_e edgeWeight (Quot.out e).1 (Quot.out e).2 t X`
where `X = configToFinset σ` and `t = exp(-2βJ)`. -/
theorem prod_exp_beta_J_edgeSpin_eq
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (β J : ℝ) (σ : Config ι) :
    ∏ e ∈ G.edgeFinset,
        Complex.exp ((β : ℂ) * (J : ℂ) * edgeSpinComplex σ e)
      = Complex.exp ((β : ℂ) * (J : ℂ) * (G.edgeFinset.card : ℂ))
          * ∏ e ∈ G.edgeFinset, edgeWeight (Quot.out e).1 (Quot.out e).2
              (Real.exp (-2 * β * J)) (configToFinset σ) := by
  rw [show (∏ e ∈ G.edgeFinset,
            Complex.exp ((β : ℂ) * (J : ℂ) * edgeSpinComplex σ e))
          = ∏ e ∈ G.edgeFinset, (Complex.exp ((β : ℂ) * (J : ℂ))
              * edgeWeight (Quot.out e).1 (Quot.out e).2
                  (Real.exp (-2 * β * J)) (configToFinset σ))
          from Finset.prod_congr rfl fun e _ => by
        rw [edgeSpinComplex_eq_quotOut σ e,
          exp_beta_J_sign_mul_sign_eq β J σ (Quot.out e).1 (Quot.out e).2]]
  rw [Finset.prod_mul_distrib, Finset.prod_const,
    ← Complex.exp_nat_mul]
  ring_nf

/-- The Lee-Yang polynomial value at the down-spin set of `σ` equals the
product over edges `e ∈ G.edgeFinset` of `edgeWeight` at the canonical
representative of `e`. -/
theorem isingEdgePoly_apply_configToFinset
    (G : SimpleGraph ι) [Fintype G.edgeSet] (t : ℝ) (σ : Config ι) :
    isingEdgePoly (graphToEdgeList G t) (configToFinset σ)
      = ∏ e ∈ G.edgeFinset, edgeWeight (Quot.out e).1 (Quot.out e).2 t
          (configToFinset σ) := by
  unfold isingEdgePoly graphToEdgeList
  rw [List.map_map]
  exact Finset.prod_map_toList G.edgeFinset _

/-- Per-configuration factorisation of the complex Boltzmann weight.
For real coupling `J`, real inverse temperature `β`, and complex field `h`:
`exp(-β · H(σ; J, h))
  = leeYangNormalization β J h |E| |ι|
    · isingEdgePoly (graphToEdgeList G t) X
    · ∏_{i∈X} leeYangFugacityVec β h i`
where `X = configToFinset σ` and `t = exp(-2βJ)`. -/
theorem exp_neg_beta_hamiltonian_eq
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (β J : ℝ) (h : ℂ) (σ : Config ι) :
    Complex.exp (-(β : ℂ) * hamiltonianComplex G (J : ℂ) h σ)
      = leeYangNormalization (β : ℂ) (J : ℂ) h
          G.edgeFinset.card (Fintype.card ι)
        * isingEdgePoly (graphToEdgeList G (Real.exp (-2 * β * J)))
            (configToFinset σ)
        * ∏ i ∈ configToFinset σ, leeYangFugacityVec (β : ℂ) h i := by
  unfold hamiltonianComplex interactionEnergyComplex externalFieldEnergyComplex
    leeYangNormalization leeYangFugacityVec
  rw [show -(β : ℂ) * (-(J : ℂ) * ∑ e ∈ G.edgeFinset, edgeSpinComplex σ e
            + -h * ∑ i : ι, Spin.sign ℂ (σ i))
          = (β : ℂ) * (J : ℂ) * ∑ e ∈ G.edgeFinset, edgeSpinComplex σ e
              + (β : ℂ) * h * ∑ i : ι, Spin.sign ℂ (σ i) from by ring]
  rw [Complex.exp_add]
  rw [Finset.mul_sum G.edgeFinset (fun e => edgeSpinComplex σ e)
        ((β : ℂ) * (J : ℂ)),
      Finset.mul_sum Finset.univ (fun i => Spin.sign ℂ (σ i))
        ((β : ℂ) * h)]
  rw [Complex.exp_sum, Complex.exp_sum]
  rw [prod_exp_beta_J_edgeSpin_eq G β J σ]
  rw [prod_exp_beta_h_sign_eq β h σ]
  rw [isingEdgePoly_apply_configToFinset G (Real.exp (-2 * β * J)) σ]
  rw [Finset.prod_const]
  rw [show Complex.exp ((β : ℂ) * (J : ℂ) * (G.edgeFinset.card : ℂ) +
              (β : ℂ) * h * (Fintype.card ι : ℂ))
          = Complex.exp ((β : ℂ) * (J : ℂ) * (G.edgeFinset.card : ℂ))
              * Complex.exp ((β : ℂ) * h * (Fintype.card ι : ℂ))
          from Complex.exp_add _ _]
  ring

/-! ### Friedli–Velenik factorisation of the partition function

The Friedli–Velenik identity (Friedli–Velenik, *Statistical Mechanics of
Lattice Systems*, (3.63)–(3.65), pp. 122–123; Glimm–Jaffe,
*Quantum Physics*, §4.6, pp. 67–68):
`Z(J, h, β) = exp(βJ|E| + βh|ι|) · P_E(z)`
with `z_i = e^{-2βh}` (uniform field), `t_e = e^{-2βJ}` (uniform coupling).

On the Lee-Yang domain the RHS is a product of a non-vanishing normalisation
and a non-vanishing polynomial evaluation (cf.
`leeYangNormalization_mul_isingEdgePoly_eval_ne_zero` above), hence `Z ≠ 0`.
The identity itself is scaffolded here and proved step by step in a
forthcoming commit. -/

/-- **Friedli–Velenik factorisation** of the complex partition function
at real ferromagnetic coupling `J > 0`, real inverse temperature `β > 0`,
uniform external field `h ∈ ℂ`:
`Z(J, h, β) = exp(βJ|E| + βh|ι|) · P_E(z)` where `z_k = e^{-2βh}` and
`P_E` is the Ising partition polynomial associated to `G` with uniform
coupling `t = e^{-2βJ}`.

Reference: Friedli–Velenik (3.63)–(3.65), pp. 122–123;
Glimm–Jaffe Thm 4.6.2, p. 68. -/
theorem partitionFunctionComplex_eq_normalization_mul_isingEdgePoly
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (β J : ℝ) (h : ℂ) :
    partitionFunctionComplex G (J : ℂ) h (β : ℂ)
      = leeYangNormalization (β : ℂ) (J : ℂ) h
          G.edgeFinset.card (Fintype.card ι)
        * (isingEdgePoly (graphToEdgeList G (Real.exp (-2 * β * J)))).eval
            (leeYangFugacityVec (β : ℂ) h) := by
  unfold partitionFunctionComplex MultilinPoly.eval
  have hterm : ∀ σ : Config ι,
      Complex.exp (-(β : ℂ) * hamiltonianComplex G (J : ℂ) h σ)
        = leeYangNormalization (β : ℂ) (J : ℂ) h
            G.edgeFinset.card (Fintype.card ι)
          * (isingEdgePoly (graphToEdgeList G (Real.exp (-2 * β * J)))
              (configToFinset σ)
            * ∏ i ∈ configToFinset σ, leeYangFugacityVec (β : ℂ) h i) := by
    intro σ
    rw [exp_neg_beta_hamiltonian_eq G β J h σ]; ring
  rw [Finset.sum_congr rfl (fun σ _ => hterm σ)]
  rw [← Finset.mul_sum]
  congr 1
  exact Fintype.sum_equiv configFinsetEquiv
    (fun σ => isingEdgePoly (graphToEdgeList G (Real.exp (-2 * β * J)))
        (configToFinset σ)
      * ∏ i ∈ configToFinset σ, leeYangFugacityVec (β : ℂ) h i)
    (fun X => isingEdgePoly (graphToEdgeList G (Real.exp (-2 * β * J))) X
      * ∏ i ∈ X, leeYangFugacityVec (β : ℂ) h i)
    (fun σ => by simp [configFinsetEquiv])

/-- **`partitionFunctionComplex` is non-zero on the Lee-Yang domain**
(uniform field, real ferromagnetic coupling `J > 0`, real `β > 0`).

This is the Lee-Yang nonvanishing half of Glimm–Jaffe Thm 4.6.2:
on `|Im h| < Re h`, the finite-volume complex partition function has no
zeros.

Nonvanishing alone is not yet sufficient for principal-branch `Complex.log`
analyticity; to combine with `freeEnergyComplex_analyticAt_h`, one further
needs `Z ∈ Complex.slitPlane`, which requires a continuous branch argument
from a real-positive basepoint (deferred to a subsequent session).

Proof: combine
`partitionFunctionComplex_eq_normalization_mul_isingEdgePoly`
(Friedli–Velenik factorisation) with
`leeYangNormalization_mul_isingEdgePoly_eval_ne_zero`. -/
theorem partitionFunctionComplex_ne_zero_on_leeYangDomain
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) {h : ℂ} (hh : h ∈ leeYangDomain) :
    partitionFunctionComplex G (J : ℂ) h (β : ℂ) ≠ 0 := by
  rw [partitionFunctionComplex_eq_normalization_mul_isingEdgePoly G β J h]
  set t : ℝ := Real.exp (-2 * β * J)
  have ht₀ : 0 ≤ t := (Real.exp_pos _).le
  have ht₁ : t < 1 := by
    refine Real.exp_lt_one_iff.mpr ?_
    have : 0 < 2 * β * J := by positivity
    linarith
  exact leeYangNormalization_mul_isingEdgePoly_eval_ne_zero
    G ht₀ ht₁ (J : ℂ) hβ hh _ _

/-- **`freeEnergyComplex` is analytic in `h` at real parameters**
(real-slice corollary; preliminary to GJ Thm 4.6.2).

For arbitrary real `J, h₀, β`, the complex free energy is analytic in `h`
at `(h₀ : ℂ)`. This combines
`partitionFunctionComplex_mem_slitPlane_of_real` (Z is a positive real
number at real parameters, hence in slitPlane) with
`freeEnergyComplex_analyticAt_h` (analyticity given slitPlane membership).
There is no Lee-Yang-domain argument and no ferromagnetic hypothesis
here; this is just a real-slice slitPlane corollary, not GJ Thm 4.6.2
itself. Extending to the full complex Lee-Yang domain `|Im h| < Re h`
requires a continuous branch selection (deferred). -/
theorem freeEnergyComplex_analyticAt_h_ofReal
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h₀ β : ℝ) :
    AnalyticAt ℂ (fun h => freeEnergyComplex G (J : ℂ) h (β : ℂ))
        (h₀ : ℂ) :=
  freeEnergyComplex_analyticAt_h G (J : ℂ) (β : ℂ) (h₀ : ℂ)
    (partitionFunctionComplex_mem_slitPlane_of_real G ⟨J, h₀, β⟩)


end IsingModel
