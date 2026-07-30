import IsingModel.Conditioning.HighTempClosed.ClosedForm

/-!
# Field-dependent high-temperature closed form (GJ §17.6.1, first brick)

The field-dependent finite-volume high-temperature (Mayer) closed form of the
Ising partition function, generalizing the zero-field closed form
`partitionFunction_high_temp_expansion_h_zero_closed`
(Friedli–Velenik §3.7.3, eq. (3.45)) by replacing the single-site factor `2`
by the field-dependent single-site factor `2·cosh(βh)` on even `X`-degree and
`2·sinh(βh)` on odd `X`-degree. This is a purely finite combinatorial identity;
no cluster-expansion / Kotecky–Preiss machinery and no new analytic input are
used. It is the first brick of the on-book programme toward GJ Theorem 17.6.1
(`∂/∂h` differentiability / `h`-analyticity of the two-point function in the
high-temperature window); see the design note
`design-gj-17.6.1-field-cluster-firstbrick.md`.

References: Friedli–Velenik §3.7.3, eq. (3.45), p. 117, gives the `h = 0`
template. Exercise 5.8, p. 238, and its solution in Appendix C, p. 531, give
the exact general-field high-temperature weight used here.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Single-site field lemmas -/

/-- **Single-spin field sum**: for real `a` and `k : ℕ`,
`∑_{s : Spin} (s.toSign)^k · exp(a·s.toSign) = 2·cosh a` if `k` is even and
`= 2·sinh a` if `k` is odd. The field-dependent replacement of
`sum_toSign_pow_real` (which reads `∑_s (s.toSign)^k = 2` on even `k`, `0`
on odd `k`); the two agree at `a = 0` since `cosh 0 = 1`, `sinh 0 = 0`.

Indeed `∑_{s=±1} s^k e^{a s} = e^a + (-1)^k e^{-a}`, equal to `2·cosh a` when
`k` is even and `2·sinh a` when `k` is odd. -/
private theorem sum_toSign_pow_field (a : ℝ) (k : ℕ) :
    (∑ s : Spin, ((s.toSign : ℝ)) ^ k * Real.exp (a * ((s.toSign : ℝ))))
      = 2 * (if Even k then Real.cosh a else Real.sinh a) := by
  have hu : (Finset.univ : Finset Spin) = {Spin.up, Spin.down} := by decide
  rw [hu, Finset.sum_pair (by decide : Spin.up ≠ Spin.down)]
  have hup : ((Spin.up.toSign : ℤ) : ℝ) = 1 := by simp [Spin.toSign]
  have hdown : ((Spin.down.toSign : ℤ) : ℝ) = -1 := by simp [Spin.toSign]
  rw [hup, hdown, one_pow, mul_one, mul_neg_one]
  by_cases hk : Even k
  · rw [if_pos hk, hk.neg_one_pow, Real.cosh_eq]; ring
  · rw [if_neg hk]
    rw [Nat.not_even_iff_odd] at hk
    rw [hk.neg_one_pow, Real.sinh_eq]; ring

/-- **Per-vertex field Fubini**: for real `a` and `k : ι → ℕ`,
\[
\sum_{\sigma}\prod_{v}(\sigma_v)^{k(v)}e^{a\sigma_v}
  =2^{|\iota|}\cosh(a)^{|\iota|}\tanh(a)^{\#\{v:\ k(v)\ \mathrm{odd}\}}.
\]
Per-vertex Fubini (`Fintype.prod_sum`) reduces the configuration sum to a
product of single-site sums, each evaluated by `sum_toSign_pow_field`; the
even/odd split uses `sinh a = cosh a · tanh a` (valid unconditionally since
`cosh a > 0`) so that `cosh^{#even}·sinh^{#odd} = cosh^{|ι|}·tanh^{#odd}`.
The field-dependent replacement of `sum_prod_toSign_pow_real`. -/
theorem sum_prod_toSign_pow_field (a : ℝ) (k : ι → ℕ) :
    (∑ σ : Config ι,
        ∏ v : ι, ((σ v).toSign : ℝ) ^ (k v) * Real.exp (a * ((σ v).toSign : ℝ)))
      = (2 : ℝ) ^ Fintype.card ι * Real.cosh a ^ Fintype.card ι *
          Real.tanh a ^ (Finset.univ.filter (fun v => Odd (k v))).card := by
  have hfubini :
      (∑ σ : Config ι,
          ∏ v : ι, ((σ v).toSign : ℝ) ^ (k v) * Real.exp (a * ((σ v).toSign : ℝ)))
        = ∏ v : ι, ∑ s : Spin,
            ((s.toSign : ℝ)) ^ (k v) * Real.exp (a * ((s.toSign : ℝ))) :=
    (Fintype.prod_sum (κ := fun _ => Spin)
      (fun v s => ((s.toSign : ℝ)) ^ (k v) * Real.exp (a * ((s.toSign : ℝ))))).symm
  have hsinh : Real.sinh a = Real.cosh a * Real.tanh a := by
    rw [Real.tanh_eq_sinh_div_cosh]; field_simp
  have hprod :
      (∏ v : ι, (if Even (k v) then Real.cosh a else Real.sinh a))
        = Real.cosh a ^ Fintype.card ι *
            Real.tanh a ^ (Finset.univ.filter (fun v => Odd (k v))).card := by
    have hstep : ∀ v : ι,
        (if Even (k v) then Real.cosh a else Real.sinh a)
          = Real.cosh a * (if Odd (k v) then Real.tanh a else 1) := by
      intro v
      by_cases hv : Even (k v)
      · rw [if_pos hv, if_neg (Nat.not_odd_iff_even.mpr hv), mul_one]
      · rw [if_neg hv, if_pos (Nat.not_even_iff_odd.mp hv), hsinh]
    rw [Finset.prod_congr rfl (fun v _ => hstep v),
        Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
    congr 1
    rw [← Finset.prod_filter, Finset.prod_const]
  rw [hfubini]
  simp_rw [sum_toSign_pow_field]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hprod]
  ring

/-! ### The field-dependent closed form -/

/-- **Field-dependent high-temperature closed form** (GJ §17.6.1 first brick):
\[
Z(G;J,h,\beta)=2^{|\iota|}\cosh(\beta J)^{|E|}\cosh(\beta h)^{|\iota|}
  \sum_{X\subseteq E}\tanh(\beta J)^{|X|}
    \tanh(\beta h)^{\,|\{v:\ \deg_X(v)\ \mathrm{odd}\}|},
\]
where `deg_X(v) = (X.filter (v ∈ ·)).card` is the `X`-degree of `v`.

Field-dependent generalization of
`partitionFunction_high_temp_expansion_h_zero_closed` (FV §3.7.3, eq. (3.45)).
Proof: start from the general-`h` subset expansion
`partitionFunction_high_temp_expansion_subset_form`; evaluate the inner
`σ`-sum in closed form via the edge-product/vertex-power bridge
`prod_edgeSpin_eq_prod_pow_filter_card`, the field exponential factorization
`exp(βh·∑_i σ_i) = ∏_v exp(βh·σ_v)`, and the per-vertex field Fubini
`sum_prod_toSign_pow_field`; then factor the `X`-independent constant
`2^{|ι|}·cosh(βh)^{|ι|}` out of the sum.

At `h = 0` this collapses to the zero-field even-subgraph closed form
(`cosh(βh) = 1`, `tanh(βh) = 0`, so `tanh(βh)^{#odd(X)} = 1` iff every vertex
has even `X`-degree). No axiom, no new analytic input.

References: Friedli–Velenik §3.7.3, eq. (3.45), p. 117, gives the `h = 0`
template. Exercise 5.8, p. 238, and its solution in Appendix C, p. 531, give
the exact general-field high-temperature weight. -/
theorem partitionFunction_high_temp_expansion_field_closed
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h β : ℝ) :
    partitionFunction G ⟨J, h, β⟩ =
      (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card *
        Real.cosh (β * h) ^ Fintype.card ι *
      ∑ X ∈ G.edgeFinset.powerset,
        Real.tanh (β * J) ^ X.card *
          Real.tanh (β * h) ^
            (Finset.univ.filter
              (fun v => Odd ((X.filter (v ∈ ·)).card))).card := by
  -- Field exponential factorizes over vertices.
  have hexp : ∀ σ : Config ι,
      Real.exp (β * h * ∑ i : ι, Spin.sign ℝ (σ i))
        = ∏ v : ι, Real.exp (β * h * ((σ v).toSign : ℝ)) := by
    intro σ
    rw [Finset.mul_sum, Real.exp_sum]
    simp only [Spin.sign]
  -- Inner σ-sum evaluated in closed form for each edge subset `X`.
  have hS : ∀ X ∈ G.edgeFinset.powerset,
      (∑ σ : Config ι, (∏ e ∈ X, edgeSpin (K := ℝ) σ e) *
          Real.exp (β * h * ∑ i : ι, Spin.sign ℝ (σ i)))
        = (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * h) ^ Fintype.card ι *
            Real.tanh (β * h) ^
              (Finset.univ.filter
                (fun v => Odd ((X.filter (v ∈ ·)).card))).card := by
    intro X hX
    have hcombine : ∀ σ : Config ι,
        (∏ v : ι, ((σ v).toSign : ℝ) ^ ((X.filter (v ∈ ·)).card)) *
          (∏ v : ι, Real.exp (β * h * ((σ v).toSign : ℝ)))
          = ∏ v : ι, (((σ v).toSign : ℝ) ^ ((X.filter (v ∈ ·)).card)
              * Real.exp (β * h * ((σ v).toSign : ℝ))) := fun _ =>
      (Finset.prod_mul_distrib).symm
    simp_rw [prod_edgeSpin_eq_prod_pow_filter_card G X (Finset.mem_powerset.mp hX),
      hexp, hcombine]
    exact sum_prod_toSign_pow_field (β * h)
      (fun v => (X.filter (v ∈ ·)).card)
  rw [partitionFunction_high_temp_expansion_subset_form G ⟨J, h, β⟩]
  change Real.cosh (β * J) ^ G.edgeFinset.card *
      ∑ X ∈ G.edgeFinset.powerset,
        Real.tanh (β * J) ^ X.card *
          ∑ σ : Config ι, (∏ e ∈ X, edgeSpin (K := ℝ) σ e) *
            Real.exp (β * h * ∑ i : ι, Spin.sign ℝ (σ i))
        = _
  rw [Finset.sum_congr rfl (fun X hX => by rw [hS X hX])]
  -- Factor the `X`-independent constant `2^{|ι|}·cosh(βh)^{|ι|}` out of the sum.
  have hreorg : ∀ X : Finset (Sym2 ι),
      Real.tanh (β * J) ^ X.card *
          ((2 : ℝ) ^ Fintype.card ι * Real.cosh (β * h) ^ Fintype.card ι *
            Real.tanh (β * h) ^ (Finset.univ.filter
              (fun v => Odd ((X.filter (v ∈ ·)).card))).card)
        = (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * h) ^ Fintype.card ι *
            (Real.tanh (β * J) ^ X.card *
              Real.tanh (β * h) ^ (Finset.univ.filter
                (fun v => Odd ((X.filter (v ∈ ·)).card))).card) := fun _ => by ring
  simp_rw [hreorg]
  rw [← Finset.mul_sum]
  ring

end IsingModel
