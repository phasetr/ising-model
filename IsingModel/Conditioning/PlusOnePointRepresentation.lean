import IsingModel.Conditioning.PlusHighTempRepresentation

/-!
# `+`-boundary high-temperature one-point representation (FV §3.7.3, eqs. 3.46–3.47)

The high-temperature (random-graph) representation of the `+`-boundary spin-product
expectation `⟨σ_A⟩⁺_Λ`, towards the high-temperature vanishing `m*(β)=0` (Issue #3613).

The numerator of `⟨σ_A⟩⁺` carries an extra spin-product factor `σ^A`, which shifts the
parity at the vertices of `A`: the relevant subgraphs `X` are those with **even** degree
at every interior vertex `v ∈ Λ \ A` and **odd** degree at every `v ∈ A ∩ Λ` (the set
`E⁺;0` of FV (3.46) for `A = {0}`).

* `spinProduct_eq_prod_pow` — `σ^A = ∏_v (σ_v)^{[v∈A]}`.
* `spinProduct_mul_prod_edgeSpin_eq_prod_pow` — the combined vertex-power form.
* `numeratorBC_plus_spinProduct_h_zero_closed` — the numerator representation (FV (3.46)).
* `gibbsExpectationBC_plus_spinProduct_h_zero_ratio` — `⟨σ_A⟩⁺` as the ratio of
  even/`A`-shifted even-subgraph sums (FV (3.46)).

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.3, eqs. (3.46)–(3.47), pp. 116–117.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Spin product as a vertex-power product**: `σ^A = ∏_v (σ_v)^{[v∈A]}`, the indicator
exponent being `1` on `A` and `0` elsewhere. -/
theorem spinProduct_eq_prod_pow (A : Finset ι) (σ : Config ι) :
    spinProduct A σ = ∏ v : ι, ((σ v).toSign : ℝ) ^ (if v ∈ A then 1 else 0) := by
  classical
  have h : ∀ v : ι, ((σ v).toSign : ℝ) ^ (if v ∈ A then 1 else 0)
      = if v ∈ A then ((σ v).toSign : ℝ) else 1 := by
    intro v; by_cases hv : v ∈ A <;> simp [hv]
  rw [spinProduct]
  simp_rw [h]
  rw [Finset.prod_ite_mem_eq]

/-- **Combined spin-product / edge-product vertex-power form**: for `X ⊆ E`,
`σ^A · ∏_{e∈X} σ_iσ_j = ∏_v (σ_v)^{[v∈A] + deg_X(v)}`, the exponent at `v` being the
`A`-shifted `X`-degree. -/
theorem spinProduct_mul_prod_edgeSpin_eq_prod_pow (G : SimpleGraph ι) [Fintype G.edgeSet]
    (A : Finset ι) (X : Finset (Sym2 ι)) (hX : X ⊆ G.edgeFinset) (σ : Config ι) :
    spinProduct A σ * (∏ e ∈ X, edgeSpin (K := ℝ) σ e)
      = ∏ v : ι, ((σ v).toSign : ℝ) ^
          ((if v ∈ A then 1 else 0) + (X.filter (v ∈ ·)).card) := by
  rw [spinProduct_eq_prod_pow, prod_edgeSpin_eq_prod_pow_filter_card G X hX,
    ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun v _ => (pow_add _ _ _).symm)

/-- **`+`-boundary one-point numerator high-temperature representation** (FV (3.46)):
`∑_σ σ^A · w⁺_Λ(σ) = 2^{|Λ|}(cosh βJ)^{|E|}∑_{X} (tanh βJ)^{|X|}`, summed over subgraphs
`X` with `[v∈A] + deg_X(v)` even at every interior vertex `v ∈ Λ` — i.e. even degree off
`A` and odd degree on `A ∩ Λ` (the set `E⁺;0` of FV (3.46) for a singleton `A`). The
`A`-shifted analogue of `partitionFunctionBC_plus_h_zero_closed`. -/
theorem numeratorBC_plus_spinProduct_h_zero_closed (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (Λ A : Finset ι) :
    (∑ σ : Config ι, spinProduct A σ *
        boltzmannWeightBC G β (fun _ => J) 0 Λ (plusConfig ι) σ)
      = (2 : ℝ) ^ Λ.card * Real.cosh (β * J) ^ G.edgeFinset.card *
        ∑ X ∈ G.edgeFinset.powerset.filter
          (fun X => ∀ v ∈ Λ, Even ((if v ∈ A then 1 else 0) + (X.filter (v ∈ ·)).card)),
          Real.tanh (β * J) ^ X.card := by
  classical
  simp_rw [boltzmannWeightBC_plus_eq_indicator G J β Λ]
  -- expand each edge product into a subset sum, carrying the spin-product factor inside
  have hexpand : ∀ σ : Config ι,
      spinProduct A σ * Set.indicator {σ : Config ι | agreesOff Λ (plusConfig ι) σ}
        (boltzmannWeight G (⟨J, 0, β⟩ : IsingParams ℝ)) σ
        = Real.cosh (β * J) ^ G.edgeFinset.card *
          ∑ X ∈ G.edgeFinset.powerset, Real.tanh (β * J) ^ X.card *
            Set.indicator {σ : Config ι | agreesOff Λ (plusConfig ι) σ}
              (fun σ => spinProduct A σ * ∏ e ∈ X, edgeSpin (K := ℝ) σ e) σ := by
    intro σ
    by_cases hσ : agreesOff Λ (plusConfig ι) σ
    · rw [Set.indicator_of_mem hσ, boltzmannWeight_h_zero_prod G J β σ,
        Finset.prod_one_add G.edgeFinset, mul_left_comm, Finset.mul_sum]
      refine congrArg _ (Finset.sum_congr rfl (fun X _ => ?_))
      rw [Set.indicator_of_mem hσ, Finset.prod_mul_distrib, Finset.prod_const]
      ring
    · rw [Set.indicator_of_notMem hσ, mul_zero]
      refine (mul_eq_zero.mpr (Or.inr ?_)).symm
      exact Finset.sum_eq_zero (fun X _ => by
        rw [Set.indicator_of_notMem hσ, mul_zero])
  simp_rw [hexpand]
  rw [← Finset.mul_sum, Finset.sum_comm]
  -- collapse the σ-sum by the pinned-boundary parity lemma with the `A`-shifted exponent
  have hpar : ∀ X ∈ G.edgeFinset.powerset,
      (∑ σ : Config ι, Real.tanh (β * J) ^ X.card *
          Set.indicator {σ : Config ι | agreesOff Λ (plusConfig ι) σ}
            (fun σ => spinProduct A σ * ∏ e ∈ X, edgeSpin (K := ℝ) σ e) σ)
        = Real.tanh (β * J) ^ X.card *
            (if (∀ v ∈ Λ, Even ((if v ∈ A then 1 else 0) + (X.filter (v ∈ ·)).card))
              then (2 : ℝ) ^ Λ.card else 0) := by
    intro X hX
    rw [← Finset.mul_sum]
    congr 1
    rw [← sum_indicator_agreesOff_plus_prod_pow Λ
      (fun v => (if v ∈ A then 1 else 0) + (X.filter (v ∈ ·)).card)]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    by_cases hσ : agreesOff Λ (plusConfig ι) σ
    · rw [Set.indicator_of_mem hσ, Set.indicator_of_mem hσ,
        spinProduct_mul_prod_edgeSpin_eq_prod_pow G A X (Finset.mem_powerset.mp hX)]
    · rw [Set.indicator_of_notMem hσ, Set.indicator_of_notMem hσ]
  rw [Finset.sum_congr rfl hpar]
  -- redistribute `2^|Λ|` and collapse to the filtered shifted-even-on-`Λ` sum
  have hdist : ∀ X : Finset (Sym2 ι),
      Real.tanh (β * J) ^ X.card *
          (if (∀ v ∈ Λ, Even ((if v ∈ A then 1 else 0) + (X.filter (v ∈ ·)).card))
            then (2 : ℝ) ^ Λ.card else 0)
        = (if (∀ v ∈ Λ, Even ((if v ∈ A then 1 else 0) + (X.filter (v ∈ ·)).card))
            then (2 : ℝ) ^ Λ.card * Real.tanh (β * J) ^ X.card else 0) := by
    intro X
    by_cases h : ∀ v ∈ Λ, Even ((if v ∈ A then 1 else 0) + (X.filter (v ∈ ·)).card)
    · rw [if_pos h, if_pos h]; ring
    · rw [if_neg h, if_neg h]; ring
  simp_rw [hdist]
  rw [← Finset.sum_filter, ← Finset.mul_sum]
  ring

/-- **`+`-boundary one-point function high-temperature ratio** (FV (3.46)):
`⟨σ_A⟩⁺_Λ` equals the ratio of the `A`-shifted-even-subgraph sum to the even-subgraph
sum, the common factor `2^{|Λ|}(cosh βJ)^{|E|}` cancelling between numerator and
partition function:
`⟨σ_A⟩⁺_Λ = (∑_{X : A-shifted even on Λ} tanh^{|X|}) / (∑_{X : even on Λ} tanh^{|X|})`. -/
theorem gibbsExpectationBC_plus_spinProduct_h_zero_ratio (G : SimpleGraph ι)
    [Fintype G.edgeSet] (J β : ℝ) (Λ A : Finset ι) :
    gibbsExpectationBC G β (fun _ => J) 0 Λ (plusConfig ι) (spinProduct A)
      = (∑ X ∈ G.edgeFinset.powerset.filter
          (fun X => ∀ v ∈ Λ, Even ((if v ∈ A then 1 else 0) + (X.filter (v ∈ ·)).card)),
          Real.tanh (β * J) ^ X.card)
        / (∑ X ∈ G.edgeFinset.powerset.filter
          (fun X => ∀ v ∈ Λ, Even ((X.filter (v ∈ ·)).card)),
          Real.tanh (β * J) ^ X.card) := by
  unfold gibbsExpectationBC
  rw [numeratorBC_plus_spinProduct_h_zero_closed G J β Λ A,
    partitionFunctionBC_plus_h_zero_closed G J β Λ]
  have hC : (2 : ℝ) ^ Λ.card * Real.cosh (β * J) ^ G.edgeFinset.card ≠ 0 := by positivity
  rw [div_eq_inv_mul, mul_inv, mul_mul_mul_comm, inv_mul_cancel₀ hC, one_mul]

/-- **Positivity of the even-subgraph sum**: `∑_{X : even on Λ} (tanh βJ)^{|X|} > 0`,
since `Z⁺_Λ > 0` and the prefactor `2^{|Λ|}(cosh βJ)^{|E|}` is positive. The denominator
of the high-temperature one-point ratio never vanishes. -/
theorem evenSubgraphSum_pos (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℝ)
    (Λ : Finset ι) :
    0 < ∑ X ∈ G.edgeFinset.powerset.filter
        (fun X => ∀ v ∈ Λ, Even ((X.filter (v ∈ ·)).card)),
        Real.tanh (β * J) ^ X.card := by
  have hZ := partitionFunctionBC_pos G β (fun _ => J) 0 Λ (plusConfig ι)
  rw [partitionFunctionBC_plus_h_zero_closed G J β Λ] at hZ
  have hC : (0 : ℝ) < (2 : ℝ) ^ Λ.card * Real.cosh (β * J) ^ G.edgeFinset.card := by
    positivity
  exact (mul_pos_iff_of_pos_left hC).mp hZ

/-- **`+`-boundary single-spin one-point function ratio** (FV (3.46)):
`⟨σ_i⟩⁺_Λ = (∑_{X ∈ E⁺;0} tanh^{|X|}) / (∑_{X : even on Λ} tanh^{|X|})`, where the numerator
runs over subgraphs with **odd** degree at `i` and **even** degree at every other interior
vertex (the set `E⁺;0` of FV (3.46)). The singleton specialization of
`gibbsExpectationBC_plus_spinProduct_h_zero_ratio`. -/
theorem gibbsExpectationBC_plus_singleSpin_h_zero_ratio (G : SimpleGraph ι)
    [Fintype G.edgeSet] (J β : ℝ) (Λ : Finset ι) (i : ι) :
    gibbsExpectationBC G β (fun _ => J) 0 Λ (plusConfig ι) (spinProduct {i})
      = (∑ X ∈ G.edgeFinset.powerset.filter
          (fun X => ∀ v ∈ Λ, Even ((if v = i then 1 else 0) + (X.filter (v ∈ ·)).card)),
          Real.tanh (β * J) ^ X.card)
        / (∑ X ∈ G.edgeFinset.powerset.filter
          (fun X => ∀ v ∈ Λ, Even ((X.filter (v ∈ ·)).card)),
          Real.tanh (β * J) ^ X.card) := by
  rw [gibbsExpectationBC_plus_spinProduct_h_zero_ratio G J β Λ {i}]
  simp only [Finset.mem_singleton]

end IsingModel
