import IsingModel.Conditioning.HighTempExpansion

/-!
# High-Temperature Closed Forms

This module is part of the split `IsingModel.Conditioning` development.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

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
theorem sum_prod_toSign_pow_real (k : ι → ℕ) :
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
theorem prod_edgeSpin_eq_prod_pow_filter_card
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

/-- **Sharper even-subgraph sum upper bound (high-temperature)**: under
`0 ≤ β·J`,
`∑_{X ⊆ G.edgeFinset, even-deg} tanh(βJ)^|X| ≤ (1 + tanh(βJ))^|E|`.

Tightens `sum_pow_tanh_even_subgraph_le_two_pow` (Step 319): the
filter is a subset of `G.edgeFinset.powerset`, all terms are
nonnegative under `0 ≤ tanh(βJ)`, and
`∑_{X ⊆ E} tanh^|X| = ∏_e (1 + tanh) = (1 + tanh)^|E|` by
`Finset.prod_one_add` + `Finset.prod_const`. Recovers `≤ 2^|E|` since
`1 + tanh ≤ 2`. -/
theorem sum_pow_tanh_even_subgraph_le_one_plus_tanh_pow
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    (∑ X ∈ G.edgeFinset.powerset.filter
        (fun X : Finset (Sym2 ι) =>
          ∀ v : ι, Even ((X.filter (v ∈ ·)).card)),
        Real.tanh (β * J) ^ X.card)
      ≤ (1 + Real.tanh (β * J)) ^ G.edgeFinset.card := by
  classical
  have htanh_nn : 0 ≤ Real.tanh (β * J) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg
      (Real.sinh_nonneg_iff.mpr hβJ) (Real.cosh_pos _).le
  -- Step 1: rewrite (1+tanh)^|E| as ∑_{X ⊆ E} tanh^|X|.
  have hpower :
      (1 + Real.tanh (β * J)) ^ G.edgeFinset.card =
        ∑ X ∈ G.edgeFinset.powerset, Real.tanh (β * J) ^ X.card := by
    rw [← Finset.prod_const, Finset.prod_one_add]
    refine Finset.sum_congr rfl ?_
    intro X _
    rw [Finset.prod_const]
  rw [hpower]
  -- Step 2: filter ⊆ powerset, all nonneg, so filtered sum ≤ unfiltered.
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset _ _) ?_
  intro X _ _
  exact pow_nonneg htanh_nn _

/-- **High-temperature even-subgraph sum upper bound**: under `0 ≤ β J`,
`∑_{X ⊆ G.edgeFinset, even-deg} tanh(βJ)^|X| ≤ 2^|E|`.

Each `tanh(βJ)^|X| ≤ 1` (since `0 ≤ tanh(βJ) ≤ 1` under `0 ≤ βJ`),
and the filter is a subset of `G.edgeFinset.powerset` (cardinality
`2^|E|`). Hence the sum is bounded by the count of summands. -/
theorem sum_pow_tanh_even_subgraph_le_two_pow
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    (∑ X ∈ G.edgeFinset.powerset.filter
        (fun X : Finset (Sym2 ι) =>
          ∀ v : ι, Even ((X.filter (v ∈ ·)).card)),
        Real.tanh (β * J) ^ X.card)
      ≤ (2 : ℝ) ^ G.edgeFinset.card := by
  classical
  have htanh_nn : 0 ≤ Real.tanh (β * J) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg
      (Real.sinh_nonneg_iff.mpr hβJ) (Real.cosh_pos _).le
  have htanh_le_one : Real.tanh (β * J) ≤ 1 := (Real.tanh_lt_one _).le
  -- Each summand ≤ 1
  have hpow_le_one : ∀ X ∈ G.edgeFinset.powerset.filter
      (fun X : Finset (Sym2 ι) =>
        ∀ v : ι, Even ((X.filter (v ∈ ·)).card)),
      Real.tanh (β * J) ^ X.card ≤ 1 := fun X _ =>
    pow_le_one₀ htanh_nn htanh_le_one
  -- ∑ summands ≤ #(filter set) ≤ #powerset = 2^|E|
  have hbound1 : ∑ X ∈ G.edgeFinset.powerset.filter
        (fun X : Finset (Sym2 ι) =>
          ∀ v : ι, Even ((X.filter (v ∈ ·)).card)),
        Real.tanh (β * J) ^ X.card
      ≤ ((G.edgeFinset.powerset.filter
          (fun X : Finset (Sym2 ι) =>
            ∀ v : ι, Even ((X.filter (v ∈ ·)).card))).card : ℝ) :=
    Finset.sum_le_card_nsmul _ _ 1 hpow_le_one |>.trans
      (by rw [nsmul_eq_mul, mul_one])
  have hbound2 : ((G.edgeFinset.powerset.filter
        (fun X : Finset (Sym2 ι) =>
          ∀ v : ι, Even ((X.filter (v ∈ ·)).card))).card : ℝ)
      ≤ (G.edgeFinset.powerset.card : ℝ) :=
    Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _))
  have hpow_eq : (G.edgeFinset.powerset.card : ℝ) = (2 : ℝ) ^ G.edgeFinset.card := by
    rw [Finset.card_powerset]; push_cast; ring
  linarith

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

/-- **FV (3.45) closed form at `J = 0` reduces to `Z = 2^|ι|`**: a
sanity check that `partitionFunction_high_temp_expansion_h_zero_closed`
specialises consistently with `partitionFunction_J_zero` at `h = 0`.
At `J = 0`: `cosh(β·0)^|E| = 1`, the even-subgraph sum reduces to `1`
(only `X = ∅` contributes), giving `Z = 2^|ι| · 1 · 1 = 2^|ι|`. -/
theorem partitionFunction_high_temp_expansion_h_zero_closed_at_J_zero
    (G : SimpleGraph ι) [Fintype G.edgeSet] (β : ℝ) :
    partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ)
      = (2 : ℝ) ^ Fintype.card ι := by
  rw [partitionFunction_high_temp_expansion_h_zero_closed]
  rw [show (β * (0 : ℝ)) = 0 from by ring, Real.cosh_zero, Real.tanh_zero]
  rw [one_pow]
  -- After simplifications: 2^|ι| * ∑_X 0^|X| · [filter] = 2^|ι|
  -- Split the sum: only X = ∅ contributes 0^0 = 1; others 0^|X| = 0
  have hsum : ∑ X ∈ G.edgeFinset.powerset.filter
        (fun X : Finset (Sym2 ι) =>
          ∀ v : ι, Even ((X.filter (v ∈ ·)).card)),
        (0 : ℝ) ^ X.card = 1 := by
    rw [Finset.sum_eq_single (∅ : Finset (Sym2 ι))]
    · simp
    · intros X hXmem hXne
      have hpos : 0 < X.card :=
        Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hXne)
      rw [zero_pow hpos.ne']
    · intro hempty_notmem
      exfalso
      apply hempty_notmem
      refine Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset _, ?_⟩
      intro v; simp
  rw [hsum]; ring

/-- **FV (3.45) closed form at `β = 0` reduces to `Z = 2^|ι|`**: a
sanity check dual to `partitionFunction_high_temp_expansion_h_zero_closed_at_J_zero`
(Step 310). At `β = 0`: `cosh(0·J)^|E| = 1`, the even-subgraph sum
reduces to `1` (only `X = ∅` contributes via `tanh(0·J)^0 = 1`),
giving `Z = 2^|ι|`, consistent with `partitionFunction_beta_zero`. -/
theorem partitionFunction_high_temp_expansion_h_zero_closed_at_beta_zero
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J : ℝ) :
    partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ)
      = (2 : ℝ) ^ Fintype.card ι := by
  rw [partitionFunction_high_temp_expansion_h_zero_closed]
  rw [show ((0 : ℝ) * J) = 0 from by ring, Real.cosh_zero, Real.tanh_zero]
  rw [one_pow]
  -- Same calculation as Step 310: the sum of 0^|X| over even-deg X reduces to 1
  have hsum : ∑ X ∈ G.edgeFinset.powerset.filter
        (fun X : Finset (Sym2 ι) =>
          ∀ v : ι, Even ((X.filter (v ∈ ·)).card)),
        (0 : ℝ) ^ X.card = 1 := by
    rw [Finset.sum_eq_single (∅ : Finset (Sym2 ι))]
    · simp
    · intros X hXmem hXne
      have hpos : 0 < X.card :=
        Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hXne)
      rw [zero_pow hpos.ne']
    · intro hempty_notmem
      exfalso
      apply hempty_notmem
      refine Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset _, ?_⟩
      intro v; simp
  rw [hsum]; ring

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

/-- **log Z high-temperature decomposition (GJ §18.3 / FV (3.45))**:
under `0 ≤ β·J`,
`log Z(G; J, 0, β) = |ι| · log 2 + |E| · log(cosh βJ) + log(∑_{X ⊆ E, even-deg} tanh(βJ)^|X|)`.
Direct corollary of FV (3.45) closed form (Step 283) by taking
logarithms; requires the even-subgraph sum to be positive (Step 295). -/
theorem log_partitionFunction_high_temp_expansion_h_zero_closed
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    Real.log (partitionFunction G ⟨J, 0, β⟩)
      = (Fintype.card ι : ℝ) * Real.log 2
        + (G.edgeFinset.card : ℝ) * Real.log (Real.cosh (β * J))
        + Real.log
            (∑ X ∈ G.edgeFinset.powerset.filter
                (fun X : Finset (Sym2 ι) =>
                  ∀ v : ι, Even ((X.filter (v ∈ ·)).card)),
              Real.tanh (β * J) ^ X.card) := by
  rw [partitionFunction_high_temp_expansion_h_zero_closed]
  have hpref_pos : (0 : ℝ) <
      (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card :=
    mul_pos (pow_pos (by norm_num) _) (pow_pos (Real.cosh_pos _) _)
  have hsum_pos : 0 < ∑ X ∈ G.edgeFinset.powerset.filter
      (fun X : Finset (Sym2 ι) =>
        ∀ v : ι, Even ((X.filter (v ∈ ·)).card)),
      Real.tanh (β * J) ^ X.card :=
    lt_of_lt_of_le zero_lt_one (one_le_sum_pow_tanh_even_subgraph G J β hβJ)
  rw [Real.log_mul hpref_pos.ne' hsum_pos.ne']
  rw [Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow]

/-- **Sharper Z high-temperature upper bound (FV (3.45))**: under
`0 ≤ β·J`,
`Z(G; J, 0, β) ≤ 2^|ι| · exp(β·J·|E|)`.

Tighter than `partitionFunction_high_temp_expansion_h_zero_upper_bound`
(`≤ 2^(|ι|+|E|)·cosh^|E|`) at small `β·J`. Uses
`sum_pow_tanh_even_subgraph_le_one_plus_tanh_pow` (Step 392)
to bound the even-subgraph sum by `(1 + tanh(β·J))^|E|`, then collapses
`cosh^|E| · (1 + tanh)^|E| = (cosh + sinh)^|E| = exp(β·J)^|E|` via
`Real.cosh_add_sinh`. -/
theorem partitionFunction_high_temp_expansion_h_zero_upper_bound_exp
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    partitionFunction G ⟨J, 0, β⟩
      ≤ (2 : ℝ) ^ Fintype.card ι *
          Real.exp (β * J * G.edgeFinset.card) := by
  rw [partitionFunction_high_temp_expansion_h_zero_closed]
  have hsum_le := sum_pow_tanh_even_subgraph_le_one_plus_tanh_pow G J β hβJ
  have hcommon_nn :
      0 ≤ (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card :=
    mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg (Real.cosh_pos _).le _)
  have hcosh_pos : 0 < Real.cosh (β * J) := Real.cosh_pos _
  have hcosh_one_plus_tanh : Real.cosh (β * J) * (1 + Real.tanh (β * J))
      = Real.exp (β * J) := by
    have hne : Real.cosh (β * J) ≠ 0 := hcosh_pos.ne'
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp
    exact Real.cosh_add_sinh (β * J)
  calc (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card *
        ∑ X ∈ G.edgeFinset.powerset.filter
          (fun X => ∀ v : ι, Even ((X.filter (v ∈ ·)).card)),
          Real.tanh (β * J) ^ X.card
      ≤ (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card *
        (1 + Real.tanh (β * J)) ^ G.edgeFinset.card :=
        mul_le_mul_of_nonneg_left hsum_le hcommon_nn
    _ = (2 : ℝ) ^ Fintype.card ι *
          (Real.cosh (β * J) * (1 + Real.tanh (β * J))) ^ G.edgeFinset.card := by
        rw [mul_pow, mul_assoc]
    _ = (2 : ℝ) ^ Fintype.card ι * Real.exp (β * J) ^ G.edgeFinset.card := by
        rw [hcosh_one_plus_tanh]
    _ = (2 : ℝ) ^ Fintype.card ι *
          Real.exp (β * J * G.edgeFinset.card) := by
        rw [← Real.exp_nat_mul]
        ring_nf

/-- **Z high-temperature upper bound from FV (3.45)**: under `0 ≤ β·J`,
`Z(G; J, 0, β) ≤ 2^(|ι|+|E|) · (cosh(βJ))^|E|`.

Pair to `partitionFunction_high_temp_expansion_h_zero_lower_bound`
(Step 286): the FV (3.45) closed form Z = 2^|ι|·cosh^|E|·S with
`1 ≤ S ≤ 2^|E|` (Steps 295/319) gives matching bounds. -/
theorem partitionFunction_high_temp_expansion_h_zero_upper_bound
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    partitionFunction G ⟨J, 0, β⟩
      ≤ (2 : ℝ) ^ (Fintype.card ι + G.edgeFinset.card) *
        Real.cosh (β * J) ^ G.edgeFinset.card := by
  rw [partitionFunction_high_temp_expansion_h_zero_closed]
  have hsum_le := sum_pow_tanh_even_subgraph_le_two_pow G J β hβJ
  have hcommon_nn :
      0 ≤ (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card :=
    mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg (Real.cosh_pos _).le _)
  calc (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card *
        ∑ X ∈ G.edgeFinset.powerset.filter
          (fun X => ∀ v : ι, Even ((X.filter (v ∈ ·)).card)),
          Real.tanh (β * J) ^ X.card
      ≤ (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card *
        (2 : ℝ) ^ G.edgeFinset.card :=
        mul_le_mul_of_nonneg_left hsum_le hcommon_nn
    _ = (2 : ℝ) ^ (Fintype.card ι + G.edgeFinset.card) *
          Real.cosh (β * J) ^ G.edgeFinset.card := by
        rw [pow_add]; ring

/-- **Sharper log Z high-temperature upper bound (FV (3.45))**: under
`0 ≤ β·J`,
`log Z(G; J, 0, β) ≤ |ι| · log 2 + β·J·|E|`.

Direct from `partitionFunction_high_temp_expansion_h_zero_upper_bound_exp`
(Step 393) by taking logarithms. Globally tighter than the
`(|ι|+|E|) log 2 + |E| · log cosh(βJ)` form derivable from the cosh
upper bound (Step 320). -/
theorem log_partitionFunction_high_temp_expansion_h_zero_upper_bound_exp
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    Real.log (partitionFunction G ⟨J, 0, β⟩)
      ≤ (Fintype.card ι : ℝ) * Real.log 2
        + β * J * G.edgeFinset.card := by
  have hZ_ub := partitionFunction_high_temp_expansion_h_zero_upper_bound_exp
    G J β hβJ
  have hZ_pos := partitionFunction_pos G ⟨J, 0, β⟩
  have hubound_pos : (0 : ℝ) <
      (2 : ℝ) ^ Fintype.card ι * Real.exp (β * J * G.edgeFinset.card) :=
    mul_pos (pow_pos (by norm_num) _) (Real.exp_pos _)
  calc Real.log (partitionFunction G ⟨J, 0, β⟩)
      ≤ Real.log ((2 : ℝ) ^ Fintype.card ι *
            Real.exp (β * J * G.edgeFinset.card)) :=
        (Real.log_le_log_iff hZ_pos hubound_pos).mpr hZ_ub
    _ = Real.log ((2 : ℝ) ^ Fintype.card ι)
        + Real.log (Real.exp (β * J * G.edgeFinset.card)) :=
        Real.log_mul (pow_pos (by norm_num) _).ne' (Real.exp_pos _).ne'
    _ = (Fintype.card ι : ℝ) * Real.log 2
        + β * J * G.edgeFinset.card := by
        rw [Real.log_pow, Real.log_exp]

/-- **Sharper log Z high-temperature sandwich (FV (3.45))**: under
`0 ≤ β·J`,
`|ι| · log 2 + |E| · log cosh(β·J) ≤ log Z ≤ |ι| · log 2 + β·J·|E|`.

Combines `log_partitionFunction_high_temp_expansion_h_zero_closed`
(decomposition; lower part via `1 ≤ ∑ tanh^|X|`) with the sharper
exp upper bound (Step 403). -/
theorem log_partitionFunction_high_temp_expansion_h_zero_sandwich_exp
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    (Fintype.card ι : ℝ) * Real.log 2
        + (G.edgeFinset.card : ℝ) * Real.log (Real.cosh (β * J))
      ≤ Real.log (partitionFunction G ⟨J, 0, β⟩) ∧
    Real.log (partitionFunction G ⟨J, 0, β⟩)
      ≤ (Fintype.card ι : ℝ) * Real.log 2
        + β * J * G.edgeFinset.card := by
  refine ⟨?_, log_partitionFunction_high_temp_expansion_h_zero_upper_bound_exp
    G J β hβJ⟩
  -- log Z ≥ |ι| log 2 + |E| log cosh(βJ) from
  -- log Z = |ι| log 2 + |E| log cosh + log(∑) and log(∑) ≥ 0.
  rw [log_partitionFunction_high_temp_expansion_h_zero_closed G J β hβJ]
  have h_one_le_sum := one_le_sum_pow_tanh_even_subgraph G J β hβJ
  have hlog_nn : 0 ≤ Real.log
      (∑ X ∈ G.edgeFinset.powerset.filter
          (fun X : Finset (Sym2 ι) =>
            ∀ v : ι, Even ((X.filter (v ∈ ·)).card)),
          Real.tanh (β * J) ^ X.card) :=
    Real.log_nonneg h_one_le_sum
  linarith

/-- **log Z deviation sandwich**: under `0 ≤ β·J`,
`0 ≤ log Z - |ι|·log 2 ≤ β·J·|E|`. -/
theorem log_partitionFunction_high_temp_expansion_h_zero_deviation_sandwich
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    0 ≤ Real.log (partitionFunction G ⟨J, 0, β⟩)
        - (Fintype.card ι : ℝ) * Real.log 2 ∧
    Real.log (partitionFunction G ⟨J, 0, β⟩)
        - (Fintype.card ι : ℝ) * Real.log 2
      ≤ β * J * G.edgeFinset.card := by
  obtain ⟨h_lb, h_ub⟩ := log_partitionFunction_high_temp_expansion_h_zero_sandwich_exp
    G J β hβJ
  refine ⟨?_, by linarith⟩
  -- log Z ≥ |ι| log 2 from |ι| log 2 + |E|·log cosh(βJ) ≤ log Z and log cosh ≥ 0.
  have hcosh_ge : 1 ≤ Real.cosh (β * J) := Real.one_le_cosh _
  have hlog_nn : 0 ≤ Real.log (Real.cosh (β * J)) :=
    Real.log_nonneg hcosh_ge
  have hedge_nn : (0 : ℝ) ≤ G.edgeFinset.card := Nat.cast_nonneg _
  have h_corr_nn : 0 ≤ (G.edgeFinset.card : ℝ) * Real.log (Real.cosh (β * J)) :=
    mul_nonneg hedge_nn hlog_nn
  linarith

/-- **log Z strict deviation under non-trivial high-temperature**:
under `0 < β·J` and `0 < |E|`, `0 < log Z - |ι|·log 2`.

Strict version of the log Z lower bound. Follows from
`|ι|·log 2 + |E|·log cosh(β·J) ≤ log Z` plus `log cosh(β·J) > 0`. -/
theorem log_partitionFunction_high_temp_expansion_h_zero_deviation_pos
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 < β * J) (hEpos : 0 < G.edgeFinset.card) :
    0 < Real.log (partitionFunction G ⟨J, 0, β⟩)
        - (Fintype.card ι : ℝ) * Real.log 2 := by
  obtain ⟨h_lb, _⟩ := log_partitionFunction_high_temp_expansion_h_zero_sandwich_exp
    G J β hβJ.le
  have hcosh_gt : 1 < Real.cosh (β * J) := by
    rw [show (1 : ℝ) = Real.cosh 0 from Real.cosh_zero.symm]
    refine Real.cosh_lt_cosh.mpr ?_
    rw [abs_zero, abs_of_pos hβJ]
    exact hβJ
  have hlog_pos : 0 < Real.log (Real.cosh (β * J)) := Real.log_pos hcosh_gt
  have hE_pos : (0 : ℝ) < G.edgeFinset.card := by exact_mod_cast hEpos
  have h_corr_pos : 0 < (G.edgeFinset.card : ℝ) * Real.log (Real.cosh (β * J)) :=
    mul_pos hE_pos hlog_pos
  linarith

/-- **Sharper log Z complete-summary exp bundle**: under `0 ≤ β·J`,
single statement bundling sharper sandwich + trivial-slice values:
  1. `|ι|·log 2 + |E|·log cosh(β·J) ≤ log Z` (lower),
  2. `log Z ≤ |ι|·log 2 + β·J·|E|` (sharper exp upper),
  3. `log Z⟨0, 0, β⟩ = |ι|·log 2` (J = 0 trivial slice),
  4. `log Z⟨J, 0, 0⟩ = |ι|·log 2` (β = 0 trivial slice). -/
theorem log_partitionFunction_high_temp_expansion_h_zero_complete_summary_exp
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    (Fintype.card ι : ℝ) * Real.log 2
        + (G.edgeFinset.card : ℝ) * Real.log (Real.cosh (β * J))
      ≤ Real.log (partitionFunction G ⟨J, 0, β⟩) ∧
    Real.log (partitionFunction G ⟨J, 0, β⟩)
      ≤ (Fintype.card ι : ℝ) * Real.log 2
        + β * J * G.edgeFinset.card ∧
    Real.log (partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ))
      = (Fintype.card ι : ℝ) * Real.log 2 ∧
    Real.log (partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ))
      = (Fintype.card ι : ℝ) * Real.log 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (log_partitionFunction_high_temp_expansion_h_zero_sandwich_exp
      G J β hβJ).1
  · exact log_partitionFunction_high_temp_expansion_h_zero_upper_bound_exp
      G J β hβJ
  · rw [partitionFunction_high_temp_expansion_h_zero_closed_at_J_zero,
        Real.log_pow]
  · rw [partitionFunction_high_temp_expansion_h_zero_closed_at_beta_zero,
        Real.log_pow]

/-- **Sharper freeEnergy high-temperature upper bound (FV (3.45))**: under
`0 < |ι|` and `0 ≤ β·J`,
`f(G; J, 0, β) ≤ log 2 + β·J·|E|/|ι|`.

Globally tighter than `freeEnergy_high_temp_h_zero_upper_bound`:
`log(2·cosh(β·J)) = log 2 + log cosh(β·J)` and `log cosh(β·J) ≤ β·J`
(since `cosh(β·J) ≤ exp(β·J)`), so this bound is sharper. Direct
corollary of `partitionFunction_high_temp_expansion_h_zero_upper_bound_exp`
(Step 393) by taking logarithms and dividing by `|ι|`. -/
theorem freeEnergy_high_temp_h_zero_upper_bound_exp
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Fintype.card ι) :
    freeEnergy G ⟨J, 0, β⟩
      ≤ Real.log 2 + β * J * G.edgeFinset.card / Fintype.card ι := by
  have hZ_ub := partitionFunction_high_temp_expansion_h_zero_upper_bound_exp G J β hβJ
  have hZ_pos := partitionFunction_pos G ⟨J, 0, β⟩
  have hcard_pos : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast hne
  have hubound_pos : (0 : ℝ) <
      (2 : ℝ) ^ Fintype.card ι * Real.exp (β * J * G.edgeFinset.card) :=
    mul_pos (pow_pos (by norm_num) _) (Real.exp_pos _)
  have hlog : Real.log (partitionFunction G ⟨J, 0, β⟩)
      ≤ (Fintype.card ι : ℝ) * Real.log 2
        + β * J * G.edgeFinset.card := by
    calc Real.log (partitionFunction G ⟨J, 0, β⟩)
        ≤ Real.log ((2 : ℝ) ^ Fintype.card ι *
              Real.exp (β * J * G.edgeFinset.card)) :=
          (Real.log_le_log_iff hZ_pos hubound_pos).mpr hZ_ub
      _ = Real.log ((2 : ℝ) ^ Fintype.card ι)
          + Real.log (Real.exp (β * J * G.edgeFinset.card)) :=
          Real.log_mul (pow_pos (by norm_num) _).ne' (Real.exp_pos _).ne'
      _ = (Fintype.card ι : ℝ) * Real.log 2
          + β * J * G.edgeFinset.card := by
          rw [Real.log_pow, Real.log_exp]
  unfold freeEnergy
  rw [show ((Fintype.card ι : ℝ)⁻¹ * Real.log (partitionFunction G ⟨J, 0, β⟩))
        = Real.log (partitionFunction G ⟨J, 0, β⟩) / Fintype.card ι by
        rw [div_eq_inv_mul]]
  rw [div_le_iff₀ hcard_pos, add_mul, mul_comm (Real.log 2) _,
      div_mul_cancel₀ _ hcard_pos.ne']
  linarith

/-- **Z strict deviation under non-trivial high-temperature**: under
`0 < β·J` and `0 < |E|`, `(2 : ℝ)^|ι| < Z(G; J, 0, β)`.

Strict version of Step 286 lower bound. Follows from
`partitionFunction_high_temp_expansion_h_zero_lower_bound` plus
strict `1 < cosh(β·J)`. -/
theorem partitionFunction_high_temp_expansion_h_zero_pow_two_lt
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 < β * J) (hEpos : 0 < G.edgeFinset.card) :
    (2 : ℝ) ^ Fintype.card ι < partitionFunction G ⟨J, 0, β⟩ := by
  have h_lb := partitionFunction_high_temp_expansion_h_zero_lower_bound
    G J β hβJ.le
  have hcosh_gt : 1 < Real.cosh (β * J) := by
    rw [show (1 : ℝ) = Real.cosh 0 from Real.cosh_zero.symm]
    refine Real.cosh_lt_cosh.mpr ?_
    rw [abs_zero, abs_of_pos hβJ]
    exact hβJ
  have hcosh_pow_gt : 1 < Real.cosh (β * J) ^ G.edgeFinset.card :=
    one_lt_pow₀ hcosh_gt hEpos.ne'
  have h2_pos : (0 : ℝ) < (2 : ℝ) ^ Fintype.card ι :=
    pow_pos (by norm_num) _
  have : (2 : ℝ) ^ Fintype.card ι < (2 : ℝ) ^ Fintype.card ι *
      Real.cosh (β * J) ^ G.edgeFinset.card := by
    rw [show (2 : ℝ) ^ Fintype.card ι = (2 : ℝ) ^ Fintype.card ι * 1 from
      (mul_one _).symm]
    rw [mul_one]
    exact (lt_mul_iff_one_lt_right h2_pos).mpr hcosh_pow_gt
  linarith

/-- **Z ratio bound at trivial slice**: under `0 ≤ β·J`,
`Z(G; J, 0, β) / Z(G; 0, 0, β) ≤ exp(β·J·|E|)`.

Combines the sharper Z upper bound `Z(J,0,β) ≤ 2^|ι|·exp(β·J·|E|)`
(Step 393) with the trivial slice `Z(0,0,β) = 2^|ι|` (Step 310). The
ratio measures how much `Z` grows relative to its "free spin"
(non-interacting) value as `J` increases. -/
theorem partitionFunction_high_temp_expansion_h_zero_ratio_bound
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    partitionFunction G ⟨J, 0, β⟩ /
        partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ)
      ≤ Real.exp (β * J * G.edgeFinset.card) := by
  have h_ub := partitionFunction_high_temp_expansion_h_zero_upper_bound_exp
    G J β hβJ
  have h_J0 : partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ)
      = (2 : ℝ) ^ Fintype.card ι :=
    partitionFunction_high_temp_expansion_h_zero_closed_at_J_zero G β
  rw [h_J0]
  rw [div_le_iff₀ (pow_pos (by norm_num) _)]
  have h2_pos : (0 : ℝ) < (2 : ℝ) ^ Fintype.card ι :=
    pow_pos (by norm_num) _
  calc partitionFunction G ⟨J, 0, β⟩
      ≤ (2 : ℝ) ^ Fintype.card ι *
          Real.exp (β * J * G.edgeFinset.card) := h_ub
    _ = Real.exp (β * J * G.edgeFinset.card) *
          (2 : ℝ) ^ Fintype.card ι := by ring

/-- **Z ratio bound at β=0 trivial slice**: under `0 ≤ β·J`,
`Z(G; J, 0, β) / Z(G; J, 0, 0) ≤ exp(β·J·|E|)`. -/
theorem partitionFunction_high_temp_expansion_h_zero_ratio_bound_beta_zero
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    partitionFunction G ⟨J, 0, β⟩ /
        partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ)
      ≤ Real.exp (β * J * G.edgeFinset.card) := by
  have h_ub := partitionFunction_high_temp_expansion_h_zero_upper_bound_exp
    G J β hβJ
  have h_β0 : partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ)
      = (2 : ℝ) ^ Fintype.card ι :=
    partitionFunction_high_temp_expansion_h_zero_closed_at_beta_zero G J
  rw [h_β0]
  rw [div_le_iff₀ (pow_pos (by norm_num) _)]
  calc partitionFunction G ⟨J, 0, β⟩
      ≤ (2 : ℝ) ^ Fintype.card ι *
          Real.exp (β * J * G.edgeFinset.card) := h_ub
    _ = Real.exp (β * J * G.edgeFinset.card) *
          (2 : ℝ) ^ Fintype.card ι := by ring

/-- **Z ratio upper bound bundle**: under `0 ≤ β·J`, single statement
bundling Z ratio upper bounds at both J=0 and β=0 trivial slices. -/
theorem partitionFunction_high_temp_expansion_h_zero_ratio_bound_bundle
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    partitionFunction G ⟨J, 0, β⟩ /
        partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ)
        ≤ Real.exp (β * J * G.edgeFinset.card) ∧
    partitionFunction G ⟨J, 0, β⟩ /
        partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ)
        ≤ Real.exp (β * J * G.edgeFinset.card) :=
  ⟨partitionFunction_high_temp_expansion_h_zero_ratio_bound G J β hβJ,
   partitionFunction_high_temp_expansion_h_zero_ratio_bound_beta_zero G J β hβJ⟩

/-- **log Z ratio sandwich at J=0 trivial slice**: under `0 ≤ β·J`,
`|E|·log cosh(β·J) ≤ log Z⟨J,0,β⟩ - log Z⟨0,0,β⟩ ≤ β·J·|E|`.

Combines `log_partitionFunction_high_temp_expansion_h_zero_sandwich_exp`
with the trivial slice `log Z⟨0,0,β⟩ = |ι|·log 2`. -/
theorem log_partitionFunction_high_temp_expansion_h_zero_ratio_sandwich
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    (G.edgeFinset.card : ℝ) * Real.log (Real.cosh (β * J))
        ≤ Real.log (partitionFunction G ⟨J, 0, β⟩)
            - Real.log (partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ)) ∧
    Real.log (partitionFunction G ⟨J, 0, β⟩)
        - Real.log (partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ))
        ≤ β * J * G.edgeFinset.card := by
  have h_J0 : partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ)
      = (2 : ℝ) ^ Fintype.card ι :=
    partitionFunction_high_temp_expansion_h_zero_closed_at_J_zero G β
  have h_log : Real.log (partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ))
      = (Fintype.card ι : ℝ) * Real.log 2 := by
    rw [h_J0, Real.log_pow]
  rw [h_log]
  obtain ⟨h_lb, h_ub⟩ :=
    log_partitionFunction_high_temp_expansion_h_zero_sandwich_exp G J β hβJ
  refine ⟨?_, ?_⟩ <;> linarith

/-- **log Z ratio sandwich at β=0 trivial slice**: under `0 ≤ β·J`,
`|E|·log cosh(β·J) ≤ log Z⟨J,0,β⟩ - log Z⟨J,0,0⟩ ≤ β·J·|E|`. -/
theorem log_partitionFunction_high_temp_expansion_h_zero_ratio_sandwich_beta_zero
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    (G.edgeFinset.card : ℝ) * Real.log (Real.cosh (β * J))
        ≤ Real.log (partitionFunction G ⟨J, 0, β⟩)
            - Real.log (partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ)) ∧
    Real.log (partitionFunction G ⟨J, 0, β⟩)
        - Real.log (partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ))
        ≤ β * J * G.edgeFinset.card := by
  have h_β0 : partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ)
      = (2 : ℝ) ^ Fintype.card ι :=
    partitionFunction_high_temp_expansion_h_zero_closed_at_beta_zero G J
  have h_log : Real.log (partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ))
      = (Fintype.card ι : ℝ) * Real.log 2 := by
    rw [h_β0, Real.log_pow]
  rw [h_log]
  obtain ⟨h_lb, h_ub⟩ :=
    log_partitionFunction_high_temp_expansion_h_zero_sandwich_exp G J β hβJ
  refine ⟨?_, ?_⟩ <;> linarith

/-- **log Z ratio sandwich bundle**: bundles both J=0 and β=0 sandwiches. -/
theorem log_partitionFunction_high_temp_expansion_h_zero_ratio_sandwich_bundle
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    ((G.edgeFinset.card : ℝ) * Real.log (Real.cosh (β * J))
        ≤ Real.log (partitionFunction G ⟨J, 0, β⟩)
            - Real.log (partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ)) ∧
      Real.log (partitionFunction G ⟨J, 0, β⟩)
          - Real.log (partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ))
          ≤ β * J * G.edgeFinset.card) ∧
    ((G.edgeFinset.card : ℝ) * Real.log (Real.cosh (β * J))
        ≤ Real.log (partitionFunction G ⟨J, 0, β⟩)
            - Real.log (partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ)) ∧
      Real.log (partitionFunction G ⟨J, 0, β⟩)
          - Real.log (partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ))
          ≤ β * J * G.edgeFinset.card) :=
  ⟨log_partitionFunction_high_temp_expansion_h_zero_ratio_sandwich G J β hβJ,
   log_partitionFunction_high_temp_expansion_h_zero_ratio_sandwich_beta_zero
     G J β hβJ⟩

/-- **Ferromagnetic log Z ratio sandwich bundle**. -/
theorem log_partitionFunction_high_temp_expansion_h_zero_ratio_sandwich_bundle_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    ((G.edgeFinset.card : ℝ) * Real.log (Real.cosh (β * J))
        ≤ Real.log (partitionFunction G ⟨J, 0, β⟩)
            - Real.log (partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ)) ∧
      Real.log (partitionFunction G ⟨J, 0, β⟩)
          - Real.log (partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ))
          ≤ β * J * G.edgeFinset.card) ∧
    ((G.edgeFinset.card : ℝ) * Real.log (Real.cosh (β * J))
        ≤ Real.log (partitionFunction G ⟨J, 0, β⟩)
            - Real.log (partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ)) ∧
      Real.log (partitionFunction G ⟨J, 0, β⟩)
          - Real.log (partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ))
          ≤ β * J * G.edgeFinset.card) :=
  log_partitionFunction_high_temp_expansion_h_zero_ratio_sandwich_bundle
    G J β (mul_nonneg hβ.le hJ)

/-- **log Z ratio bound at J=0 trivial slice**: under `0 ≤ β·J`,
`log Z⟨J, 0, β⟩ - log Z⟨0, 0, β⟩ ≤ β·J·|E|`.

Combines the sharper log Z upper bound (Step 403) with
`log Z⟨0, 0, β⟩ = |ι|·log 2`. -/
theorem log_partitionFunction_high_temp_expansion_h_zero_ratio_bound
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    Real.log (partitionFunction G ⟨J, 0, β⟩)
        - Real.log (partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ))
      ≤ β * J * G.edgeFinset.card := by
  have h_J0 : partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ)
      = (2 : ℝ) ^ Fintype.card ι :=
    partitionFunction_high_temp_expansion_h_zero_closed_at_J_zero G β
  have h_log : Real.log (partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ))
      = (Fintype.card ι : ℝ) * Real.log 2 := by
    rw [h_J0, Real.log_pow]
  rw [h_log]
  linarith [log_partitionFunction_high_temp_expansion_h_zero_upper_bound_exp
    G J β hβJ]

/-- **log Z ratio bound at β=0 trivial slice**: under `0 ≤ β·J`,
`log Z⟨J, 0, β⟩ - log Z⟨J, 0, 0⟩ ≤ β·J·|E|`. -/
theorem log_partitionFunction_high_temp_expansion_h_zero_ratio_bound_beta_zero
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    Real.log (partitionFunction G ⟨J, 0, β⟩)
        - Real.log (partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ))
      ≤ β * J * G.edgeFinset.card := by
  have h_β0 : partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ)
      = (2 : ℝ) ^ Fintype.card ι :=
    partitionFunction_high_temp_expansion_h_zero_closed_at_beta_zero G J
  have h_log : Real.log (partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ))
      = (Fintype.card ι : ℝ) * Real.log 2 := by
    rw [h_β0, Real.log_pow]
  rw [h_log]
  linarith [log_partitionFunction_high_temp_expansion_h_zero_upper_bound_exp
    G J β hβJ]

/-- **log Z ratio bound bundle**: under `0 ≤ β·J`, single statement
bundling log Z ratio upper bounds at both J=0 and β=0 trivial slices. -/
theorem log_partitionFunction_high_temp_expansion_h_zero_ratio_bound_bundle
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    Real.log (partitionFunction G ⟨J, 0, β⟩)
        - Real.log (partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ))
        ≤ β * J * G.edgeFinset.card ∧
    Real.log (partitionFunction G ⟨J, 0, β⟩)
        - Real.log (partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ))
        ≤ β * J * G.edgeFinset.card :=
  ⟨log_partitionFunction_high_temp_expansion_h_zero_ratio_bound G J β hβJ,
   log_partitionFunction_high_temp_expansion_h_zero_ratio_bound_beta_zero
     G J β hβJ⟩

/-- **Ferromagnetic log Z ratio bound at J=0**. -/
theorem log_partitionFunction_high_temp_expansion_h_zero_ratio_bound_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    Real.log (partitionFunction G ⟨J, 0, β⟩)
        - Real.log (partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ))
      ≤ β * J * G.edgeFinset.card :=
  log_partitionFunction_high_temp_expansion_h_zero_ratio_bound
    G J β (mul_nonneg hβ.le hJ)

/-- **Ferromagnetic log Z ratio bound at β=0**. -/
theorem log_partitionFunction_high_temp_expansion_h_zero_ratio_bound_beta_zero_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    Real.log (partitionFunction G ⟨J, 0, β⟩)
        - Real.log (partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ))
      ≤ β * J * G.edgeFinset.card :=
  log_partitionFunction_high_temp_expansion_h_zero_ratio_bound_beta_zero
    G J β (mul_nonneg hβ.le hJ)

/-- **Ferromagnetic log Z ratio bound bundle**. -/
theorem log_partitionFunction_high_temp_expansion_h_zero_ratio_bound_bundle_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    Real.log (partitionFunction G ⟨J, 0, β⟩)
        - Real.log (partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ))
        ≤ β * J * G.edgeFinset.card ∧
    Real.log (partitionFunction G ⟨J, 0, β⟩)
        - Real.log (partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ))
        ≤ β * J * G.edgeFinset.card :=
  log_partitionFunction_high_temp_expansion_h_zero_ratio_bound_bundle
    G J β (mul_nonneg hβ.le hJ)

/-- **Sharper Z complete-summary exp bundle**: under `0 ≤ β·J`,
single statement bundling sharper sandwich + trivial-slice values:
  1. `2^|ι|·cosh^|E| ≤ Z` (lower),
  2. `Z ≤ 2^|ι|·exp(β·J·|E|)` (sharper exp upper),
  3. `Z⟨0, 0, β⟩ = 2^|ι|` (J = 0 trivial slice),
  4. `Z⟨J, 0, 0⟩ = 2^|ι|` (β = 0 trivial slice).
Useful as a single import for downstream applications. -/
theorem partitionFunction_high_temp_expansion_h_zero_complete_summary_exp
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    (2 : ℝ) ^ Fintype.card ι *
        Real.cosh (β * J) ^ G.edgeFinset.card
      ≤ partitionFunction G ⟨J, 0, β⟩ ∧
    partitionFunction G ⟨J, 0, β⟩
      ≤ (2 : ℝ) ^ Fintype.card ι *
          Real.exp (β * J * G.edgeFinset.card) ∧
    partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ)
      = (2 : ℝ) ^ Fintype.card ι ∧
    partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ)
      = (2 : ℝ) ^ Fintype.card ι :=
  ⟨partitionFunction_high_temp_expansion_h_zero_lower_bound G J β hβJ,
   partitionFunction_high_temp_expansion_h_zero_upper_bound_exp G J β hβJ,
   partitionFunction_high_temp_expansion_h_zero_closed_at_J_zero G β,
   partitionFunction_high_temp_expansion_h_zero_closed_at_beta_zero G J⟩

/-- **Sharper Z high-temperature sandwich (FV (3.45))**: under
`0 ≤ β·J`,
`2^|ι| · (cosh βJ)^|E| ≤ Z(G; J, 0, β) ≤ 2^|ι| · exp(β·J·|E|)`.

Combines `partitionFunction_high_temp_expansion_h_zero_lower_bound`
(Step 286) with `partitionFunction_high_temp_expansion_h_zero_upper_bound_exp`
(Step 393). Globally sharper than the cosh-only sandwich of Step 326. -/
theorem partitionFunction_high_temp_expansion_h_zero_sandwich_exp
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    (2 : ℝ) ^ Fintype.card ι *
        Real.cosh (β * J) ^ G.edgeFinset.card
      ≤ partitionFunction G ⟨J, 0, β⟩ ∧
    partitionFunction G ⟨J, 0, β⟩
      ≤ (2 : ℝ) ^ Fintype.card ι *
          Real.exp (β * J * G.edgeFinset.card) :=
  ⟨partitionFunction_high_temp_expansion_h_zero_lower_bound G J β hβJ,
   partitionFunction_high_temp_expansion_h_zero_upper_bound_exp G J β hβJ⟩

/-- **Z relative-deviation sandwich**: under `0 ≤ β·J`,
`cosh(β·J)^|E| ≤ Z(G; J, 0, β) / 2^|ι| ≤ exp(β·J·|E|)`.

Divides the Z sandwich by `2^|ι|` to give a normalized "deviation" form.
The lower bound `cosh^|E|` matches the contribution of the empty-X term
in FV (3.45); the upper bound `exp(β·J·|E|)` is the linear-`β·J`
exponential. -/
theorem partitionFunction_high_temp_expansion_h_zero_relative_sandwich
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    Real.cosh (β * J) ^ G.edgeFinset.card
      ≤ partitionFunction G ⟨J, 0, β⟩ / (2 : ℝ) ^ Fintype.card ι ∧
    partitionFunction G ⟨J, 0, β⟩ / (2 : ℝ) ^ Fintype.card ι
      ≤ Real.exp (β * J * G.edgeFinset.card) := by
  have h2_pos : (0 : ℝ) < (2 : ℝ) ^ Fintype.card ι :=
    pow_pos (by norm_num) _
  obtain ⟨h_lb, h_ub⟩ := partitionFunction_high_temp_expansion_h_zero_sandwich_exp
    G J β hβJ
  refine ⟨?_, ?_⟩
  · rw [le_div_iff₀ h2_pos]; linarith
  · rw [div_le_iff₀ h2_pos]; linarith

/-- **Z ratio sandwich at trivial slice**: under `0 ≤ β·J`,
`cosh(β·J)^|E| ≤ Z(G; J, 0, β) / Z(G; 0, 0, β) ≤ exp(β·J·|E|)`. -/
theorem partitionFunction_high_temp_expansion_h_zero_ratio_sandwich
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    Real.cosh (β * J) ^ G.edgeFinset.card
      ≤ partitionFunction G ⟨J, 0, β⟩ /
          partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ) ∧
    partitionFunction G ⟨J, 0, β⟩ /
        partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ)
      ≤ Real.exp (β * J * G.edgeFinset.card) := by
  have h_J0 : partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ)
      = (2 : ℝ) ^ Fintype.card ι :=
    partitionFunction_high_temp_expansion_h_zero_closed_at_J_zero G β
  rw [h_J0]
  exact partitionFunction_high_temp_expansion_h_zero_relative_sandwich G J β hβJ

/-- **Z ratio sandwich at β=0 trivial slice**: under `0 ≤ β·J`,
`cosh(β·J)^|E| ≤ Z(G; J, 0, β) / Z(G; J, 0, 0) ≤ exp(β·J·|E|)`. -/
theorem partitionFunction_high_temp_expansion_h_zero_ratio_sandwich_beta_zero
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    Real.cosh (β * J) ^ G.edgeFinset.card
      ≤ partitionFunction G ⟨J, 0, β⟩ /
          partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ) ∧
    partitionFunction G ⟨J, 0, β⟩ /
        partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ)
      ≤ Real.exp (β * J * G.edgeFinset.card) := by
  have h_β0 : partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ)
      = (2 : ℝ) ^ Fintype.card ι :=
    partitionFunction_high_temp_expansion_h_zero_closed_at_beta_zero G J
  rw [h_β0]
  exact partitionFunction_high_temp_expansion_h_zero_relative_sandwich G J β hβJ

/-- **Z ratio sandwich bundle**: under `0 ≤ β·J`, single statement
bundling Z ratios at both `J = 0` and `β = 0` trivial slices. -/
theorem partitionFunction_high_temp_expansion_h_zero_ratio_sandwich_bundle
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    (Real.cosh (β * J) ^ G.edgeFinset.card
        ≤ partitionFunction G ⟨J, 0, β⟩ /
            partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ) ∧
      partitionFunction G ⟨J, 0, β⟩ /
          partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ)
        ≤ Real.exp (β * J * G.edgeFinset.card)) ∧
    (Real.cosh (β * J) ^ G.edgeFinset.card
        ≤ partitionFunction G ⟨J, 0, β⟩ /
            partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ) ∧
      partitionFunction G ⟨J, 0, β⟩ /
          partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ)
        ≤ Real.exp (β * J * G.edgeFinset.card)) :=
  ⟨partitionFunction_high_temp_expansion_h_zero_ratio_sandwich G J β hβJ,
   partitionFunction_high_temp_expansion_h_zero_ratio_sandwich_beta_zero
     G J β hβJ⟩

/-- **Ferromagnetic Z ratio sandwich at J=0 trivial slice**. -/
theorem partitionFunction_high_temp_expansion_h_zero_ratio_sandwich_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    Real.cosh (β * J) ^ G.edgeFinset.card
      ≤ partitionFunction G ⟨J, 0, β⟩ /
          partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ) ∧
    partitionFunction G ⟨J, 0, β⟩ /
        partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ)
      ≤ Real.exp (β * J * G.edgeFinset.card) :=
  partitionFunction_high_temp_expansion_h_zero_ratio_sandwich
    G J β (mul_nonneg hβ.le hJ)

/-- **Ferromagnetic Z ratio sandwich at β=0 trivial slice**. -/
theorem partitionFunction_high_temp_expansion_h_zero_ratio_sandwich_beta_zero_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    Real.cosh (β * J) ^ G.edgeFinset.card
      ≤ partitionFunction G ⟨J, 0, β⟩ /
          partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ) ∧
    partitionFunction G ⟨J, 0, β⟩ /
        partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ)
      ≤ Real.exp (β * J * G.edgeFinset.card) :=
  partitionFunction_high_temp_expansion_h_zero_ratio_sandwich_beta_zero
    G J β (mul_nonneg hβ.le hJ)

/-- **Ferromagnetic Z ratio sandwich bundle**. -/
theorem partitionFunction_high_temp_expansion_h_zero_ratio_sandwich_bundle_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    (Real.cosh (β * J) ^ G.edgeFinset.card
        ≤ partitionFunction G ⟨J, 0, β⟩ /
            partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ) ∧
      partitionFunction G ⟨J, 0, β⟩ /
          partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ)
        ≤ Real.exp (β * J * G.edgeFinset.card)) ∧
    (Real.cosh (β * J) ^ G.edgeFinset.card
        ≤ partitionFunction G ⟨J, 0, β⟩ /
            partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ) ∧
      partitionFunction G ⟨J, 0, β⟩ /
          partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ)
        ≤ Real.exp (β * J * G.edgeFinset.card)) :=
  partitionFunction_high_temp_expansion_h_zero_ratio_sandwich_bundle
    G J β (mul_nonneg hβ.le hJ)

/-- **Ferromagnetic Z ratio upper bound at J=0**. -/
theorem partitionFunction_high_temp_expansion_h_zero_ratio_bound_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    partitionFunction G ⟨J, 0, β⟩ /
        partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ)
      ≤ Real.exp (β * J * G.edgeFinset.card) :=
  partitionFunction_high_temp_expansion_h_zero_ratio_bound
    G J β (mul_nonneg hβ.le hJ)

/-- **Ferromagnetic Z ratio upper bound at β=0**. -/
theorem partitionFunction_high_temp_expansion_h_zero_ratio_bound_beta_zero_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    partitionFunction G ⟨J, 0, β⟩ /
        partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ)
      ≤ Real.exp (β * J * G.edgeFinset.card) :=
  partitionFunction_high_temp_expansion_h_zero_ratio_bound_beta_zero
    G J β (mul_nonneg hβ.le hJ)

/-- **Ferromagnetic Z ratio upper bound bundle**: under `0 ≤ J, 0 < β`. -/
theorem partitionFunction_high_temp_expansion_h_zero_ratio_bound_bundle_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    partitionFunction G ⟨J, 0, β⟩ /
        partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ)
        ≤ Real.exp (β * J * G.edgeFinset.card) ∧
    partitionFunction G ⟨J, 0, β⟩ /
        partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ)
        ≤ Real.exp (β * J * G.edgeFinset.card) :=
  partitionFunction_high_temp_expansion_h_zero_ratio_bound_bundle
    G J β (mul_nonneg hβ.le hJ)

/-- **Ferromagnetic Z relative-deviation sandwich**: under `0 ≤ J, 0 < β`,
`cosh(β·J)^|E| ≤ Z / 2^|ι| ≤ exp(β·J·|E|)`. -/
theorem partitionFunction_high_temp_expansion_h_zero_relative_sandwich_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    Real.cosh (β * J) ^ G.edgeFinset.card
      ≤ partitionFunction G ⟨J, 0, β⟩ / (2 : ℝ) ^ Fintype.card ι ∧
    partitionFunction G ⟨J, 0, β⟩ / (2 : ℝ) ^ Fintype.card ι
      ≤ Real.exp (β * J * G.edgeFinset.card) :=
  partitionFunction_high_temp_expansion_h_zero_relative_sandwich
    G J β (mul_nonneg hβ.le hJ)

/-- **Ferromagnetic Z strict deviation**: under `0 < J, 0 < β` and
`0 < |E|`, `2^|ι| < Z`. -/
theorem partitionFunction_high_temp_expansion_h_zero_pow_two_lt_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 < J) (hβ : 0 < β) (hEpos : 0 < G.edgeFinset.card) :
    (2 : ℝ) ^ Fintype.card ι < partitionFunction G ⟨J, 0, β⟩ :=
  partitionFunction_high_temp_expansion_h_zero_pow_two_lt
    G J β (mul_pos hβ hJ) hEpos

/-- **Ferromagnetic log Z strict deviation**: under `0 < J, 0 < β` and
`0 < |E|`, `0 < log Z - |ι|·log 2`. -/
theorem log_partitionFunction_high_temp_expansion_h_zero_deviation_pos_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 < J) (hβ : 0 < β) (hEpos : 0 < G.edgeFinset.card) :
    0 < Real.log (partitionFunction G ⟨J, 0, β⟩)
        - (Fintype.card ι : ℝ) * Real.log 2 :=
  log_partitionFunction_high_temp_expansion_h_zero_deviation_pos
    G J β (mul_pos hβ hJ) hEpos

/-- **Ferromagnetic sharper Z high-temperature upper bound**: under
`0 ≤ J, 0 < β`, `Z(G; J, 0, β) ≤ 2^|ι| · exp(β·J·|E|)`. Bridges
ferromagnetic-style hypotheses with Step 393 via `mul_nonneg hβ.le hJ`. -/
theorem partitionFunction_high_temp_expansion_h_zero_upper_bound_exp_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    partitionFunction G ⟨J, 0, β⟩
      ≤ (2 : ℝ) ^ Fintype.card ι *
          Real.exp (β * J * G.edgeFinset.card) :=
  partitionFunction_high_temp_expansion_h_zero_upper_bound_exp
    G J β (mul_nonneg hβ.le hJ)

/-- **Ferromagnetic sharper log Z high-temperature upper bound**: under
`0 ≤ J, 0 < β`, `log Z ≤ |ι|·log 2 + β·J·|E|`. Bridges ferromagnetic
hypotheses with Step 403. -/
theorem log_partitionFunction_high_temp_expansion_h_zero_upper_bound_exp_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    Real.log (partitionFunction G ⟨J, 0, β⟩)
      ≤ (Fintype.card ι : ℝ) * Real.log 2
        + β * J * G.edgeFinset.card :=
  log_partitionFunction_high_temp_expansion_h_zero_upper_bound_exp
    G J β (mul_nonneg hβ.le hJ)

/-- **Ferromagnetic sharper f high-temperature upper bound**: under
`0 < |ι|`, `0 ≤ J, 0 < β`, `f ≤ log 2 + β·J·|E|/|ι|`. Bridges
ferromagnetic hypotheses with Step 394. -/
theorem freeEnergy_high_temp_h_zero_upper_bound_exp_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Fintype.card ι) :
    freeEnergy G ⟨J, 0, β⟩
      ≤ Real.log 2 + β * J * G.edgeFinset.card / Fintype.card ι :=
  freeEnergy_high_temp_h_zero_upper_bound_exp
    G J β (mul_nonneg hβ.le hJ) hne

/-- **freeEnergy high-temperature upper bound from FV (3.45)**: under
`0 < |ι|` and `0 ≤ β·J`,
`freeEnergy(G; J, 0, β) ≤ log 2 + (|E|/|ι|) · log(2 · cosh(β·J))`.

Pair to `freeEnergy_high_temp_h_zero_lower_bound` (Step 288).
Direct from `partitionFunction_high_temp_expansion_h_zero_upper_bound`
(Step 320) by taking logs and dividing by `|ι|`. -/
theorem freeEnergy_high_temp_h_zero_upper_bound
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Fintype.card ι) :
    freeEnergy G ⟨J, 0, β⟩
      ≤ Real.log 2
        + (G.edgeFinset.card : ℝ) / Fintype.card ι *
            Real.log (2 * Real.cosh (β * J)) := by
  have hZ_ub := partitionFunction_high_temp_expansion_h_zero_upper_bound G J β hβJ
  have hZ_pos := partitionFunction_pos G ⟨J, 0, β⟩
  have hcosh_pos : 0 < Real.cosh (β * J) := Real.cosh_pos _
  have hubound_pos : (0 : ℝ) <
      (2 : ℝ) ^ (Fintype.card ι + G.edgeFinset.card) *
      Real.cosh (β * J) ^ G.edgeFinset.card :=
    mul_pos (pow_pos (by norm_num) _) (pow_pos hcosh_pos _)
  -- Take logs
  have hlog : Real.log (partitionFunction G ⟨J, 0, β⟩) ≤
      Real.log ((2 : ℝ) ^ (Fintype.card ι + G.edgeFinset.card) *
        Real.cosh (β * J) ^ G.edgeFinset.card) :=
    Real.log_le_log hZ_pos hZ_ub
  -- Simplify the RHS log
  have hlog_rhs :
      Real.log ((2 : ℝ) ^ (Fintype.card ι + G.edgeFinset.card) *
        Real.cosh (β * J) ^ G.edgeFinset.card)
        = ((Fintype.card ι : ℝ) + G.edgeFinset.card) * Real.log 2
          + (G.edgeFinset.card : ℝ) * Real.log (Real.cosh (β * J)) := by
    rw [Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow]
    push_cast; ring
  rw [hlog_rhs] at hlog
  -- Divide by |ι| > 0
  unfold freeEnergy
  have hι_pos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hne
  rw [show (Real.log 2 + (G.edgeFinset.card : ℝ) / Fintype.card ι *
              Real.log (2 * Real.cosh (β * J)))
        = (Fintype.card ι : ℝ)⁻¹ *
          (((Fintype.card ι : ℝ) + G.edgeFinset.card) * Real.log 2
            + (G.edgeFinset.card : ℝ) * Real.log (Real.cosh (β * J))) from by
      rw [Real.log_mul (by norm_num) hcosh_pos.ne']
      field_simp; ring]
  exact mul_le_mul_of_nonneg_left hlog (by positivity)

/-- **Z high-temperature sandwich bounds (GJ §18.3 / FV (3.45))**: under
`0 ≤ β·J`,
`2^|ι| · (cosh βJ)^|E| ≤ Z(G; J, 0, β) ≤ 2^(|ι|+|E|) · (cosh βJ)^|E|`.
Combines `partitionFunction_high_temp_expansion_h_zero_lower_bound`
(Step 286) and `partitionFunction_high_temp_expansion_h_zero_upper_bound`
(Step 320) into a single sandwich statement. -/
theorem partitionFunction_high_temp_expansion_h_zero_sandwich
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card
      ≤ partitionFunction G ⟨J, 0, β⟩
    ∧ partitionFunction G ⟨J, 0, β⟩
      ≤ (2 : ℝ) ^ (Fintype.card ι + G.edgeFinset.card) *
          Real.cosh (β * J) ^ G.edgeFinset.card :=
  ⟨partitionFunction_high_temp_expansion_h_zero_lower_bound G J β hβJ,
   partitionFunction_high_temp_expansion_h_zero_upper_bound G J β hβJ⟩

omit [DecidableEq ι] in
/-- **Z high-temp bounds consistency**: the FV (3.45) lower bound is
always at most the upper bound:
`2^|ι| · cosh^|E| ≤ 2^(|ι|+|E|) · cosh^|E|`. Trivial sanity check. -/
theorem partitionFunction_high_temp_h_zero_lower_le_upper
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℝ) :
    (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card
      ≤ (2 : ℝ) ^ (Fintype.card ι + G.edgeFinset.card) *
          Real.cosh (β * J) ^ G.edgeFinset.card := by
  have hpref_nn : 0 ≤
      (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card :=
    mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg (Real.cosh_pos _).le _)
  rw [show (Fintype.card ι + G.edgeFinset.card : ℕ)
      = Fintype.card ι + G.edgeFinset.card from rfl, pow_add]
  calc (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card
      = 1 * ((2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card) := by ring
    _ ≤ (2 : ℝ) ^ G.edgeFinset.card *
        ((2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card) := by
        apply mul_le_mul_of_nonneg_right _ hpref_nn
        exact one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)
    _ = (2 : ℝ) ^ Fintype.card ι * (2 : ℝ) ^ G.edgeFinset.card *
        Real.cosh (β * J) ^ G.edgeFinset.card := by ring

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

/-- **Sharper f high-temperature sandwich (FV (3.45))**: under
`0 < |ι|` and `0 ≤ β·J`,
`log 2 + (|E|/|ι|)·log cosh(β·J) ≤ f ≤ log 2 + β·J·|E|/|ι|`.

Combines `freeEnergy_high_temp_h_zero_lower_bound` with
`freeEnergy_high_temp_h_zero_upper_bound_exp` (Step 394). Globally
sharper than the cosh-based sandwich at the upper side. -/
theorem freeEnergy_high_temp_h_zero_sandwich_exp
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Fintype.card ι) :
    Real.log 2 +
        (G.edgeFinset.card : ℝ) / Fintype.card ι *
          Real.log (Real.cosh (β * J))
      ≤ freeEnergy G ⟨J, 0, β⟩ ∧
    freeEnergy G ⟨J, 0, β⟩
      ≤ Real.log 2 + β * J * G.edgeFinset.card / Fintype.card ι :=
  ⟨freeEnergy_high_temp_h_zero_lower_bound G J β hβJ hne,
   freeEnergy_high_temp_h_zero_upper_bound_exp G J β hβJ hne⟩

/-- **Ferromagnetic sharper Z complete-summary exp bundle**: under
`0 ≤ J, 0 < β`. -/
theorem partitionFunction_high_temp_expansion_h_zero_complete_summary_exp_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    (2 : ℝ) ^ Fintype.card ι *
        Real.cosh (β * J) ^ G.edgeFinset.card
      ≤ partitionFunction G ⟨J, 0, β⟩ ∧
    partitionFunction G ⟨J, 0, β⟩
      ≤ (2 : ℝ) ^ Fintype.card ι *
          Real.exp (β * J * G.edgeFinset.card) ∧
    partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ)
      = (2 : ℝ) ^ Fintype.card ι ∧
    partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ)
      = (2 : ℝ) ^ Fintype.card ι :=
  partitionFunction_high_temp_expansion_h_zero_complete_summary_exp
    G J β (mul_nonneg hβ.le hJ)

/-- **Ferromagnetic sharper log Z complete-summary exp bundle**: under
`0 ≤ J, 0 < β`. -/
theorem log_partitionFunction_high_temp_expansion_h_zero_complete_summary_exp_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    (Fintype.card ι : ℝ) * Real.log 2
        + (G.edgeFinset.card : ℝ) * Real.log (Real.cosh (β * J))
      ≤ Real.log (partitionFunction G ⟨J, 0, β⟩) ∧
    Real.log (partitionFunction G ⟨J, 0, β⟩)
      ≤ (Fintype.card ι : ℝ) * Real.log 2
        + β * J * G.edgeFinset.card ∧
    Real.log (partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ))
      = (Fintype.card ι : ℝ) * Real.log 2 ∧
    Real.log (partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ))
      = (Fintype.card ι : ℝ) * Real.log 2 :=
  log_partitionFunction_high_temp_expansion_h_zero_complete_summary_exp
    G J β (mul_nonneg hβ.le hJ)

/-- **Ferromagnetic sharper Z high-temperature sandwich**: under
`0 ≤ J, 0 < β`,
`2^|ι|·cosh^|E| ≤ Z(G;J,0,β) ≤ 2^|ι|·exp(β·J·|E|)`. Bridges
ferromagnetic hypotheses with Step 407 via `mul_nonneg hβ.le hJ`. -/
theorem partitionFunction_high_temp_expansion_h_zero_sandwich_exp_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    (2 : ℝ) ^ Fintype.card ι *
        Real.cosh (β * J) ^ G.edgeFinset.card
      ≤ partitionFunction G ⟨J, 0, β⟩ ∧
    partitionFunction G ⟨J, 0, β⟩
      ≤ (2 : ℝ) ^ Fintype.card ι *
          Real.exp (β * J * G.edgeFinset.card) :=
  partitionFunction_high_temp_expansion_h_zero_sandwich_exp
    G J β (mul_nonneg hβ.le hJ)

/-- **Ferromagnetic sharper f high-temperature sandwich**: under
`0 < |ι|`, `0 ≤ J, 0 < β`,
`log 2 + (|E|/|ι|)·log cosh(β·J) ≤ f ≤ log 2 + β·J·|E|/|ι|`. -/
theorem freeEnergy_high_temp_h_zero_sandwich_exp_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Fintype.card ι) :
    Real.log 2 +
        (G.edgeFinset.card : ℝ) / Fintype.card ι *
          Real.log (Real.cosh (β * J))
      ≤ freeEnergy G ⟨J, 0, β⟩ ∧
    freeEnergy G ⟨J, 0, β⟩
      ≤ Real.log 2 + β * J * G.edgeFinset.card / Fintype.card ι :=
  freeEnergy_high_temp_h_zero_sandwich_exp G J β
    (mul_nonneg hβ.le hJ) hne

/-- **Sharper f complete-summary bundle**: under `0 < |ι|` and
`0 ≤ β·J`, single statement bundling sharper sandwich + trivial-slice
values:
  1. `log 2 + (|E|/|ι|)·log cosh(β·J) ≤ f` (lower),
  2. `f ≤ log 2 + β·J·|E|/|ι|` (sharper exp upper),
  3. `f⟨0, 0, β⟩ = log 2` (J = 0 trivial slice),
  4. `f⟨J, 0, 0⟩ = log 2` (β = 0 trivial slice).
Useful as a single import for downstream applications. -/
theorem freeEnergy_high_temp_h_zero_complete_summary_exp
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Fintype.card ι) :
    Real.log 2 +
        (G.edgeFinset.card : ℝ) / Fintype.card ι *
          Real.log (Real.cosh (β * J))
      ≤ freeEnergy G ⟨J, 0, β⟩ ∧
    freeEnergy G ⟨J, 0, β⟩
      ≤ Real.log 2 + β * J * G.edgeFinset.card / Fintype.card ι ∧
    freeEnergy G (⟨0, 0, β⟩ : IsingParams ℝ) = Real.log 2 ∧
    freeEnergy G (⟨J, 0, 0⟩ : IsingParams ℝ) = Real.log 2 :=
  ⟨freeEnergy_high_temp_h_zero_lower_bound G J β hβJ hne,
   freeEnergy_high_temp_h_zero_upper_bound_exp G J β hβJ hne,
   by
     have := freeEnergy_J_zero G (0 : ℝ) β hne
     simpa [mul_zero, Real.cosh_zero] using this,
   freeEnergy_beta_zero G J 0 hne⟩

/-- **Ferromagnetic sharper f complete-summary exp bundle**: under
`0 < |ι|`, `0 ≤ J, 0 < β`. Bridges via `mul_nonneg hβ.le hJ`. -/
theorem freeEnergy_high_temp_h_zero_complete_summary_exp_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Fintype.card ι) :
    Real.log 2 +
        (G.edgeFinset.card : ℝ) / Fintype.card ι *
          Real.log (Real.cosh (β * J))
      ≤ freeEnergy G ⟨J, 0, β⟩ ∧
    freeEnergy G ⟨J, 0, β⟩
      ≤ Real.log 2 + β * J * G.edgeFinset.card / Fintype.card ι ∧
    freeEnergy G (⟨0, 0, β⟩ : IsingParams ℝ) = Real.log 2 ∧
    freeEnergy G (⟨J, 0, 0⟩ : IsingParams ℝ) = Real.log 2 :=
  freeEnergy_high_temp_h_zero_complete_summary_exp
    G J β (mul_nonneg hβ.le hJ) hne

/-- **Sharper f deviation bound from `log 2`**: under `0 < |ι|` and
`0 ≤ β·J`, `freeEnergy G ⟨J, 0, β⟩ - log 2 ≤ β·J·|E|/|ι|`.

Direct from `freeEnergy_high_temp_h_zero_upper_bound_exp` (Step 394) by
subtracting `log 2`. Quantitative high-temperature deviation estimate. -/
theorem freeEnergy_high_temp_h_zero_deviation_bound_exp
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Fintype.card ι) :
    freeEnergy G ⟨J, 0, β⟩ - Real.log 2
      ≤ β * J * G.edgeFinset.card / Fintype.card ι := by
  have h := freeEnergy_high_temp_h_zero_upper_bound_exp G J β hβJ hne
  linarith

/-- **f quantitative continuity at `J = 0` from deviation bound**:
under `0 ≤ β·J` and `0 < |ι|`,
`|f(J, 0, β) - f(0, 0, β)| ≤ β·J·|E|/|ι|`.

`f(0, 0, β) = log 2` from `freeEnergy_zero_params`, so the bound reads
`f - log 2 ≤ β·J·|E|/|ι|` (Step 420). The reverse direction
`f(0, 0, β) - f ≤ 0 ≤ β·J·|E|/|ι|` follows from the cosh-form lower
bound being non-negative under `0 ≤ β·J` (since `log cosh ≥ 0`).

Quantitative right-continuity: as `β·J → 0+` the deviation vanishes. -/
theorem freeEnergy_high_temp_h_zero_continuity_at_J_zero
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Fintype.card ι) :
    |freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨0, 0, β⟩ : IsingParams ℝ)|
      ≤ β * J * G.edgeFinset.card / Fintype.card ι := by
  have hf0 : freeEnergy G (⟨0, 0, β⟩ : IsingParams ℝ) = Real.log 2 := by
    have := freeEnergy_J_zero G (0 : ℝ) β hne
    simpa [mul_zero, Real.cosh_zero] using this
  rw [hf0]
  -- |f - log 2| ≤ β·J·|E|/|ι|
  have h_upper : freeEnergy G ⟨J, 0, β⟩ - Real.log 2
      ≤ β * J * G.edgeFinset.card / Fintype.card ι :=
    freeEnergy_high_temp_h_zero_deviation_bound_exp G J β hβJ hne
  have h_lower : Real.log 2 ≤ freeEnergy G ⟨J, 0, β⟩ := by
    -- log 2 ≤ log 2 + (|E|/|ι|)·log cosh(βJ) ≤ f, since log cosh ≥ 0
    have h_lb : Real.log 2 + (G.edgeFinset.card : ℝ) / Fintype.card ι *
          Real.log (Real.cosh (β * J)) ≤ freeEnergy G ⟨J, 0, β⟩ :=
      freeEnergy_high_temp_h_zero_lower_bound G J β hβJ hne
    have hcosh_ge : 1 ≤ Real.cosh (β * J) := Real.one_le_cosh _
    have hlog_nn : 0 ≤ Real.log (Real.cosh (β * J)) :=
      Real.log_nonneg hcosh_ge
    have hcard_pos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hne
    have hedge_nn : 0 ≤ ((G.edgeFinset.card : ℝ) / Fintype.card ι) :=
      div_nonneg (Nat.cast_nonneg _) hcard_pos.le
    have h_corr_nn : 0 ≤ ((G.edgeFinset.card : ℝ) / Fintype.card ι) *
          Real.log (Real.cosh (β * J)) := mul_nonneg hedge_nn hlog_nn
    linarith
  rw [abs_sub_le_iff]
  refine ⟨h_upper, ?_⟩
  have h_dev_nn : (0 : ℝ) ≤ β * J * G.edgeFinset.card / Fintype.card ι := by
    have hcard_pos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hne
    have hedge_nn : (0 : ℝ) ≤ G.edgeFinset.card := Nat.cast_nonneg _
    have h_num : 0 ≤ β * J * G.edgeFinset.card := mul_nonneg hβJ hedge_nn
    exact div_nonneg h_num hcard_pos.le
  linarith

/-- **f quantitative continuity at `β = 0` from deviation bound**:
under `0 ≤ β·J` and `0 < |ι|`,
`|f(J, 0, β) - f(J, 0, 0)| ≤ β·J·|E|/|ι|`.

`f(J, 0, 0) = log 2` from `freeEnergy_beta_zero`, so the bound is the
same as `f - log 2 ≤ β·J·|E|/|ι|` plus `0 ≤ f - log 2`. Quantitative
right-continuity at `β = 0`. -/
theorem freeEnergy_high_temp_h_zero_continuity_at_beta_zero
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Fintype.card ι) :
    |freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨J, 0, 0⟩ : IsingParams ℝ)|
      ≤ β * J * G.edgeFinset.card / Fintype.card ι := by
  rw [freeEnergy_beta_zero G J 0 hne]
  -- Same proof structure as continuity at J=0 since both trivial slices = log 2
  have h_upper : freeEnergy G ⟨J, 0, β⟩ - Real.log 2
      ≤ β * J * G.edgeFinset.card / Fintype.card ι :=
    freeEnergy_high_temp_h_zero_deviation_bound_exp G J β hβJ hne
  have h_lower : Real.log 2 ≤ freeEnergy G ⟨J, 0, β⟩ := by
    have h_lb : Real.log 2 + (G.edgeFinset.card : ℝ) / Fintype.card ι *
          Real.log (Real.cosh (β * J)) ≤ freeEnergy G ⟨J, 0, β⟩ :=
      freeEnergy_high_temp_h_zero_lower_bound G J β hβJ hne
    have hcosh_ge : 1 ≤ Real.cosh (β * J) := Real.one_le_cosh _
    have hlog_nn : 0 ≤ Real.log (Real.cosh (β * J)) :=
      Real.log_nonneg hcosh_ge
    have hcard_pos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hne
    have hedge_nn : 0 ≤ ((G.edgeFinset.card : ℝ) / Fintype.card ι) :=
      div_nonneg (Nat.cast_nonneg _) hcard_pos.le
    have h_corr_nn : 0 ≤ ((G.edgeFinset.card : ℝ) / Fintype.card ι) *
          Real.log (Real.cosh (β * J)) := mul_nonneg hedge_nn hlog_nn
    linarith
  rw [abs_sub_le_iff]
  refine ⟨h_upper, ?_⟩
  have hcard_pos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hne
  have hedge_nn : (0 : ℝ) ≤ G.edgeFinset.card := Nat.cast_nonneg _
  have h_num : 0 ≤ β * J * G.edgeFinset.card := mul_nonneg hβJ hedge_nn
  have h_dev_nn : (0 : ℝ) ≤ β * J * G.edgeFinset.card / Fintype.card ι :=
    div_nonneg h_num hcard_pos.le
  linarith

/-- **f continuity bundle at trivial slices**: under `0 ≤ β·J` and
`0 < |ι|`, single statement bundling continuity at both `J = 0` and
`β = 0` trivial slices. -/
theorem freeEnergy_high_temp_h_zero_continuity_bundle
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Fintype.card ι) :
    |freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨0, 0, β⟩ : IsingParams ℝ)|
        ≤ β * J * G.edgeFinset.card / Fintype.card ι ∧
    |freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨J, 0, 0⟩ : IsingParams ℝ)|
        ≤ β * J * G.edgeFinset.card / Fintype.card ι :=
  ⟨freeEnergy_high_temp_h_zero_continuity_at_J_zero G J β hβJ hne,
   freeEnergy_high_temp_h_zero_continuity_at_beta_zero G J β hβJ hne⟩

/-- **Ferromagnetic f continuity at `J = 0`**: under `0 ≤ J, 0 < β`
and `0 < |ι|`, `|f(J,0,β) - f(0,0,β)| ≤ β·J·|E|/|ι|`. -/
theorem freeEnergy_high_temp_h_zero_continuity_at_J_zero_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Fintype.card ι) :
    |freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨0, 0, β⟩ : IsingParams ℝ)|
      ≤ β * J * G.edgeFinset.card / Fintype.card ι :=
  freeEnergy_high_temp_h_zero_continuity_at_J_zero
    G J β (mul_nonneg hβ.le hJ) hne

/-- **Ferromagnetic f continuity at `β = 0`**: under `0 ≤ J, 0 < β`
and `0 < |ι|`, `|f(J,0,β) - f(J,0,0)| ≤ β·J·|E|/|ι|`. -/
theorem freeEnergy_high_temp_h_zero_continuity_at_beta_zero_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Fintype.card ι) :
    |freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨J, 0, 0⟩ : IsingParams ℝ)|
      ≤ β * J * G.edgeFinset.card / Fintype.card ι :=
  freeEnergy_high_temp_h_zero_continuity_at_beta_zero
    G J β (mul_nonneg hβ.le hJ) hne

/-- **Ferromagnetic f continuity bundle**: under `0 ≤ J, 0 < β` and
`0 < |ι|`, both `J = 0` and `β = 0` continuity bounds. -/
theorem freeEnergy_high_temp_h_zero_continuity_bundle_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Fintype.card ι) :
    |freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨0, 0, β⟩ : IsingParams ℝ)|
        ≤ β * J * G.edgeFinset.card / Fintype.card ι ∧
    |freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨J, 0, 0⟩ : IsingParams ℝ)|
        ≤ β * J * G.edgeFinset.card / Fintype.card ι :=
  freeEnergy_high_temp_h_zero_continuity_bundle
    G J β (mul_nonneg hβ.le hJ) hne

/-- **f deviation sandwich**: under `0 ≤ β·J` and `0 < |ι|`,
`0 ≤ f - log 2 ≤ β·J·|E|/|ι|`.

Combines the lower bound `log 2 ≤ f` (from Step 288 + `cosh ≥ 1`) with
the deviation bound `f - log 2 ≤ β·J·|E|/|ι|` (Step 420). Pins the
free-energy deviation from the trivial slice in a tight non-negative
linear interval. -/
theorem freeEnergy_high_temp_h_zero_deviation_sandwich
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Fintype.card ι) :
    0 ≤ freeEnergy G ⟨J, 0, β⟩ - Real.log 2 ∧
    freeEnergy G ⟨J, 0, β⟩ - Real.log 2
      ≤ β * J * G.edgeFinset.card / Fintype.card ι := by
  refine ⟨?_, freeEnergy_high_temp_h_zero_deviation_bound_exp G J β hβJ hne⟩
  have h_lb : Real.log 2 + (G.edgeFinset.card : ℝ) / Fintype.card ι *
        Real.log (Real.cosh (β * J)) ≤ freeEnergy G ⟨J, 0, β⟩ :=
    freeEnergy_high_temp_h_zero_lower_bound G J β hβJ hne
  have hcosh_ge : 1 ≤ Real.cosh (β * J) := Real.one_le_cosh _
  have hlog_nn : 0 ≤ Real.log (Real.cosh (β * J)) :=
    Real.log_nonneg hcosh_ge
  have hcard_pos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hne
  have hedge_nn : 0 ≤ ((G.edgeFinset.card : ℝ) / Fintype.card ι) :=
    div_nonneg (Nat.cast_nonneg _) hcard_pos.le
  have h_corr_nn : 0 ≤ ((G.edgeFinset.card : ℝ) / Fintype.card ι) *
        Real.log (Real.cosh (β * J)) := mul_nonneg hedge_nn hlog_nn
  linarith

/-- **Ferromagnetic f deviation sandwich**: under `0 ≤ J, 0 < β`
and `0 < |ι|`, `0 ≤ f - log 2 ≤ β·J·|E|/|ι|`. -/
theorem freeEnergy_high_temp_h_zero_deviation_sandwich_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Fintype.card ι) :
    0 ≤ freeEnergy G ⟨J, 0, β⟩ - Real.log 2 ∧
    freeEnergy G ⟨J, 0, β⟩ - Real.log 2
      ≤ β * J * G.edgeFinset.card / Fintype.card ι :=
  freeEnergy_high_temp_h_zero_deviation_sandwich
    G J β (mul_nonneg hβ.le hJ) hne

/-- **Ferromagnetic log Z deviation sandwich**: under `0 ≤ J, 0 < β`,
`0 ≤ log Z - |ι|·log 2 ≤ β·J·|E|`. -/
theorem log_partitionFunction_high_temp_expansion_h_zero_deviation_sandwich_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    0 ≤ Real.log (partitionFunction G ⟨J, 0, β⟩)
        - (Fintype.card ι : ℝ) * Real.log 2 ∧
    Real.log (partitionFunction G ⟨J, 0, β⟩)
        - (Fintype.card ι : ℝ) * Real.log 2
      ≤ β * J * G.edgeFinset.card :=
  log_partitionFunction_high_temp_expansion_h_zero_deviation_sandwich
    G J β (mul_nonneg hβ.le hJ)

/-- **f strict deviation under non-trivial high-temperature**: under
`0 < β·J`, `0 < |ι|`, and `0 < |E|`, `0 < f - log 2`.

Strengthens Step 433 lower bound (`0 ≤ f - log 2`) to strict
positivity at non-trivial parameters. Follows from the lower bound
`log 2 + (|E|/|ι|)·log cosh(β·J) ≤ f` plus `log cosh(β·J) > 0` (since
`cosh(β·J) > 1` when `β·J ≠ 0`) plus `|E|/|ι| > 0`. -/
theorem freeEnergy_high_temp_h_zero_deviation_pos
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 < β * J) (hne : 0 < Fintype.card ι)
    (hEpos : 0 < G.edgeFinset.card) :
    0 < freeEnergy G ⟨J, 0, β⟩ - Real.log 2 := by
  have h_lb : Real.log 2 + (G.edgeFinset.card : ℝ) / Fintype.card ι *
        Real.log (Real.cosh (β * J)) ≤ freeEnergy G ⟨J, 0, β⟩ :=
    freeEnergy_high_temp_h_zero_lower_bound G J β hβJ.le hne
  have hcosh_gt : 1 < Real.cosh (β * J) := by
    rw [show (1 : ℝ) = Real.cosh 0 from Real.cosh_zero.symm]
    refine Real.cosh_lt_cosh.mpr ?_
    rw [abs_zero, abs_of_pos hβJ]
    exact hβJ
  have hlog_pos : 0 < Real.log (Real.cosh (β * J)) := Real.log_pos hcosh_gt
  have hcard_pos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hne
  have hE_pos : (0 : ℝ) < G.edgeFinset.card := by exact_mod_cast hEpos
  have hratio_pos : 0 < (G.edgeFinset.card : ℝ) / Fintype.card ι :=
    div_pos hE_pos hcard_pos
  have h_corr_pos : 0 < ((G.edgeFinset.card : ℝ) / Fintype.card ι) *
        Real.log (Real.cosh (β * J)) := mul_pos hratio_pos hlog_pos
  linarith

/-- **Ferromagnetic f strict deviation**: under `0 < J, 0 < β`,
`0 < |ι|`, `0 < |E|`, `0 < f - log 2`. -/
theorem freeEnergy_high_temp_h_zero_deviation_pos_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 < J) (hβ : 0 < β) (hne : 0 < Fintype.card ι)
    (hEpos : 0 < G.edgeFinset.card) :
    0 < freeEnergy G ⟨J, 0, β⟩ - Real.log 2 :=
  freeEnergy_high_temp_h_zero_deviation_pos
    G J β (mul_pos hβ hJ) hne hEpos

/-- **f ratio bound at J=0 trivial slice**: under `0 ≤ β·J` and
`0 < |ι|`, `f(G; J, 0, β) - f(G; 0, 0, β) ≤ β·J·|E|/|ι|`.

Equivalent reformulation of the f deviation bound using the trivial
slice `f(0, 0, β) = log 2`. -/
theorem freeEnergy_high_temp_h_zero_ratio_bound
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Fintype.card ι) :
    freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨0, 0, β⟩ : IsingParams ℝ)
      ≤ β * J * G.edgeFinset.card / Fintype.card ι := by
  have hf0 : freeEnergy G (⟨0, 0, β⟩ : IsingParams ℝ) = Real.log 2 := by
    have := freeEnergy_J_zero G (0 : ℝ) β hne
    simpa [mul_zero, Real.cosh_zero] using this
  rw [hf0]
  exact freeEnergy_high_temp_h_zero_deviation_bound_exp G J β hβJ hne

/-- **f ratio bound at β=0 trivial slice**. -/
theorem freeEnergy_high_temp_h_zero_ratio_bound_beta_zero
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Fintype.card ι) :
    freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨J, 0, 0⟩ : IsingParams ℝ)
      ≤ β * J * G.edgeFinset.card / Fintype.card ι := by
  rw [freeEnergy_beta_zero G J 0 hne]
  exact freeEnergy_high_temp_h_zero_deviation_bound_exp G J β hβJ hne

/-- **f ratio bound bundle**: under `0 ≤ β·J` and `0 < |ι|`, single
statement bundling f ratio bounds at both J=0 and β=0 trivial slices. -/
theorem freeEnergy_high_temp_h_zero_ratio_bound_bundle
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Fintype.card ι) :
    freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨0, 0, β⟩ : IsingParams ℝ)
        ≤ β * J * G.edgeFinset.card / Fintype.card ι ∧
    freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨J, 0, 0⟩ : IsingParams ℝ)
        ≤ β * J * G.edgeFinset.card / Fintype.card ι :=
  ⟨freeEnergy_high_temp_h_zero_ratio_bound G J β hβJ hne,
   freeEnergy_high_temp_h_zero_ratio_bound_beta_zero G J β hβJ hne⟩

/-- **Ferromagnetic f ratio bound at J=0**. -/
theorem freeEnergy_high_temp_h_zero_ratio_bound_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Fintype.card ι) :
    freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨0, 0, β⟩ : IsingParams ℝ)
      ≤ β * J * G.edgeFinset.card / Fintype.card ι :=
  freeEnergy_high_temp_h_zero_ratio_bound G J β (mul_nonneg hβ.le hJ) hne

/-- **Ferromagnetic f ratio bound at β=0**. -/
theorem freeEnergy_high_temp_h_zero_ratio_bound_beta_zero_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Fintype.card ι) :
    freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨J, 0, 0⟩ : IsingParams ℝ)
      ≤ β * J * G.edgeFinset.card / Fintype.card ι :=
  freeEnergy_high_temp_h_zero_ratio_bound_beta_zero
    G J β (mul_nonneg hβ.le hJ) hne

/-- **f ratio sandwich at J=0 trivial slice**: under `0 ≤ β·J` and
`0 < |ι|`, `(|E|/|ι|)·log cosh(β·J) ≤ f⟨J,0,β⟩ - f⟨0,0,β⟩ ≤ β·J·|E|/|ι|`. -/
theorem freeEnergy_high_temp_h_zero_ratio_sandwich
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Fintype.card ι) :
    (G.edgeFinset.card : ℝ) / Fintype.card ι * Real.log (Real.cosh (β * J))
        ≤ freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨0, 0, β⟩ : IsingParams ℝ) ∧
    freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨0, 0, β⟩ : IsingParams ℝ)
        ≤ β * J * G.edgeFinset.card / Fintype.card ι := by
  have hf0 : freeEnergy G (⟨0, 0, β⟩ : IsingParams ℝ) = Real.log 2 := by
    have := freeEnergy_J_zero G (0 : ℝ) β hne
    simpa [mul_zero, Real.cosh_zero] using this
  rw [hf0]
  refine ⟨?_, ?_⟩
  · linarith [freeEnergy_high_temp_h_zero_lower_bound G J β hβJ hne]
  · exact freeEnergy_high_temp_h_zero_deviation_bound_exp G J β hβJ hne

/-- **f ratio sandwich at β=0 trivial slice**. -/
theorem freeEnergy_high_temp_h_zero_ratio_sandwich_beta_zero
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Fintype.card ι) :
    (G.edgeFinset.card : ℝ) / Fintype.card ι * Real.log (Real.cosh (β * J))
        ≤ freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨J, 0, 0⟩ : IsingParams ℝ) ∧
    freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨J, 0, 0⟩ : IsingParams ℝ)
        ≤ β * J * G.edgeFinset.card / Fintype.card ι := by
  rw [freeEnergy_beta_zero G J 0 hne]
  refine ⟨?_, ?_⟩
  · linarith [freeEnergy_high_temp_h_zero_lower_bound G J β hβJ hne]
  · exact freeEnergy_high_temp_h_zero_deviation_bound_exp G J β hβJ hne

/-- **f ratio sandwich bundle**: bundles both J=0 and β=0 sandwiches. -/
theorem freeEnergy_high_temp_h_zero_ratio_sandwich_bundle
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Fintype.card ι) :
    ((G.edgeFinset.card : ℝ) / Fintype.card ι * Real.log (Real.cosh (β * J))
        ≤ freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨0, 0, β⟩ : IsingParams ℝ) ∧
      freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨0, 0, β⟩ : IsingParams ℝ)
        ≤ β * J * G.edgeFinset.card / Fintype.card ι) ∧
    ((G.edgeFinset.card : ℝ) / Fintype.card ι * Real.log (Real.cosh (β * J))
        ≤ freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨J, 0, 0⟩ : IsingParams ℝ) ∧
      freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨J, 0, 0⟩ : IsingParams ℝ)
        ≤ β * J * G.edgeFinset.card / Fintype.card ι) :=
  ⟨freeEnergy_high_temp_h_zero_ratio_sandwich G J β hβJ hne,
   freeEnergy_high_temp_h_zero_ratio_sandwich_beta_zero G J β hβJ hne⟩

/-- **Ferromagnetic f ratio sandwich bundle**. -/
theorem freeEnergy_high_temp_h_zero_ratio_sandwich_bundle_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Fintype.card ι) :
    ((G.edgeFinset.card : ℝ) / Fintype.card ι * Real.log (Real.cosh (β * J))
        ≤ freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨0, 0, β⟩ : IsingParams ℝ) ∧
      freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨0, 0, β⟩ : IsingParams ℝ)
        ≤ β * J * G.edgeFinset.card / Fintype.card ι) ∧
    ((G.edgeFinset.card : ℝ) / Fintype.card ι * Real.log (Real.cosh (β * J))
        ≤ freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨J, 0, 0⟩ : IsingParams ℝ) ∧
      freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨J, 0, 0⟩ : IsingParams ℝ)
        ≤ β * J * G.edgeFinset.card / Fintype.card ι) :=
  freeEnergy_high_temp_h_zero_ratio_sandwich_bundle
    G J β (mul_nonneg hβ.le hJ) hne

/-- **Ferromagnetic f ratio bound bundle**. -/
theorem freeEnergy_high_temp_h_zero_ratio_bound_bundle_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Fintype.card ι) :
    freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨0, 0, β⟩ : IsingParams ℝ)
        ≤ β * J * G.edgeFinset.card / Fintype.card ι ∧
    freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨J, 0, 0⟩ : IsingParams ℝ)
        ≤ β * J * G.edgeFinset.card / Fintype.card ι :=
  freeEnergy_high_temp_h_zero_ratio_bound_bundle
    G J β (mul_nonneg hβ.le hJ) hne

/-- **Triple ratio sandwich bundle at J=0 trivial slice**: under `0 ≤ β·J`
and `0 < |ι|`, single statement bundling Z, log Z, and f ratio sandwiches
at the J=0 slice. -/
theorem partitionFunction_high_temp_expansion_h_zero_triple_ratio_sandwich_bundle
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Fintype.card ι) :
    (Real.cosh (β * J) ^ G.edgeFinset.card
        ≤ partitionFunction G ⟨J, 0, β⟩ /
            partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ) ∧
      partitionFunction G ⟨J, 0, β⟩ /
          partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ)
          ≤ Real.exp (β * J * G.edgeFinset.card)) ∧
    ((G.edgeFinset.card : ℝ) * Real.log (Real.cosh (β * J))
        ≤ Real.log (partitionFunction G ⟨J, 0, β⟩)
            - Real.log (partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ)) ∧
      Real.log (partitionFunction G ⟨J, 0, β⟩)
          - Real.log (partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ))
          ≤ β * J * G.edgeFinset.card) ∧
    ((G.edgeFinset.card : ℝ) / Fintype.card ι * Real.log (Real.cosh (β * J))
        ≤ freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨0, 0, β⟩ : IsingParams ℝ) ∧
      freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨0, 0, β⟩ : IsingParams ℝ)
        ≤ β * J * G.edgeFinset.card / Fintype.card ι) :=
  ⟨partitionFunction_high_temp_expansion_h_zero_ratio_sandwich G J β hβJ,
   log_partitionFunction_high_temp_expansion_h_zero_ratio_sandwich G J β hβJ,
   freeEnergy_high_temp_h_zero_ratio_sandwich G J β hβJ hne⟩

/-- **Triple ratio sandwich bundle at β=0 trivial slice**. -/
theorem partitionFunction_high_temp_expansion_h_zero_triple_ratio_sandwich_bundle_beta_zero
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Fintype.card ι) :
    (Real.cosh (β * J) ^ G.edgeFinset.card
        ≤ partitionFunction G ⟨J, 0, β⟩ /
            partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ) ∧
      partitionFunction G ⟨J, 0, β⟩ /
          partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ)
          ≤ Real.exp (β * J * G.edgeFinset.card)) ∧
    ((G.edgeFinset.card : ℝ) * Real.log (Real.cosh (β * J))
        ≤ Real.log (partitionFunction G ⟨J, 0, β⟩)
            - Real.log (partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ)) ∧
      Real.log (partitionFunction G ⟨J, 0, β⟩)
          - Real.log (partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ))
          ≤ β * J * G.edgeFinset.card) ∧
    ((G.edgeFinset.card : ℝ) / Fintype.card ι * Real.log (Real.cosh (β * J))
        ≤ freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨J, 0, 0⟩ : IsingParams ℝ) ∧
      freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨J, 0, 0⟩ : IsingParams ℝ)
        ≤ β * J * G.edgeFinset.card / Fintype.card ι) :=
  ⟨partitionFunction_high_temp_expansion_h_zero_ratio_sandwich_beta_zero
     G J β hβJ,
   log_partitionFunction_high_temp_expansion_h_zero_ratio_sandwich_beta_zero
     G J β hβJ,
   freeEnergy_high_temp_h_zero_ratio_sandwich_beta_zero G J β hβJ hne⟩

/-- **Ferromagnetic triple ratio sandwich bundle at J=0**. -/
theorem partitionFunction_high_temp_expansion_h_zero_triple_ratio_sandwich_bundle_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Fintype.card ι) :
    (Real.cosh (β * J) ^ G.edgeFinset.card
        ≤ partitionFunction G ⟨J, 0, β⟩ /
            partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ) ∧
      partitionFunction G ⟨J, 0, β⟩ /
          partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ)
          ≤ Real.exp (β * J * G.edgeFinset.card)) ∧
    ((G.edgeFinset.card : ℝ) * Real.log (Real.cosh (β * J))
        ≤ Real.log (partitionFunction G ⟨J, 0, β⟩)
            - Real.log (partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ)) ∧
      Real.log (partitionFunction G ⟨J, 0, β⟩)
          - Real.log (partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ))
          ≤ β * J * G.edgeFinset.card) ∧
    ((G.edgeFinset.card : ℝ) / Fintype.card ι * Real.log (Real.cosh (β * J))
        ≤ freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨0, 0, β⟩ : IsingParams ℝ) ∧
      freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨0, 0, β⟩ : IsingParams ℝ)
        ≤ β * J * G.edgeFinset.card / Fintype.card ι) :=
  partitionFunction_high_temp_expansion_h_zero_triple_ratio_sandwich_bundle
    G J β (mul_nonneg hβ.le hJ) hne

/-- **Ferromagnetic triple ratio sandwich bundle at β=0**. -/
theorem
partitionFunction_high_temp_expansion_h_zero_triple_ratio_sandwich_bundle_beta_zero_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Fintype.card ι) :
    (Real.cosh (β * J) ^ G.edgeFinset.card
        ≤ partitionFunction G ⟨J, 0, β⟩ /
            partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ) ∧
      partitionFunction G ⟨J, 0, β⟩ /
          partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ)
          ≤ Real.exp (β * J * G.edgeFinset.card)) ∧
    ((G.edgeFinset.card : ℝ) * Real.log (Real.cosh (β * J))
        ≤ Real.log (partitionFunction G ⟨J, 0, β⟩)
            - Real.log (partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ)) ∧
      Real.log (partitionFunction G ⟨J, 0, β⟩)
          - Real.log (partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ))
          ≤ β * J * G.edgeFinset.card) ∧
    ((G.edgeFinset.card : ℝ) / Fintype.card ι * Real.log (Real.cosh (β * J))
        ≤ freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨J, 0, 0⟩ : IsingParams ℝ) ∧
      freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨J, 0, 0⟩ : IsingParams ℝ)
        ≤ β * J * G.edgeFinset.card / Fintype.card ι) :=
  partitionFunction_high_temp_expansion_h_zero_triple_ratio_sandwich_bundle_beta_zero
    G J β (mul_nonneg hβ.le hJ) hne

/-- **Triple ratio bound bundle at J=0 trivial slice**: under `0 ≤ β·J`
and `0 < |ι|`, single statement bundling Z, log Z, and f ratio bounds:
  1. `Z⟨J,0,β⟩ / Z⟨0,0,β⟩ ≤ exp(β·J·|E|)`,
  2. `log Z⟨J,0,β⟩ - log Z⟨0,0,β⟩ ≤ β·J·|E|`,
  3. `f⟨J,0,β⟩ - f⟨0,0,β⟩ ≤ β·J·|E|/|ι|`. -/
theorem partitionFunction_high_temp_expansion_h_zero_triple_ratio_bound_bundle
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Fintype.card ι) :
    partitionFunction G ⟨J, 0, β⟩ /
        partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ)
        ≤ Real.exp (β * J * G.edgeFinset.card) ∧
    Real.log (partitionFunction G ⟨J, 0, β⟩)
        - Real.log (partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ))
        ≤ β * J * G.edgeFinset.card ∧
    freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨0, 0, β⟩ : IsingParams ℝ)
        ≤ β * J * G.edgeFinset.card / Fintype.card ι :=
  ⟨partitionFunction_high_temp_expansion_h_zero_ratio_bound G J β hβJ,
   log_partitionFunction_high_temp_expansion_h_zero_ratio_bound G J β hβJ,
   freeEnergy_high_temp_h_zero_ratio_bound G J β hβJ hne⟩

/-- **Triple ratio bound bundle at β=0 trivial slice**. -/
theorem partitionFunction_high_temp_expansion_h_zero_triple_ratio_bound_bundle_beta_zero
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Fintype.card ι) :
    partitionFunction G ⟨J, 0, β⟩ /
        partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ)
        ≤ Real.exp (β * J * G.edgeFinset.card) ∧
    Real.log (partitionFunction G ⟨J, 0, β⟩)
        - Real.log (partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ))
        ≤ β * J * G.edgeFinset.card ∧
    freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨J, 0, 0⟩ : IsingParams ℝ)
        ≤ β * J * G.edgeFinset.card / Fintype.card ι :=
  ⟨partitionFunction_high_temp_expansion_h_zero_ratio_bound_beta_zero G J β hβJ,
   log_partitionFunction_high_temp_expansion_h_zero_ratio_bound_beta_zero
     G J β hβJ,
   freeEnergy_high_temp_h_zero_ratio_bound_beta_zero G J β hβJ hne⟩

/-- **Ferromagnetic triple ratio bound bundle at J=0**. -/
theorem partitionFunction_high_temp_expansion_h_zero_triple_ratio_bound_bundle_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Fintype.card ι) :
    partitionFunction G ⟨J, 0, β⟩ /
        partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ)
        ≤ Real.exp (β * J * G.edgeFinset.card) ∧
    Real.log (partitionFunction G ⟨J, 0, β⟩)
        - Real.log (partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ))
        ≤ β * J * G.edgeFinset.card ∧
    freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨0, 0, β⟩ : IsingParams ℝ)
        ≤ β * J * G.edgeFinset.card / Fintype.card ι :=
  partitionFunction_high_temp_expansion_h_zero_triple_ratio_bound_bundle
    G J β (mul_nonneg hβ.le hJ) hne

/-- **Ferromagnetic triple ratio bound bundle at β=0**. -/
theorem
partitionFunction_high_temp_expansion_h_zero_triple_ratio_bound_bundle_beta_zero_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Fintype.card ι) :
    partitionFunction G ⟨J, 0, β⟩ /
        partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ)
        ≤ Real.exp (β * J * G.edgeFinset.card) ∧
    Real.log (partitionFunction G ⟨J, 0, β⟩)
        - Real.log (partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ))
        ≤ β * J * G.edgeFinset.card ∧
    freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨J, 0, 0⟩ : IsingParams ℝ)
        ≤ β * J * G.edgeFinset.card / Fintype.card ι :=
  partitionFunction_high_temp_expansion_h_zero_triple_ratio_bound_bundle_beta_zero
    G J β (mul_nonneg hβ.le hJ) hne

/-- **Strict deviation bundle**: under `0 < β·J`, `0 < |E|`,
`0 < |ι|`, single statement bundling Z, log Z, and f strict deviations. -/
theorem partitionFunction_high_temp_expansion_h_zero_strict_deviation_bundle
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 < β * J) (hne : 0 < Fintype.card ι)
    (hEpos : 0 < G.edgeFinset.card) :
    (2 : ℝ) ^ Fintype.card ι < partitionFunction G ⟨J, 0, β⟩ ∧
    0 < Real.log (partitionFunction G ⟨J, 0, β⟩)
        - (Fintype.card ι : ℝ) * Real.log 2 ∧
    0 < freeEnergy G ⟨J, 0, β⟩ - Real.log 2 :=
  ⟨partitionFunction_high_temp_expansion_h_zero_pow_two_lt G J β hβJ hEpos,
   log_partitionFunction_high_temp_expansion_h_zero_deviation_pos
     G J β hβJ hEpos,
   freeEnergy_high_temp_h_zero_deviation_pos G J β hβJ hne hEpos⟩

/-- **Ferromagnetic sharper f deviation bound**: under `0 ≤ J, 0 < β`
and `0 < |ι|`, `f - log 2 ≤ β·J·|E|/|ι|`. Bridges via
`mul_nonneg hβ.le hJ`. -/
theorem freeEnergy_high_temp_h_zero_deviation_bound_exp_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Fintype.card ι) :
    freeEnergy G ⟨J, 0, β⟩ - Real.log 2
      ≤ β * J * G.edgeFinset.card / Fintype.card ι :=
  freeEnergy_high_temp_h_zero_deviation_bound_exp
    G J β (mul_nonneg hβ.le hJ) hne

/-- **Free-energy high-temperature expansion decomposition (GJ §18.3 / FV (3.45))**:
under `0 < |ι|` and `0 ≤ β·J`,
`freeEnergy(G; J, 0, β) = log 2 + (|E|/|ι|) · log(cosh βJ) + log(∑_{X even} tanh^|X|) / |ι|`.

Direct corollary of `log_partitionFunction_high_temp_expansion_h_zero_closed`
(Step 315) by dividing by `|ι|`. The first two terms recover the
graph-aware lower bound `freeEnergy_high_temp_h_zero_lower_bound`
(Step 288); the third (the `log ∑` term) is the residual contribution
absent from the bound. -/
theorem freeEnergy_high_temp_expansion_h_zero_closed
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Fintype.card ι) :
    freeEnergy G ⟨J, 0, β⟩
      = Real.log 2
        + (G.edgeFinset.card : ℝ) / Fintype.card ι *
            Real.log (Real.cosh (β * J))
        + Real.log
            (∑ X ∈ G.edgeFinset.powerset.filter
                (fun X : Finset (Sym2 ι) =>
                  ∀ v : ι, Even ((X.filter (v ∈ ·)).card)),
              Real.tanh (β * J) ^ X.card) / Fintype.card ι := by
  unfold freeEnergy
  rw [log_partitionFunction_high_temp_expansion_h_zero_closed G J β hβJ]
  have hι_ne : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast hne.ne'
  field_simp

/-- **freeEnergy high-temperature sandwich bounds (GJ §18.3 / FV (3.45))**:
under `0 < |ι|` and `0 ≤ β·J`,
`log 2 + (|E|/|ι|) · log(cosh βJ) ≤ f(G; J, 0, β) ≤ log 2 + (|E|/|ι|) · log(2 · cosh βJ)`.
Combines `freeEnergy_high_temp_h_zero_lower_bound` (Step 288) and
`freeEnergy_high_temp_h_zero_upper_bound` (Step 322). -/
theorem freeEnergy_high_temp_h_zero_sandwich
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Fintype.card ι) :
    Real.log 2 +
        (G.edgeFinset.card : ℝ) / Fintype.card ι *
          Real.log (Real.cosh (β * J))
      ≤ freeEnergy G ⟨J, 0, β⟩
    ∧ freeEnergy G ⟨J, 0, β⟩
      ≤ Real.log 2
        + (G.edgeFinset.card : ℝ) / Fintype.card ι *
            Real.log (2 * Real.cosh (β * J)) :=
  ⟨freeEnergy_high_temp_h_zero_lower_bound G J β hβJ hne,
   freeEnergy_high_temp_h_zero_upper_bound G J β hβJ hne⟩

omit [DecidableEq ι] in
/-- **freeEnergy high-temp bounds consistency**: the FV (3.45) lower
bound is always at most the upper bound:
`log 2 + (|E|/|ι|) · log cosh(βJ) ≤ log 2 + (|E|/|ι|) · log(2·cosh βJ)`.

Trivial sanity check: `log cosh ≤ log(2·cosh) = log 2 + log cosh`,
i.e., `log 2 ≥ 0`. -/
theorem freeEnergy_high_temp_h_zero_lower_le_upper
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℝ) (_hβJ : 0 ≤ β * J) :
    Real.log 2 +
        (G.edgeFinset.card : ℝ) / Fintype.card ι *
          Real.log (Real.cosh (β * J))
      ≤ Real.log 2
        + (G.edgeFinset.card : ℝ) / Fintype.card ι *
            Real.log (2 * Real.cosh (β * J)) := by
  have hcosh_pos : 0 < Real.cosh (β * J) := Real.cosh_pos _
  have hlog_le : Real.log (Real.cosh (β * J)) ≤ Real.log (2 * Real.cosh (β * J)) := by
    apply Real.log_le_log hcosh_pos
    linarith [Real.one_le_cosh (β * J)]
  have hcoeff_nn : (0 : ℝ) ≤
      (G.edgeFinset.card : ℝ) / Fintype.card ι := by positivity
  linarith [mul_le_mul_of_nonneg_left hlog_le hcoeff_nn]


end IsingModel
