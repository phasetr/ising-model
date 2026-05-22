import IsingModel.Conditioning.HighTempExpansion

/-!
# High-temperature closed forms

Mechanical child split from `Conditioning/HighTempClosed.lean`.
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


end IsingModel
