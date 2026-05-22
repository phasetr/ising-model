import IsingModel.RandomCurrent.Core

/-!
# Bounded random-current finite sums

Mechanical child split from `RandomCurrent/BoundedExpansion.lean`.
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

abbrev CurrentBounded (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (N : ℕ) :=
  (e : (inducedGraph G Λ).edgeSet) → Fin (N + 1)

/-- **Coercion `CurrentBounded → Current`**: forget the bound
on each edge value. -/
def CurrentBounded.toCurrent (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] {N : ℕ}
    (n : CurrentBounded G Λ N) : Current G Λ :=
  fun e => (n e).val

/-- **Finite weight sum over A-source bounded currents**:
`∑ n : CurrentBounded G Λ N, if n.toCurrent.sources = A then n.toCurrent.weight β J else 0`.
Unlike `Current.weightSum` (which uses `tsum`), this is a plain
`Finset.sum` since `CurrentBounded G Λ N` is automatically
`Fintype`. Used as the truncated approximant; the limit
`N → ∞` gives the unbounded `Current.weightSum`. -/
noncomputable def CurrentBounded.weightSum (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (N : ℕ) (A : Finset ↑Λ) (β J : ℝ) : ℝ :=
  ∑ n : CurrentBounded G Λ N,
    if (n.toCurrent G Λ).sources G Λ = A
      then (n.toCurrent G Λ).weight G Λ β J
      else 0

omit [DecidableEq V] in
/-- **Bounded weight sum is nonneg under nonneg coupling**: each
summand is either `0` or a nonneg weight; `Finset.sum_nonneg`
finishes. -/
theorem CurrentBounded.weightSum_nonneg (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (N : ℕ) (A : Finset ↑Λ) {β J : ℝ} (hβJ : 0 ≤ β * J) :
    0 ≤ CurrentBounded.weightSum G Λ N A β J := by
  unfold CurrentBounded.weightSum
  refine Finset.sum_nonneg (fun n _ => ?_)
  by_cases h : (n.toCurrent G Λ).sources G Λ = A
  · simp [h, Current.weight_nonneg G Λ hβJ (n.toCurrent G Λ)]
  · simp [h]

/-- **Spin sum of `toSign` powers**: for any `k : ℕ`,
`∑ s : Spin, ((s.toSign : ℝ))^k = 2` if `k` is even, else `0`.
This is the elementary spin-sum identity that drives the
random-current expansion of `Z` and `⟨σ_A⟩^Λ`: summing over a
single spin gives `2` (when the cumulative power is even) or `0`
(when odd). -/
theorem Spin.sum_toSign_pow_real (k : ℕ) :
    (∑ s : Spin, ((s.toSign : ℝ))^k) = if Even k then 2 else 0 := by
  have hu : (Finset.univ : Finset Spin) = {Spin.up, Spin.down} := by decide
  rw [hu, Finset.sum_pair (by decide : Spin.up ≠ Spin.down)]
  have hup : ((Spin.up.toSign : ℤ) : ℝ) = 1 := by simp [Spin.toSign]
  have hdown : ((Spin.down.toSign : ℤ) : ℝ) = -1 := by simp [Spin.toSign]
  rw [hup, hdown, one_pow]
  by_cases hk : Even k
  · rw [if_pos hk, hk.neg_one_pow]; norm_num
  · rw [if_neg hk]
    have hodd : Odd k := Nat.not_even_iff_odd.mp hk
    rw [hodd.neg_one_pow]; norm_num

/-- **Multi-vertex spin sum**: for any `k : ι → ℕ` on a Fintype `ι`,
`∑ σ : ι → Spin, ∏ v : ι, ((σ v).toSign : ℝ)^(k v) = 2^(Fintype.card ι)`
when every `k v` is even, else `0`. The Fubini-style sum-product
swap reduces to per-vertex sums (`Spin.sum_toSign_pow_real`); each
factor is `2` (even exponent) or `0` (odd exponent), so the product
is `2^|ι|` when all even, else `0`. The central spin-sum step of
the random-current expansion (FV §3.7). -/
theorem Config.sum_prod_toSign_pow_real {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ι → ℕ) :
    (∑ σ : ι → Spin, ∏ v : ι, ((σ v).toSign : ℝ)^(k v))
      = if ∀ v : ι, Even (k v) then 2^(Fintype.card ι) else 0 := by
  have hfubini : (∑ σ : ι → Spin, ∏ v : ι, ((σ v).toSign : ℝ)^(k v))
      = ∏ v : ι, ∑ s : Spin, ((s.toSign : ℝ))^(k v) :=
    (Fintype.prod_sum (κ := fun _ => Spin)
      (fun v s => ((s.toSign : ℝ))^(k v))).symm
  rw [hfubini]
  simp_rw [Spin.sum_toSign_pow_real]
  -- Goal: ∏ v, (if Even (k v) then 2 else 0) = if (∀ v, Even (k v)) then 2^|ι| else 0
  by_cases h : ∀ v : ι, Even (k v)
  · rw [if_pos h]
    rw [Finset.prod_congr rfl (fun v _ => if_pos (h v))]
    simp [Finset.prod_const, Finset.card_univ]
  · rw [if_neg h]
    push Not at h
    obtain ⟨v, hv⟩ := h
    refine Finset.prod_eq_zero (Finset.mem_univ v) ?_
    rw [if_neg hv]

/-- **Sum of `spinProduct A`**: for any Finset `A`,
`∑ σ : ι → Spin, spinProduct A σ = 2^(Fintype.card ι)` if `A = ∅`,
else `0`. The basic spin-sum identity feeding into the
random-current expansion of `Z = ∑_σ exp(-βH)` and
`⟨σ_A⟩^Λ = (∑_σ σ^A · exp(-βH)) / Z` (FV §3.7). Direct corollary
of `Config.sum_prod_toSign_pow_real` with the indicator exponent
`k v := if v ∈ A then 1 else 0`. -/
theorem Config.sum_spinProduct {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Finset ι) :
    (∑ σ : ι → Spin, IsingModel.spinProduct A σ)
      = if A = ∅ then 2^(Fintype.card ι) else 0 := by
  have hrw : ∀ σ : ι → Spin, IsingModel.spinProduct A σ
      = ∏ v : ι, ((σ v).toSign : ℝ)^(if v ∈ A then 1 else 0) := by
    intro σ
    unfold IsingModel.spinProduct
    rw [show (A : Finset ι) = (Finset.univ : Finset ι).filter (· ∈ A) by
      ext v; simp]
    rw [Finset.prod_filter]
    refine Finset.prod_congr rfl (fun v _ => ?_)
    by_cases hv : v ∈ A
    · simp [hv]
    · simp [hv]
  simp_rw [hrw]
  rw [Config.sum_prod_toSign_pow_real]
  -- Goal: if (∀ v, Even (if v ∈ A then 1 else 0)) then 2^|ι| else 0 = if A = ∅ then 2^|ι| else 0
  congr 1
  refine propext ?_
  constructor
  · intro h
    ext v
    simp only [Finset.notMem_empty, iff_false]
    intro hv
    have := h v
    rw [if_pos hv] at this
    exact (Nat.not_even_one this).elim
  · intro hAempty v
    by_cases hv : v ∈ A
    · rw [hAempty] at hv
      exact absurd hv (Finset.notMem_empty v)
    · rw [if_neg hv]
      exact ⟨0, rfl⟩

/-- **Edge-subset current**: the current that takes value `1` on
edges in `S` and `0` elsewhere. The basic 0/1 currents that
form the underlying combinatorial substrate of the random-current
sum (each finite-support current is a sum of indicator currents
weighted by edge multiplicities). -/
def Current.fromEdgeFinset (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (S : Finset (inducedGraph G Λ).edgeSet) : Current G Λ :=
  fun e => if e ∈ S then 1 else 0

omit [DecidableEq V] in
/-- **`fromEdgeFinset` of empty set is the zero current**. -/
@[simp]
theorem Current.fromEdgeFinset_empty (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ] :
    Current.fromEdgeFinset G Λ (∅ : Finset (inducedGraph G Λ).edgeSet)
      = (0 : Current G Λ) := by
  funext e
  simp [Current.fromEdgeFinset]

omit [DecidableEq V] in
/-- **Weight of `fromEdgeFinset S`**: equals `(β J)^(S.card)`
since each edge in `S` contributes `(β J)^1 / 1! = β J` and each
edge outside `S` contributes `(β J)^0 / 0! = 1`. -/
theorem Current.fromEdgeFinset_weight (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (S : Finset (inducedGraph G Λ).edgeSet) (β J : ℝ) :
    (Current.fromEdgeFinset G Λ S).weight G Λ β J = (β * J)^(S.card) := by
  unfold Current.weight Current.fromEdgeFinset
  -- factorials are all 1 (since (if … then 1 else 0).factorial = 1)
  have h_factorial : ∀ e : (inducedGraph G Λ).edgeSet,
      ((if e ∈ S then 1 else 0 : ℕ).factorial : ℝ) = 1 := by
    intro e; by_cases he : e ∈ S <;> simp [he]
  simp_rw [h_factorial, div_one]
  -- Reduce (β * J)^(if e ∈ S then 1 else 0) to ite (β * J) 1.
  have h_pow : ∀ e : (inducedGraph G Λ).edgeSet,
      (β * J)^(if e ∈ S then 1 else 0 : ℕ) = if e ∈ S then β * J else 1 := by
    intro e; by_cases he : e ∈ S <;> simp [he]
  simp_rw [h_pow]
  -- ∏ e ∈ univ, (if e ∈ S then β J else 1) = (β J)^|S|
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one,
    Finset.filter_univ_mem]

omit [DecidableEq V] in
/-- **Support of `fromEdgeFinset S` is `S`**: the set of edges
where the 0/1 indicator current is non-zero is exactly `S`. -/
@[simp]
theorem Current.fromEdgeFinset_support (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (S : Finset (inducedGraph G Λ).edgeSet) :
    (Current.fromEdgeFinset G Λ S).support G Λ = S := by
  classical
  ext e
  simp only [Current.support, Current.fromEdgeFinset, Finset.mem_filter,
    Finset.mem_univ, true_and]
  by_cases he : e ∈ S
  · simp [he]
  · simp [he]

omit [DecidableEq V] in
/-- **Parity of `fromEdgeFinset {e₀}` at vertex `v`**: equals `1`
in `ZMod 2` iff `v` is an endpoint of `e₀`, else `0`. -/
theorem Current.fromEdgeFinset_singleton_parity
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (e₀ : (inducedGraph G Λ).edgeSet) (v : ↑Λ) :
    (Current.fromEdgeFinset G Λ {e₀}).parity G Λ v
      = if v ∈ (e₀ : Sym2 ↑Λ) then (1 : ZMod 2) else 0 := by
  unfold Current.parity Current.fromEdgeFinset
  -- ∑ e, if v ∈ e then ((if e ∈ {e₀} then 1 else 0 : ℕ) : ZMod 2) else 0
  rw [Finset.sum_eq_single e₀]
  · -- main term: e = e₀ contributes (if v ∈ e₀ then 1 else 0)
    by_cases hv : v ∈ (e₀ : Sym2 ↑Λ)
    · simp [hv, Finset.mem_singleton]
    · simp [hv]
  · -- other terms: e ≠ e₀ contribute 0 since e ∉ {e₀}
    intro b _ hb_ne
    have : b ∉ ({e₀} : Finset _) := Finset.notMem_singleton.mpr hb_ne
    by_cases hv : v ∈ (b : Sym2 ↑Λ)
    · simp [hv, this]
    · simp [hv]
  · -- e₀ ∈ univ
    intro h
    exact absurd (Finset.mem_univ e₀) h

omit [DecidableEq V] in
/-- **Sources of `fromEdgeFinset {e₀}`**: equals the endpoint
finset of `e₀`, i.e. `(e₀ : Sym2 ↑Λ).toFinset`. Direct
consequence of `fromEdgeFinset_singleton_parity` and
`mem_sources_iff`. -/
@[simp]
theorem Current.fromEdgeFinset_singleton_sources
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (e₀ : (inducedGraph G Λ).edgeSet) :
    (Current.fromEdgeFinset G Λ {e₀}).sources G Λ
      = (e₀ : Sym2 ↑Λ).toFinset := by
  classical
  ext v
  rw [Current.mem_sources_iff, Current.fromEdgeFinset_singleton_parity,
      Sym2.mem_toFinset]
  by_cases hv : v ∈ (e₀ : Sym2 ↑Λ) <;> simp [hv]

omit [DecidableEq V] in
/-- **Cardinality of `fromEdgeFinset {e₀}.sources` is `2`**: a
singleton-edge indicator current has exactly two sources, the two
endpoints of `e₀` in `↑Λ`. Distinctness comes from
`SimpleGraph.not_isDiag_of_mem_edgeSet` (the underlying
`inducedGraph` is loopless). -/
@[simp]
theorem Current.fromEdgeFinset_singleton_sources_card
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (e₀ : (inducedGraph G Λ).edgeSet) :
    ((Current.fromEdgeFinset G Λ {e₀}).sources G Λ).card = 2 := by
  rw [Current.fromEdgeFinset_singleton_sources,
    Sym2.card_toFinset_of_not_isDiag _
      ((inducedGraph G Λ).not_isDiag_of_mem_edgeSet e₀.2)]

omit [DecidableEq V] in
/-- **General `fromEdgeFinset` parity formula**: parity at vertex
`v` of the indicator current `fromEdgeFinset G Λ S` equals the
sum over edges `e ∈ S` incident to `v`, in `ZMod 2`. Generalises
the singleton-edge form `fromEdgeFinset_singleton_parity`. -/
theorem Current.fromEdgeFinset_parity
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (S : Finset (inducedGraph G Λ).edgeSet) (v : ↑Λ) :
    (Current.fromEdgeFinset G Λ S).parity G Λ v
      = ∑ e ∈ S, if v ∈ (e : Sym2 ↑Λ) then (1 : ZMod 2) else 0 := by
  unfold Current.parity Current.fromEdgeFinset
  -- swap inner ifs to get (∑ e ∈ univ, if e ∈ S then (if v ∈ e then 1 else 0) else 0)
  have hswap : ∀ e : (inducedGraph G Λ).edgeSet,
      (if v ∈ (e : Sym2 ↑Λ)
          then (((if e ∈ S then (1 : ℕ) else 0) : ℕ) : ZMod 2) else 0)
        = if e ∈ S
            then (if v ∈ (e : Sym2 ↑Λ) then (1 : ZMod 2) else 0) else 0 := by
    intro e
    by_cases he : e ∈ S
    · by_cases hv : v ∈ (e : Sym2 ↑Λ) <;> simp [he, hv]
    · by_cases hv : v ∈ (e : Sym2 ↑Λ) <;> simp [he, hv]
  simp_rw [hswap]
  -- ∑ e ∈ univ, if e ∈ S then f e else 0 = ∑ e ∈ S, f e
  rw [← Finset.sum_filter]
  congr 1
  ext e
  simp

omit [DecidableEq V] in
/-- **Source characterisation for `fromEdgeFinset`**: a vertex `v`
is a source of `fromEdgeFinset G Λ S` iff an odd number of edges
in `S` are incident to `v`. The standard combinatorial source
characterisation (FV §3.7), feeding the source-set
manipulations in the random-current expansion of `⟨σ_A⟩^Λ` and
the Aizenman switching lemma. -/
@[simp]
theorem Current.mem_fromEdgeFinset_sources_iff
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (S : Finset (inducedGraph G Λ).edgeSet) (v : ↑Λ) :
    v ∈ (Current.fromEdgeFinset G Λ S).sources G Λ
      ↔ Odd (S.filter
          (fun e : (inducedGraph G Λ).edgeSet => v ∈ (e : Sym2 ↑Λ))).card := by
  classical
  rw [Current.mem_sources_iff, Current.fromEdgeFinset_parity,
    Finset.sum_boole, Ne, ZMod.natCast_eq_zero_iff,
    ← even_iff_two_dvd, ← Nat.not_even_iff_odd]

omit [DecidableEq V] in
/-- **`degreeAt` of `fromEdgeFinset`**: equals the cardinality of
the edges in `S` incident to `v`. The ℕ-valued analogue of
`mem_fromEdgeFinset_sources_iff` (without the parity reduction). -/
@[simp]
theorem Current.fromEdgeFinset_degreeAt (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (S : Finset (inducedGraph G Λ).edgeSet) (v : ↑Λ) :
    (Current.fromEdgeFinset G Λ S).degreeAt G Λ v
      = (S.filter
          (fun e : (inducedGraph G Λ).edgeSet => v ∈ (e : Sym2 ↑Λ))).card := by
  classical
  unfold Current.degreeAt Current.fromEdgeFinset
  -- ∑ e : univ, if v ∈ e then (if e ∈ S then 1 else 0) else 0
  have hswap : ∀ e : (inducedGraph G Λ).edgeSet,
      (if v ∈ (e : Sym2 ↑Λ) then (if e ∈ S then (1 : ℕ) else 0) else 0)
        = if e ∈ S then (if v ∈ (e : Sym2 ↑Λ) then (1 : ℕ) else 0) else 0 := by
    intro e
    by_cases he : e ∈ S
    · by_cases hv : v ∈ (e : Sym2 ↑Λ) <;> simp [he, hv]
    · by_cases hv : v ∈ (e : Sym2 ↑Λ) <;> simp [he, hv]
  simp_rw [hswap]
  rw [← Finset.sum_filter]
  have huniv : (Finset.univ.filter
      (fun e : (inducedGraph G Λ).edgeSet => e ∈ S)) = S := by
    ext e; simp
  rw [huniv, Finset.sum_boole, Nat.cast_id]

omit [DecidableEq V] in
/-- **Edge → vertex sum identity (smul form)**: for any
`f : ↑Λ → M` (`M` an `AddCommMonoid`),
`∑_v degreeAt n v • f v = ∑_e n e • (e.toFinset.sum f)`. The
additive form of the central combinatorial step in the
random-current expansion of the Ising partition function
(FV §3.7); converts a vertex-side count weighted by edge
multiplicities into an edge-side count weighted by per-vertex
sums. -/
theorem Current.sum_degreeAt_smul {M : Type*} [AddCommMonoid M]
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (f : ↑Λ → M) :
    ∑ v ∈ (Finset.univ : Finset ↑Λ), n.degreeAt G Λ v • f v
      = ∑ e : (inducedGraph G Λ).edgeSet,
          n e • ((e : Sym2 ↑Λ).toFinset.sum f) := by
  classical
  -- LHS: expand degreeAt and pull smul through the sum
  simp only [Current.degreeAt, Finset.sum_smul]
  -- ∑ v, ∑ e, (if v ∈ e then n e else 0) • f v
  --   = ∑ v, ∑ e, if v ∈ e then n e • f v else 0   [push smul through if]
  have hpush : ∀ (v : ↑Λ) (e : (inducedGraph G Λ).edgeSet),
      (if v ∈ (e : Sym2 ↑Λ) then n e else 0) • f v
        = if v ∈ (e : Sym2 ↑Λ) then n e • f v else 0 := by
    intro v e
    by_cases hv : v ∈ (e : Sym2 ↑Λ) <;> simp [hv]
  simp_rw [hpush]
  -- swap summation order
  rw [Finset.sum_comm]
  -- ∑ e, ∑ v, if v ∈ e then n e • f v else 0
  --   = ∑ e, n e • ∑ v ∈ univ.filter (· ∈ e), f v
  --   = ∑ e, n e • e.toFinset.sum f
  congr 1
  ext e
  rw [← Finset.sum_filter, Finset.smul_sum]
  -- ∑ v ∈ univ.filter (· ∈ e), n e • f v = n e • ∑ v ∈ e.toFinset, f v
  congr 1
  ext v
  simp

omit [DecidableEq V] in
/-- **Edge → vertex product identity (pow form)**: for any
`g : ↑Λ → M` (`M` a `CommMonoid`),
`∏_v g v ^ degreeAt n v = ∏_e (e.toFinset.prod g) ^ n e`. The
multiplicative analogue of `sum_degreeAt_smul`; used to convert
the per-vertex spin product `∏_v σ_v^(degree)` into the per-edge
product `∏_e (σ_u σ_w)^(n e)` in the random-current expansion of
the Ising partition function (FV §3.7). -/
theorem Current.prod_pow_degreeAt {M : Type*} [CommMonoid M]
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (g : ↑Λ → M) :
    ∏ v ∈ (Finset.univ : Finset ↑Λ), g v ^ n.degreeAt G Λ v
      = ∏ e : (inducedGraph G Λ).edgeSet,
          ((e : Sym2 ↑Λ).toFinset.prod g) ^ n e := by
  classical
  simp only [Current.degreeAt]
  -- ∏ v, g v ^ (∑ e, if v ∈ e then n e else 0)
  --   = ∏ v, ∏ e, g v ^ (if v ∈ e then n e else 0)
  simp_rw [← Finset.prod_pow_eq_pow_sum]
  -- push pow through if
  have hpush : ∀ (v : ↑Λ) (e : (inducedGraph G Λ).edgeSet),
      g v ^ (if v ∈ (e : Sym2 ↑Λ) then n e else 0)
        = if v ∈ (e : Sym2 ↑Λ) then g v ^ n e else 1 := by
    intro v e
    by_cases hv : v ∈ (e : Sym2 ↑Λ) <;> simp [hv]
  simp_rw [hpush]
  -- swap the two products
  rw [Finset.prod_comm]
  -- ∏ e, ∏ v, if v ∈ e then g v ^ n e else 1
  --   = ∏ e, ∏ v ∈ univ.filter (· ∈ e), g v ^ n e
  --   = ∏ e, (e.toFinset.prod g) ^ n e
  congr 1
  ext e
  rw [← Finset.prod_filter, ← Finset.prod_pow]
  congr 1
  ext v
  simp

omit [DecidableEq V] in
/-- **Spin-edge product = spin-vertex power (via degreeAt)**: for
any current `n` and spin configuration `σ : ↑Λ → Spin`,
`∏_v σ_v ^ degreeAt n v = ∏_e (e.toFinset.prod σ.toSign) ^ n e`.
The specialization of `prod_pow_degreeAt` to the spin-sign
function `(· : Spin).toSign : Spin → ℝ`. -/
theorem Config.prod_pow_spin_degreeAt
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (σ : ↑Λ → Spin) (n : Current G Λ) :
    ∏ v ∈ (Finset.univ : Finset ↑Λ), ((σ v).toSign : ℝ) ^ n.degreeAt G Λ v
      = ∏ e : (inducedGraph G Λ).edgeSet,
          ((e : Sym2 ↑Λ).toFinset.prod
            (fun v => ((σ v).toSign : ℝ))) ^ n e :=
  Current.prod_pow_degreeAt (M := ℝ) G Λ n (fun v => ((σ v).toSign : ℝ))

omit [DecidableEq V] in
/-- **Spin sum of the spin-edge product at fixed current**: at
fixed current `n`,
`∑_σ ∏_e (e.toFinset.prod σ.toSign) ^ n e = 2^|Λ|` if
`degreeAt n` is even at every vertex (i.e. `n` is source-free),
else `0`. Direct consequence of `prod_pow_spin_degreeAt` and
`Config.sum_prod_toSign_pow_real`; the per-current spin-sum step
of the random-current expansion (FV §3.7). -/
theorem Config.sum_prod_spin_pow_degreeAt
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) :
    (∑ σ : ↑Λ → Spin, ∏ e : (inducedGraph G Λ).edgeSet,
        ((e : Sym2 ↑Λ).toFinset.prod
          (fun v => ((σ v).toSign : ℝ))) ^ n e)
      = if (∀ v : ↑Λ, Even (n.degreeAt G Λ v))
        then (2 : ℝ)^(Fintype.card ↑Λ) else 0 := by
  simp_rw [← Config.prod_pow_spin_degreeAt G Λ _ n]
  exact Config.sum_prod_toSign_pow_real (k := n.degreeAt G Λ)

omit [DecidableEq V] in
/-- **Even `degreeAt` everywhere ↔ source-free**: a current `n`
is source-free iff its total incident degree is even at every
vertex. Bridges the degree-side condition (output of
`Config.sum_prod_spin_pow_degreeAt`) with the parity-side
characterisation (`isSourceFree_iff`). -/
theorem Current.even_degreeAt_iff_isSourceFree
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) :
    (∀ v : ↑Λ, Even (n.degreeAt G Λ v)) ↔ n.IsSourceFree G Λ := by
  rw [Current.isSourceFree_iff]
  refine forall_congr' (fun v => ?_)
  rw [Current.parity_eq_degreeAt, ZMod.natCast_eq_zero_iff,
    ← even_iff_two_dvd]

omit [DecidableEq V] in
/-- **Spin sum at fixed current — source-free form**: at fixed
current `n`, the spin sum of the spin-edge product equals
`2^|Λ|` if `n` is source-free, else `0`. Combines
`Config.sum_prod_spin_pow_degreeAt` with
`Current.even_degreeAt_iff_isSourceFree` to produce the per-current
spin-sum identity in its final form (FV §3.7, eq. (3.45)). -/
theorem Config.sum_prod_spin_pow_degreeAt_isSourceFree
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) [Decidable (n.IsSourceFree G Λ)] :
    (∑ σ : ↑Λ → Spin, ∏ e : (inducedGraph G Λ).edgeSet,
        ((e : Sym2 ↑Λ).toFinset.prod
          (fun v => ((σ v).toSign : ℝ))) ^ n e)
      = if n.IsSourceFree G Λ
        then (2 : ℝ)^(Fintype.card ↑Λ) else 0 := by
  rw [Config.sum_prod_spin_pow_degreeAt]
  exact if_congr (Current.even_degreeAt_iff_isSourceFree G Λ n) rfl rfl

omit [DecidableEq V] in
/-- **Subset spin-product as per-vertex indicator power**: for any
spin configuration `σ : ↑Λ → Spin` and subset `A ⊆ ↑Λ`,
`∏_{a ∈ A} ((σ a).toSign : ℝ) = ∏_v ((σ v).toSign : ℝ)^(1_A v)`.
The indicator-power form needed to combine `σ_A` with the
per-vertex spin powers in the random-current expansion of
`⟨σ_A⟩^Λ` (FV §3.7). -/
theorem Config.prod_subset_eq_prod_pow_indicator
    (Λ : Finset V) [Fintype ↑Λ] [DecidableEq ↑Λ]
    (σ : ↑Λ → Spin) (A : Finset ↑Λ) :
    (∏ a ∈ A, ((σ a).toSign : ℝ))
      = ∏ v : ↑Λ, ((σ v).toSign : ℝ)^(if v ∈ A then 1 else 0) := by
  classical
  -- ∏_v σ.toSign(v)^(if v ∈ A then 1 else 0)
  --   = ∏_v if v ∈ A then σ.toSign(v) else 1
  --   = (univ.filter (· ∈ A)).prod σ.toSign
  --   = A.prod σ.toSign
  have hpow : ∀ v : ↑Λ,
      ((σ v).toSign : ℝ)^(if v ∈ A then (1 : ℕ) else 0)
        = if v ∈ A then ((σ v).toSign : ℝ) else 1 := by
    intro v
    by_cases hv : v ∈ A <;> simp [hv]
  simp_rw [hpow]
  rw [← Finset.prod_filter]
  congr 1
  ext v
  simp

omit [DecidableEq V] in
/-- **`σ_A` × spin-edge product as single per-vertex power**:
`σ_A · ∏_e (e.toFinset.prod σ.toSign)^n e
  = ∏_v ((σ v).toSign : ℝ)^((1_A v) + degreeAt n v)`.
Combines the indicator-power form of `σ_A` with the per-vertex
power form of the spin-edge product, ready to apply
`Config.sum_prod_toSign_pow_real` for the A-source spin sum
(FV §3.7). -/
theorem Config.spinA_mul_prod_spin_pow_eq_prod_pow_sum
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (σ : ↑Λ → Spin) (n : Current G Λ) (A : Finset ↑Λ) :
    (∏ a ∈ A, ((σ a).toSign : ℝ))
    * (∏ e : (inducedGraph G Λ).edgeSet,
        ((e : Sym2 ↑Λ).toFinset.prod
          (fun v => ((σ v).toSign : ℝ))) ^ n e)
      = ∏ v : ↑Λ, ((σ v).toSign : ℝ) ^
          ((if v ∈ A then (1 : ℕ) else 0) + n.degreeAt G Λ v) := by
  rw [Config.prod_subset_eq_prod_pow_indicator Λ σ A,
    ← Config.prod_pow_spin_degreeAt G Λ σ n,
    ← Finset.prod_mul_distrib]
  congr 1
  ext v
  rw [← pow_add]

omit [DecidableEq V] in
/-- **A-source spin sum at fixed current — degree+indicator
form**: at fixed current `n` and source set `A ⊆ ↑Λ`,
`∑_σ σ_A · ∏_e (e.toFinset.prod σ.toSign)^n e
  = 2^|Λ|` if `(1_A v) + degreeAt n v` is even at every vertex,
else `0`. Combines `spinA_mul_prod_spin_pow_eq_prod_pow_sum`
with `Config.sum_prod_toSign_pow_real`. -/
theorem Config.sum_spinA_prod_spin_pow_eq_pow_card_iff
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (A : Finset ↑Λ) :
    (∑ σ : ↑Λ → Spin,
      (∏ a ∈ A, ((σ a).toSign : ℝ))
      * (∏ e : (inducedGraph G Λ).edgeSet,
          ((e : Sym2 ↑Λ).toFinset.prod
            (fun v => ((σ v).toSign : ℝ))) ^ n e))
      = if (∀ v : ↑Λ,
            Even ((if v ∈ A then (1 : ℕ) else 0) + n.degreeAt G Λ v))
        then (2 : ℝ)^(Fintype.card ↑Λ) else 0 := by
  simp_rw [Config.spinA_mul_prod_spin_pow_eq_prod_pow_sum G Λ _ n A]
  exact Config.sum_prod_toSign_pow_real
    (k := fun v => (if v ∈ A then (1 : ℕ) else 0) + n.degreeAt G Λ v)

omit [DecidableEq V] in
/-- **Even (`1_A v + degreeAt n v`) at every vertex ↔
`n.HasSources A`**: a current `n` has source set exactly `A` iff
`(1_A v) + degreeAt n v` is even at every vertex. The A-source
analogue of `even_degreeAt_iff_isSourceFree`. -/
theorem Current.even_indicator_add_degreeAt_iff_hasSources
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (A : Finset ↑Λ) :
    (∀ v : ↑Λ,
        Even ((if v ∈ A then (1 : ℕ) else 0) + n.degreeAt G Λ v))
      ↔ n.HasSources G Λ A := by
  classical
  unfold Current.HasSources
  -- Each summand: Even (1_A v + degreeAt n v)
  --   ↔ ((1_A v + degreeAt n v : ℕ) : ZMod 2) = 0
  --   ↔ (1_A v : ZMod 2) + parity n v = 0
  --   ↔ parity n v = -(1_A v : ZMod 2) = (1_A v : ZMod 2)  (char 2)
  have hper : ∀ v : ↑Λ,
      Even ((if v ∈ A then (1 : ℕ) else 0) + n.degreeAt G Λ v)
        ↔ n.parity G Λ v = (if v ∈ A then (1 : ZMod 2) else 0) := by
    intro v
    rw [even_iff_two_dvd, ← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [← Current.parity_eq_degreeAt]
    -- Goal: (if v ∈ A then 1 else 0 : ZMod 2) + parity n v = 0
    --       ↔ parity n v = if v ∈ A then 1 else 0
    by_cases hvA : v ∈ A
    · simp only [if_pos hvA]
      -- (1 : ZMod 2) + parity = 0 ↔ parity = 1
      have h2 : ∀ x : ZMod 2, 1 + x = 0 ↔ x = 1 := by decide
      exact h2 _
    · simp only [if_neg hvA]
      -- (0 : ZMod 2) + parity = 0 ↔ parity = 0
      simp
  rw [forall_congr' hper]
  -- ∀ v, parity n v = (if v ∈ A then 1 else 0 : ZMod 2) ↔ sources n = A
  have hZMod2 : ∀ x : ZMod 2, x ≠ 0 ↔ x = 1 := by decide
  constructor
  · intro h
    ext v
    rw [Current.mem_sources_iff, h v]
    by_cases hvA : v ∈ A
    · simp only [if_pos hvA]
      exact iff_of_true ((hZMod2 1).mpr rfl) hvA
    · simp only [if_neg hvA]
      exact iff_of_false (by simp) hvA
  · intro h v
    have hmem : (v ∈ n.sources G Λ) ↔ (v ∈ A) := by rw [h]
    rw [Current.mem_sources_iff] at hmem
    by_cases hvA : v ∈ A
    · rw [if_pos hvA]
      exact (hZMod2 _).mp (hmem.mpr hvA)
    · rw [if_neg hvA]
      by_contra hne
      exact hvA (hmem.mp hne)

omit [DecidableEq V] in
/-- **A-source spin sum at fixed current — `HasSources` form**:
\(∑_σ σ_A · ∏_e (e.toFinset.prod σ.toSign)^n e
  = 2^|Λ|\) if `n.HasSources A`, else `0`. Final form combining
`Config.sum_spinA_prod_spin_pow_eq_pow_card_iff` and
`Current.even_indicator_add_degreeAt_iff_hasSources`; the
A-source per-current spin-sum identity in its final form,
ready to feed into the random-current expression of
`⟨σ_A⟩^Λ` (FV §3.7). -/
theorem Config.sum_spinA_prod_spin_pow_hasSources
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (A : Finset ↑Λ)
    [Decidable (n.HasSources G Λ A)] :
    (∑ σ : ↑Λ → Spin,
      (∏ a ∈ A, ((σ a).toSign : ℝ))
      * (∏ e : (inducedGraph G Λ).edgeSet,
          ((e : Sym2 ↑Λ).toFinset.prod
            (fun v => ((σ v).toSign : ℝ))) ^ n e))
      = if n.HasSources G Λ A
        then (2 : ℝ)^(Fintype.card ↑Λ) else 0 := by
  rw [Config.sum_spinA_prod_spin_pow_eq_pow_card_iff]
  exact if_congr
    (Current.even_indicator_add_degreeAt_iff_hasSources G Λ n A) rfl rfl

omit [DecidableEq V] in
/-- **`weightSum` at zero β collapses to indicator on `A = ∅`**:
\(Current.weightSum\,A\,0\,J = 1\) if `A = ∅`, else `0`. At zero
coupling, only the zero current contributes (its source set is
`∅`); uses `Current.weight_beta_zero` and `tsum_eq_single`. -/
theorem Current.weightSum_beta_zero (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (A : Finset ↑Λ) (J : ℝ) :
    Current.weightSum G Λ A 0 J = if A = ∅ then 1 else 0 := by
  classical
  unfold Current.weightSum
  -- Only n = 0 contributes since weight 0 J n = 0 for n ≠ 0.
  have h_single : ∀ n : Current G Λ, n ≠ 0 →
      (if n.sources G Λ = A then n.weight G Λ 0 J else 0) = 0 := by
    intro n hn
    by_cases hsr : n.sources G Λ = A
    · rw [if_pos hsr, Current.weight_beta_zero, if_neg hn]
    · rw [if_neg hsr]
  rw [tsum_eq_single (0 : Current G Λ) h_single,
    Current.zero_sources, Current.zero_weight]
  exact if_congr eq_comm rfl rfl

omit [DecidableEq V] in
/-- **`weightSum` at zero J collapses to indicator on `A = ∅`**:
\(Current.weightSum\,A\,β\,0 = 1\) if `A = ∅`, else `0`.
Symmetric counterpart of `weightSum_beta_zero`. -/
theorem Current.weightSum_J_zero (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (A : Finset ↑Λ) (β : ℝ) :
    Current.weightSum G Λ A β 0 = if A = ∅ then 1 else 0 := by
  classical
  unfold Current.weightSum
  have h_single : ∀ n : Current G Λ, n ≠ 0 →
      (if n.sources G Λ = A then n.weight G Λ β 0 else 0) = 0 := by
    intro n hn
    by_cases hsr : n.sources G Λ = A
    · rw [if_pos hsr, Current.weight_J_zero, if_neg hn]
    · rw [if_neg hsr]
  rw [tsum_eq_single (0 : Current G Λ) h_single,
    Current.zero_sources, Current.zero_weight]
  exact if_congr eq_comm rfl rfl

omit [DecidableEq V] in
/-- **Weight × edge-product of powers**: for any edge-indexed
`x : edgeSet → ℝ`,
`weight β J n · (∏_e (x e)^(n e)) = ∏_e (β * J * x e)^(n e) / (n e)!`.
The per-current summand identity bridging \`weight\` with the
per-edge Taylor terms `(β J σ_u σ_w)^k / k!`, preparing the
random-current expansion of the partition function
(FV §3.7, eq. (3.45)). -/
theorem Current.weight_mul_prod_pow (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (β J : ℝ) (n : Current G Λ)
    (x : (inducedGraph G Λ).edgeSet → ℝ) :
    n.weight G Λ β J * (∏ e : (inducedGraph G Λ).edgeSet, (x e)^(n e))
      = ∏ e : (inducedGraph G Λ).edgeSet,
          (β * J * x e)^(n e) / ((n e).factorial : ℝ) := by
  unfold Current.weight
  rw [← Finset.prod_mul_distrib]
  congr 1
  ext e
  rw [mul_pow]
  ring

end Ambient
end IsingModel
