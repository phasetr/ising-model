import IsingModel.AmbientLattice

/-!
# Random current foundation (GJ §5.1 Simon-Lieb attempt, step 1)

A current on a finite induced subgraph is an `ℕ`-valued function
on its (finite) edge set. This file fixes the type and the basic
algebraic operations (`Zero`, `Add`); subsequent PRs will add the
parity, the source/sink characterisation, and ultimately the
Aizenman switching lemma feeding the random-current expression of
`⟨σ^A⟩^Λ` and Simon-Lieb (FV Prop 9.31).

Reference: Glimm–Jaffe *Quantum Physics* 2nd ed., §5.1 pp. 76–79;
Friedli–Velenik §3.7, Prop 9.31. -/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Current on a finite induced subgraph**: an `ℕ`-valued
function on the (finite) edge set of `inducedGraph G Λ`. The
underlying type used for the random-current representation of the
Ising 2-point function in GJ §5.1 / FV Prop 9.31. -/
abbrev Current (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :=
  (inducedGraph G Λ).edgeSet → ℕ

/-- **Zero current**: the constant zero function. -/
instance Current.instZero (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] : Zero (Current G Λ) :=
  ⟨fun _ => 0⟩

/-- **Pointwise addition** of currents. -/
instance Current.instAdd (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] : Add (Current G Λ) :=
  ⟨fun n m => fun e => n e + m e⟩

/-- **Parity at a vertex**: for a current `n` and a vertex
`v : ↑Λ`, the parity (mod 2) of the sum of `n e` over edges `e`
incident to `v`. The source set of `n` is the set of vertices
where the parity is non-zero; the parity drives the source/sink
characterisation and the Aizenman switching lemma in subsequent
PRs (FV §3.7). -/
def Current.parity (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (v : ↑Λ) : ZMod 2 :=
  ∑ e : (inducedGraph G Λ).edgeSet,
    if v ∈ (e : Sym2 ↑Λ) then ((n e : ℕ) : ZMod 2) else 0

omit [DecidableEq V] in
/-- **Zero parity**: the zero current has parity `0` at every
vertex (each summand vanishes). -/
@[simp]
theorem Current.zero_parity (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (v : ↑Λ) :
    (0 : Current G Λ).parity G Λ v = 0 := by
  unfold Current.parity
  simp only [show ((0 : Current G Λ) : (inducedGraph G Λ).edgeSet → ℕ) = fun _ => 0
    from rfl]
  simp

omit [DecidableEq V] in
/-- **Additive parity**: parity distributes over addition of
currents (sum of parities equals parity of the sum). -/
theorem Current.add_parity (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n m : Current G Λ) (v : ↑Λ) :
    (n + m).parity G Λ v = n.parity G Λ v + m.parity G Λ v := by
  unfold Current.parity
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  by_cases hv : v ∈ (e : Sym2 ↑Λ)
  · simp [hv, show ((n + m) e : ℕ) = n e + m e from rfl, Nat.cast_add]
  · simp [hv]

/-- **Source set** of a current `n`: the Finset of vertices `v`
with odd parity (`n.parity v ≠ 0`). The standard "boundary" `∂n`
in the random-current literature; `⟨σ_A⟩^Λ` is expressed as a
weighted sum over currents whose source set is exactly `A`
(FV §3.7). -/
noncomputable def Current.sources (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) : Finset ↑Λ :=
  (Finset.univ : Finset ↑Λ).filter (fun v => n.parity G Λ v ≠ 0)

omit [DecidableEq V] in
/-- **Membership in `Current.sources`**: `v ∈ n.sources` iff
`n.parity v ≠ 0`. -/
@[simp]
theorem Current.mem_sources_iff (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (v : ↑Λ) :
    v ∈ n.sources G Λ ↔ n.parity G Λ v ≠ 0 := by
  classical
  simp [Current.sources]

omit [DecidableEq V] in
/-- **Zero current has empty source set**: every vertex has parity
`0` for the zero current, so the source filter is empty. -/
@[simp]
theorem Current.zero_sources (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ] :
    (0 : Current G Λ).sources G Λ = ∅ := by
  classical
  ext v
  simp

omit [DecidableEq V] in
/-- **Parity zero iff not a source**: `n.parity v = 0` iff
`v ∉ n.sources`. -/
theorem Current.parity_eq_zero_iff (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (v : ↑Λ) :
    n.parity G Λ v = 0 ↔ v ∉ n.sources G Λ := by
  rw [Current.mem_sources_iff, not_not]

omit [DecidableEq V] in
/-- **Sources of a sum is the symmetric difference**:
`(n + m).sources = n.sources △ m.sources`.
At each vertex `v`, `(n + m).parity v = n.parity v + m.parity v`
in `ZMod 2`; this is non-zero iff exactly one summand is. -/
theorem Current.add_sources_eq (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n m : Current G Λ) :
    (n + m).sources G Λ
      = symmDiff (n.sources G Λ) (m.sources G Λ) := by
  classical
  ext v
  simp only [Current.mem_sources_iff, Finset.mem_symmDiff,
    Current.add_parity]
  -- Goal in ZMod 2: a + b ≠ 0 ↔ (a ≠ 0 ∧ ¬ b ≠ 0) ∨ (b ≠ 0 ∧ ¬ a ≠ 0).
  generalize n.parity G Λ v = a
  generalize m.parity G Λ v = b
  revert a b
  decide

/-- **Random-current weight** for uniform coupling `J` and inverse
temperature `β`: `weight β J n := ∏_e (β J)^(n e) / (n e)!`.
The weight of a current `n` in the random-current expansion of
the Ising partition function (FV (3.45)). Expectation values
`⟨σ_A⟩^Λ` are expressed as weighted sums over `A`-source
currents. -/
noncomputable def Current.weight (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (β J : ℝ) (n : Current G Λ) : ℝ :=
  ∏ e : (inducedGraph G Λ).edgeSet,
    (β * J) ^ (n e) / ((n e).factorial : ℝ)

omit [DecidableEq V] in
/-- **Zero current has weight 1**: each factor is
`(β J)^0 / 0! = 1 / 1 = 1`, so the product over edges is `1`. -/
@[simp]
theorem Current.zero_weight (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β J : ℝ) :
    (0 : Current G Λ).weight G Λ β J = 1 := by
  unfold Current.weight
  simp

omit [DecidableEq V] in
/-- **Weight is nonneg under nonneg coupling**: when `0 ≤ β J`,
each factor `(β J)^(n e) / (n e)!` is nonneg, hence the product
is nonneg. -/
theorem Current.weight_nonneg (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : Current G Λ) :
    0 ≤ n.weight G Λ β J := by
  unfold Current.weight
  refine Finset.prod_nonneg (fun e _ => ?_)
  refine div_nonneg (pow_nonneg hβJ _) ?_
  exact Nat.cast_nonneg _

omit [DecidableEq V] in
/-- **Weight is strictly positive under positive coupling**: when
`0 < β J`, each factor `(β J)^(n e) / (n e)!` is strictly
positive, hence the product is strictly positive. -/
theorem Current.weight_pos (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 < β * J) (n : Current G Λ) :
    0 < n.weight G Λ β J := by
  unfold Current.weight
  refine Finset.prod_pos (fun e _ => ?_)
  refine div_pos (pow_pos hβJ _) ?_
  exact_mod_cast Nat.factorial_pos _

/-- **Edge support of a current**: the Finset of edges with
non-zero current value. Used in the random-current sum: weight
of a current depends only on its values on the support. -/
noncomputable def Current.support (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) :
    Finset (inducedGraph G Λ).edgeSet :=
  (Finset.univ : Finset (inducedGraph G Λ).edgeSet).filter (fun e => n e ≠ 0)

omit [DecidableEq V] in
/-- **Zero current has empty support**: every edge has value `0`. -/
@[simp]
theorem Current.support_zero (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ] :
    (0 : Current G Λ).support G Λ = ∅ := by
  classical
  ext e
  simp [Current.support]

omit [DecidableEq V] in
/-- **Support of a sum is contained in the union of supports**:
if `(n + m) e ≠ 0` then `n e ≠ 0 ∨ m e ≠ 0`. -/
theorem Current.support_add_subset (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n m : Current G Λ) :
    (n + m).support G Λ ⊆ n.support G Λ ∪ m.support G Λ := by
  classical
  intro e he
  simp only [Current.support, Finset.mem_filter, Finset.mem_univ,
    true_and] at he
  simp only [Finset.mem_union, Current.support, Finset.mem_filter,
    Finset.mem_univ, true_and]
  by_contra hne
  rw [not_or] at hne
  obtain ⟨hn, hm⟩ := hne
  apply he
  change n e + m e = 0
  rw [not_ne_iff.mp hn, not_ne_iff.mp hm]

/-- **Sum of weights over A-source currents**:
`weightSum A β J := ∑' n : Current G Λ, if n.sources = A then weight β J n else 0`.
The unnormalized random-current measure of A-source currents,
central to the random-current expression of correlations
`⟨σ_A⟩^Λ = weightSum A / weightSum ∅` (FV (3.45)).

If the underlying sum is not Summable, mathlib's `tsum` returns
`0` as a junk value; convergence is analysed in subsequent PRs. -/
noncomputable def Current.weightSum (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (A : Finset ↑Λ) (β J : ℝ) : ℝ :=
  ∑' n : Current G Λ,
    if n.sources G Λ = A then n.weight G Λ β J else 0

omit [DecidableEq V] in
/-- **`weightSum` is nonneg under nonneg coupling**: each summand
is either `0` (if the source set differs from `A`) or
`weight n ≥ 0` (when `0 ≤ β J`); `tsum_nonneg` finishes. -/
theorem Current.weightSum_nonneg (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (A : Finset ↑Λ) {β J : ℝ} (hβJ : 0 ≤ β * J) :
    0 ≤ Current.weightSum G Λ A β J := by
  unfold Current.weightSum
  refine tsum_nonneg (fun n => ?_)
  by_cases h : n.sources G Λ = A
  · simp [h, Current.weight_nonneg G Λ hβJ n]
  · simp [h]

end Ambient

end IsingModel
