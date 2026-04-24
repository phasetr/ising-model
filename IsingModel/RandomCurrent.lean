import IsingModel.AmbientLattice
import Mathlib.Analysis.SpecialFunctions.Exponential

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

omit [DecidableEq V] in
/-- **Current extensionality**: two currents are equal iff they
agree on every edge. Just `funext` exposed under the `Current`
namespace for use as `@[ext]`. -/
@[ext]
theorem Current.ext (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] {n m : Current G Λ}
    (h : ∀ e, n e = m e) : n = m := funext h

omit [DecidableEq V] in
/-- **Pointwise zero**: `(0 : Current G Λ) e = 0` (by definition). -/
@[simp]
theorem Current.zero_apply (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (e : (inducedGraph G Λ).edgeSet) :
    (0 : Current G Λ) e = 0 := rfl

omit [DecidableEq V] in
/-- **Pointwise sum**: `(n + m) e = n e + m e` (by definition). -/
@[simp]
theorem Current.add_apply (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (n m : Current G Λ) (e : (inducedGraph G Λ).edgeSet) :
    (n + m) e = n e + m e := rfl

/-- **`Current G Λ` is an `AddCommMonoid`**: lifts the pointwise
`Zero` and `Add` to the full additive commutative monoid
structure (via `Pi.addCommMonoid`). Allows use of `Finset.sum`,
`nsmul`, etc. on currents in subsequent random-current expansion
PRs (FV §3.7). -/
instance Current.instAddCommMonoid (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    AddCommMonoid (Current G Λ) :=
  Pi.addCommMonoid

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

/-- **Total incident degree at a vertex**: for a current `n` and a
vertex `v : ↑Λ`, the ℕ-valued sum of `n e` over edges `e`
incident to `v`. Lifts `parity` from `ZMod 2` to ℕ; equals the
exponent of `σ_v` in the random-current expansion of the Ising
partition function (FV §3.7). -/
def Current.degreeAt (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (v : ↑Λ) : ℕ :=
  ∑ e : (inducedGraph G Λ).edgeSet, if v ∈ (e : Sym2 ↑Λ) then n e else 0

omit [DecidableEq V] in
/-- **Parity equals `degreeAt mod 2`**: the ZMod 2 parity is the
ℕ→ZMod 2 cast of the integer-valued total incident degree. -/
theorem Current.parity_eq_degreeAt (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (v : ↑Λ) :
    n.parity G Λ v = ((n.degreeAt G Λ v : ℕ) : ZMod 2) := by
  unfold Current.parity Current.degreeAt
  rw [Nat.cast_sum]
  congr 1
  ext e
  by_cases hv : v ∈ (e : Sym2 ↑Λ) <;> simp [hv]

omit [DecidableEq V] in
/-- **Zero `degreeAt`**: the zero current has degree `0` at every
vertex (each summand vanishes). -/
@[simp]
theorem Current.zero_degreeAt (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (v : ↑Λ) :
    (0 : Current G Λ).degreeAt G Λ v = 0 := by
  unfold Current.degreeAt
  simp

omit [DecidableEq V] in
/-- **Linearity of `degreeAt`**:
`(n + m).degreeAt v = n.degreeAt v + m.degreeAt v`. Each summand
splits because `if v ∈ e then n e + m e else 0` distributes
under `+`. -/
@[simp]
theorem Current.add_degreeAt (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n m : Current G Λ) (v : ↑Λ) :
    (n + m).degreeAt G Λ v = n.degreeAt G Λ v + m.degreeAt G Λ v := by
  unfold Current.degreeAt
  rw [← Finset.sum_add_distrib]
  congr 1
  ext e
  by_cases hv : v ∈ (e : Sym2 ↑Λ) <;> simp [hv]

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

omit [DecidableEq V] in
/-- **Weight at zero β collapses to indicator on `n = 0`**:
\(n.weight\,0\,J = 1\) if `n = 0`, else `0`. Each non-zero edge
multiplicity gives a `0^(n e) = 0` factor. -/
theorem Current.weight_beta_zero (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J : ℝ) (n : Current G Λ) :
    n.weight G Λ 0 J = if n = 0 then 1 else 0 := by
  classical
  by_cases hn : n = 0
  · subst hn; simp
  · rw [if_neg hn]
    obtain ⟨e₀, he₀⟩ : ∃ e, n e ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hn (funext hall)
    unfold Current.weight
    refine Finset.prod_eq_zero (Finset.mem_univ e₀) ?_
    rw [zero_mul, zero_pow he₀, zero_div]

omit [DecidableEq V] in
/-- **Weight at zero J collapses to indicator on `n = 0`**:
\(n.weight\,β\,0 = 1\) if `n = 0`, else `0`. Symmetric counterpart
of `weight_beta_zero`. -/
theorem Current.weight_J_zero (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (β : ℝ) (n : Current G Λ) :
    n.weight G Λ β 0 = if n = 0 then 1 else 0 := by
  classical
  by_cases hn : n = 0
  · subst hn; simp
  · rw [if_neg hn]
    obtain ⟨e₀, he₀⟩ : ∃ e, n e ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hn (funext hall)
    unfold Current.weight
    refine Finset.prod_eq_zero (Finset.mem_univ e₀) ?_
    rw [mul_zero, zero_pow he₀, zero_div]

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

/-- **Source-free current**: a current with no sources
(`n.sources = ∅`). The class summed over for the partition
function in the random-current representation. -/
def Current.IsSourceFree (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) : Prop :=
  n.sources G Λ = ∅

/-- **Current with prescribed sources**: a current whose source
set equals a given Finset `A`. The class summed over for the
random-current representation of `⟨σ_A⟩^Λ`. -/
def Current.HasSources (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (A : Finset ↑Λ) : Prop :=
  n.sources G Λ = A

omit [DecidableEq V] in
/-- **Zero current is source-free**: every vertex has parity `0`. -/
@[simp]
theorem Current.zero_isSourceFree (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ] :
    (0 : Current G Λ).IsSourceFree G Λ := by
  unfold Current.IsSourceFree
  exact Current.zero_sources G Λ

omit [DecidableEq V] in
/-- **Source-free characterisation by parity**: a current is
source-free iff every vertex has parity `0`. -/
theorem Current.isSourceFree_iff (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) :
    n.IsSourceFree G Λ ↔ ∀ v : ↑Λ, n.parity G Λ v = 0 := by
  unfold Current.IsSourceFree
  constructor
  · intro h v
    rw [Current.parity_eq_zero_iff, h]
    exact Finset.notMem_empty v
  · intro h
    ext v
    simp [Current.mem_sources_iff, h v]

omit [DecidableEq V] in
/-- **Zero current `HasSources A` iff A = ∅**: the zero current
is source-free, hence has prescribed sources `A` only when
`A = ∅`. -/
theorem Current.zero_hasSources_iff (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (A : Finset ↑Λ) :
    (0 : Current G Λ).HasSources G Λ A ↔ A = ∅ := by
  unfold Current.HasSources
  rw [Current.zero_sources]
  exact eq_comm

omit [DecidableEq V] in
/-- **Sum of currents has prescribed sources iff parities give
the symmetric difference**: `(n + m).HasSources A ↔
symmDiff n.sources m.sources = A`. Direct consequence of
`add_sources_eq`. -/
theorem Current.add_hasSources_iff (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n m : Current G Λ) (A : Finset ↑Λ) :
    (n + m).HasSources G Λ A
      ↔ symmDiff (n.sources G Λ) (m.sources G Λ) = A := by
  unfold Current.HasSources
  rw [Current.add_sources_eq]

/-- **Bounded current**: a current with each edge value bounded
by `N`. Automatically `Fintype` (each edge contributes a finite
choice from `Fin (N+1)`, and the edge set is itself `Fintype`),
enabling finite-sum manipulations as a stepping stone toward the
limit-based random-current expansion. -/
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

/-- **Real-valued edge spin product**: for a spin configuration
`σ : W → Spin` and an edge `e : Sym2 W`, the product of
`(σ v).toSign : ℝ` over `v ∈ e.toFinset`. For a non-loop edge
`e = s(u, w)` this is `(σ u).toSign * (σ w).toSign ∈ {-1, +1}`;
for a (nonexistent in a `SimpleGraph`) loop edge `e = s(v, v)` it
is just `(σ v).toSign ∈ {-1, +1}`. The per-edge factor in the
Taylor expansion `exp(β J σ_u σ_w) = ∑_k (β J σ_u σ_w)^k / k!`
feeding the random-current representation (FV §3.7). -/
noncomputable def Config.spinEdgeProduct {W : Type*} [DecidableEq W]
    (σ : W → Spin) (e : Sym2 W) : ℝ :=
  e.toFinset.prod (fun v => ((σ v).toSign : ℝ))

/-- **Squared edge spin product on a non-loop edge is `1`**: for a
non-diagonal `e : Sym2 W`, `(spinEdgeProduct σ e)^2 = 1`. Since
`(σ v).toSign ∈ {-1, +1}` for each endpoint, the product of two
such values squared is `1`. The ±1 control feeding absolute
convergence of the Taylor series. -/
theorem Config.spinEdgeProduct_mul_self_of_not_isDiag {W : Type*}
    [DecidableEq W] (σ : W → Spin) (e : Sym2 W) (he : ¬ e.IsDiag) :
    (Config.spinEdgeProduct σ e) ^ 2 = 1 := by
  unfold Config.spinEdgeProduct
  refine Sym2.inductionOn e (fun u w hne => ?_) he
  -- e = s(u, w), non-diag ↔ u ≠ w
  rw [Sym2.toFinset_mk_eq]
  rw [Sym2.mk_isDiag_iff] at hne
  rw [Finset.prod_insert (Finset.notMem_singleton.mpr hne),
    Finset.prod_singleton]
  -- ((σ u).toSign * (σ w).toSign)^2 = ((σ u).toSign)^2 * ((σ w).toSign)^2
  rw [mul_pow]
  -- ((σ v).toSign : ℝ)^2 = 1 for all v
  have h_one : ∀ v : W, ((σ v).toSign : ℝ)^2 = 1 := by
    intro v
    have := Spin.toSign_sq (σ v)
    exact_mod_cast this
  rw [h_one, h_one]; norm_num

/-- **Edge spin product is `±1` on a non-loop edge**: for a
non-diagonal `e : Sym2 W`,
`spinEdgeProduct σ e = 1 ∨ spinEdgeProduct σ e = -1`. Direct
corollary of `spinEdgeProduct_mul_self_of_not_isDiag` via
`sq_eq_one_iff`. -/
theorem Config.spinEdgeProduct_eq_one_or_neg_one_of_not_isDiag
    {W : Type*} [DecidableEq W] (σ : W → Spin) (e : Sym2 W)
    (he : ¬ e.IsDiag) :
    Config.spinEdgeProduct σ e = 1 ∨ Config.spinEdgeProduct σ e = -1 :=
  sq_eq_one_iff.mp (Config.spinEdgeProduct_mul_self_of_not_isDiag σ e he)

/-- **Edge spin product has absolute value `1` on a non-loop
edge**: \(|spinEdgeProduct σ e| = 1\) for non-diagonal `e`.
Feeding absolute convergence of the Taylor series for
`exp(β J σ_u σ_w)`. -/
theorem Config.abs_spinEdgeProduct_of_not_isDiag {W : Type*}
    [DecidableEq W] (σ : W → Spin) (e : Sym2 W) (he : ¬ e.IsDiag) :
    |Config.spinEdgeProduct σ e| = 1 := by
  rcases Config.spinEdgeProduct_eq_one_or_neg_one_of_not_isDiag σ e he with h | h
  · rw [h]; norm_num
  · rw [h]; norm_num

omit [DecidableEq V] in
/-- **Squared edge spin product on `inducedGraph` edge is `1`**:
edgeSet variant of `spinEdgeProduct_mul_self_of_not_isDiag`,
auto-deriving non-diagonality from `not_isDiag_of_mem_edgeSet`. -/
theorem Config.spinEdgeProduct_inducedGraph_mul_self
    (G : SimpleGraph V) (Λ : Finset V) [DecidableEq ↑Λ]
    (σ : ↑Λ → Spin) (e : (inducedGraph G Λ).edgeSet) :
    (Config.spinEdgeProduct σ (e : Sym2 ↑Λ)) ^ 2 = 1 :=
  Config.spinEdgeProduct_mul_self_of_not_isDiag σ _
    ((inducedGraph G Λ).not_isDiag_of_mem_edgeSet e.2)

omit [DecidableEq V] in
/-- **Edge spin product on `inducedGraph` edge is `±1`**: edgeSet
variant of `spinEdgeProduct_eq_one_or_neg_one_of_not_isDiag`. -/
theorem Config.spinEdgeProduct_inducedGraph_eq_one_or_neg_one
    (G : SimpleGraph V) (Λ : Finset V) [DecidableEq ↑Λ]
    (σ : ↑Λ → Spin) (e : (inducedGraph G Λ).edgeSet) :
    Config.spinEdgeProduct σ (e : Sym2 ↑Λ) = 1 ∨
      Config.spinEdgeProduct σ (e : Sym2 ↑Λ) = -1 :=
  Config.spinEdgeProduct_eq_one_or_neg_one_of_not_isDiag σ _
    ((inducedGraph G Λ).not_isDiag_of_mem_edgeSet e.2)

omit [DecidableEq V] in
/-- **Edge spin product on `inducedGraph` edge has |·| = 1**:
edgeSet variant of `abs_spinEdgeProduct_of_not_isDiag`. -/
theorem Config.abs_spinEdgeProduct_inducedGraph
    (G : SimpleGraph V) (Λ : Finset V) [DecidableEq ↑Λ]
    (σ : ↑Λ → Spin) (e : (inducedGraph G Λ).edgeSet) :
    |Config.spinEdgeProduct σ (e : Sym2 ↑Λ)| = 1 :=
  Config.abs_spinEdgeProduct_of_not_isDiag σ _
    ((inducedGraph G Λ).not_isDiag_of_mem_edgeSet e.2)

omit [DecidableEq V] in
/-- **Source-free spin sum in `spinEdgeProduct` form**:
`∑_σ ∏_e (spinEdgeProduct σ e)^(n e)
  = 2^|Λ|` if `n.IsSourceFree`, else `0`. Restatement of
`Config.sum_prod_spin_pow_degreeAt_isSourceFree` using the named
\`Config.spinEdgeProduct\`. -/
theorem Config.sum_prod_spinEdgeProduct_pow_isSourceFree
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) [Decidable (n.IsSourceFree G Λ)] :
    (∑ σ : ↑Λ → Spin, ∏ e : (inducedGraph G Λ).edgeSet,
        (Config.spinEdgeProduct σ (e : Sym2 ↑Λ))^(n e))
      = if n.IsSourceFree G Λ
        then (2 : ℝ)^(Fintype.card ↑Λ) else 0 :=
  Config.sum_prod_spin_pow_degreeAt_isSourceFree G Λ n

omit [DecidableEq V] in
/-- **A-source spin sum in `spinEdgeProduct` form**:
`∑_σ σ_A · ∏_e (spinEdgeProduct σ e)^(n e)
  = 2^|Λ|` if `n.HasSources A`, else `0`. Restatement of
`Config.sum_spinA_prod_spin_pow_hasSources` using the named
\`Config.spinEdgeProduct\`. -/
theorem Config.sum_spinA_prod_spinEdgeProduct_pow_hasSources
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (A : Finset ↑Λ)
    [Decidable (n.HasSources G Λ A)] :
    (∑ σ : ↑Λ → Spin,
      (∏ a ∈ A, ((σ a).toSign : ℝ))
      * (∏ e : (inducedGraph G Λ).edgeSet,
          (Config.spinEdgeProduct σ (e : Sym2 ↑Λ))^(n e)))
      = if n.HasSources G Λ A
        then (2 : ℝ)^(Fintype.card ↑Λ) else 0 :=
  Config.sum_spinA_prod_spin_pow_hasSources G Λ n A

omit [DecidableEq V] in
/-- **Per-current σ-sum with weight**: at fixed current `n` and
source set `A`,
`∑_σ σ_A · weight β J n · ∏_e (spinEdgeProduct σ e)^(n e)
  = weight β J n · 2^|Λ|` if `n.HasSources A`, else `0`. The
per-current contribution to the random-current expression of
`⟨σ_A⟩^Λ` (FV §3.7). -/
theorem Config.sum_spinA_weight_prod_spinEdgeProduct_pow_hasSources
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (β J : ℝ) (n : Current G Λ) (A : Finset ↑Λ)
    [Decidable (n.HasSources G Λ A)] :
    (∑ σ : ↑Λ → Spin,
      (∏ a ∈ A, ((σ a).toSign : ℝ))
      * (n.weight G Λ β J
        * ∏ e : (inducedGraph G Λ).edgeSet,
            (Config.spinEdgeProduct σ (e : Sym2 ↑Λ))^(n e)))
      = if n.HasSources G Λ A
        then n.weight G Λ β J * (2 : ℝ)^(Fintype.card ↑Λ) else 0 := by
  -- Pull the σ-independent weight out of the σ-sum.
  have heq : ∀ σ : ↑Λ → Spin,
      (∏ a ∈ A, ((σ a).toSign : ℝ))
      * (n.weight G Λ β J
        * ∏ e : (inducedGraph G Λ).edgeSet,
            (Config.spinEdgeProduct σ (e : Sym2 ↑Λ))^(n e))
      = n.weight G Λ β J *
        ((∏ a ∈ A, ((σ a).toSign : ℝ))
         * ∏ e : (inducedGraph G Λ).edgeSet,
            (Config.spinEdgeProduct σ (e : Sym2 ↑Λ))^(n e)) := by
    intro σ; ring
  rw [Finset.sum_congr rfl (fun σ _ => heq σ), ← Finset.mul_sum,
    Config.sum_spinA_prod_spinEdgeProduct_pow_hasSources]
  by_cases hA : n.HasSources G Λ A
  · rw [if_pos hA, if_pos hA]
  · rw [if_neg hA, if_neg hA, mul_zero]

omit [DecidableEq V] in
/-- **Per-current σ-sum in Taylor-coefficient form**: at fixed
current `n` and source set `A`,
`∑_σ σ_A · ∏_e (β J · spinEdgeProduct σ e)^(n e) / (n e)!
  = weight β J n · 2^|Λ|` if `n.HasSources A`, else `0`. The
per-current contribution to the random-current expansion of
`Z · ⟨σ_A⟩` in the standard Taylor-coefficient form
(FV §3.7, eq. (3.45)). -/
theorem Config.sum_spinA_prod_taylor_pow_hasSources
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (β J : ℝ) (n : Current G Λ) (A : Finset ↑Λ)
    [Decidable (n.HasSources G Λ A)] :
    (∑ σ : ↑Λ → Spin,
      (∏ a ∈ A, ((σ a).toSign : ℝ))
      * ∏ e : (inducedGraph G Λ).edgeSet,
          (β * J * Config.spinEdgeProduct σ (e : Sym2 ↑Λ))^(n e)
            / ((n e).factorial : ℝ))
      = if n.HasSources G Λ A
        then n.weight G Λ β J * (2 : ℝ)^(Fintype.card ↑Λ) else 0 := by
  have heq : ∀ σ : ↑Λ → Spin,
      (∏ a ∈ A, ((σ a).toSign : ℝ))
      * ∏ e : (inducedGraph G Λ).edgeSet,
          (β * J * Config.spinEdgeProduct σ (e : Sym2 ↑Λ))^(n e)
            / ((n e).factorial : ℝ)
      = (∏ a ∈ A, ((σ a).toSign : ℝ))
        * (n.weight G Λ β J
          * ∏ e : (inducedGraph G Λ).edgeSet,
              (Config.spinEdgeProduct σ (e : Sym2 ↑Λ))^(n e)) := by
    intro σ
    rw [← Current.weight_mul_prod_pow G Λ β J n
      (fun e => Config.spinEdgeProduct σ (e : Sym2 ↑Λ))]
  rw [Finset.sum_congr rfl (fun σ _ => heq σ)]
  exact Config.sum_spinA_weight_prod_spinEdgeProduct_pow_hasSources
    G Λ β J n A

omit [DecidableEq V] in
/-- **Edge product of Taylor partial sums = current-bounded sum**:
the Fubini swap
`∏_e ∑_{k ≤ N} (β J · spinEdgeProduct σ e)^k / k!
  = ∑_{n : CurrentBounded N} ∏_e (β J · spinEdgeProduct σ e)^(n e) / (n e)!`.
The finite analogue (using `Fintype.prod_sum`) of the infinite
Taylor expansion that links the partition function to the
random-current sum (FV §3.7). -/
theorem Config.prod_sum_taylor_eq_sum_currentBounded
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (β J : ℝ) (N : ℕ) (σ : ↑Λ → Spin) :
    (∏ e : (inducedGraph G Λ).edgeSet,
       ∑ k : Fin (N+1),
         (β * J * Config.spinEdgeProduct σ (e : Sym2 ↑Λ))^(k : ℕ)
           / (((k : ℕ)).factorial : ℝ))
     = ∑ n : CurrentBounded G Λ N,
         ∏ e : (inducedGraph G Λ).edgeSet,
           (β * J * Config.spinEdgeProduct σ (e : Sym2 ↑Λ))^((n e : ℕ))
             / (((n e : ℕ)).factorial : ℝ) :=
  Fintype.prod_sum (κ := fun _ : (inducedGraph G Λ).edgeSet => Fin (N+1))
    (fun e k =>
      (β * J * Config.spinEdgeProduct σ (e : Sym2 ↑Λ))^(k : ℕ)
        / (((k : ℕ)).factorial : ℝ))

omit [DecidableEq V] in
/-- **Bounded random-current expansion of `∑_σ σ_A · ∏_e Taylor
partial sum`**: the finite-`N` analogue of the random-current
expansion of `Z · ⟨σ_A⟩` (FV §3.7, eq. (3.45)),
\(∑_σ σ_A · ∏_e ∑_{k ≤ N} (β J σ_e)^k / k!
  = ∑_{n : CurrentBounded N} [n.toCurrent.HasSources A]
     · weight β J n.toCurrent · 2^|Λ|\).
Combines `prod_sum_taylor_eq_sum_currentBounded` with
`sum_spinA_prod_taylor_pow_hasSources`. -/
theorem Config.sum_spinA_prod_taylor_partialSum_eq_sum_currentBounded
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (β J : ℝ) (N : ℕ) (A : Finset ↑Λ)
    [∀ n : CurrentBounded G Λ N,
      Decidable ((n.toCurrent G Λ).HasSources G Λ A)] :
    (∑ σ : ↑Λ → Spin,
      (∏ a ∈ A, ((σ a).toSign : ℝ))
      * ∏ e : (inducedGraph G Λ).edgeSet,
          ∑ k : Fin (N+1),
            (β * J * Config.spinEdgeProduct σ (e : Sym2 ↑Λ))^(k : ℕ)
              / (((k : ℕ)).factorial : ℝ))
      = ∑ n : CurrentBounded G Λ N,
          if (n.toCurrent G Λ).HasSources G Λ A
          then (n.toCurrent G Λ).weight G Λ β J * (2 : ℝ)^(Fintype.card ↑Λ)
          else 0 := by
  -- Step 1: replace inner edge product with sum over CurrentBounded.
  simp_rw [Config.prod_sum_taylor_eq_sum_currentBounded G Λ β J N _]
  -- ∑_σ σ_A · ∑_n (∏_e ...)
  -- Step 2: distribute σ_A through the inner sum, then swap σ-sum and n-sum.
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  -- Step 3: each inner ∑_σ σ_A · (∏_e ...) is exactly per-current Taylor sum.
  exact Finset.sum_congr rfl (fun n _ =>
    Config.sum_spinA_prod_taylor_pow_hasSources G Λ β J
      (n.toCurrent G Λ) A)

omit [DecidableEq V] in
/-- **Bounded random-current expansion via `CurrentBounded.weightSum`**:
clean reformulation of `sum_spinA_prod_taylor_partialSum_eq_sum_currentBounded`
collecting the indicator+weight sum into the existing
`CurrentBounded.weightSum` definition,
\(∑_σ σ_A · ∏_e ∑_{k ≤ N} (β J σ_e)^k / k!
  = 2^|Λ| · CurrentBounded.weightSum N A β J\). The finite-`N`
analogue ready for the `N → ∞` limit step (FV §3.7, eq. (3.45)). -/
theorem Config.sum_spinA_prod_taylor_partialSum_eq_pow_card_mul_currentBounded_weightSum
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (β J : ℝ) (N : ℕ) (A : Finset ↑Λ) :
    (∑ σ : ↑Λ → Spin,
      (∏ a ∈ A, ((σ a).toSign : ℝ))
      * ∏ e : (inducedGraph G Λ).edgeSet,
          ∑ k : Fin (N+1),
            (β * J * Config.spinEdgeProduct σ (e : Sym2 ↑Λ))^(k : ℕ)
              / (((k : ℕ)).factorial : ℝ))
      = (2 : ℝ)^(Fintype.card ↑Λ)
        * CurrentBounded.weightSum G Λ N A β J := by
  classical
  rw [Config.sum_spinA_prod_taylor_partialSum_eq_sum_currentBounded G Λ β J N A]
  unfold CurrentBounded.weightSum Current.HasSources
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  split_ifs <;> ring

omit [DecidableEq V] in
/-- **`CurrentBounded.weightSum` at zero β collapses to indicator
on `A = ∅`**: `CurrentBounded.weightSum N A 0 J = 1` if `A = ∅`,
else `0`. The finite-sum analogue of `weightSum_beta_zero`; only
the zero current contributes since `weight 0 J n = 0` for any
non-zero `n`. -/
theorem CurrentBounded.weightSum_beta_zero (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    [DecidableEq ↑Λ] (N : ℕ) (A : Finset ↑Λ) (J : ℝ) :
    CurrentBounded.weightSum G Λ N A 0 J = if A = ∅ then 1 else 0 := by
  classical
  unfold CurrentBounded.weightSum
  -- Only n = 0 contributes since weight 0 J n.toCurrent = 0 for n.toCurrent ≠ 0.
  have h_single : ∀ n : CurrentBounded G Λ N, n ≠ 0 →
      (if (n.toCurrent G Λ).sources G Λ = A
        then (n.toCurrent G Λ).weight G Λ 0 J else 0) = 0 := by
    intro n hn
    have hntc : n.toCurrent G Λ ≠ 0 := by
      intro hnc
      apply hn
      funext e
      have hval : (n.toCurrent G Λ) e = 0 := by rw [hnc]; rfl
      simpa [CurrentBounded.toCurrent] using hval
    by_cases hsr : (n.toCurrent G Λ).sources G Λ = A
    · rw [if_pos hsr, Current.weight_beta_zero, if_neg hntc]
    · rw [if_neg hsr]
  rw [Finset.sum_eq_single (0 : CurrentBounded G Λ N)
    (fun n _ hn => h_single n hn) (fun h => absurd (Finset.mem_univ _) h)]
  -- Goal: if (0.toCurrent).sources = A then weight 0 J ... else 0 = if A = ∅ then 1 else 0
  have h0tc : (0 : CurrentBounded G Λ N).toCurrent G Λ = 0 := by
    funext e; rfl
  rw [h0tc, Current.zero_sources, Current.zero_weight]
  exact if_congr eq_comm rfl rfl

omit [DecidableEq V] in
/-- **`CurrentBounded.weightSum` at zero J collapses to indicator
on `A = ∅`**: symmetric counterpart of `weightSum_beta_zero`. -/
theorem CurrentBounded.weightSum_J_zero (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    [DecidableEq ↑Λ] (N : ℕ) (A : Finset ↑Λ) (β : ℝ) :
    CurrentBounded.weightSum G Λ N A β 0 = if A = ∅ then 1 else 0 := by
  classical
  unfold CurrentBounded.weightSum
  have h_single : ∀ n : CurrentBounded G Λ N, n ≠ 0 →
      (if (n.toCurrent G Λ).sources G Λ = A
        then (n.toCurrent G Λ).weight G Λ β 0 else 0) = 0 := by
    intro n hn
    have hntc : n.toCurrent G Λ ≠ 0 := by
      intro hnc
      apply hn
      funext e
      have hval : (n.toCurrent G Λ) e = 0 := by rw [hnc]; rfl
      simpa [CurrentBounded.toCurrent] using hval
    by_cases hsr : (n.toCurrent G Λ).sources G Λ = A
    · rw [if_pos hsr, Current.weight_J_zero, if_neg hntc]
    · rw [if_neg hsr]
  rw [Finset.sum_eq_single (0 : CurrentBounded G Λ N)
    (fun n _ hn => h_single n hn) (fun h => absurd (Finset.mem_univ _) h)]
  have h0tc : (0 : CurrentBounded G Λ N).toCurrent G Λ = 0 := by
    funext e; rfl
  rw [h0tc, Current.zero_sources, Current.zero_weight]
  exact if_congr eq_comm rfl rfl

omit [DecidableEq V] in
/-- **Joint weight = sum-weight × product of binomial coefficients**:
the key combinatorial identity feeding the **Aizenman switching
lemma** (FV §3.7), \(weight β J n₁ \cdot weight β J n₂
  = weight β J (n₁ + n₂) \cdot ∏_e \binom{n₁ e + n₂ e}{n₁ e}\).
Each per-edge factor uses
`Nat.add_choose_mul_factorial_mul_factorial`. -/
theorem Current.weight_mul_weight_eq_weight_add_mul_choose
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (β J : ℝ) (n₁ n₂ : Current G Λ) :
    n₁.weight G Λ β J * n₂.weight G Λ β J
      = (n₁ + n₂).weight G Λ β J
        * ∏ e : (inducedGraph G Λ).edgeSet,
            (Nat.choose (n₁ e + n₂ e) (n₁ e) : ℝ) := by
  unfold Current.weight
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun e _ => ?_)
  rw [Current.add_apply, pow_add]
  -- Express (n₁+n₂)! = choose · n₁! · n₂!  in ℝ.
  have hchoose : ((n₁ e + n₂ e).factorial : ℝ)
      = ((n₁ e + n₂ e).choose (n₁ e) : ℝ)
        * ((n₁ e).factorial : ℝ) * ((n₂ e).factorial : ℝ) := by
    have hk : (n₂ e + n₁ e).choose (n₁ e) * (n₂ e).factorial * (n₁ e).factorial
              = (n₂ e + n₁ e).factorial :=
      Nat.add_choose_mul_factorial_mul_factorial _ _
    rw [Nat.add_comm (n₂ e) (n₁ e)] at hk
    have heq : ((n₁ e + n₂ e).factorial : ℝ)
        = (((n₁ e + n₂ e).choose (n₁ e) * (n₂ e).factorial
            * (n₁ e).factorial : ℕ) : ℝ) := by
      exact_mod_cast hk.symm
    rw [heq]; push_cast; ring
  rw [hchoose]
  have hf1 : ((n₁ e).factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_pos _).ne'
  have hf2 : ((n₂ e).factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_pos _).ne'
  have hch : ((n₁ e + n₂ e).choose (n₁ e) : ℝ) ≠ 0 := by
    have h_nat : (n₁ e + n₂ e).choose (n₁ e) ≠ 0 :=
      (Nat.choose_pos (Nat.le_add_right _ _)).ne'
    exact_mod_cast h_nat
  field_simp

/-- **Joint factor**: per-edge binomial product
\(jointFactor n₁ n₂ := ∏_e \binom{n₁ e + n₂ e}{n₁ e}\). The
\(σ\)-independent factor in the switching-lemma identity
`weight n₁ * weight n₂ = weight (n₁+n₂) * jointFactor n₁ n₂`
(see #843). The structural object underlying Aizenman switching
(FV §3.7). -/
noncomputable def Current.jointFactor (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (n₁ n₂ : Current G Λ) : ℝ :=
  ∏ e : (inducedGraph G Λ).edgeSet,
    (Nat.choose (n₁ e + n₂ e) (n₁ e) : ℝ)

omit [DecidableEq V] in
/-- **`jointFactor` is symmetric**: \(jointFactor n₁ n₂ = jointFactor n₂ n₁\).
Each per-edge factor `Nat.choose (n₁ e + n₂ e) (n₁ e)` equals
`Nat.choose (n₂ e + n₁ e) (n₂ e)` by `Nat.choose_symm_add`
(after commuting the sum). -/
theorem Current.jointFactor_symm (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (n₁ n₂ : Current G Λ) :
    Current.jointFactor G Λ n₁ n₂ = Current.jointFactor G Λ n₂ n₁ := by
  unfold Current.jointFactor
  refine Finset.prod_congr rfl (fun e _ => ?_)
  congr 1
  rw [Nat.add_comm (n₁ e) (n₂ e)]
  exact (Nat.choose_symm_add).symm

omit [DecidableEq V] in
/-- **`jointFactor 0 n = 1`**: each per-edge factor
`Nat.choose (0 + n e) 0 = 1`. -/
@[simp]
theorem Current.jointFactor_zero_left (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n : Current G Λ) :
    Current.jointFactor G Λ 0 n = 1 := by
  unfold Current.jointFactor
  refine Finset.prod_eq_one (fun e _ => ?_)
  change ((Nat.choose ((0 : Current G Λ) e + n e) ((0 : Current G Λ) e) : ℝ)) = 1
  simp

omit [DecidableEq V] in
/-- **`jointFactor n 0 = 1`**: by `jointFactor_symm` and `_zero_left`. -/
@[simp]
theorem Current.jointFactor_zero_right (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n : Current G Λ) :
    Current.jointFactor G Λ n 0 = 1 := by
  rw [Current.jointFactor_symm, Current.jointFactor_zero_left]

omit [DecidableEq V] in
/-- **`jointFactor` is strictly positive**: every per-edge
`Nat.choose (n₁ e + n₂ e) (n₁ e)` is `> 0` (by `Nat.choose_pos`
since `n₁ e ≤ n₁ e + n₂ e`). -/
theorem Current.jointFactor_pos (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (n₁ n₂ : Current G Λ) :
    0 < Current.jointFactor G Λ n₁ n₂ := by
  unfold Current.jointFactor
  refine Finset.prod_pos (fun e _ => ?_)
  exact_mod_cast Nat.choose_pos (Nat.le_add_right _ _)

omit [DecidableEq V] in
/-- **Joint weight = sum-weight × `jointFactor`**: clean alias of
`Current.weight_mul_weight_eq_weight_add_mul_choose` (#843)
using the named `Current.jointFactor` (#844). The Aizenman
switching key identity in its final form (FV §3.7). -/
theorem Current.weight_mul_weight_eq_weight_add_mul_jointFactor
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (β J : ℝ) (n₁ n₂ : Current G Λ) :
    n₁.weight G Λ β J * n₂.weight G Λ β J
      = (n₁ + n₂).weight G Λ β J * Current.jointFactor G Λ n₁ n₂ :=
  Current.weight_mul_weight_eq_weight_add_mul_choose G Λ β J n₁ n₂

omit [DecidableEq V] in
/-- **`CurrentBounded.weightSum_empty_pos` (non-negative coupling)**:
\(CurrentBounded.weightSum N ∅ β J ≥ 1 > 0\) when `0 ≤ β * J`,
since the zero current is bounded, has \(\text{sources} = ∅\),
and contributes weight `1`. The other terms are `≥ 0`. -/
theorem CurrentBounded.weightSum_empty_pos (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    [DecidableEq ↑Λ] (N : ℕ) {β J : ℝ} (hβJ : 0 ≤ β * J) :
    0 < CurrentBounded.weightSum G Λ N ∅ β J := by
  unfold CurrentBounded.weightSum
  -- 0 ∈ univ, summand at 0 = if (0).sources = ∅ then weight 0 else 0 = weight 0 = 1
  have h_zero_summand :
      (if ((0 : CurrentBounded G Λ N).toCurrent G Λ).sources G Λ = ∅
        then ((0 : CurrentBounded G Λ N).toCurrent G Λ).weight G Λ β J
        else 0) = 1 := by
    have h0tc : (0 : CurrentBounded G Λ N).toCurrent G Λ = 0 := by
      funext e; rfl
    rw [h0tc, Current.zero_sources, if_pos rfl, Current.zero_weight]
  refine Finset.sum_pos' (fun n _ => ?_) ⟨0, Finset.mem_univ _, ?_⟩
  · by_cases h : (n.toCurrent G Λ).sources G Λ = ∅
    · simp only [h, if_true]
      exact Current.weight_nonneg G Λ hβJ _
    · simp only [h, if_false, le_refl]
  · rw [h_zero_summand]; exact zero_lt_one

omit [DecidableEq V] in
/-- **Sum of two currents is source-free iff their source sets
agree**: `(n + m).IsSourceFree ↔ n.sources = m.sources`. Direct
consequence of `add_sources_eq` and `symmDiff_eq_bot` (the
symmetric difference vanishes iff the two sets agree). The
"squaring" step at the heart of the Aizenman switching lemma's
source-set bookkeeping. -/
theorem Current.add_isSourceFree_iff (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n m : Current G Λ) :
    (n + m).IsSourceFree G Λ ↔ n.sources G Λ = m.sources G Λ := by
  unfold Current.IsSourceFree
  rw [Current.add_sources_eq, ← Finset.bot_eq_empty, symmDiff_eq_bot]

omit [DecidableEq V] in
/-- **Self-add is always source-free**: \(n + n\) is source-free
because each parity contribution is doubled (hence even), or
equivalently \(n.sources \triangle n.sources = ∅\). Direct
corollary of `add_isSourceFree_iff`. -/
@[simp]
theorem Current.self_add_isSourceFree (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) :
    (n + n).IsSourceFree G Λ :=
  (Current.add_isSourceFree_iff G Λ n n).mpr rfl

/-- **Real exponential as a real Taylor `tsum`**:
\(Real.exp x = ∑' n, x^n / n!\). Local convenience wrapper
composing `Real.exp_eq_exp_ℝ` (Real.exp matches `NormedSpace.exp`)
and `NormedSpace.exp_eq_tsum_div` (the `exp = ∑' n, x^n / n!`
formula in `CharZero` algebras). Bridges `Real.exp` and the
bounded Taylor partial-sum form used in
`Config.sum_spinA_prod_taylor_partialSum_eq_pow_card_mul_currentBounded_weightSum`
(#841) for the random-current expansion (FV §3.7). -/
theorem Real.exp_eq_tsum_div_factorial (x : ℝ) :
    Real.exp x = ∑' n : ℕ, x ^ n / (n.factorial : ℝ) := by
  rw [Real.exp_eq_exp_ℝ]
  exact congrFun NormedSpace.exp_eq_tsum_div x

/-- **Real Taylor partial sum converges to `Real.exp`**:
\(∑_{k ≤ N} x^k / k! → Real.exp x\) as `N → ∞`. The first analytic
limit step toward `N → ∞` in the bounded random-current expansion
(FV §3.7). Combines `Real.exp_eq_tsum_div_factorial` with
`Real.summable_pow_div_factorial` and `Summable.tendsto_sum_tsum_nat`,
shifting the index from `range N` to `range (N+1)` via
`tendsto_add_atTop_nat 1`. -/
theorem Real.tendsto_partial_sum_atTop_exp (x : ℝ) :
    Filter.Tendsto
      (fun N : ℕ => ∑ k ∈ Finset.range (N + 1), x ^ k / (k.factorial : ℝ))
      Filter.atTop (nhds (Real.exp x)) := by
  rw [Real.exp_eq_tsum_div_factorial]
  have h_summable : Summable (fun k : ℕ => x ^ k / (k.factorial : ℝ)) :=
    Real.summable_pow_div_factorial x
  exact (Summable.tendsto_sum_tsum_nat h_summable).comp
    (Filter.tendsto_add_atTop_nat 1)

omit [DecidableEq V] in
/-- **Edge-product of Taylor partial sums converges to product of
exponentials**: as `N → ∞`,
\(∏_e ∑_{k ≤ N} (β J σ_e)^k / k! → ∏_e Real.exp (β J σ_e)\).
The finite product is continuous in each factor (`tendsto_finset_prod`),
and each per-edge factor converges by
`Real.tendsto_partial_sum_atTop_exp` (#851). The `Fin (N+1)` sum
matches the `range (N+1)` sum via `Fin.sum_univ_eq_sum_range`.
Second analytic step toward the `N → ∞` limit of the bounded
random-current expansion (FV §3.7). -/
theorem Config.tendsto_prod_Fin_partial_sum_atTop_prod_exp
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (β J : ℝ) (σ : ↑Λ → Spin) :
    Filter.Tendsto
      (fun N : ℕ =>
        ∏ e : (inducedGraph G Λ).edgeSet,
          ∑ k : Fin (N + 1),
            (β * J * Config.spinEdgeProduct σ (e : Sym2 ↑Λ)) ^ (k : ℕ)
              / (((k : ℕ).factorial : ℝ)))
      Filter.atTop
      (nhds
        (∏ e : (inducedGraph G Λ).edgeSet,
          Real.exp (β * J * Config.spinEdgeProduct σ (e : Sym2 ↑Λ)))) := by
  -- Convert Fin (N+1) sums to range (N+1) sums.
  have hconv : ∀ N : ℕ,
      (∏ e : (inducedGraph G Λ).edgeSet,
          ∑ k : Fin (N + 1),
            (β * J * Config.spinEdgeProduct σ (e : Sym2 ↑Λ)) ^ (k : ℕ)
              / (((k : ℕ).factorial : ℝ)))
        = ∏ e : (inducedGraph G Λ).edgeSet,
            ∑ k ∈ Finset.range (N + 1),
              (β * J * Config.spinEdgeProduct σ (e : Sym2 ↑Λ)) ^ k
                / ((k.factorial : ℝ)) := by
    intro N
    refine Finset.prod_congr rfl (fun e _ => ?_)
    exact Fin.sum_univ_eq_sum_range
      (fun k => (β * J * Config.spinEdgeProduct σ (e : Sym2 ↑Λ)) ^ k
                  / ((k.factorial : ℝ))) (N + 1)
  simp_rw [hconv]
  refine tendsto_finset_prod _ (fun e _ => ?_)
  exact Real.tendsto_partial_sum_atTop_exp _

omit [DecidableEq V] in
/-- **Sum-σ-A × edge-product partial sum → sum-σ-A × edge-product exp**:
as `N → ∞`,
\(∑_σ σ_A · ∏_e ∑_{k ≤ N} (β J σ_e)^k / k!
  → ∑_σ σ_A · ∏_e Real.exp (β J σ_e)\).
The third analytic step in the `N → ∞` limit, combining
`tendsto_prod_Fin_partial_sum_atTop_prod_exp` (#852, per-σ
edge-product convergence) with `Tendsto.const_mul` (σ_A is
`N`-independent) and `tendsto_finset_sum` (finite σ-sum is
continuous). Bridges the bounded random-current expansion with
the actual Boltzmann weight `Z · ⟨σ_A⟩` (FV §3.7). -/
theorem Config.tendsto_sum_spinA_prod_partial_sum_atTop_sum_spinA_prod_exp
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (β J : ℝ) (A : Finset ↑Λ) :
    Filter.Tendsto
      (fun N : ℕ => ∑ σ : ↑Λ → Spin,
        (∏ a ∈ A, ((σ a).toSign : ℝ))
        * ∏ e : (inducedGraph G Λ).edgeSet,
            ∑ k : Fin (N + 1),
              (β * J * Config.spinEdgeProduct σ (e : Sym2 ↑Λ)) ^ (k : ℕ)
                / (((k : ℕ).factorial : ℝ)))
      Filter.atTop
      (nhds
        (∑ σ : ↑Λ → Spin,
          (∏ a ∈ A, ((σ a).toSign : ℝ))
          * ∏ e : (inducedGraph G Λ).edgeSet,
              Real.exp (β * J * Config.spinEdgeProduct σ (e : Sym2 ↑Λ)))) := by
  refine tendsto_finset_sum _ (fun σ _ => ?_)
  exact (Config.tendsto_prod_Fin_partial_sum_atTop_prod_exp G Λ β J σ).const_mul _

omit [DecidableEq V] in
/-- **Bounded `CurrentBounded.weightSum` × `2^|Λ|` converges to
the Boltzmann sum**: as `N → ∞`,
\(2^|Λ| · CurrentBounded.weightSum N A β J
  → ∑_σ σ_A · ∏_e Real.exp (β J σ_e)\).
Combines `sum_spinA_prod_taylor_partialSum_eq_pow_card_mul_currentBounded_weightSum`
(#841) with
`tendsto_sum_spinA_prod_partial_sum_atTop_sum_spinA_prod_exp`
(#853). Closes the LHS-side `N → ∞` limit, connecting the
bounded random-current sum to the actual Ising Boltzmann weight
`Z · ⟨σ_A⟩` (FV §3.7). -/
theorem Config.tendsto_pow_card_mul_currentBounded_weightSum_atTop_sum_spinA_prod_exp
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (β J : ℝ) (A : Finset ↑Λ) :
    Filter.Tendsto
      (fun N : ℕ =>
        (2 : ℝ) ^ (Fintype.card ↑Λ) * CurrentBounded.weightSum G Λ N A β J)
      Filter.atTop
      (nhds
        (∑ σ : ↑Λ → Spin,
          (∏ a ∈ A, ((σ a).toSign : ℝ))
          * ∏ e : (inducedGraph G Λ).edgeSet,
              Real.exp (β * J * Config.spinEdgeProduct σ (e : Sym2 ↑Λ)))) := by
  have hbridge :
      (fun N : ℕ =>
        (2 : ℝ) ^ (Fintype.card ↑Λ) * CurrentBounded.weightSum G Λ N A β J)
      = fun N : ℕ => ∑ σ : ↑Λ → Spin,
        (∏ a ∈ A, ((σ a).toSign : ℝ))
        * ∏ e : (inducedGraph G Λ).edgeSet,
            ∑ k : Fin (N + 1),
              (β * J * Config.spinEdgeProduct σ (e : Sym2 ↑Λ)) ^ (k : ℕ)
                / (((k : ℕ).factorial : ℝ)) := by
    funext N
    exact (Config.sum_spinA_prod_taylor_partialSum_eq_pow_card_mul_currentBounded_weightSum
      G Λ β J N A).symm
  rw [hbridge]
  exact Config.tendsto_sum_spinA_prod_partial_sum_atTop_sum_spinA_prod_exp G Λ β J A

omit [DecidableEq V] in
/-- **`CurrentBounded.toCurrent` is injective**: two bounded
currents with the same `Current` representative agree as
functions, hence as bounded currents (`Fin (N+1)` is determined
by `.val`). -/
theorem CurrentBounded.toCurrent_injective (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet] {N : ℕ} :
    Function.Injective
      (CurrentBounded.toCurrent G Λ : CurrentBounded G Λ N → Current G Λ) := by
  intro n₁ n₂ h
  funext e
  apply Fin.ext
  exact congrFun h e

/-- **`Current.boundedFinset N`**: the `Finset` of currents
\(n : Current G Λ\) with \(n e ≤ N\) for every edge \(e\),
realised as the image of `CurrentBounded G Λ N` under `toCurrent`.
The natural `Finset` filtration of `Current G Λ` whose limit
covers all currents (every current has finite max value since the
edge set is finite). Foundation for the RHS-side `N → ∞` limit
of the random-current expansion (FV §3.7). -/
noncomputable def Current.boundedFinset (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (N : ℕ) :
    Finset (Current G Λ) := by
  classical
  exact (Finset.univ : Finset (CurrentBounded G Λ N)).image
    (CurrentBounded.toCurrent G Λ)

/-- **Membership in `boundedFinset N`**: \(n ∈ boundedFinset N\)
iff every edge value satisfies \(n e ≤ N\). -/
theorem Current.mem_boundedFinset_iff (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (N : ℕ) (n : Current G Λ) :
    n ∈ Current.boundedFinset G Λ N ↔ ∀ e : (inducedGraph G Λ).edgeSet, n e ≤ N := by
  unfold Current.boundedFinset
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨nB, rfl⟩ e
    change ((nB e).val : ℕ) ≤ N
    exact Nat.lt_succ_iff.mp (nB e).is_lt
  · intro hbound
    refine ⟨fun e => ⟨n e, ?_⟩, ?_⟩
    · exact Nat.lt_succ_iff.mpr (hbound e)
    · funext e
      rfl

/-- **`boundedFinset` is monotone in `N`**:
\(N_1 ≤ N_2 → boundedFinset\,N_1 ⊆ boundedFinset\,N_2\).
A larger bound includes more currents. Direct via
`mem_boundedFinset_iff`. -/
theorem Current.boundedFinset_mono (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] {N₁ N₂ : ℕ} (h : N₁ ≤ N₂) :
    Current.boundedFinset G Λ N₁ ⊆ Current.boundedFinset G Λ N₂ := by
  intro n hn
  rw [Current.mem_boundedFinset_iff] at hn ⊢
  exact fun e => le_trans (hn e) h

/-- **Every current eventually lies in some `boundedFinset N`**:
for every `n : Current G Λ`, there exists `N : ℕ` such that
\(n ∈ boundedFinset N\). Concretely take
\(N = max_{e} n e\) (the supremum over the finite edge set).
The cofinality property of the filtration. -/
theorem Current.exists_mem_boundedFinset (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (n : Current G Λ) :
    ∃ N : ℕ, n ∈ Current.boundedFinset G Λ N := by
  classical
  refine ⟨Finset.univ.sup n, ?_⟩
  rw [Current.mem_boundedFinset_iff]
  intro e
  exact Finset.le_sup (Finset.mem_univ e)

/-- **`boundedFinset` is cofinal in `Filter.atTop` on
`Finset (Current G Λ)`**: for every finset `s` of currents,
eventually `s ⊆ boundedFinset N` (take `N` = max bound across all
currents in `s` and all edges). Bridges the ℕ-indexed `atTop`
filter with the unconditional summation filter on `Finset`. -/
theorem Current.tendsto_boundedFinset_atTop_finsetAtTop
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    Filter.Tendsto (Current.boundedFinset G Λ)
      Filter.atTop (Filter.atTop : Filter (Finset (Current G Λ))) := by
  classical
  rw [Filter.tendsto_atTop_atTop]
  intro s
  refine ⟨s.sup (fun n => Finset.univ.sup n), ?_⟩
  intro M hM n hn
  rw [Current.mem_boundedFinset_iff]
  intro e
  calc n e ≤ Finset.univ.sup n := Finset.le_sup (Finset.mem_univ e)
    _ ≤ s.sup (fun n => Finset.univ.sup n) := Finset.le_sup hn
    _ ≤ M := hM

/-- **Summable partial sums over `boundedFinset` converge to
`tsum`**: under `Summable f`, the partial sums
\(∑ n ∈ boundedFinset N, f n → ∑' n, f n\) as `N → ∞`. Composing
the cofinal sequence (`tendsto_boundedFinset_atTop_finsetAtTop`)
with `Summable.hasSum`. -/
theorem Summable.tendsto_sum_boundedFinset
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {α : Type*} [AddCommMonoid α] [TopologicalSpace α]
    {f : Current G Λ → α} (hf : Summable f) :
    Filter.Tendsto (fun N : ℕ => ∑ n ∈ Current.boundedFinset G Λ N, f n)
      Filter.atTop (nhds (∑' n, f n)) :=
  hf.hasSum.comp (Current.tendsto_boundedFinset_atTop_finsetAtTop G Λ)

/-- **Bounded weight sum as sum over `boundedFinset`**: rewrite
\(CurrentBounded.weightSum N A β J\) as a sum over the image
finset \(boundedFinset N\) of currents. Uses `Finset.sum_bij`
with `toCurrent` as the bijection. Bridges the bounded sum (over
`CurrentBounded N` as Fintype) with the `Current G Λ`-indexed
Finset sum used in subsequent N → ∞ arguments. -/
theorem CurrentBounded.weightSum_eq_sum_boundedFinset (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    [DecidableEq ↑Λ] (N : ℕ) (A : Finset ↑Λ) (β J : ℝ) :
    CurrentBounded.weightSum G Λ N A β J
      = ∑ n ∈ Current.boundedFinset G Λ N,
          if n.sources G Λ = A then n.weight G Λ β J else 0 := by
  classical
  unfold CurrentBounded.weightSum
  refine Finset.sum_bij
    (fun (nB : CurrentBounded G Λ N) _ => CurrentBounded.toCurrent G Λ nB)
    ?_ ?_ ?_ ?_
  · -- maps into boundedFinset
    intro nB _
    rw [Current.mem_boundedFinset_iff]
    intro e
    exact Nat.lt_succ_iff.mp (nB e).is_lt
  · -- injective on Finset.univ
    intro nB₁ _ nB₂ _ hbij
    exact CurrentBounded.toCurrent_injective G Λ hbij
  · -- surjective onto boundedFinset
    intro n hn
    rw [Current.mem_boundedFinset_iff] at hn
    refine ⟨fun e => ⟨n e, Nat.lt_succ_iff.mpr (hn e)⟩, Finset.mem_univ _, ?_⟩
    funext e; rfl
  · -- summand match
    intro nB _
    rfl

set_option linter.unusedDecidableInType false in
/-- **RHS-side `N → ∞` limit capstone**: under summability of the
weight-with-source-condition function,
\(CurrentBounded.weightSum N A β J → Current.weightSum A β J\) as
`N → ∞`. Combines `weightSum_eq_sum_boundedFinset` (#858) with
`Summable.tendsto_sum_boundedFinset` (#857). Together with
the LHS-side limit (#854), gives
`Current.weightSum A β J = (1/2^|Λ|) · ∑_σ σ_A · ∏_e Real.exp (β J σ_e)`
under summability — the random-current expression of the Ising
correlation function (FV §3.7). -/
theorem CurrentBounded.tendsto_weightSum_atTop_currentWeightSum
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (β J : ℝ) (A : Finset ↑Λ)
    (hf : Summable (fun n : Current G Λ =>
      if n.sources G Λ = A then n.weight G Λ β J else 0)) :
    Filter.Tendsto (fun N : ℕ => CurrentBounded.weightSum G Λ N A β J)
      Filter.atTop (nhds (Current.weightSum G Λ A β J)) := by
  have h_eq : ∀ N, CurrentBounded.weightSum G Λ N A β J
              = ∑ n ∈ Current.boundedFinset G Λ N,
                  if n.sources G Λ = A then n.weight G Λ β J else 0 :=
    fun N => CurrentBounded.weightSum_eq_sum_boundedFinset G Λ N A β J
  simp_rw [h_eq]
  unfold Current.weightSum
  exact Summable.tendsto_sum_boundedFinset G Λ hf

set_option linter.unusedDecidableInType false in
/-- **`CurrentBounded.weightSum` is monotone in `N`** under
non-negative coupling: \(N_1 ≤ N_2 →
CurrentBounded.weightSum N_1 A β J ≤ CurrentBounded.weightSum N_2 A β J\).
A larger bound includes more (non-negative) summands. Combines
`weightSum_eq_sum_boundedFinset` with `boundedFinset_mono` and
`Finset.sum_le_sum_of_subset_of_nonneg`. -/
theorem CurrentBounded.weightSum_mono (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (A : Finset ↑Λ) {β J : ℝ} (hβJ : 0 ≤ β * J)
    {N₁ N₂ : ℕ} (h : N₁ ≤ N₂) :
    CurrentBounded.weightSum G Λ N₁ A β J
      ≤ CurrentBounded.weightSum G Λ N₂ A β J := by
  rw [CurrentBounded.weightSum_eq_sum_boundedFinset,
    CurrentBounded.weightSum_eq_sum_boundedFinset]
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (Current.boundedFinset_mono G Λ h) (fun n _ _ => ?_)
  split_ifs
  · exact Current.weight_nonneg G Λ hβJ n
  · exact le_refl 0

set_option linter.unusedDecidableInType false in
/-- **Monotone convergence of `CurrentBounded.weightSum`** under
non-negative coupling and bounded-above hypothesis:
\(Tendsto (fun N => CurrentBounded.weightSum N A β J) atTop
  (nhds (⨆ N, CurrentBounded.weightSum N A β J))\).
Combines `CurrentBounded.weightSum_mono` (#860) with
`tendsto_atTop_ciSup`. Avoids the explicit `Summable` hypothesis
of `tendsto_weightSum_atTop_currentWeightSum` (#859). -/
theorem CurrentBounded.tendsto_weightSum_atTop_iSup
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (A : Finset ↑Λ) {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hbdd : BddAbove (Set.range (fun N =>
      CurrentBounded.weightSum G Λ N A β J))) :
    Filter.Tendsto (fun N : ℕ => CurrentBounded.weightSum G Λ N A β J)
      Filter.atTop
      (nhds (⨆ N : ℕ, CurrentBounded.weightSum G Λ N A β J)) :=
  tendsto_atTop_ciSup
    (fun _ _ h => CurrentBounded.weightSum_mono G Λ A hβJ h) hbdd

/-- **Real Taylor partial sum is bounded by `Real.exp`** for
non-negative arguments: for `x ≥ 0`,
\(∑_{k ≤ N} x^k / k! ≤ Real.exp x\). Direct via
`Real.exp_eq_tsum_div_factorial` (#850),
`Real.summable_pow_div_factorial` (mathlib), and
`Summable.sum_le_tsum`. The per-edge upper bound foundation for
the BddAbove of `CurrentBounded.weightSum` under non-negative
coupling. -/
theorem Real.partial_sum_le_exp_of_nonneg {x : ℝ} (hx : 0 ≤ x) (N : ℕ) :
    ∑ k ∈ Finset.range (N + 1), x ^ k / (k.factorial : ℝ) ≤ Real.exp x := by
  rw [Real.exp_eq_tsum_div_factorial]
  refine Summable.sum_le_tsum _ (fun k _ => ?_)
    (Real.summable_pow_div_factorial x)
  exact div_nonneg (pow_nonneg hx k) (Nat.cast_nonneg _)

set_option linter.unusedSectionVars false in
set_option linter.unusedDecidableInType false in
/-- **`CurrentBounded.weightSum` is uniformly bounded by
`Real.exp (β J)^|edgeSet|`** under non-negative coupling.
\(CurrentBounded.weightSum N A β J ≤ Real.exp (β * J) ^ |edgeSet|\)
for every `N`. The N-independent bound, providing a concrete
`BddAbove` for `tendsto_weightSum_atTop_iSup` (#861). Combines:
(1) drop indicator (sum monotone), (2) `Fintype.prod_sum` (bounded
sum equals product of partial sums), (3) per-edge
`Real.partial_sum_le_exp_of_nonneg` (#862), (4) `Finset.prod_le_prod`
monotonicity, (5) `Finset.prod_const` for `∏ exp = exp^card`. -/
theorem CurrentBounded.weightSum_le_exp_pow_card
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (N : ℕ) (A : Finset ↑Λ) {β J : ℝ} (hβJ : 0 ≤ β * J) :
    CurrentBounded.weightSum G Λ N A β J
      ≤ Real.exp (β * J) ^ Fintype.card (inducedGraph G Λ).edgeSet := by
  -- Step 1: Drop the indicator (each summand bounded above by weight when present).
  have h1 : CurrentBounded.weightSum G Λ N A β J
            ≤ ∑ n : CurrentBounded G Λ N, (n.toCurrent G Λ).weight G Λ β J := by
    unfold CurrentBounded.weightSum
    refine Finset.sum_le_sum (fun n _ => ?_)
    split_ifs
    · exact le_refl _
    · exact Current.weight_nonneg G Λ hβJ _
  -- Step 2: Fintype.prod_sum gives ∑_n ∏_e (β J)^(n e) / (n e)!
  --                              = ∏_e ∑_k (β J)^k / k! (via toCurrent unfolding).
  have h2 : ∑ n : CurrentBounded G Λ N, (n.toCurrent G Λ).weight G Λ β J
          = ∏ e : (inducedGraph G Λ).edgeSet,
              ∑ k : Fin (N + 1), (β * J)^(k : ℕ) / (((k : ℕ).factorial : ℝ)) := by
    symm
    exact Fintype.prod_sum
      (κ := fun _ : (inducedGraph G Λ).edgeSet => Fin (N + 1))
      (fun _ k => (β * J)^(k : ℕ) / (((k : ℕ).factorial : ℝ)))
  -- Step 3: per-edge partial sum bounded by exp.
  have h3 : ∏ e : (inducedGraph G Λ).edgeSet,
              ∑ k : Fin (N + 1), (β * J)^(k : ℕ) / (((k : ℕ).factorial : ℝ))
          ≤ ∏ _e : (inducedGraph G Λ).edgeSet, Real.exp (β * J) := by
    refine Finset.prod_le_prod (fun e _ => ?_) (fun e _ => ?_)
    · refine Finset.sum_nonneg (fun k _ => ?_)
      exact div_nonneg (pow_nonneg hβJ _) (Nat.cast_nonneg _)
    · have hpartial := Real.partial_sum_le_exp_of_nonneg hβJ N
      rw [← Fin.sum_univ_eq_sum_range
        (fun k => (β * J)^k / ((k.factorial : ℝ))) (N + 1)] at hpartial
      exact hpartial
  -- Step 4: ∏_e exp(β J) = exp(β J)^|edgeSet|
  have h4 : ∏ _e : (inducedGraph G Λ).edgeSet, Real.exp (β * J)
          = Real.exp (β * J) ^ Fintype.card (inducedGraph G Λ).edgeSet := by
    rw [Finset.prod_const, Finset.card_univ]
  exact h1.trans (h2.le.trans (h3.trans h4.le))

set_option linter.unusedDecidableInType false in
/-- **Unconditional monotone-convergence of `CurrentBounded.weightSum`**:
under non-negative coupling `0 ≤ β J` (without external BddAbove
hypothesis), `Tendsto (fun N => CurrentBounded.weightSum N A β J)
atTop (nhds (⨆ N, CurrentBounded.weightSum N A β J))`.
Combines `tendsto_weightSum_atTop_iSup` (#861) with
`weightSum_le_exp_pow_card` (#863), the latter discharging the
`BddAbove` hypothesis with the explicit bound
`exp(β J)^|edgeSet|`. -/
theorem CurrentBounded.tendsto_weightSum_atTop_iSup_of_nonneg
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (A : Finset ↑Λ) {β J : ℝ} (hβJ : 0 ≤ β * J) :
    Filter.Tendsto (fun N : ℕ => CurrentBounded.weightSum G Λ N A β J)
      Filter.atTop
      (nhds (⨆ N : ℕ, CurrentBounded.weightSum G Λ N A β J)) := by
  refine CurrentBounded.tendsto_weightSum_atTop_iSup G Λ A hβJ ?_
  refine ⟨Real.exp (β * J) ^ Fintype.card (inducedGraph G Λ).edgeSet, ?_⟩
  rintro x ⟨N, rfl⟩
  exact CurrentBounded.weightSum_le_exp_pow_card G Λ N A hβJ

set_option linter.unusedDecidableInType false in
/-- **Random-current expression of the Ising correlation function**
(unconditional, under non-negative coupling): for `0 ≤ β J`,
\(2^|Λ| · (⨆_N CurrentBounded.weightSum N A β J)
  = ∑_σ σ_A · ∏_e Real.exp (β J σ_e)\).
The bidirectional limit capstone: by `tendsto_nhds_unique`,
combines the LHS-side limit (#854) with the unconditional RHS-side
monotone-convergence limit (#864) — no external `Summable` or
`BddAbove` hypothesis needed (the bound `exp(β J)^|edgeSet|`
established in #863 discharges it). The random-current expression
of the Ising correlation function `Z · ⟨σ_A⟩` (FV §3.7 eq. (3.45))
in `iSup` form. -/
theorem CurrentBounded.pow_card_mul_iSup_weightSum_eq_sum_spinA_prod_exp
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (A : Finset ↑Λ) {β J : ℝ} (hβJ : 0 ≤ β * J) :
    (2 : ℝ) ^ Fintype.card ↑Λ
        * (⨆ N : ℕ, CurrentBounded.weightSum G Λ N A β J)
      = ∑ σ : ↑Λ → Spin,
          (∏ a ∈ A, ((σ a).toSign : ℝ))
          * ∏ e : (inducedGraph G Λ).edgeSet,
              Real.exp (β * J * Config.spinEdgeProduct σ (e : Sym2 ↑Λ)) := by
  refine tendsto_nhds_unique
    ((CurrentBounded.tendsto_weightSum_atTop_iSup_of_nonneg
      G Λ A hβJ).const_mul _)
    (Config.tendsto_pow_card_mul_currentBounded_weightSum_atTop_sum_spinA_prod_exp
      G Λ β J A)

omit [DecidableEq V] in
/-- **Pointwise order on currents**: `n ≤ m` iff `n e ≤ m e` for
every edge `e`. The Pi LE on `Current G Λ` (an `abbrev` for the
edge function type) unfolds definitionally to the pointwise order.
Used in the Aizenman switching lemma (Aizenman 1982 Lemma 4.1 /
FV §3.7) to parameterize pairs `(n₁, n₂)` with `n₁ + n₂ = n`. -/
theorem Current.le_def (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n m : Current G Λ) :
    n ≤ m ↔ ∀ e, n e ≤ m e := Iff.rfl

omit [DecidableEq V] in
/-- **Zero is the least current**: `(0 : Current G Λ) ≤ n` for any
current `n`. Each component `0 ≤ n e` in `ℕ`. -/
theorem Current.zero_le (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n : Current G Λ) :
    (0 : Current G Λ) ≤ n := fun _ => Nat.zero_le _

omit [DecidableEq V] in
/-- **Left summand is below the sum**: `n ≤ n + m`, since
`n e ≤ n e + m e` for every edge `e`. -/
theorem Current.le_self_add_right (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n m : Current G Λ) :
    n ≤ n + m := fun _ => Nat.le_add_right _ _

omit [DecidableEq V] in
/-- **Right summand is below the sum**: `n ≤ m + n`, since
`n e ≤ m e + n e` for every edge `e`. -/
theorem Current.le_self_add_left (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n m : Current G Λ) :
    n ≤ m + n := fun _ => Nat.le_add_left _ _

/-- **Finset of currents bounded by `n`**: the `Finset` of currents
`m` with `m ≤ n` pointwise, enumerated via
`Fintype.piFinset (fun e => Finset.range (n e + 1))`. This is the
parameterizing set for the Aizenman switching pair-bijection
`{(n₁, n₂) : n₁ + n₂ = n} ↔ {m : m ≤ n}` (Aizenman 1982 Lemma 4.1 /
FV §3.7). -/
def Current.subFinset (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n : Current G Λ) :
    Finset (Current G Λ) :=
  Fintype.piFinset (fun e => Finset.range (n e + 1))

set_option linter.unusedDecidableInType false in
/-- **Membership in `subFinset`**: `m ∈ subFinset n ↔ m ≤ n`,
via `Fintype.mem_piFinset` + `Finset.mem_range` + `Nat.lt_succ_iff`. -/
@[simp]
theorem Current.mem_subFinset_iff (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (n m : Current G Λ) :
    m ∈ Current.subFinset G Λ n ↔ m ≤ n := by
  unfold Current.subFinset
  rw [Fintype.mem_piFinset]
  simp only [Finset.mem_range, Nat.lt_succ_iff]
  rfl

set_option linter.unusedDecidableInType false in
/-- **Cardinality of `subFinset`**:
`#(subFinset n) = ∏_e (n e + 1)`. The number of currents `m ≤ n` is
the product of per-edge multiplicities `n e + 1`, by
`Fintype.card_piFinset` + `Finset.card_range`. The combinatorial
count behind the joint factor `∏_e Nat.choose (n e) (m e)` in
`Current.weight_mul_weight_eq_weight_add_mul_jointFactor`
(PR #845). -/
theorem Current.subFinset_card_eq_prod (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n : Current G Λ) :
    (Current.subFinset G Λ n).card
      = ∏ e : (inducedGraph G Λ).edgeSet, (n e + 1) := by
  unfold Current.subFinset
  rw [Fintype.card_piFinset]
  simp [Finset.card_range]

/-- **Pointwise truncated subtraction** of currents: `(n - m) e := n e - m e`
in `ℕ` (which is `Nat.sub`, cut off at `0`). The truncation primitive
needed for the switching pair-bijection (Aizenman 1982 Lemma 4.1 /
FV §3.7), parameterized by `m ↦ (m, n - m)` for `m ≤ n`. -/
instance Current.instSub (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] : Sub (Current G Λ) :=
  ⟨fun n m => fun e => n e - m e⟩

omit [DecidableEq V] in
/-- **Pointwise sub**: `(n - m) e = n e - m e` (by definition of
`Current.instSub`, which uses `Nat.sub`). -/
@[simp]
theorem Current.sub_apply (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (n m : Current G Λ) (e : (inducedGraph G Λ).edgeSet) :
    (n - m) e = n e - m e := rfl

omit [DecidableEq V] in
/-- **Truncation cancels under `m ≤ n`**: `(n - m) + m = n`.
Pointwise via `Nat.sub_add_cancel`. The naming `sub_add_cancel`
follows mathlib's `Nat.sub_add_cancel` / `tsub_add_cancel_of_le`. -/
theorem Current.sub_add_cancel_of_le (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {n m : Current G Λ} (h : m ≤ n) :
    (n - m) + m = n := by
  ext e
  simp [Nat.sub_add_cancel (h e)]

omit [DecidableEq V] in
/-- **Truncation cancels (commuted form) under `m ≤ n`**:
`m + (n - m) = n`. By commutativity + `sub_add_cancel_of_le`. -/
theorem Current.add_sub_cancel_of_le (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {n m : Current G Λ} (h : m ≤ n) :
    m + (n - m) = n := by
  rw [add_comm]
  exact Current.sub_add_cancel_of_le G Λ h

omit [DecidableEq V] in
/-- **Truncated sub is bounded above by the minuend**:
`n - m ≤ n` for any currents `n, m`. Pointwise via `Nat.sub_le`. -/
theorem Current.sub_le_self (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (n m : Current G Λ) :
    n - m ≤ n := fun _ => Nat.sub_le _ _

set_option linter.unusedDecidableInType false in
/-- **Pair-Finset of currents summing to `n`**: the `Finset` of pairs
`(n₁, n₂) : Current G Λ × Current G Λ` with `n₁ + n₂ = n`, realized
concretely as `(subFinset n).image (m ↦ (m, n - m))`. The LHS of
the Aizenman switching pair-bijection
`{(n₁, n₂) : n₁ + n₂ = n} ↔ {m : m ≤ n}` (Aizenman 1982 Lemma 4.1 /
FV §3.7). -/
def Current.pairFinset (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n : Current G Λ) :
    Finset (Current G Λ × Current G Λ) :=
  (Current.subFinset G Λ n).image (fun m => (m, n - m))

set_option linter.unusedDecidableInType false in
/-- **Membership in `pairFinset`**: `(m₁, m₂) ∈ pairFinset n ↔ m₁ + m₂ = n`.
Forward: any pair in the image has the form `(k, n - k)` with `k ≤ n`,
so `k + (n - k) = n` by `add_sub_cancel_of_le`. Backward: from
`m₁ + m₂ = n` we get `m₁ ≤ n` (`le_self_add_right`) and
`m₂ = n - m₁` (pointwise from `m₁ e + m₂ e = n e`), so `(m₁, n - m₁) = (m₁, m₂)`. -/
@[simp]
theorem Current.mem_pairFinset_iff (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (n : Current G Λ) (p : Current G Λ × Current G Λ) :
    p ∈ Current.pairFinset G Λ n ↔ p.1 + p.2 = n := by
  unfold Current.pairFinset
  rw [Finset.mem_image]
  constructor
  · rintro ⟨k, hk, rfl⟩
    rw [Current.mem_subFinset_iff] at hk
    exact Current.add_sub_cancel_of_le G Λ hk
  · intro hsum
    refine ⟨p.1, ?_, ?_⟩
    · rw [Current.mem_subFinset_iff]
      intro e
      have heq : p.1 e + p.2 e = n e := congrFun hsum e
      exact heq ▸ Nat.le_add_right (p.1 e) (p.2 e)
    · ext
      · rfl
      · rename_i e
        simp only [Current.sub_apply]
        have heq : p.1 e + p.2 e = n e := by
          have h := congrFun hsum e
          simpa [Pi.add_apply] using h
        omega

set_option linter.unusedDecidableInType false in
/-- **`pairFinset` cardinality matches `subFinset`**:
`(pairFinset n).card = (subFinset n).card`, since the defining map
`m ↦ (m, n - m)` is injective (the first coordinate is `m`). -/
theorem Current.pairFinset_card_eq_subFinset_card
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n : Current G Λ) :
    (Current.pairFinset G Λ n).card = (Current.subFinset G Λ n).card := by
  unfold Current.pairFinset
  apply Finset.card_image_of_injective
  intro m₁ m₂ h
  exact congrArg Prod.fst h

set_option linter.unusedDecidableInType false in
/-- **`pairFinset` cardinality formula**:
`(pairFinset n).card = ∏ e, (n e + 1)`, by composing
`pairFinset_card_eq_subFinset_card` with `subFinset_card_eq_prod`
(PR #866). The number of pairs `(n₁, n₂)` with `n₁ + n₂ = n` equals
the per-edge product of multiplicities. -/
theorem Current.pairFinset_card_eq_prod (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n : Current G Λ) :
    (Current.pairFinset G Λ n).card
      = ∏ e : (inducedGraph G Λ).edgeSet, (n e + 1) := by
  rw [Current.pairFinset_card_eq_subFinset_card,
      Current.subFinset_card_eq_prod]

set_option linter.unusedDecidableInType false in
/-- **Sum over `pairFinset` reindexes via `subFinset`**:
`∑ p ∈ pairFinset n, f p = ∑ m ∈ subFinset n, f (m, n - m)`.
The pair-bijection `m ↦ (m, n - m)` is injective, so summing over
the image equals summing pre-image with the function composed with
the bijection (`Finset.sum_image`). The fundamental sum reindexing
behind the Aizenman switching identity (FV §3.7). -/
theorem Current.sum_pairFinset_eq_sum_subFinset
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (n : Current G Λ) (f : Current G Λ × Current G Λ → ℝ) :
    ∑ p ∈ Current.pairFinset G Λ n, f p
      = ∑ m ∈ Current.subFinset G Λ n, f (m, n - m) := by
  unfold Current.pairFinset
  rw [Finset.sum_image]
  intro m₁ _ m₂ _ h
  exact congrArg Prod.fst h

set_option linter.unusedDecidableInType false in
/-- **Pair-weight identity (Aizenman switching scaling)**: the sum of
`weight β J n₁ · weight β J n₂` over pairs `(n₁, n₂)` with sum `n`
equals `weight β J n` times the sum of `jointFactor m (n - m)` over
`m ≤ n`. By `sum_pairFinset_eq_sum_subFinset`, then per-term
`weight_mul_weight_eq_weight_add_mul_jointFactor` (PR #845) with
`m + (n - m) = n` (PR #867 `add_sub_cancel_of_le`), then
`Finset.mul_sum` to factor out the constant `weight β J n`. -/
theorem Current.sum_pairFinset_weight_mul_weight
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (n : Current G Λ) (β J : ℝ) :
    ∑ p ∈ Current.pairFinset G Λ n,
        Current.weight G Λ β J p.1 * Current.weight G Λ β J p.2
      = Current.weight G Λ β J n
        * ∑ m ∈ Current.subFinset G Λ n,
            Current.jointFactor G Λ m (n - m) := by
  rw [Current.sum_pairFinset_eq_sum_subFinset, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Current.mem_subFinset_iff] at hm
  rw [Current.weight_mul_weight_eq_weight_add_mul_jointFactor,
      Current.add_sub_cancel_of_le G Λ hm]

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **Sources of `n - m` is the symmetric difference under `m ≤ n`**:
`(n - m).sources = symmDiff (sources n) (sources m)` when `m ≤ n`.
Combine `sub_add_cancel_of_le` (PR #867: `(n - m) + m = n`) with
`add_sources_eq` (sources of a sum is symmDiff of summand sources)
and the involution of `symmDiff` on the right. -/
theorem Current.sub_sources_eq_symmDiff (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    {n m : Current G Λ} (h : m ≤ n) :
    (n - m).sources G Λ
      = symmDiff (n.sources G Λ) (m.sources G Λ) := by
  have h₁ : ((n - m) + m).sources G Λ
              = symmDiff ((n - m).sources G Λ) (m.sources G Λ) :=
    Current.add_sources_eq G Λ (n - m) m
  rw [Current.sub_add_cancel_of_le G Λ h] at h₁
  rw [h₁, symmDiff_assoc, symmDiff_self, symmDiff_bot]

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **`(n - m).HasSources A` is the symmetric-difference equation under
`m ≤ n`**: `(n - m).HasSources A ↔ symmDiff (sources n) (sources m) = A`.
By unfolding `HasSources` and `sub_sources_eq_symmDiff`. -/
theorem Current.sub_hasSources_iff (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    {n m : Current G Λ} (h : m ≤ n) (A : Finset ↑Λ) :
    (n - m).HasSources G Λ A
      ↔ symmDiff (n.sources G Λ) (m.sources G Λ) = A := by
  unfold Current.HasSources
  rw [Current.sub_sources_eq_symmDiff G Λ h]

omit [DecidableEq V] in
/-- **`n - 0 = n`**: subtracting the zero current is the identity. -/
@[simp]
theorem Current.sub_zero (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n : Current G Λ) :
    n - (0 : Current G Λ) = n := by
  ext e
  simp

omit [DecidableEq V] in
/-- **`0 - n = 0`**: truncated subtraction (`Nat.sub`) at the zero
current pointwise is `0 - n e = 0`. -/
@[simp]
theorem Current.zero_sub (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n : Current G Λ) :
    (0 : Current G Λ) - n = 0 := by
  ext e
  simp

omit [DecidableEq V] in
/-- **`n - n = 0`**: pointwise `n e - n e = 0` in `ℕ`. -/
@[simp]
theorem Current.sub_self (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n : Current G Λ) :
    n - n = (0 : Current G Λ) := by
  ext e
  simp

set_option linter.unusedDecidableInType false in
/-- **`subFinset 0 = {0}`**: the only current `m ≤ 0` is `m = 0`,
since each component `m e ≤ 0` forces `m e = 0`. By `Finset.ext`
+ `mem_subFinset_iff` + `Finset.mem_singleton`. -/
theorem Current.subFinset_zero (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    Current.subFinset G Λ (0 : Current G Λ) = {0} := by
  ext m
  rw [Current.mem_subFinset_iff, Finset.mem_singleton]
  constructor
  · intro h
    ext e
    have := h e
    simp only [Pi.zero_apply, Nat.le_zero] at this
    exact this
  · rintro rfl
    intro _
    simp

set_option linter.unusedDecidableInType false in
/-- **`(0, n) ∈ pairFinset n`**: the trivial pair `(0, n)` lies in
the pair-Finset since `0 + n = n`. -/
theorem Current.zero_mem_pairFinset (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n : Current G Λ) :
    ((0 : Current G Λ), n) ∈ Current.pairFinset G Λ n := by
  rw [Current.mem_pairFinset_iff]
  exact zero_add n

set_option linter.unusedDecidableInType false in
/-- **`(n, 0) ∈ pairFinset n`**: the trivial pair `(n, 0)` lies in
the pair-Finset since `n + 0 = n`. -/
theorem Current.self_mem_pairFinset (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n : Current G Λ) :
    (n, (0 : Current G Λ)) ∈ Current.pairFinset G Λ n := by
  rw [Current.mem_pairFinset_iff]
  exact add_zero n

set_option linter.unusedDecidableInType false in
/-- **`pairFinset 0 = {(0, 0)}`**: the only pair `(n₁, n₂)` summing
to `0` is `(0, 0)`, since both components must vanish. -/
theorem Current.pairFinset_zero (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    Current.pairFinset G Λ (0 : Current G Λ)
      = {((0 : Current G Λ), (0 : Current G Λ))} := by
  ext p
  rw [Current.mem_pairFinset_iff, Finset.mem_singleton]
  constructor
  · intro hsum
    have hp1 : p.1 = 0 := by
      ext e
      have h := congrFun hsum e
      simp only [Pi.add_apply, Pi.zero_apply] at h
      change p.1 e = 0
      omega
    have hp2 : p.2 = 0 := by
      ext e
      have h := congrFun hsum e
      simp only [Pi.add_apply, Pi.zero_apply] at h
      change p.2 e = 0
      omega
    rw [Prod.ext_iff]
    exact ⟨hp1, hp2⟩
  · rintro rfl
    simp

omit [DecidableEq V] in
/-- **Double truncation cancels under `m ≤ n`**:
`n - (n - m) = m` when `m ≤ n`. Pointwise via `Nat.sub_sub_self`. -/
theorem Current.sub_sub_self_of_le (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {n m : Current G Λ} (h : m ≤ n) :
    n - (n - m) = m := by
  ext e
  change n e - (n e - m e) = m e
  exact Nat.sub_sub_self (h e)

set_option linter.unusedDecidableInType false in
/-- **Complement involution preserves `subFinset`**:
`(subFinset n).image (m ↦ n - m) = subFinset n`. Each `m ≤ n` maps
to `n - m ≤ n` (`sub_le_self`); conversely each `k ≤ n` is the
image of `n - k` (since `n - (n - k) = k` by `sub_sub_self_of_le`).
The natural involution corresponding to swapping `(m, n - m) ↔ (n - m, m)`
in the pair-bijection (PR #868). -/
theorem Current.subFinset_image_compl (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n : Current G Λ) :
    (Current.subFinset G Λ n).image (fun m => n - m)
      = Current.subFinset G Λ n := by
  ext k
  rw [Finset.mem_image]
  constructor
  · rintro ⟨m, hm, rfl⟩
    rw [Current.mem_subFinset_iff] at hm
    rw [Current.mem_subFinset_iff]
    exact Current.sub_le_self G Λ n m
  · intro hk
    rw [Current.mem_subFinset_iff] at hk
    refine ⟨n - k, ?_, ?_⟩
    · rw [Current.mem_subFinset_iff]
      exact Current.sub_le_self G Λ n k
    · exact Current.sub_sub_self_of_le G Λ hk

set_option linter.unusedDecidableInType false in
/-- **`pairFinset` is invariant under `Prod.swap`**:
`(pairFinset n).image Prod.swap = pairFinset n`. By the commutativity
of `+` on currents, `(n₁, n₂) ∈ pairFinset n ↔ (n₂, n₁) ∈ pairFinset n`. -/
theorem Current.pairFinset_image_swap_eq_self
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n : Current G Λ) :
    (Current.pairFinset G Λ n).image Prod.swap
      = Current.pairFinset G Λ n := by
  ext p
  rw [Finset.mem_image]
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [Current.mem_pairFinset_iff] at hq
    rw [Current.mem_pairFinset_iff]
    change q.2 + q.1 = n
    rw [add_comm]; exact hq
  · intro hp
    rw [Current.mem_pairFinset_iff] at hp
    refine ⟨p.swap, ?_, ?_⟩
    · rw [Current.mem_pairFinset_iff]
      change p.2 + p.1 = n
      rw [add_comm]; exact hp
    · exact Prod.swap_swap p

set_option linter.unusedDecidableInType false in
/-- **`pairFinset n` is nonempty**: contains `(n, 0)` since `n + 0 = n`
(`self_mem_pairFinset`, PR #872). -/
theorem Current.pairFinset_nonempty (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n : Current G Λ) :
    (Current.pairFinset G Λ n).Nonempty :=
  ⟨(n, 0), Current.self_mem_pairFinset G Λ n⟩

omit [DecidableEq V] in
/-- **`jointFactor m (n - m) = ∏ e, C(n e, m e)`** for `m ≤ n`:
since `m + (n - m) = n` pointwise, the binomial argument simplifies. -/
theorem Current.jointFactor_compl_eq_prod_choose
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {n m : Current G Λ} (h : m ≤ n) :
    Current.jointFactor G Λ m (n - m)
      = ∏ e : (inducedGraph G Λ).edgeSet, (Nat.choose (n e) (m e) : ℝ) := by
  unfold Current.jointFactor
  refine Finset.prod_congr rfl (fun e _ => ?_)
  congr 2
  change m e + (n - m) e = n e
  rw [Current.sub_apply]
  exact Nat.add_sub_cancel' (h e)

set_option linter.unusedDecidableInType false in
/-- **Closed-form sum `∑ m ∈ subFinset n, jointFactor m (n - m) = 2^(∑ e, n e)`**:
combine `jointFactor_compl_eq_prod_choose` (per-summand simplification)
with Fubini (`Finset.prod_univ_sum`) and the binomial-row identity
`Nat.sum_range_choose : ∑ k ∈ range (n + 1), C(n, k) = 2^n`, then
`Finset.prod_pow_eq_pow_sum` to reassemble `∏ e, 2^(n e) = 2^(∑ e, n e)`.
The closed form completing PR #869's pair-weight scaling identity. -/
theorem Current.sum_subFinset_jointFactor_compl_eq_pow_two
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n : Current G Λ) :
    ∑ m ∈ Current.subFinset G Λ n, Current.jointFactor G Λ m (n - m)
      = (2 : ℝ) ^ (∑ e : (inducedGraph G Λ).edgeSet, n e) := by
  have step1 : ∑ m ∈ Current.subFinset G Λ n, Current.jointFactor G Λ m (n - m)
      = ∑ m ∈ Current.subFinset G Λ n,
          ∏ e : (inducedGraph G Λ).edgeSet, (Nat.choose (n e) (m e) : ℝ) := by
    refine Finset.sum_congr rfl (fun m hm => ?_)
    rw [Current.mem_subFinset_iff] at hm
    exact Current.jointFactor_compl_eq_prod_choose G Λ hm
  rw [step1]
  unfold Current.subFinset
  have fubini :
      ∏ e : (inducedGraph G Λ).edgeSet,
          ∑ k ∈ Finset.range (n e + 1), ((n e).choose k : ℝ)
        = ∑ m ∈ Fintype.piFinset (fun e => Finset.range (n e + 1)),
            ∏ e : (inducedGraph G Λ).edgeSet, ((n e).choose (m e) : ℝ) :=
    Finset.prod_univ_sum _ _
  rw [← fubini]
  trans ∏ e : (inducedGraph G Λ).edgeSet, (2 : ℝ) ^ n e
  · refine Finset.prod_congr rfl (fun e _ => ?_)
    rw [← Nat.cast_sum, Nat.sum_range_choose]
    push_cast
    rfl
  · exact Finset.prod_pow_eq_pow_sum _ _ _

set_option linter.unusedDecidableInType false in
/-- **Pair-weight closed form (capstone)**: combining the pair-weight
scaling identity (PR #869) with the joint-factor sum closed form
(PR #875), the random-current pair sum factors completely:
\(∑ p ∈ pairFinset n, weight β J p.1 · weight β J p.2
  = weight β J n · 2^{∑_e n e}\). The single-current weight times an
exponential of the total current degree, with no remaining combinatorial
sum. Useful in switching applications. -/
theorem Current.sum_pairFinset_weight_mul_weight_eq_weight_pow_two
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (n : Current G Λ) (β J : ℝ) :
    ∑ p ∈ Current.pairFinset G Λ n,
        Current.weight G Λ β J p.1 * Current.weight G Λ β J p.2
      = Current.weight G Λ β J n
        * (2 : ℝ) ^ (∑ e : (inducedGraph G Λ).edgeSet, n e) := by
  rw [Current.sum_pairFinset_weight_mul_weight,
      Current.sum_subFinset_jointFactor_compl_eq_pow_two]

/-- **Source-conditioned pair-Finset**: pairs `(n₁, n₂) ∈ pairFinset n`
filtered by `n₁.HasSources A ∧ n₂.HasSources B`. The LHS / RHS data
type for source-bijection statements of the switching lemma
(Aizenman 1982 Lemma 4.1 / FV §3.7). -/
noncomputable def Current.pairFinset_with_sources
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (A B : Finset ↑Λ) :
    Finset (Current G Λ × Current G Λ) := by
  classical
  exact (Current.pairFinset G Λ n).filter
    (fun p => p.1.HasSources G Λ A ∧ p.2.HasSources G Λ B)

set_option linter.unusedDecidableInType false in
/-- **Membership in `pairFinset_with_sources`**:
`(n₁, n₂) ∈ pairFinset_with_sources n A B
  ↔ n₁ + n₂ = n ∧ n₁.HasSources A ∧ n₂.HasSources B`. -/
theorem Current.mem_pairFinset_with_sources_iff
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (A B : Finset ↑Λ)
    (p : Current G Λ × Current G Λ) :
    p ∈ Current.pairFinset_with_sources G Λ n A B
      ↔ p.1 + p.2 = n ∧ p.1.HasSources G Λ A ∧ p.2.HasSources G Λ B := by
  classical
  unfold Current.pairFinset_with_sources
  simp only [Finset.mem_filter, Current.mem_pairFinset_iff]

set_option linter.unusedDecidableInType false in
/-- **Empty when source XOR doesn't match**: if `symmDiff A B ≠ sources n`,
then `pairFinset_with_sources n A B = ∅`. The constraint
`(n₁, n₂)` with `sources n₁ = A`, `sources n₂ = B`, `n₁ + n₂ = n`
forces `sources n = symmDiff A B` (`add_sources_eq`). -/
theorem Current.pairFinset_with_sources_eq_empty_of_sources_mismatch
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (A B : Finset ↑Λ)
    (h : symmDiff A B ≠ n.sources G Λ) :
    Current.pairFinset_with_sources G Λ n A B = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro p hp
  rw [Current.mem_pairFinset_with_sources_iff] at hp
  obtain ⟨hsum, hA, hB⟩ := hp
  apply h
  change p.1.sources G Λ = A at hA
  change p.2.sources G Λ = B at hB
  rw [show n = p.1 + p.2 from hsum.symm, Current.add_sources_eq, hA, hB]

/-- **Source-conditioned subFinset**: `(subFinset n).filter (fun m => m.HasSources A)`.
The dual to `pairFinset_with_sources` (PR #877) via the pair-bijection
`m ↦ (m, n - m)` (PR #868). -/
noncomputable def Current.subFinset_with_source
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (A : Finset ↑Λ) :
    Finset (Current G Λ) := by
  classical
  exact (Current.subFinset G Λ n).filter (fun m => m.HasSources G Λ A)

set_option linter.unusedDecidableInType false in
/-- **Membership in `subFinset_with_source`**:
`m ∈ subFinset_with_source n A ↔ m ≤ n ∧ m.HasSources A`. -/
theorem Current.mem_subFinset_with_source_iff
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (A : Finset ↑Λ) (m : Current G Λ) :
    m ∈ Current.subFinset_with_source G Λ n A
      ↔ m ≤ n ∧ m.HasSources G Λ A := by
  classical
  unfold Current.subFinset_with_source
  simp only [Finset.mem_filter, Current.mem_subFinset_iff]

set_option linter.unusedDecidableInType false in
/-- **`subFinset_with_source` is a subset of `subFinset`**: by definition
as a filter. -/
theorem Current.subFinset_with_source_subset
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (A : Finset ↑Λ) :
    Current.subFinset_with_source G Λ n A ⊆ Current.subFinset G Λ n := by
  classical
  unfold Current.subFinset_with_source
  exact Finset.filter_subset _ _

set_option linter.unusedDecidableInType false in
/-- **Bridge: `pairFinset_with_sources` is the image of `subFinset_with_source`
under `m ↦ (m, n - m)`** (when sources XOR matches): if
`symmDiff (sources n) A = B`, then `pairFinset_with_sources n A B
= (subFinset_with_source n A).image (fun m => (m, n - m))`.
Combines pair-bijection (PR #868), `sub_add_cancel_of_le` (PR #867),
`sub_sources_eq_symmDiff` (PR #870). -/
theorem Current.pairFinset_with_sources_eq_image_subFinset_with_source
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (A B : Finset ↑Λ)
    (hAB : symmDiff (n.sources G Λ) A = B) :
    Current.pairFinset_with_sources G Λ n A B
      = (Current.subFinset_with_source G Λ n A).image (fun m => (m, n - m)) := by
  ext p
  rw [Current.mem_pairFinset_with_sources_iff, Finset.mem_image]
  constructor
  · rintro ⟨hsum, hA, hB⟩
    refine ⟨p.1, ?_, ?_⟩
    · rw [Current.mem_subFinset_with_source_iff]
      refine ⟨?_, hA⟩
      rw [← hsum]
      exact Current.le_self_add_right G Λ p.1 p.2
    · ext
      · rfl
      · rename_i e
        simp only [Current.sub_apply]
        have heq : p.1 e + p.2 e = n e := by
          have h := congrFun hsum e
          simpa [Pi.add_apply] using h
        omega
  · rintro ⟨m, hm, rfl⟩
    rw [Current.mem_subFinset_with_source_iff] at hm
    obtain ⟨hle, hsrc⟩ := hm
    refine ⟨Current.add_sub_cancel_of_le G Λ hle, hsrc, ?_⟩
    -- Goal: (n - m).HasSources G Λ B
    rw [Current.sub_hasSources_iff G Λ hle]
    change m.sources G Λ = A at hsrc
    rw [hsrc]
    exact hAB

set_option linter.unusedDecidableInType false in
/-- **Sum reindexing for source-conditioned pair-Finset**:
when `symmDiff (sources n) A = B`,
`∑ p ∈ pairFinset_with_sources n A B, f p
  = ∑ m ∈ subFinset_with_source n A, f (m, n - m)`.
By the image identity (`pairFinset_with_sources_eq_image_subFinset_with_source`)
+ `Finset.sum_image` on the injective map. -/
theorem Current.sum_pairFinset_with_sources_eq_sum_subFinset_with_source
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (A B : Finset ↑Λ)
    (hAB : symmDiff (n.sources G Λ) A = B)
    (f : Current G Λ × Current G Λ → ℝ) :
    ∑ p ∈ Current.pairFinset_with_sources G Λ n A B, f p
      = ∑ m ∈ Current.subFinset_with_source G Λ n A, f (m, n - m) := by
  rw [Current.pairFinset_with_sources_eq_image_subFinset_with_source G Λ n A B hAB]
  rw [Finset.sum_image]
  intro m₁ _ m₂ _ h
  exact congrArg Prod.fst h

set_option linter.unusedDecidableInType false in
/-- **Source-conditioned pair-weight scaling identity** (analog of PR #876
for source-filtered pairs): under `symmDiff (sources n) A = B`,
\[
∑_{p ∈ \text{pairFinset\_with\_sources}\ n\ A\ B}
  \text{weight}\ p.1 \cdot \text{weight}\ p.2
 = \text{weight}\ n \cdot
   ∑_{m ∈ \text{subFinset\_with\_source}\ n\ A}
     \text{jointFactor}\ m\ (n - m).
\]
Apply PR #879 bridge (sum reindexing) + per-summand
`weight_mul_weight_eq_weight_add_mul_jointFactor` (PR #845) +
`add_sub_cancel_of_le` (PR #867: `m + (n - m) = n` for `m ≤ n`),
factored via `Finset.mul_sum`. The source-conditioned version of the
central scaling identity for the switching lemma. -/
theorem Current.sum_pairFinset_with_sources_weight_mul_weight
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (A B : Finset ↑Λ)
    (hAB : symmDiff (n.sources G Λ) A = B) (β J : ℝ) :
    ∑ p ∈ Current.pairFinset_with_sources G Λ n A B,
        Current.weight G Λ β J p.1 * Current.weight G Λ β J p.2
      = Current.weight G Λ β J n
        * ∑ m ∈ Current.subFinset_with_source G Λ n A,
            Current.jointFactor G Λ m (n - m) := by
  rw [Current.sum_pairFinset_with_sources_eq_sum_subFinset_with_source
        G Λ n A B hAB, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Current.mem_subFinset_with_source_iff] at hm
  obtain ⟨hle, _⟩ := hm
  rw [Current.weight_mul_weight_eq_weight_add_mul_jointFactor,
      Current.add_sub_cancel_of_le G Λ hle]

set_option linter.unusedDecidableInType false in
/-- **Mismatch corollary**: when `symmDiff A B ≠ sources n`, the
source-conditioned pair-weight sum is `0` (empty Finset).
By `pairFinset_with_sources_eq_empty_of_sources_mismatch` (PR #877). -/
theorem Current.sum_pairFinset_with_sources_weight_mul_weight_of_mismatch
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (A B : Finset ↑Λ)
    (h : symmDiff A B ≠ n.sources G Λ) (β J : ℝ) :
    ∑ p ∈ Current.pairFinset_with_sources G Λ n A B,
        Current.weight G Λ β J p.1 * Current.weight G Λ β J p.2 = 0 := by
  rw [Current.pairFinset_with_sources_eq_empty_of_sources_mismatch
        G Λ n A B h, Finset.sum_empty]

set_option linter.unusedDecidableInType false in
/-- **`subFinset_with_source 0 ∅ = {0}`**: the only `m ≤ 0` is `m = 0`
(`subFinset_zero`, PR #871), and `0.sources = ∅` (`zero_sources`). -/
theorem Current.subFinset_with_source_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ] :
    Current.subFinset_with_source G Λ (0 : Current G Λ) ∅ = {0} := by
  classical
  ext m
  rw [Current.mem_subFinset_with_source_iff, Finset.mem_singleton]
  constructor
  · rintro ⟨hle, hsrc⟩
    have : m ∈ Current.subFinset G Λ 0 :=
      (Current.mem_subFinset_iff G Λ 0 m).mpr hle
    rw [Current.subFinset_zero] at this
    exact Finset.mem_singleton.mp this
  · rintro rfl
    refine ⟨?_, ?_⟩
    · exact fun _ => Nat.zero_le _
    · exact Current.zero_sources G Λ

set_option linter.unusedDecidableInType false in
/-- **`subFinset_with_source 0 A = ∅` for `A ≠ ∅`**: the only `m ≤ 0`
is `m = 0`, but `0.sources = ∅ ≠ A`. -/
theorem Current.subFinset_with_source_zero_of_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    {A : Finset ↑Λ} (hA : A ≠ ∅) :
    Current.subFinset_with_source G Λ (0 : Current G Λ) A = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro m hm
  rw [Current.mem_subFinset_with_source_iff] at hm
  obtain ⟨hle, hsrc⟩ := hm
  apply hA
  change m.sources G Λ = A at hsrc
  have hmem : m ∈ Current.subFinset G Λ 0 :=
    (Current.mem_subFinset_iff G Λ 0 m).mpr hle
  rw [Current.subFinset_zero] at hmem
  obtain rfl := Finset.mem_singleton.mp hmem
  rw [Current.zero_sources] at hsrc
  exact hsrc.symm

set_option linter.unusedDecidableInType false in
/-- **`pairFinset_with_sources 0 ∅ ∅ = {(0, 0)}`**: only `(0, 0)`
satisfies `n₁ + n₂ = 0` and both source-free. -/
theorem Current.pairFinset_with_sources_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ] :
    Current.pairFinset_with_sources G Λ (0 : Current G Λ) ∅ ∅
      = {((0 : Current G Λ), (0 : Current G Λ))} := by
  classical
  ext p
  rw [Current.mem_pairFinset_with_sources_iff, Finset.mem_singleton]
  constructor
  · rintro ⟨hsum, _, _⟩
    have hpair : p ∈ Current.pairFinset G Λ 0 :=
      (Current.mem_pairFinset_iff G Λ 0 p).mpr hsum
    rw [Current.pairFinset_zero] at hpair
    exact Finset.mem_singleton.mp hpair
  · rintro rfl
    refine ⟨zero_add 0, ?_, ?_⟩
    · exact Current.zero_sources G Λ
    · exact Current.zero_sources G Λ

set_option linter.unusedDecidableInType false in
/-- **`pairFinset_with_sources 0 A B = ∅` when `A ≠ ∅` or `B ≠ ∅`**:
the only pair summing to `0` is `(0, 0)`, both source-free. -/
theorem Current.pairFinset_with_sources_zero_of_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    {A B : Finset ↑Λ} (h : A ≠ ∅ ∨ B ≠ ∅) :
    Current.pairFinset_with_sources G Λ (0 : Current G Λ) A B = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro p hp
  rw [Current.mem_pairFinset_with_sources_iff] at hp
  obtain ⟨hsum, hA, hB⟩ := hp
  change p.1.sources G Λ = A at hA
  change p.2.sources G Λ = B at hB
  have hpair : p ∈ Current.pairFinset G Λ 0 :=
    (Current.mem_pairFinset_iff G Λ 0 p).mpr hsum
  rw [Current.pairFinset_zero] at hpair
  obtain rfl := Finset.mem_singleton.mp hpair
  rw [Current.zero_sources] at hA hB
  rcases h with hA' | hB'
  · exact hA' hA.symm
  · exact hB' hB.symm

set_option linter.unusedDecidableInType false in
/-- **Source-conditioned `jointFactor` sum is bounded by the unrestricted
closed form**: `∑ m ∈ subFinset_with_source n A, jointFactor m (n - m)
≤ 2^(∑ e, n e)`. By `Finset.sum_le_sum_of_subset_of_nonneg` (filter is a
subset, jointFactor ≥ 0) + PR #875 closed form on the unrestricted sum. -/
theorem Current.sum_subFinset_with_source_jointFactor_le_pow_two
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (A : Finset ↑Λ) :
    ∑ m ∈ Current.subFinset_with_source G Λ n A,
        Current.jointFactor G Λ m (n - m)
      ≤ (2 : ℝ) ^ (∑ e : (inducedGraph G Λ).edgeSet, n e) := by
  rw [← Current.sum_subFinset_jointFactor_compl_eq_pow_two G Λ n]
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (Current.subFinset_with_source_subset G Λ n A) (fun m _ _ => ?_)
  unfold Current.jointFactor
  refine Finset.prod_nonneg (fun e _ => ?_)
  exact Nat.cast_nonneg _

set_option linter.unusedDecidableInType false in
/-- **Pair-weight bound (corollary)** under `0 ≤ β J` and
`symmDiff sources_n A = B`:
`∑ p ∈ pairFinset_with_sources n A B, weight β J p.1 * weight β J p.2
  ≤ weight β J n * 2^(∑ e, n e)`. By PR #880 (pair-weight identity) +
weight nonneg + the previous theorem. -/
theorem Current.sum_pairFinset_with_sources_weight_mul_weight_le
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (A B : Finset ↑Λ)
    (hAB : symmDiff (n.sources G Λ) A = B)
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    ∑ p ∈ Current.pairFinset_with_sources G Λ n A B,
        Current.weight G Λ β J p.1 * Current.weight G Λ β J p.2
      ≤ Current.weight G Λ β J n
        * (2 : ℝ) ^ (∑ e : (inducedGraph G Λ).edgeSet, n e) := by
  rw [Current.sum_pairFinset_with_sources_weight_mul_weight G Λ n A B hAB]
  exact mul_le_mul_of_nonneg_left
    (Current.sum_subFinset_with_source_jointFactor_le_pow_two G Λ n A)
    (Current.weight_nonneg G Λ hβJ n)

set_option linter.unusedDecidableInType false in
/-- **Source-conditioned pair-Finset swap image identity**:
`(pairFinset_with_sources n A B).image Prod.swap = pairFinset_with_sources n B A`.
By `add_comm` on the pair sum and swap of sources A ↔ B. The
source-conditioned analog of PR #874's `pairFinset_image_swap_eq_self`. -/
theorem Current.pairFinset_with_sources_image_swap_eq
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (A B : Finset ↑Λ) :
    (Current.pairFinset_with_sources G Λ n A B).image Prod.swap
      = Current.pairFinset_with_sources G Λ n B A := by
  ext p
  rw [Finset.mem_image, Current.mem_pairFinset_with_sources_iff]
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [Current.mem_pairFinset_with_sources_iff] at hq
    obtain ⟨hsum, hA, hB⟩ := hq
    refine ⟨?_, hB, hA⟩
    change q.2 + q.1 = n
    rw [add_comm]; exact hsum
  · rintro ⟨hsum, hB, hA⟩
    refine ⟨p.swap, ?_, ?_⟩
    · rw [Current.mem_pairFinset_with_sources_iff]
      refine ⟨?_, hA, hB⟩
      change p.2 + p.1 = n
      rw [add_comm]; exact hsum
    · exact Prod.swap_swap p

set_option linter.unusedDecidableInType false in
/-- **Source-conditioned pair-Finset sum swap invariance**:
`∑ p ∈ pairFinset_with_sources n A B, f p
  = ∑ p ∈ pairFinset_with_sources n B A, f p.swap`.
By the swap image identity + `Finset.sum_image` on the involutive
`Prod.swap`. -/
theorem Current.sum_pairFinset_with_sources_image_swap_eq
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (A B : Finset ↑Λ)
    (f : Current G Λ × Current G Λ → ℝ) :
    ∑ p ∈ Current.pairFinset_with_sources G Λ n A B, f p
      = ∑ p ∈ Current.pairFinset_with_sources G Λ n B A, f p.swap := by
  rw [← Current.pairFinset_with_sources_image_swap_eq G Λ n A B]
  rw [Finset.sum_image]
  · simp [Prod.swap_swap]
  · intro a _ b _ h
    exact (Prod.swap_injective h)

set_option linter.unusedDecidableInType false in
/-- **Source-conditioned pair-Finset card symmetry in (A, B)**:
`(pairFinset_with_sources n A B).card = (pairFinset_with_sources n B A).card`.
By the swap image identity + `Finset.card_image_of_injective` on the
injective `Prod.swap`. -/
theorem Current.pairFinset_with_sources_card_eq_swap
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (A B : Finset ↑Λ) :
    (Current.pairFinset_with_sources G Λ n A B).card
      = (Current.pairFinset_with_sources G Λ n B A).card := by
  rw [← Current.pairFinset_with_sources_image_swap_eq G Λ n A B]
  exact (Finset.card_image_of_injective _ Prod.swap_injective).symm

end Ambient

end IsingModel
