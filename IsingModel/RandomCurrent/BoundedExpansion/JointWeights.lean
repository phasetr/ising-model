import IsingModel.RandomCurrent.BoundedExpansion.Taylor

/-!
# Bounded random-current joint weights

Mechanical child split from `RandomCurrent/BoundedExpansion.lean`.
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

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
lemma** (FV §3.10.6), \(weight β J n₁ \cdot weight β J n₂
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
(FV §3.10.6). -/
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
switching key identity in its final form (FV §3.10.6). -/
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

end Ambient
end IsingModel
