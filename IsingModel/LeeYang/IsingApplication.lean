import IsingModel.LeeYang.Nonvanishing

/-!
# Lee-Yang circle theorem split — application to the Ising partition polynomial

Part of the split Lee-Yang circle-theorem layer (Issue #1850).
-/

namespace IsingModel

open Finset Complex

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Application to Ising model -/

/-- The edge weight factor for the Ising partition polynomial.
For an edge `(i, j)` with coupling `t`, the weight of subset `X` is
`t` if exactly one of `i, j` is in `X`, and `1` otherwise.

Reference: Friedli–Velenik, (3.63), p. 122. -/
def edgeWeight (i j : ι) (t : ℝ) (X : Finset ι) : ℂ :=
  if (i ∈ X) = (j ∈ X) then 1 else ↑t

/-- The Ising partition polynomial for a list of edges with couplings.
`P_E(z) = Σ_{X⊆V} (∏_e w_e(X)) ∏_{i∈X} z_i` where `w_e(X) = t_e` if
exactly one endpoint of `e` is in `X`, and `1` otherwise.

This captures the multilinear form of the Ising partition function with
`z_i = e^{-2h_i}`, `t_e = e^{-2β J_e}`.

Reference: Friedli–Velenik, (3.63)--(3.65), pp. 122--123. -/
noncomputable def isingEdgePoly (edges : List (ι × ι × ℝ)) : MultilinPoly ι :=
  fun X => (edges.map fun e => edgeWeight e.1 e.2.1 e.2.2 X).prod

/-- The sum over all subsets of the product of selected elements equals the product of (1 + z_i).
`∑_{X⊆ι} ∏_{i∈X} z_i = ∏_i (1 + z_i)`. -/
private lemma eval_one_poly {ι : Type*} [Fintype ι] (z : ι → ℂ) :
    MultilinPoly.eval (fun (_ : Finset ι) => (1 : ℂ)) z = ∏ k : ι, (1 + z k) := by
  simp only [MultilinPoly.eval, one_mul]
  have := @Finset.prod_one_add ι ℂ _ z Finset.univ
  rw [Finset.powerset_univ] at this
  exact this.symm

/-- The Ising matrix constructed from an edge list.
For vertices `i ≠ j`, `isingMatrix edges i j = ∏_{e connecting i,j} t_e`.
For `i = j`, `isingMatrix edges i i = 1`.

This matrix is real symmetric (hence Hermitian) with `|A i j| ≤ 1` when
all couplings satisfy `0 ≤ t_e < 1`. -/
noncomputable def isingMatrix (edges : List (ι × ι × ℝ)) (i j : ι) : ℂ :=
  (edges.map fun e =>
    if (e.1 = i ∧ e.2.1 = j) ∨ (e.1 = j ∧ e.2.1 = i) then (e.2.2 : ℂ) else 1).prod

omit [Fintype ι] in
/-- The Ising matrix is symmetric: `isingMatrix edges i j = isingMatrix edges j i`. -/
private lemma isingMatrix_symm (edges : List (ι × ι × ℝ)) (i j : ι) :
    isingMatrix edges i j = isingMatrix edges j i := by
  unfold isingMatrix
  congr 1
  apply List.map_congr_left
  intro e _
  simp only [or_comm]

omit [Fintype ι] in
/-- Cons decomposition of the Ising matrix. -/
private lemma isingMatrix_cons (e : ι × ι × ℝ) (edges : List (ι × ι × ℝ)) (i j : ι) :
    isingMatrix (e :: edges) i j =
    (if (e.1 = i ∧ e.2.1 = j) ∨ (e.1 = j ∧ e.2.1 = i) then (e.2.2 : ℂ) else 1) *
    isingMatrix edges i j := by
  simp [isingMatrix, List.map_cons, List.prod_cons]

/-- Pull a constant-condition `if` out of a `Finset.prod`. -/
private lemma prod_ite_const_cond {α : Type*} {S : Finset α} {p : Prop} [Decidable p]
    {f : α → ℂ} :
    ∏ j ∈ S, (if p then f j else 1) = if p then ∏ j ∈ S, f j else 1 := by
  split_ifs <;> simp_all

set_option maxHeartbeats 400000 in
-- edgeWeight_eq_prod: 4 case splits on (i∈X, j∈X), each with Finset.prod simplification
/-- For a single edge `e`, the edge weight equals the product of the single-edge
matrix entries over all cross-boundary pairs `(i,j)` with `i ∈ X, j ∉ X`.

The proof factors the condition `(a=i ∧ b=j) ∨ (a=j ∧ b=i)` into two independent
conditions (one for each endpoint), uses `Finset.prod_ite_eq` to collapse inner/outer
products, then matches the result with `edgeWeight` by case analysis. -/
private lemma edgeWeight_eq_prod (e : ι × ι × ℝ) (hne : e.1 ≠ e.2.1) (X : Finset ι) :
    edgeWeight e.1 e.2.1 e.2.2 X =
    ∏ i ∈ X, ∏ j ∈ Finset.univ \ X,
      (if (e.1 = i ∧ e.2.1 = j) ∨ (e.1 = j ∧ e.2.1 = i) then (e.2.2 : ℂ) else 1) := by
  -- Factor: (a=i∧b=j)∨(a=j∧b=i) ↔ (a=i then b=j) × (b=i then a=j) [disjoint since a≠b]
  have h_factor : ∀ (i j : ι),
      (if (e.1 = i ∧ e.2.1 = j) ∨ (e.1 = j ∧ e.2.1 = i) then (e.2.2 : ℂ) else 1) =
      (if e.1 = i then if e.2.1 = j then ↑e.2.2 else 1 else 1) *
      (if e.2.1 = i then if e.1 = j then ↑e.2.2 else 1 else 1) := by
    intro i j; by_cases h1 : e.1 = i <;> by_cases h2 : e.2.1 = i <;> simp_all
  -- Simplify: factor products, pull constant conditions, apply prod_ite_eq
  simp_rw [h_factor, Finset.prod_mul_distrib, prod_ite_const_cond, Finset.prod_ite_eq]
  -- Result: (if a∈X then (if b∈univ\X then t else 1) else 1) * (...same with a,b swapped...)
  -- = edgeWeight by case analysis
  unfold edgeWeight
  by_cases ha : e.1 ∈ X <;> by_cases hb : e.2.1 ∈ X <;> simp_all [Finset.mem_sdiff]

/-- The Ising edge polynomial coefficient equals the Lee-Yang polynomial coefficient
constructed from the Ising matrix: `isingEdgePoly edges X = ∏_{i∈X} ∏_{j∉X} isingMatrix edges i j`.
This bridges the combinatorial (edge-based) and matrix (entry-based) formulations.

Reference: Friedli–Velenik, (3.63)--(3.65), pp. 122--123. -/
private lemma isingEdgePoly_eq_leeYangCoeff (edges : List (ι × ι × ℝ))
    (hne : ∀ e ∈ edges, e.1 ≠ e.2.1) (X : Finset ι) :
    isingEdgePoly edges X =
    ∏ i ∈ X, ∏ j ∈ Finset.univ \ X, isingMatrix edges i j := by
  induction edges with
  | nil => simp [isingEdgePoly, isingMatrix]
  | cons e edges' ih =>
    have hne' := fun e' he' => hne e' (List.mem_cons_of_mem _ he')
    -- isingEdgePoly (e::edges') X = edgeWeight · isingEdgePoly edges' X
    have hcons : isingEdgePoly (e :: edges') X =
        edgeWeight e.1 e.2.1 e.2.2 X * isingEdgePoly edges' X := by
      simp [isingEdgePoly]
    rw [hcons, ih hne']
    -- Factor the RHS: isingMatrix(e::edges') = g(e) · isingMatrix(edges')
    suffices h : ∏ i ∈ X, ∏ j ∈ Finset.univ \ X, isingMatrix (e :: edges') i j =
        (∏ i ∈ X, ∏ j ∈ Finset.univ \ X,
          (if (e.1 = i ∧ e.2.1 = j) ∨ (e.1 = j ∧ e.2.1 = i) then (e.2.2 : ℂ) else 1)) *
        (∏ i ∈ X, ∏ j ∈ Finset.univ \ X, isingMatrix edges' i j) by
      rw [h]; congr 1
      exact edgeWeight_eq_prod e (hne e List.mem_cons_self) X
    simp_rw [isingMatrix_cons, Finset.prod_mul_distrib]

/-- The base case: `isingEdgePoly [] = 1` (constant polynomial). -/
private lemma isingEdgePoly_nil : isingEdgePoly (ι := ι) [] = fun _ => 1 := by
  ext X; simp [isingEdgePoly]

/-- **Lee-Yang circle theorem**: The Ising partition polynomial does not vanish
on the open unit polydisk. Reference: Friedli–Velenik, Theorem 3.43, pp. 122–127. -/
theorem lee_yang_circle (edges : List (ι × ι × ℝ))
    (hne : ∀ e ∈ edges, e.1 ≠ e.2.1)
    (ht : ∀ e ∈ edges, 0 ≤ e.2.2 ∧ e.2.2 < 1)
    (z : ι → ℂ) (hz : ∀ k, ‖z k‖ < 1) :
    (isingEdgePoly edges).eval z ≠ 0 := by
  induction edges with
  | nil =>
    -- P(z) = ∏_i (1 + z_i) ≠ 0 since each factor ≠ 0 for |z_i| < 1
    rw [show isingEdgePoly (ι := ι) [] = fun _ => 1 from isingEdgePoly_nil, eval_one_poly]
    exact Finset.prod_ne_zero_iff.mpr (fun k _ h => by
      have : z k = -1 := by linear_combination h
      linarith [hz k, show ‖z k‖ = 1 from by rw [this, norm_neg, norm_one]])
  | cons e edges' _ =>
    -- Use Harcos/Ruelle approach via the Ising matrix.
    -- Step 1: isingEdgePoly = leeYangPoly for the Ising matrix
    have hcoeff : ∀ X, isingEdgePoly (e :: edges') X =
        ∏ i ∈ X, ∏ j ∈ Finset.univ \ X, isingMatrix (e :: edges') i j :=
      fun X => isingEdgePoly_eq_leeYangCoeff _ (fun e' he' => hne e' he') X
    -- Step 2: eval identity
    have heval : (isingEdgePoly (e :: edges')).eval z =
        MultilinPoly.eval (fun S => ∏ i ∈ S, ∏ j ∈ Finset.univ \ S,
          isingMatrix (e :: edges') i j) z := by
      unfold MultilinPoly.eval
      congr 1; ext S; congr 1; exact hcoeff S
    rw [heval]
    -- Step 3: Transport to Fin n via Fintype.equivFin and apply leeYangPoly_nonvanishing
    let A : Matrix ι ι ℂ := isingMatrix (e :: edges')
    let equiv := Fintype.equivFin ι
    let A' : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ :=
      A.submatrix equiv.symm equiv.symm
    let z' : Fin (Fintype.card ι) → ℂ := z ∘ equiv.symm
    -- A is Hermitian: conj(A i j) = A j i
    -- Proof: entries are real (conj = id) and symmetric (isingMatrix_symm)
    have hAH : A'.IsHermitian := by
      ext i j
      simp only [Matrix.conjTranspose_apply, RCLike.star_def]
      -- conj(isingMatrix i j) = isingMatrix i j (real entries)
      have hreal : ∀ (edges : List (ι × ι × ℝ)) (a b : ι),
          starRingEnd ℂ (isingMatrix edges a b) = isingMatrix edges a b := by
        intro edges a b; unfold isingMatrix
        induction edges with
        | nil => simp
        | cons e' l ih =>
          simp only [List.map_cons, List.prod_cons, map_mul, ih]
          congr 1; split_ifs <;> simp
      change starRingEnd ℂ (isingMatrix _ _ _) = isingMatrix _ _ _
      rw [hreal]; exact isingMatrix_symm _ _ _
    -- |A' i j| ≤ 1 (product of factors in [0,1])
    have hAB : ∀ i j, ‖A' i j‖ ≤ 1 := by
      intro i j; change ‖isingMatrix _ _ _‖ ≤ 1
      -- Show ‖isingMatrix edges a b‖ ≤ 1 by induction on edges
      suffices h : ∀ (edges : List (ι × ι × ℝ)),
          (∀ e' ∈ edges, 0 ≤ e'.2.2 ∧ e'.2.2 < 1) →
          ∀ a b : ι, ‖isingMatrix edges a b‖ ≤ 1 from h _ ht _ _
      intro edges ht' a b; unfold isingMatrix
      induction edges with
      | nil => simp
      | cons e' l ih =>
        simp only [List.map_cons, List.prod_cons, norm_mul]
        exact mul_le_one₀
          (by split_ifs
              · rw [norm_real, Real.norm_of_nonneg (ht' e' List.mem_cons_self).1]
                exact le_of_lt (ht' e' List.mem_cons_self).2
              · simp)
          (norm_nonneg _)
          (ih (fun e'' he'' => ht' e'' (List.mem_cons_of_mem _ he'')))
    -- The eval under reindexing matches
    have hTransport : MultilinPoly.eval (fun S => ∏ i ∈ S, ∏ j ∈ Finset.univ \ S, A i j) z =
        (leeYangPoly A').eval z' := by
      unfold MultilinPoly.eval leeYangPoly
      apply Fintype.sum_equiv (Equiv.finsetCongr equiv)
      intro S; simp only [Equiv.finsetCongr_apply]
      -- S ↦ S.map equiv: show eval terms match
      have hcompl : Finset.univ \ S.map equiv.toEmbedding =
          (Finset.univ \ S).map equiv.toEmbedding := by
        ext x; simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
          Finset.mem_map, Function.Embedding.coeFn_mk]
        constructor
        · intro hx; exact ⟨equiv.symm x, fun h => hx ⟨_, h, equiv.apply_symm_apply x⟩,
            equiv.apply_symm_apply x⟩
        · rintro ⟨y, hy, rfl⟩; intro ⟨w, hw, he⟩; exact hy (equiv.injective he ▸ hw)
      -- Monomial: ∏_{k∈S.map e} z'(k) = ∏_{k∈S} z(k)
      -- Coefficient: ∏_{i∈S.map e} ∏_{j∈compl} A'(i)(j) = ∏_{i∈S} ∏_{j∈univ\S} A(i)(j)
      change (fun S => ∏ i ∈ S, ∏ j ∈ Finset.univ \ S, A i j) S * ∏ k ∈ S, z k =
        (∏ i ∈ S.map equiv.toEmbedding, ∏ j ∈ Finset.univ \ S.map equiv.toEmbedding,
          A (equiv.symm i) (equiv.symm j)) *
        ∏ k ∈ S.map equiv.toEmbedding, z (equiv.symm k)
      simp only [Finset.prod_map, hcompl, Function.Embedding.coeFn_mk, Equiv.symm_apply_apply]
    rw [hTransport]
    exact leeYangPoly_nonvanishing A' hAH hAB z' (fun k => hz _)



end IsingModel
