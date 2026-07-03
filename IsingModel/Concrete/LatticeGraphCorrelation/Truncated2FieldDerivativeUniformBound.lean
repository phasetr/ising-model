import IsingModel.Concrete.LatticeGraphCorrelation.Truncated2GeneralFieldFiniteVolumeMajorant
import IsingModel.FieldDerivative.CorrelationMonotonicity

/-!
# Field- and volume-uniform bound for the ∂/∂h two-point derivative (GJ Thm 17.6.1)

The *Option B* capstone of the `∂/∂h` route of Glimm--Jaffe Theorem 17.6.1
(*Quantum Physics*, 2nd ed., p. 313; tracking issue #4413).  On a `Preconnected`
finite induced subgraph `inducedGraph (latticeGraph d) Λ`, for a ferromagnetic
field `⟨J, h, β⟩` with `h ≥ 0` in the strict high-temperature window
`0 < β J (2d) < 1` and distinct sites `i ≠ j`, the finite-volume two-point
function `h' ↦ ⟨σ_i σ_j⟩_{h'}` is differentiable at `h`, and its derivative `g'`
satisfies the two-sided bound
`0 ≤ g' ≤ β (M(i) + M(j) + 2)`,
with `M(x) = ∑_l exp(m) · exp(-m · d_{ℓ¹}(x, l))`, `m = simonLiebRate β J d`,
the finite tsum majorant of brick 2.  The upper bound is **independent of the
field `h` and of the finite volume `Λ`**, giving equi-Lipschitz control of the
family `{h' ↦ ⟨σ_i σ_j⟩_{h'}}_Λ` — exactly the input GJ uses Thm 17.6.1 for
(differential inequalities, critical-exponent bounds).

This is the book-faithful *finite* deliverable: differentiability plus a
field/volume-uniform derivative bound by sums of products of two-point functions,
`TRUE`, axiom-free, and on-book through the Lebowitz correlation inequalities of
§4.3 (GKS-I/II Cor. 4.3.3, GHS Cor. 4.3.4).  It deliberately does **not** claim
infinite-volume `∂/∂h` differentiability (the general-`h` four-point Lebowitz
sign / equicontinuity wall of the class of #4386; the naive full-Ursell
`κ₄ ≤ 0` is numerically false).

## Proof outline

1. `hasDerivAt_correlation_field` at `A = {i, j}` provides `HasDerivAt` with
   derivative `g' = β (⟨σ_iσ_j M⟩_h − ⟨σ_iσ_j⟩_h ⟨M⟩_h)`.
2. `0 ≤ g'` is `correlation_field_deriv_nonneg` at `A = {i, j}` (GKS-II).
3. For the upper bound, `gibbsExpectation_spinProd_mul_mag` and
   `gibbsExpectation_totalMag_eq_sum` rewrite the derivative as a site-sum
   `g' = β ∑_l (⟨σ^{{i,j}△{l}}⟩_h − ⟨σ_iσ_j⟩_h ⟨σ_l⟩_h)`.  Splitting the sum
   into the two diagonal sites `l = i, j` and the off-diagonal remainder:
   * each diagonal term lies in `[0, 1]` (`{i,j}△{i} = {j}`, GKS-I/GKS-II),
     contributing `≤ 2`;
   * the off-diagonal remainder is the semi-truncated two-block susceptibility,
     bounded by `M(i) + M(j)` via brick 2
     `sum_semiTruncated_pair_le_finiteVolumeMajorant`.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., Theorem 17.6.1 (p. 313);
  §4.3, Cor. 4.3.3 (GKS-II), Cor. 4.3.4 (GHS inequality).
-/

namespace IsingModel

namespace Ambient

open Finset

/-- **Field- and volume-uniform bound for the ∂/∂h two-point derivative** (GJ
Theorem 17.6.1, *Quantum Physics*, 2nd ed., p. 313, Option B capstone): on a
`Preconnected` finite induced subgraph `inducedGraph (latticeGraph d) Λ`, for a
ferromagnetic field `⟨J, h, β⟩` with `h ≥ 0`, strict high temperature
`0 < β J (2d) < 1`, and distinct sites `i ≠ j`, the map
`h' ↦ ⟨σ_i σ_j⟩_{h'} = correlation (inducedGraph (latticeGraph d) Λ) ⟨J,h',β⟩ {i,j}`
is differentiable at `h` with a derivative `g'` obeying the two-sided,
field- and volume-uniform bound
`0 ≤ g' ≤ β (M(i) + M(j) + 2)`,
`M(x) = ∑_l exp(m) · exp(-m · d_{ℓ¹}(x, l))`, `m = simonLiebRate β J d`.

Proof: `hasDerivAt_correlation_field` at `A = {i, j}` supplies the derivative
value `β (⟨σ_iσ_j M⟩_h − ⟨σ_iσ_j⟩_h ⟨M⟩_h)` (the `∃ g'` witness);
`correlation_field_deriv_nonneg` gives `0 ≤ g'` (GKS-II).  For the upper bound,
`gibbsExpectation_spinProd_mul_mag` and `gibbsExpectation_totalMag_eq_sum`
recast the derivative as a site-sum, split into the two diagonal sites `l = i, j`
(each in `[0, 1]` by GKS-I/GKS-II, using `{i,j}△{i} = {j}` and `{i,j}△{j} = {i}`)
and the off-diagonal remainder (the semi-truncated two-block susceptibility,
`≤ M(i) + M(j)` by brick 2 `sum_semiTruncated_pair_le_finiteVolumeMajorant`),
whence `g' ≤ β (M(i) + M(j) + 2)`. -/
theorem hasDerivAt_correlation_h_uniform_bound
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J h : ℝ} (hf : Ferromagnetic (⟨J, h, β⟩ : IsingParams ℝ))
    (hβJ2d_pos : 0 < β * J * (2 * (d : ℝ))) (hβJ2d_lt : β * J * (2 * (d : ℝ)) < 1)
    (hconn : (inducedGraph (IsingModel.latticeGraph d) Λ).Preconnected)
    {i j : ↑Λ} (hij : i ≠ j) :
    ∃ g', HasDerivAt (fun h' => correlation (inducedGraph (IsingModel.latticeGraph d) Λ)
              (⟨J, h', β⟩ : IsingParams ℝ) {i, j}) g' h
      ∧ 0 ≤ g'
      ∧ g' ≤ β * ((∑' x : Fin d → ℤ, Real.exp (simonLiebRate β J d)
              * Real.exp (-(simonLiebRate β J d)
                  * (latticeDistance d (i : Fin d → ℤ) x : ℝ)))
          + (∑' x : Fin d → ℤ, Real.exp (simonLiebRate β J d)
              * Real.exp (-(simonLiebRate β J d)
                  * (latticeDistance d (j : Fin d → ℤ) x : ℝ)))
          + 2) := by
  refine ⟨_, hasDerivAt_correlation_field (inducedGraph (IsingModel.latticeGraph d) Λ) J h β
      {i, j},
    correlation_field_deriv_nonneg (inducedGraph (IsingModel.latticeGraph d) Λ) J h β {i, j} hf,
    ?_⟩
  -- Brick-2 off-diagonal semi-truncated majorant (computed before the abbreviation
  -- so `set pr` folds its field data too).
  have hbrick := (sum_semiTruncated_pair_le_finiteVolumeMajorant d Λ hf hβJ2d_pos hβJ2d_lt
    hconn hij).2
  set pr := (⟨J, h, β⟩ : IsingParams ℝ) with hpr
  -- Step 3: recast the derivative value as a GKS-II site-sum.
  rw [gibbsExpectation_spinProd_mul_mag, gibbsExpectation_totalMag_eq_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine mul_le_mul_of_nonneg_left ?_ hf.hβ.le
  -- Off-diagonal terms: `{i,j}△{l} = {i,j,l}` for `l ≠ i, j`, matching brick 2.
  have hoff_eq : ∑ l ∈ Finset.univ.filter (fun l : ↑Λ => l ≠ i ∧ l ≠ j),
        (correlation (inducedGraph (IsingModel.latticeGraph d) Λ) pr (symmDiff {i, j} {l})
          - correlation (inducedGraph (IsingModel.latticeGraph d) Λ) pr {i, j}
            * correlation (inducedGraph (IsingModel.latticeGraph d) Λ) pr {l})
      = ∑ l ∈ Finset.univ.filter (fun l : ↑Λ => l ≠ i ∧ l ≠ j),
        (correlation (inducedGraph (IsingModel.latticeGraph d) Λ) pr {i, j, l}
          - correlation (inducedGraph (IsingModel.latticeGraph d) Λ) pr {i, j}
            * correlation (inducedGraph (IsingModel.latticeGraph d) Λ) pr {l}) := by
    refine Finset.sum_congr rfl (fun l hl => ?_)
    rw [Finset.mem_filter] at hl
    have hsymm : symmDiff ({i, j} : Finset ↑Λ) {l} = ({i, j, l} : Finset ↑Λ) := by
      ext x
      simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro (⟨h | rfl, _⟩ | ⟨rfl, _⟩)
        · exact Or.inl h
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
      · rintro (rfl | rfl | rfl)
        · exact Or.inl ⟨Or.inl rfl, hl.2.1.symm⟩
        · exact Or.inl ⟨Or.inr rfl, hl.2.2.symm⟩
        · exact Or.inr ⟨rfl, fun hx => hx.elim hl.2.1 hl.2.2⟩
    rw [hsymm]
  -- Diagonal terms: the complement filter is exactly the pair `{i, j}`.
  have hcompl : ∑ l ∈ Finset.univ.filter (fun l : ↑Λ => ¬(l ≠ i ∧ l ≠ j)),
        (correlation (inducedGraph (IsingModel.latticeGraph d) Λ) pr (symmDiff {i, j} {l})
          - correlation (inducedGraph (IsingModel.latticeGraph d) Λ) pr {i, j}
            * correlation (inducedGraph (IsingModel.latticeGraph d) Λ) pr {l})
      = (correlation (inducedGraph (IsingModel.latticeGraph d) Λ) pr (symmDiff {i, j} {i})
            - correlation (inducedGraph (IsingModel.latticeGraph d) Λ) pr {i, j}
              * correlation (inducedGraph (IsingModel.latticeGraph d) Λ) pr {i})
        + (correlation (inducedGraph (IsingModel.latticeGraph d) Λ) pr (symmDiff {i, j} {j})
            - correlation (inducedGraph (IsingModel.latticeGraph d) Λ) pr {i, j}
              * correlation (inducedGraph (IsingModel.latticeGraph d) Λ) pr {j}) := by
    rw [show Finset.univ.filter (fun l : ↑Λ => ¬(l ≠ i ∧ l ≠ j)) = ({i, j} : Finset ↑Λ)
        from ?_, Finset.sum_pair hij]
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and_or, not_not,
      Finset.mem_insert, Finset.mem_singleton]
  -- Diagonal `l = i`: `{i,j}△{i} = {j}`, term in `[0, 1]` by GKS-I/GKS-II.
  have hSi_le : correlation (inducedGraph (IsingModel.latticeGraph d) Λ) pr (symmDiff {i, j} {i})
        - correlation (inducedGraph (IsingModel.latticeGraph d) Λ) pr {i, j}
          * correlation (inducedGraph (IsingModel.latticeGraph d) Λ) pr {i} ≤ 1 := by
    have hsymm : symmDiff ({i, j} : Finset ↑Λ) {i} = ({j} : Finset ↑Λ) := by
      ext x
      simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro (⟨hx, hxi⟩ | ⟨hxi, hx⟩)
        · rcases hx with rfl | rfl
          · exact absurd rfl hxi
          · rfl
        · exact absurd (Or.inl hxi) hx
      · rintro rfl
        exact Or.inl ⟨Or.inr rfl, hij.symm⟩
    rw [hsymm]
    have h1 : correlation (inducedGraph (IsingModel.latticeGraph d) Λ) pr {j} ≤ 1 :=
      le_trans (le_abs_self _)
        (abs_correlation_le_one (inducedGraph (IsingModel.latticeGraph d) Λ) pr {j})
    have h2 : 0 ≤ correlation (inducedGraph (IsingModel.latticeGraph d) Λ) pr {i, j}
          * correlation (inducedGraph (IsingModel.latticeGraph d) Λ) pr {i} :=
      mul_nonneg (gks_first (inducedGraph (IsingModel.latticeGraph d) Λ) pr hf {i, j})
        (gks_first (inducedGraph (IsingModel.latticeGraph d) Λ) pr hf {i})
    linarith
  -- Diagonal `l = j`: `{i,j}△{j} = {i}`, term in `[0, 1]` by GKS-I/GKS-II.
  have hSj_le : correlation (inducedGraph (IsingModel.latticeGraph d) Λ) pr (symmDiff {i, j} {j})
        - correlation (inducedGraph (IsingModel.latticeGraph d) Λ) pr {i, j}
          * correlation (inducedGraph (IsingModel.latticeGraph d) Λ) pr {j} ≤ 1 := by
    have hsymm : symmDiff ({i, j} : Finset ↑Λ) {j} = ({i} : Finset ↑Λ) := by
      ext x
      simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro (⟨hx, hxj⟩ | ⟨hxj, hx⟩)
        · rcases hx with rfl | rfl
          · rfl
          · exact absurd rfl hxj
        · exact absurd (Or.inr hxj) hx
      · rintro rfl
        exact Or.inl ⟨Or.inl rfl, hij⟩
    rw [hsymm]
    have h1 : correlation (inducedGraph (IsingModel.latticeGraph d) Λ) pr {i} ≤ 1 :=
      le_trans (le_abs_self _)
        (abs_correlation_le_one (inducedGraph (IsingModel.latticeGraph d) Λ) pr {i})
    have h2 : 0 ≤ correlation (inducedGraph (IsingModel.latticeGraph d) Λ) pr {i, j}
          * correlation (inducedGraph (IsingModel.latticeGraph d) Λ) pr {j} :=
      mul_nonneg (gks_first (inducedGraph (IsingModel.latticeGraph d) Λ) pr hf {i, j})
        (gks_first (inducedGraph (IsingModel.latticeGraph d) Λ) pr hf {j})
    linarith
  -- Split the site-sum into diagonal + off-diagonal and assemble the bounds.
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun l : ↑Λ => l ≠ i ∧ l ≠ j),
    hoff_eq, hcompl]
  linarith [hbrick, hSi_le, hSj_le]

end Ambient

end IsingModel
