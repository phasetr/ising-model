import IsingModel.ComplexAnalyticity.Basic

/-!
# Polynomial Lower Bounds

This module is part of the split `IsingModel.ComplexAnalyticity` development.
-/

namespace IsingModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped Complex

/-! ## Uniform one-variable specialisation of multilinear polynomials -/

/-- Specialise a multilinear polynomial to one variable by setting all
coordinates equal to the same complex number. -/
noncomputable def MultilinPoly.uniformPolynomial (p : MultilinPoly ι) : Polynomial ℂ :=
  ∑ X : Finset ι, Polynomial.monomial X.card (p X)

omit [DecidableEq ι] in
/-- Evaluating the one-variable specialisation agrees with evaluating the
multilinear polynomial at a constant vector. -/
theorem MultilinPoly.uniformPolynomial_eval (p : MultilinPoly ι) (z : ℂ) :
    p.uniformPolynomial.eval z = p.eval (fun _ : ι => z) := by
  unfold MultilinPoly.uniformPolynomial MultilinPoly.eval
  rw [Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl ?_
  intro X _
  rw [Polynomial.eval_monomial]
  simp [Finset.prod_const]

omit [DecidableEq ι] in
/-- The one-variable specialisation has degree at most the number of variables. -/
theorem MultilinPoly.uniformPolynomial_natDegree_le_card (p : MultilinPoly ι) :
    p.uniformPolynomial.natDegree ≤ Fintype.card ι := by
  unfold MultilinPoly.uniformPolynomial
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
  intro X _
  exact (Polynomial.natDegree_monomial_le (p X)).trans X.card_le_univ

omit [DecidableEq ι] in
/-- A multilinear polynomial evaluated at the zero vector gives its constant
coefficient. -/
theorem MultilinPoly.eval_const_zero (p : MultilinPoly ι) :
    p.eval (fun _ : ι => (0 : ℂ)) = p ∅ := by
  classical
  unfold MultilinPoly.eval
  simpa using
    (Finset.sum_eq_single (s := (Finset.univ : Finset (Finset ι))) (a := (∅ : Finset ι))
      (f := fun X : Finset ι => p X * ∏ i ∈ X, (fun _ : ι => (0 : ℂ)) i)
      (by
        intro X _ hX
        have hne : X.Nonempty := Finset.nonempty_iff_ne_empty.mpr hX
        rcases hne with ⟨i, hi⟩
        have hprod : (∏ i ∈ X, (fun _ : ι => (0 : ℂ)) i) = 0 :=
          Finset.prod_eq_zero hi rfl
        simp [hprod])
      (by intro hmem; simp at hmem))

/-! ## One-variable root-product lower bound -/

/-- If a complex polynomial has value `1` at `0` and all roots have modulus at
least one, then on `‖z‖ ≤ r < 1` its value is bounded below by
`(1 - r)^natDegree`. -/
theorem Polynomial.one_sub_radius_pow_natDegree_le_norm_eval_of_roots_norm_ge_one
    (p : Polynomial ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hp0 : p.eval 0 = 1)
    (hroots : ∀ a ∈ p.roots, 1 ≤ ‖a‖) {z : ℂ} (hz : ‖z‖ ≤ r) :
    (1 - r) ^ p.natDegree ≤ ‖p.eval z‖ := by
  have hsplit : p.Splits := IsAlgClosed.splits p
  have hcard : p.roots.card = p.natDegree := hsplit.natDegree_eq_card_roots.symm
  have h1r_nonneg : 0 ≤ 1 - r := by linarith
  have h_eval_z := hsplit.eval_eq_prod_roots z
  have h_eval_0 := hsplit.eval_eq_prod_roots (0 : ℂ)
  have hnorm_prod_z :
      ‖(p.roots.map (fun a => z - a)).prod‖ =
        (p.roots.map (fun a => ‖z - a‖)).prod := by
    change (NormedField.toMulRingNorm ℂ) (p.roots.map (fun a => z - a)).prod =
      (p.roots.map (fun a => (NormedField.toMulRingNorm ℂ) (z - a))).prod
    exact (p.roots.prod_hom' (NormedField.toMulRingNorm ℂ) (fun a : ℂ => z - a)).symm
  have hnorm_prod_0' :
      ‖(p.roots.map (fun a => (0 : ℂ) - a)).prod‖ =
        (p.roots.map (fun a => ‖(0 : ℂ) - a‖)).prod := by
    change (NormedField.toMulRingNorm ℂ) (p.roots.map (fun a => (0 : ℂ) - a)).prod =
      (p.roots.map (fun a => (NormedField.toMulRingNorm ℂ) ((0 : ℂ) - a))).prod
    exact
      (p.roots.prod_hom' (NormedField.toMulRingNorm ℂ)
        (fun a : ℂ => (0 : ℂ) - a)).symm
  have hnorm_prod_0 :
      ‖(p.roots.map (fun a => (0 : ℂ) - a)).prod‖ =
        (p.roots.map (fun a => ‖a‖)).prod := by
    rw [hnorm_prod_0']
    congr 1
    ext a
    simp
  have hnorm_z :
      ‖p.eval z‖ = ‖p.leadingCoeff‖ * (p.roots.map (fun a => ‖z - a‖)).prod := by
    rw [h_eval_z, norm_mul, hnorm_prod_z]
  have hnorm0 : ‖p.leadingCoeff‖ * (p.roots.map (fun a => ‖a‖)).prod = 1 := by
    have := congrArg norm hp0
    rw [h_eval_0, norm_mul, hnorm_prod_0, norm_one] at this
    exact this
  have hfactor_le :
      (p.roots.map (fun a => (1 - r) * ‖a‖)).prod
        ≤ (p.roots.map (fun a => ‖z - a‖)).prod := by
    refine Multiset.prod_map_le_prod_map₀
      (fun a => (1 - r) * ‖a‖) (fun a => ‖z - a‖) ?_ ?_
    · intro a _
      exact mul_nonneg h1r_nonneg (norm_nonneg a)
    · intro a ha
      have ha1 : 1 ≤ ‖a‖ := hroots a ha
      have hsub : ‖a‖ - ‖z‖ ≤ ‖z - a‖ := by
        simpa [norm_sub_rev] using norm_sub_norm_le a z
      calc
        (1 - r) * ‖a‖ = ‖a‖ - r * ‖a‖ := by ring
        _ ≤ ‖a‖ - r := by
          gcongr
          exact le_mul_of_one_le_right hr0 ha1
        _ ≤ ‖a‖ - ‖z‖ := by gcongr
        _ ≤ ‖z - a‖ := hsub
  have hfactor_eq :
      (p.roots.map (fun a => (1 - r) * ‖a‖)).prod =
        (1 - r) ^ p.roots.card * (p.roots.map (fun a => ‖a‖)).prod := by
    rw [Multiset.prod_map_mul]
    simp [Multiset.prod_replicate]
  calc
    (1 - r) ^ p.natDegree
        = (1 - r) ^ p.roots.card * 1 := by rw [hcard, mul_one]
    _ = (1 - r) ^ p.roots.card *
          (‖p.leadingCoeff‖ * (p.roots.map (fun a => ‖a‖)).prod) := by rw [hnorm0]
    _ = ‖p.leadingCoeff‖ *
          ((1 - r) ^ p.roots.card * (p.roots.map (fun a => ‖a‖)).prod) := by ring
    _ ≤ ‖p.leadingCoeff‖ * (p.roots.map (fun a => ‖z - a‖)).prod := by
      gcongr
      rwa [← hfactor_eq]
    _ = ‖p.eval z‖ := hnorm_z.symm

end IsingModel
