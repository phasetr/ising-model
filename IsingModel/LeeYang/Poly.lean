import IsingModel.Asano

/-!
# Lee-Yang circle theorem split — Lee-Yang polynomial and coefficient helpers

Part of the split Lee-Yang circle-theorem layer (Issue #1850).
-/

namespace IsingModel

open Finset Complex

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Lee-Yang circle theorem (Harcos/Ruelle approach) -/

/-- The Lee-Yang polynomial for an `n × n` matrix `A`:
`f_A(z) = Σ_{S⊆[n]} (∏_{i∈S, j∉S} a_{ij}) · (∏_{k∈S} z_k)`.

When `A` is Hermitian with `|a_{ij}| ≤ 1`, this polynomial does not vanish on the
open unit polydisk. This is the key object in the Harcos/Ruelle proof of the
Lee-Yang circle theorem.

Reference: Harcos, based on Ruelle, Ann. of Math. 171 (2010), 589–603. -/
noncomputable def leeYangPoly {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    MultilinPoly (Fin n) :=
  fun S => ∏ i ∈ S, ∏ j ∈ Finset.univ \ S, A i j

/-- For a Hermitian matrix, `conj(A i j) = A j i`. -/
lemma hermitian_conj_entry {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (i j : Fin n) :
    starRingEnd ℂ (A i j) = A j i := by
  have h := congr_fun (congr_fun hA.eq j) i
  simp only [Matrix.conjTranspose_apply, RCLike.star_def] at h
  exact h

/-- The complement of `T.map castSucc` in `Fin (m+1)` is
`{last} ∪ (univ \ T).map castSucc`. -/
private lemma complement_map_castSucc {m : ℕ} (T : Finset (Fin m)) :
    Finset.univ \ T.map ⟨Fin.castSucc, Fin.castSucc_injective m⟩ =
    insert (Fin.last m) ((Finset.univ \ T).map ⟨Fin.castSucc, Fin.castSucc_injective m⟩) := by
  ext j
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_map,
    Finset.mem_insert, Function.Embedding.coeFn_mk]
  constructor
  · intro hj
    induction j using Fin.lastCases with
    | last => left; rfl
    | cast i =>
      right
      exact ⟨i, fun hT => hj ⟨i, hT, rfl⟩, rfl⟩
  · rintro (rfl | ⟨x, hx, rfl⟩)
    · rintro ⟨y, _, hy⟩; exact absurd hy (Fin.castSucc_ne_last y)
    · rintro ⟨y, hy, hc⟩
      exact hx ((Fin.castSucc_injective m hc) ▸ hy)

/-- The complement of `insert last (T.map castSucc)` in `Fin (m+1)` is
`(univ \ T).map castSucc`. -/
private lemma complement_insert_last_map_castSucc {m : ℕ} (T : Finset (Fin m)) :
    Finset.univ \ insert (Fin.last m) (T.map ⟨Fin.castSucc, Fin.castSucc_injective m⟩) =
    (Finset.univ \ T).map ⟨Fin.castSucc, Fin.castSucc_injective m⟩ := by
  ext j
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_map, Function.Embedding.coeFn_mk]
  constructor
  · intro h
    have hne : j ≠ Fin.last m := fun heq => h (Or.inl heq)
    have hni : ¬∃ a ∈ T, a.castSucc = j := fun hex => h (Or.inr hex)
    induction j using Fin.lastCases with
    | last => exact absurd rfl hne
    | cast i => exact ⟨i, fun hi => hni ⟨i, hi, rfl⟩, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    intro h
    rcases h with heq | ⟨y, hy, hc⟩
    · exact absurd heq (Fin.castSucc_ne_last x)
    · exact hx ((Fin.castSucc_injective m hc) ▸ hy)

/-- Conjugation of Lee-Yang coefficients corresponds to taking the complement.
For Hermitian `A`: `conj(leeYangPoly A T) = leeYangPoly A (univ \ T)`. -/
private lemma leeYangPoly_conj_eq_compl {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (T : Finset (Fin n)) :
    starRingEnd ℂ (leeYangPoly A T) = leeYangPoly A (Finset.univ \ T) := by
  unfold leeYangPoly
  simp only [map_prod]
  simp_rw [hermitian_conj_entry A hA]
  rw [Finset.prod_comm]
  congr 1; ext j; congr 1
  ext x; simp

/-- Coefficient identity for `last ∉ S`: the Lee-Yang coefficient of `T.map castSucc`
factors into the submatrix coefficient times the coupling to the last row.

`leeYangPoly A (T.map cs) = leeYangPoly B T · ∏_{i∈T} A (cs i) last`

where `B = A.submatrix castSucc castSucc`. -/
lemma leeYangPoly_coeff_notin {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (T : Finset (Fin m)) (z : Fin (m + 1) → ℂ) :
    leeYangPoly A (T.map ⟨Fin.castSucc, Fin.castSucc_injective m⟩) *
      ∏ k ∈ T.map ⟨Fin.castSucc, Fin.castSucc_injective m⟩, z k =
    leeYangPoly (A.submatrix Fin.castSucc Fin.castSucc) T *
      ∏ i ∈ T, (A (Fin.castSucc i) (Fin.last m) * z (Fin.castSucc i)) := by
  unfold leeYangPoly
  rw [Finset.prod_map, Finset.prod_map]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  congr 1; ext i
  rw [complement_map_castSucc T]
  have hlast_nmem : Fin.last m ∉
      (Finset.univ \ T).map ⟨Fin.castSucc, Fin.castSucc_injective m⟩ := by
    simp [Finset.mem_map, Fin.castSucc_ne_last]
  rw [Finset.prod_insert hlast_nmem, Finset.prod_map]
  simp only [Matrix.submatrix_apply, Function.Embedding.coeFn_mk]
  ring

/-- Coefficient identity for `last ∈ S`: the Lee-Yang coefficient of
`insert last (T.map castSucc)` factors into the submatrix coefficient times
the coupling from the last column.

`leeYangPoly A (insert last (T.map cs)) = leeYangPoly B T · ∏_{j∈univ\T} A last (cs j)` -/
lemma leeYangPoly_coeff_in {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (T : Finset (Fin m)) :
    leeYangPoly A (insert (Fin.last m) (T.map ⟨Fin.castSucc, Fin.castSucc_injective m⟩)) =
    leeYangPoly (A.submatrix Fin.castSucc Fin.castSucc) T *
      ∏ j ∈ (Finset.univ \ T), A (Fin.last m) (Fin.castSucc j) := by
  unfold leeYangPoly
  rw [complement_insert_last_map_castSucc]
  have hlast_nmem : Fin.last m ∉
      T.map ⟨Fin.castSucc, Fin.castSucc_injective m⟩ := by
    simp [Finset.mem_map, Fin.castSucc_ne_last]
  rw [Finset.prod_insert hlast_nmem]
  rw [Finset.prod_map, Finset.prod_map]
  simp_rw [Finset.prod_map]
  simp only [Matrix.submatrix_apply, Function.Embedding.coeFn_mk]
  ring

/-- Torus identity for the multilinear evaluation.  For Hermitian `B` and any vector `a`,
the α-polynomial `∑_T (lyp B T · ∏_{j∉T} conj a_j) ∏_{k∈T} v_k` equals
`(∏ v_k) · conj(∑_S lyp B S · ∏_{k∈S} (a_k · v_k))` when `‖v_k‖ = 1`.
This is the core algebraic identity in the Harcos/Ruelle proof. -/
lemma torus_identity {m : ℕ}
    (B : Matrix (Fin m) (Fin m) ℂ) (hB : B.IsHermitian)
    (a : Fin m → ℂ) (v : Fin m → ℂ) (hv : ∀ k, ‖v k‖ = 1) :
    MultilinPoly.eval (fun T : Finset (Fin m) =>
      leeYangPoly B T * ∏ j ∈ Finset.univ \ T, starRingEnd ℂ (a j)) v =
    (∏ k : Fin m, v k) *
      starRingEnd ℂ ((leeYangPoly B).eval (fun i => a i * v i)) := by
  unfold MultilinPoly.eval
  simp only [map_sum, map_mul, map_prod, Finset.mul_sum,
    leeYangPoly_conj_eq_compl B hB]
  simp_rw [Finset.prod_mul_distrib]
  have hconj_inv : ∀ z : ℂ, ‖z‖ = 1 → starRingEnd ℂ z = z⁻¹ := fun z hz =>
    eq_comm.mp (inv_eq_of_mul_eq_one_right (by rw [@RCLike.mul_conj ℂ _ z, hz]; norm_num))
  have hprod_sdiff : ∀ T : Finset (Fin m),
      (∏ k : Fin m, v k) * ∏ i ∈ T, starRingEnd ℂ (v i) = ∏ k ∈ Finset.univ \ T, v k := by
    intro T
    simp_rw [hconj_inv _ (hv _), Finset.prod_inv_distrib]
    rw [show (∏ k : Fin m, v k) = (∏ k ∈ Finset.univ \ T, v k) * ∏ k ∈ T, v k from
      (Finset.prod_sdiff (Finset.subset_univ T)).symm, mul_assoc,
      mul_inv_cancel₀ (Finset.prod_ne_zero_iff.mpr (fun k _ =>
        norm_ne_zero_iff.mp (by rw [hv k]; exact one_ne_zero))), mul_one]
  have hrearrange : ∀ S : Finset (Fin m),
      (∏ k : Fin m, v k) *
        (leeYangPoly B (Finset.univ \ S) *
          ((∏ x ∈ S, starRingEnd ℂ (a x)) *
            ∏ x ∈ S, (starRingEnd ℂ) (v x))) =
      leeYangPoly B (Finset.univ \ S) * (∏ x ∈ S, starRingEnd ℂ (a x)) *
        ((∏ k : Fin m, v k) * ∏ x ∈ S, (starRingEnd ℂ) (v x)) := fun S => by ring
  simp_rw [hrearrange, hprod_sdiff]
  let compl_equiv : Finset (Fin m) ≃ Finset (Fin m) :=
    ⟨(Finset.univ \ ·), (Finset.univ \ ·),
      fun S => by simp [sdiff_sdiff_right_self],
      fun S => by simp [sdiff_sdiff_right_self]⟩
  exact (Fintype.sum_equiv compl_equiv _ _ (fun T => by
    simp only [compl_equiv, Equiv.coe_fn_mk, sdiff_sdiff_right_self,
      inf_eq_inter, Finset.univ_inter])).symm


end IsingModel
