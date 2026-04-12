import IsingModel.Asano

/-!
# Lee-Yang circle theorem

The Lee-Yang circle theorem states that the Ising partition polynomial does not
vanish on the open unit polydisk. We follow the Harcos/Ruelle approach, which uses
an n×n Hermitian matrix formulation, induction on n, and the maximum modulus principle.

## Main results

* `leeYangPoly_nonvanishing` — for Hermitian `A` with `|a_{ij}| ≤ 1`,
  `f_A(z) ≠ 0` on `|z_k| < 1`.
* `lee_yang_circle` — the Ising partition polynomial does not vanish on the open
  unit polydisk.

## References

* Harcos, "The Lee-Yang Circle Theorem" (based on Ruelle, Ann. of Math. 171, 2010)
* Friedli–Velenik, §3.7, pp. 122–127
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
private lemma hermitian_conj_entry {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
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
private lemma leeYangPoly_coeff_notin {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
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
private lemma leeYangPoly_coeff_in {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
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
private lemma torus_identity {m : ℕ}
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

/-- The scaled α-polynomial for the approximation argument.
`alphaT B a t` is the multilinear polynomial with coefficients
`leeYangPoly B T * ∏_{j∉T} conj(t * a_j)`. At `t = 1` this recovers the
α-coefficient of the Lee-Yang decomposition. -/
private noncomputable def alphaT {m : ℕ}
    (B : Matrix (Fin m) (Fin m) ℂ) (a : Fin m → ℂ) (t : ℂ) :
    MultilinPoly (Fin m) :=
  fun T => leeYangPoly B T * ∏ j ∈ Finset.univ \ T, starRingEnd ℂ (t * a j)

/-- The scaled β-evaluation for the approximation argument.
`betaT B a t v = (leeYangPoly B).eval (fun k => t * a_k * v_k)`. -/
private noncomputable def betaT {m : ℕ}
    (B : Matrix (Fin m) (Fin m) ℂ) (a : Fin m → ℂ) (t : ℂ) :
    (Fin m → ℂ) → ℂ :=
  fun v => (leeYangPoly B).eval (fun k => t * a k * v k)

/-- Single-variable max modulus for a ratio `f/g` where `g ≠ 0` on `closedBall 0 1`.
Given globally differentiable `f` and `g`, if `‖f(update v k t)‖ ≤ ‖g(update v k t)‖`
for `‖t‖ = 1`, then `‖f v‖ ≤ ‖g v‖` when `‖v k‖ < 1`. -/
private lemma one_var_max_ratio {m : ℕ}
    (f g : (Fin m → ℂ) → ℂ) (v : Fin m → ℂ) (k : Fin m)
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hgne : ∀ z : ℂ, ‖z‖ ≤ 1 → g (Function.update v k z) ≠ 0)
    (hk : ‖v k‖ < 1)
    (hbd : ∀ t : ℂ, ‖t‖ = 1 →
      ‖f (Function.update v k t)‖ ≤ ‖g (Function.update v k t)‖) :
    ‖f v‖ ≤ ‖g v‖ := by
  have hgv : g v ≠ 0 := by
    have h := hgne (v k) (hk.le)
    rwa [Function.update_eq_self] at h
  rw [← div_le_one (norm_pos_iff.mpr hgv), ← norm_div]
  have hupd : Differentiable ℂ (fun z : ℂ => Function.update v k z) := by
    rw [show (fun z => Function.update v k z) =
        (fun z i => if i = k then z else v i) from by
      ext z i; simp [Function.update, eq_comm]]
    rw [differentiable_pi]; intro i
    split_ifs <;> [exact differentiable_id; exact differentiable_const _]
  have hfd := hf.comp hupd
  have hgd := hg.comp hupd
  let r : ℂ → ℂ := fun z => f (Function.update v k z) / g (Function.update v k z)
  have hdc : DiffContOnCl ℂ r (Metric.ball 0 1) :=
    ⟨hfd.differentiableOn.div hgd.differentiableOn
      (fun z hz => hgne z (by simpa [dist_zero_right] using (Metric.mem_ball.mp hz).le)),
     by rw [closure_ball (0 : ℂ) one_ne_zero]
        exact hfd.continuous.continuousOn.div hgd.continuous.continuousOn
          (fun z hz => hgne z (by rwa [Metric.mem_closedBall, dist_zero_right] at hz))⟩
  have h := Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hdc
    (fun z hz => by
      rw [frontier_ball (0 : ℂ) one_ne_zero, Metric.mem_sphere, dist_zero_right] at hz
      change ‖r z‖ ≤ 1; simp only [r, norm_div]
      exact (div_le_one (norm_pos_iff.mpr (hgne z (le_of_eq hz)))).mpr (hbd z hz))
    (subset_closure (Metric.mem_ball.mpr (by rwa [dist_zero_right])))
  rwa [show r (v k) = f v / g v from by simp [r]] at h

/-- Iterated max modulus for a ratio of globally differentiable functions.
If `‖f v‖ ≤ ‖g v��` on the torus and `g ≠ 0` on the closed polydisk,
then `‖f w‖ ≤ ‖g w‖` inside the open polydisk. -/
private lemma iterated_ratio {m : ℕ}
    (f g : (Fin m → ℂ) → ℂ)
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hgne : ∀ u : Fin m → ℂ, (∀ j, ‖u j‖ ≤ 1) → g u ≠ 0)
    (htorus : ∀ v : Fin m → ℂ, (∀ k, ‖v k‖ = 1) → ‖f v‖ ≤ ‖g v‖)
    (w : Fin m → ℂ) (hw : ∀ k, ‖w k‖ < 1) :
    ‖f w‖ ≤ ‖g w‖ := by
  -- Induction: move variables one at a time from the torus to the interior.
  -- T tracks which variables are at w (inside the disk); others are on the torus.
  suffices h : ∀ (T : Finset (Fin m)) (v : Fin m → ℂ),
      (∀ k ∉ T, ‖v k‖ = 1) → (∀ k ∈ T, v k = w k) → ‖f v‖ ≤ ‖g v‖ from
    h Finset.univ w (fun k hk => absurd (Finset.mem_univ k) hk) (fun _ _ => rfl)
  intro T
  induction T using Finset.induction_on with
  | empty => intro v hv _; exact htorus v (fun k => hv k (by simp))
  | @insert k₀ T' hk₀ ihT =>
    intro v hv_out hv_in
    -- All components of v have norm ≤ 1
    have hv_le : ∀ j, ‖v j‖ ≤ 1 := fun j => by
      by_cases hj : j ∈ insert k₀ T'
      · exact hv_in j hj ▸ (hw j).le
      · exact le_of_eq (hv_out j hj)
    -- g(update v k₀ z) ≠ 0 for ‖z‖ ≤ 1
    have hgne' : ∀ z : ℂ, ‖z‖ ≤ 1 → g (Function.update v k₀ z) ≠ 0 := by
      intro z hz; apply hgne; intro j; by_cases hjk : j = k₀
      · subst hjk; simp only [Function.update_self]; exact hz
      · rw [Function.update_of_ne hjk]; exact hv_le j
    apply one_var_max_ratio f g v k₀ hf hg hgne'
      (hv_in k₀ (Finset.mem_insert_self _ _) ▸ hw k₀)
    intro t ht
    apply ihT (Function.update v k₀ t)
    · intro k hk; by_cases hkk : k = k₀
      · subst hkk; simp only [Function.update_self]; exact ht
      · rw [Function.update_of_ne hkk]; exact hv_out k (by
          rw [Finset.mem_insert]; push Not; exact ⟨hkk, hk⟩)
    · intro k hk
      have hkk : k ≠ k₀ := ne_of_mem_of_not_mem hk hk₀
      rw [Function.update_of_ne hkk]; exact hv_in k (Finset.mem_insert_of_mem hk)

set_option maxHeartbeats 800000 in
-- Iterated DiffContOnCl + approximation argument requires extra heartbeats
/-- The ratio of the `z_last`-coefficient to the constant term in the Lee-Yang polynomial
is bounded by 1, by the maximum modulus principle.

Specifically, in `f_A(z) = β + z_last · α` where
`β = f_B(a·z)` and `α = Σ_{S : last ∈ S} coeff(S) · ∏_{k∈S\{last}} z_k`,
we have `‖α‖ ≤ ‖β‖` for `|z_k| < 1`.

Proof sketch (Harcos/Ruelle):
1. When `|a_{k,n}| < 1` (strictly), `β ≠ 0` on the closed polydisk
   (by induction, since `|a_k · z_k| ≤ |a_k| < 1`).
2. The ratio `g = α/β` is holomorphic on the closed polydisk.
3. On the torus `|z_k| = 1`: by the Hermitian property,
   `α = (∏ z_k) · conj(β)`, so `|α/β| = |∏ z_k| = 1`.
4. By iterated maximum modulus principle
   (`Complex.norm_le_of_forall_mem_frontier_norm_le`):
   `|α/β| ≤ 1` on the open polydisk.
5. Extend to `|a_{k,n}| ≤ 1` by continuity.

Reference: Harcos, based on Ruelle, Ann. of Math. 171 (2010), 589–603. -/
private lemma leeYangPoly_ratio_bound {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (hA : A.IsHermitian) (hbound : ∀ i j, ‖A i j‖ ≤ 1)
    (z : Fin (m + 1) → ℂ) (hz : ∀ k, ‖z k‖ < 1)
    (ih : ∀ (A' : Matrix (Fin m) (Fin m) ℂ), A'.IsHermitian →
      (∀ i j, ‖A' i j‖ ≤ 1) → ∀ z', (∀ k, ‖z' k‖ < 1) → (leeYangPoly A').eval z' ≠ 0) :
    ‖∑ S ∈ (Finset.univ : Finset (Finset (Fin (m + 1)))).filter (fun S => Fin.last m ∈ S),
        leeYangPoly A S * ∏ k ∈ S.erase (Fin.last m), z k‖ ≤
    ‖(leeYangPoly (A.submatrix Fin.castSucc Fin.castSucc)).eval
        (fun i => A (Fin.castSucc i) (Fin.last m) * z (Fin.castSucc i))‖ := by
  -- Multilinear eval is differentiable (polynomial → entire)
  have diff_prod : ∀ (S : Finset (Fin m)),
      Differentiable ℂ (fun (w : Fin m → ℂ) => Finset.prod S (fun k => w k)) := by
    intro S; induction S using Finset.induction_on with
    | empty => simp [differentiable_const]
    | insert a s hna ih =>
      have : (fun (w : Fin m → ℂ) => Finset.prod (insert a s) (fun k => w k)) =
          fun w => w a * Finset.prod s (fun k => w k) := by
        ext w; exact Finset.prod_insert hna
      rw [this]; exact (differentiable_apply _).mul ih
  have diff_eval : ∀ (p : MultilinPoly (Fin m)),
      Differentiable ℂ (fun (w : Fin m → ℂ) => p.eval w) := by
    intro p; change Differentiable ℂ (fun w => ∑ S : Finset (Fin m), p S * _)
    have h : (fun (w : Fin m → ℂ) => ∑ S : Finset (Fin m),
        p S * Finset.prod S (fun k => w k)) =
        ∑ S ∈ (Finset.univ : Finset (Finset (Fin m))),
          (fun (w : Fin m → ℂ) => p S * Finset.prod S (fun k => w k)) := by
      ext w; simp [Finset.sum_apply]
    rw [h]; exact Differentiable.sum (fun S _ =>
      (differentiable_const _).mul (diff_prod S))
  set B := A.submatrix Fin.castSucc Fin.castSucc with hB_def
  -- α coefficient reparametrized to Fin m:
  -- p_α(T) = leeYangPoly B T * ∏_{j∉T} A(last)(castSucc j)
  set p_α : MultilinPoly (Fin m) := fun T =>
    leeYangPoly B T * ∏ j ∈ Finset.univ \ T, A (Fin.last m) (Fin.castSucc j) with hp_α_def
  -- Both αfun and βfun are multilinear evals of w, hence differentiable
  set αfun : (Fin m → ℂ) → ℂ := fun w => p_α.eval w with hαfun_def
  set βfun : (Fin m → ℂ) → ℂ := fun w =>
    (leeYangPoly B).eval (fun i => A (Fin.castSucc i) (Fin.last m) * w i) with hβfun_def
  have hα_diff : Differentiable ℂ αfun := diff_eval p_α
  -- βfun(w) = eval of (fun T => leeYangPoly B T) at (fun i => a_i * w_i)
  -- This is a composition of multilinear eval with a linear map, hence differentiable.
  -- The linear map w ↦ (fun i => a_i * w_i) is differentiable (componentwise linear).
  have diff_scaled_prod : ∀ (c : Fin m → ℂ) (S : Finset (Fin m)),
      Differentiable ℂ (fun (w : Fin m → ℂ) => Finset.prod S (fun k => c k * w k)) := by
    intro c S; induction S using Finset.induction_on with
    | empty => simp [differentiable_const]
    | insert a s hna ih =>
      have : (fun (w : Fin m → ℂ) => Finset.prod (insert a s) (fun k => c k * w k)) =
          fun w => (c a * w a) * Finset.prod s (fun k => c k * w k) := by
        ext w; exact Finset.prod_insert hna
      rw [this]; exact ((differentiable_const _).mul (differentiable_apply _)).mul ih
  have hβ_diff : Differentiable ℂ βfun := by
    change Differentiable ℂ (fun w => ∑ S : Finset (Fin m), _)
    have h : (fun (w : Fin m → ℂ) => ∑ S : Finset (Fin m),
        leeYangPoly B S * ∏ k ∈ S, (A (Fin.castSucc k) (Fin.last m) * w k)) =
        ∑ S ∈ (Finset.univ : Finset (Finset (Fin m))),
          (fun (w : Fin m → ℂ) =>
            leeYangPoly B S * ∏ k ∈ S, (A (Fin.castSucc k) (Fin.last m) * w k)) := by
      ext w; simp [Finset.sum_apply]
    rw [h]; exact Differentiable.sum (fun S _ =>
      (differentiable_const _).mul (diff_scaled_prod _ S))
  -- Key identity: the actual α and β equal αfun(w) and βfun(w) at w = z ∘ castSucc
  let w : Fin m → ℂ := fun i => z (Fin.castSucc i)
  -- β(z) = βfun(w) (by definition)
  -- α(z) = αfun(w) requires the bijection S ↔ T (same as hdecomp's second sum)
  -- For now, sorry the identity and the max modulus bound
  have hα_eq : ∑ S ∈ (Finset.univ : Finset (Finset (Fin (m + 1)))).filter
      (fun S => Fin.last m ∈ S), leeYangPoly A S * ∏ k ∈ S.erase (Fin.last m), z k =
      αfun w := by
    symm
    apply Finset.sum_nbij (fun T =>
      insert (Fin.last m) (T.map ⟨Fin.castSucc, Fin.castSucc_injective m⟩))
    · intro T _; simp [Finset.mem_filter, Finset.mem_insert]
    · -- Injective
      intro T₁ _ T₂ _ h
      have h1 : Fin.last m ∉ T₁.map ⟨Fin.castSucc, Fin.castSucc_injective m⟩ := by
        simp [Finset.mem_map, Fin.castSucc_ne_last]
      have h2 : Fin.last m ∉ T₂.map ⟨Fin.castSucc, Fin.castSucc_injective m⟩ := by
        simp [Finset.mem_map, Fin.castSucc_ne_last]
      have := congr_arg (Finset.erase · (Fin.last m)) h
      simp only [Finset.erase_insert h1, Finset.erase_insert h2] at this
      exact (Finset.map_injOn (f := ⟨Fin.castSucc, Fin.castSucc_injective m⟩)
        (Set.injOn_of_injective (Fin.castSucc_injective m))).eq_iff.mp this
    · -- Surjective
      intro S hS
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hS
      refine ⟨(S.erase (Fin.last m)).preimage Fin.castSucc
        (Fin.castSucc_injective m |>.injOn),
        Finset.mem_coe.mpr (Finset.mem_univ _), ?_⟩
      ext j; simp only [Finset.mem_insert, Finset.mem_map, Finset.mem_preimage,
        Finset.mem_erase, ne_eq, Function.Embedding.coeFn_mk]
      constructor
      · rintro (rfl | ⟨k, ⟨_, hk2⟩, rfl⟩)
        · exact hS
        · exact hk2
      · intro hj; by_cases hje : j = Fin.last m
        · left; exact hje
        · right; induction j using Fin.lastCases with
          | last => exact absurd rfl hje
          | cast i => exact ⟨i, ⟨hje, hj⟩, rfl⟩
    · -- Terms match
      intro T _
      rw [leeYangPoly_coeff_in]; congr 1
      rw [Finset.erase_insert (by simp [Finset.mem_map, Fin.castSucc_ne_last])]
      rw [Finset.prod_map]; rfl
  rw [hα_eq]
  -- Now need: ‖αfun w‖ ≤ ‖βfun w‖ where w i = z(castSucc i), ‖w‖ < 1.
  -- Case m = 0: αfun and βfun are constants. αfun = leeYangPoly B ∅ * ∏... = 1,
  -- βfun = (leeYangPoly B).eval ... = 1. So ‖1‖ ≤ ‖1‖. ✓
  -- Case m ≥ 1: apply maximum modulus principle.
  by_cases hm : m = 0
  · -- m = 0: both eval to 1 (Fin 0 is empty, only subset is ∅)
    subst hm
    have hempty : ∀ (S : Finset (Fin 0)), S = ∅ := Finset.eq_empty_of_isEmpty
    have hα1 : αfun w = 1 := by
      change p_α.eval w = 1; unfold MultilinPoly.eval
      rw [Fintype.sum_eq_single ∅ (fun S hS => absurd (hempty S) hS)]
      simp [p_α, leeYangPoly]
    have hβ1 : βfun w = 1 := by
      change (leeYangPoly B).eval _ = 1; unfold MultilinPoly.eval
      rw [Fintype.sum_eq_single ∅ (fun S hS => absurd (hempty S) hS)]
      simp [leeYangPoly]
    change ‖αfun w‖ ≤ ‖βfun w‖; rw [hα1, hβ1]
  · -- m ≥ 1: maximum modulus principle
    have hm_pos : 0 < m := Nat.pos_of_ne_zero hm
    haveI : Nonempty (Fin m) := ⟨⟨0, hm_pos⟩⟩
    haveI : Nontrivial (Fin m → ℂ) := Function.nontrivial
    -- Step 1: β ≠ 0 on closed polydisk (ih, ‖a_k·v_k‖ ≤ ‖a_k‖·‖v_k‖ ≤ 1·1 ≤ 1,
    -- with strict < 1 because ‖v_k‖ ≤ 1 and we need one factor < 1).
    -- For the closed ball, we need ‖a_k‖ < 1 (strict). Use approximation t·A.
    -- Step 2: DiffContOnCl for αfun/βfun (both differentiable, β ≠ 0 on closure).
    -- Step 3: On torus |v_k| = 1: α(v) = (∏v_k)·conj(β(v)) by Hermitian.
    -- Step 4: max modulus → ‖α/β‖ ≤ 1.
    -- Step 5: t → 1 continuity gives ‖α‖ ≤ ‖β‖ for |a_k| ≤ 1.
    -- 1-variable max modulus step: for each variable v_k, replace it by a
    -- value on the unit circle without increasing ‖g‖.
    have one_var_max : ∀ (g : (Fin m → ℂ) → ℂ) (v : Fin m → ℂ) (k : Fin m),
        Differentiable ℂ g → ‖v k‖ < 1 →
        (∀ t : ℂ, ‖t‖ = 1 → ‖g (Function.update v k t)‖ ≤ 1) →
        ‖g v‖ ≤ 1 := by
      intro g v k hg hk hbd
      let f : ℂ → ℂ := fun t => g (Function.update v k t)
      have hupd : Differentiable ℂ (fun t : ℂ => Function.update v k t) := by
        rw [show (fun t => Function.update v k t) =
            (fun t i => if i = k then t else v i) from by
          ext t i; simp [Function.update, eq_comm]]
        rw [differentiable_pi]
        intro i; split_ifs <;> [exact differentiable_id; exact differentiable_const _]
      have hf_diff : Differentiable ℂ f := hg.comp hupd
      have h := Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball
        ⟨hf_diff.differentiableOn, hf_diff.continuous.continuousOn⟩
        (fun z hz => by
          rw [frontier_ball (0 : ℂ) one_ne_zero] at hz
          exact hbd z (by simpa [dist_zero_right] using hz))
        (subset_closure (Metric.mem_ball.mpr (by rwa [dist_zero_right])))
      rwa [show f (v k) = g v from by simp [f]] at h
    -- Torus identity: on |v_k| = 1, αfun(v) = (∏v_k)·conj(βfun(v))
    -- Hence |αfun/βfun| = |∏v_k| = 1 on the torus.
    -- This follows from leeYangPoly_conj_eq_compl + Hermitian structure.
    have torus_bound : ∀ v : Fin m → ℂ, (∀ k, ‖v k‖ = 1) → ‖αfun v‖ = ‖βfun v‖ := by
      intro v hv
      -- Key identity: αfun(v) = (∏ v_k) · conj(βfun(v))
      -- Then ‖αfun v‖ = |∏v_k| · ‖βfun v‖ = 1 · ‖βfun v‖.
      suffices hid : αfun v = (∏ k : Fin m, v k) * starRingEnd ℂ (βfun v) by
        rw [hid, norm_mul, Complex.norm_prod]
        simp only [hv, Finset.prod_const_one, one_mul]
        rw [RCLike.norm_conj]
      -- Helper: conj(z) = z⁻¹ when ‖z‖ = 1
      have hconj_inv : ∀ z : ℂ, ‖z‖ = 1 → starRingEnd ℂ z = z⁻¹ := fun z hz =>
        eq_comm.mp (inv_eq_of_mul_eq_one_right (by rw [@RCLike.mul_conj ℂ _ z, hz]; norm_num))
      -- Helper: (∏v) · ∏_{T} conj(v) = ∏_{univ\T} v
      have hprod_sdiff : ∀ T : Finset (Fin m),
          (∏ k : Fin m, v k) * ∏ i ∈ T, starRingEnd ℂ (v i) = ∏ k ∈ Finset.univ \ T, v k := by
        intro T
        simp_rw [hconj_inv _ (hv _), Finset.prod_inv_distrib]
        rw [show (∏ k : Fin m, v k) = (∏ k ∈ Finset.univ \ T, v k) * ∏ k ∈ T, v k from
          (Finset.prod_sdiff (Finset.subset_univ T)).symm, mul_assoc,
          mul_inv_cancel₀ (Finset.prod_ne_zero_iff.mpr (fun k _ =>
            norm_ne_zero_iff.mp (by rw [hv k]; exact one_ne_zero))), mul_one]
      -- Unfold set definitions and distribute conj
      rw [hαfun_def, hβfun_def]; unfold MultilinPoly.eval
      simp only [map_sum, map_mul, map_prod, Finset.mul_sum,
        leeYangPoly_conj_eq_compl B (hA.submatrix Fin.castSucc)]
      -- Now RHS has ∏ conj(a·v). Distribute: conj(a·v) = conj(a)·conj(v)
      -- and conj(a) = A(last)(cs) by Hermitian
      -- conj(a)·conj(v) already distributed by simp. Use Hermitian, split products.
      simp_rw [hermitian_conj_entry A hA, Finset.prod_mul_distrib]
      -- Rearrange: move (∏ v) next to ∏ conj(v) and apply hprod_sdiff
      have hrearrange : ∀ S : Finset (Fin m),
          (∏ k : Fin m, v k) *
            (leeYangPoly B (Finset.univ \ S) *
              ((∏ x ∈ S, A (Fin.last m) (Fin.castSucc x)) *
                ∏ x ∈ S, (starRingEnd ℂ) (v x))) =
          leeYangPoly B (Finset.univ \ S) * (∏ x ∈ S, A (Fin.last m) (Fin.castSucc x)) *
            ((∏ k : Fin m, v k) * ∏ x ∈ S, (starRingEnd ℂ) (v x)) := fun S => by ring
      simp_rw [hrearrange, hprod_sdiff]
      -- Expand p_α, then reindex RHS by complement
      simp_rw [hp_α_def]
      let compl_equiv : Finset (Fin m) ≃ Finset (Fin m) :=
        ⟨(Finset.univ \ ·), (Finset.univ \ ·),
          fun S => by simp [sdiff_sdiff_right_self],
          fun S => by simp [sdiff_sdiff_right_self]⟩
      exact (Fintype.sum_equiv compl_equiv _ _ (fun T => by
        simp only [compl_equiv, Equiv.coe_fn_mk, sdiff_sdiff_right_self,
          inf_eq_inter, Finset.univ_inter])).symm
    -- Iterated max modulus: for Differentiable g with ‖g v‖ ≤ 1 on torus,
    -- one_var_max gives ‖g v‖ ≤ 1 for all v with ‖v_k‖ ≤ 1.
    -- We apply this to g = αfun/βfun in the strict case, then continuity.
    -- For now, sorry the combined argument (torus_bound is the key input).
    -- ‖αfun w‖ ≤ ‖βfun w‖ by approximation + iterated max modulus.
    -- Scale last column by t < 1, then β_t ≠ 0 on closed polydisk.
    -- Torus identity gives ‖α_t‖ = ‖β_t‖ on the torus.
    -- Iterated max modulus via DiffContOnCl gives ‖α_t w‖ ≤ ‖β_t w‖.
    -- Pass to the limit t → 1.
    change ‖αfun w‖ ≤ ‖βfun w‖
    -- Use alphaT / betaT (private defs) to avoid whnf timeout on let bindings
    let a : Fin m → ℂ := fun k => A (Fin.castSucc k) (Fin.last m)
    -- At t = 1: alphaT/betaT recover αfun/βfun
    have hα1 : (alphaT B a 1).eval w = αfun w := by
      change MultilinPoly.eval _ w = p_α.eval w
      unfold MultilinPoly.eval; congr 1; ext T
      simp only [alphaT, hp_α_def, one_mul]
      simp_rw [show ∀ x : Fin m, a x = A (Fin.castSucc x) (Fin.last m) from fun _ => rfl,
        hermitian_conj_entry A hA]
    have hβ1 : betaT B a 1 w = βfun w := by
      change (leeYangPoly B).eval _ = (leeYangPoly B).eval _
      congr 1; ext k
      change (↑(1 : ℝ) * a k) * w k = A (Fin.castSucc k) (Fin.last m) * w k
      rw [Complex.ofReal_one, one_mul]
    -- β_t ≠ 0 on the closed polydisk when |t| < 1
    have hβt_ne : ∀ (t : ℝ), |t| < 1 → ∀ u : Fin m → ℂ,
        (∀ j, ‖u j‖ ≤ 1) → betaT B a (↑t) u ≠ 0 := by
      intro t ht u hu
      apply ih B (hA.submatrix Fin.castSucc) (fun i j => hbound _ _)
      intro k; show ‖(↑t * a k) * u k‖ < 1
      calc ‖(↑t * a k) * u k‖
          = ‖(↑t : ℂ)‖ * ‖a k‖ * ‖u k‖ := by rw [norm_mul, norm_mul]
        _ ≤ |t| * 1 * 1 := by
            rw [Complex.norm_real]
            exact mul_le_mul (mul_le_mul_of_nonneg_left (hbound _ _) (abs_nonneg t))
              (hu k) (norm_nonneg _) (by positivity)
        _ < 1 := by linarith
    -- For 0 ≤ t < 1: ‖αt‖ ≤ ‖βt‖ via iterated_ratio
    have hle_t : ∀ (t : ℝ), 0 ≤ t → t < 1 →
        ‖(alphaT B a (↑t)).eval w‖ ≤ ‖betaT B a (↑t) w‖ := by
      intro t ht0 ht1
      -- Torus norm equality for t-scaled
      have htorus : ∀ v : Fin m → ℂ, (∀ k, ‖v k‖ = 1) →
          ‖(alphaT B a (↑t)).eval v‖ ≤ ‖betaT B a (↑t) v‖ := by
        intro v hv
        have hid := torus_identity B (hA.submatrix Fin.castSucc)
          (fun k => (↑t : ℂ) * a k) v hv
        rw [show (fun k => (↑t * a k) * v k) = (fun k => ↑t * a k * v k)
          from by ext; ring] at hid
        apply le_of_eq; unfold alphaT betaT
        rw [show (fun i => (↑t * a i) * v i) = (fun i => ↑t * a i * v i)
          from by ext; ring] at hid
        rw [hid, norm_mul, Complex.norm_prod]
        simp only [hv, Finset.prod_const_one, one_mul, RCLike.norm_conj]
      -- βt differentiable (via diff_scaled_prod)
      have hβt_diff : Differentiable ℂ (betaT B a (↑t)) := by
        unfold betaT; exact (diff_eval (leeYangPoly B)).comp
          (differentiable_pi.mpr (fun k =>
            (differentiable_const ((↑t : ℂ) * a k)).mul (differentiable_apply k)))
      exact iterated_ratio ((alphaT B a (↑t)).eval) (betaT B a (↑t))
        (diff_eval _) hβt_diff
        (hβt_ne t (by rwa [abs_of_nonneg ht0]))
        htorus w (fun k => hz (Fin.castSucc k))
    -- Pass to the limit t → 1: both sides are continuous in t
    rw [← hα1, ← hβ1]
    -- Both sides are continuous in t (polynomial expressions), so the bound
    -- extends from [0,1) to t=1 via closure of the sub-level set.
    have hα_cont : Continuous (fun t : ℝ => (alphaT B a ↑t).eval w) := by
      unfold alphaT MultilinPoly.eval
      apply continuous_finset_sum; intro T _
      apply Continuous.mul
      · apply Continuous.mul
        · exact continuous_const
        · apply continuous_finset_prod; intro j _
          exact RCLike.continuous_conj.comp
            (Complex.continuous_ofReal.mul continuous_const)
      · exact continuous_const
    have hβ_cont : Continuous (fun t : ℝ => betaT B a ↑t w) := by
      unfold betaT MultilinPoly.eval
      apply continuous_finset_sum; intro S _
      apply Continuous.mul
      · exact continuous_const
      · apply continuous_finset_prod; intro k _
        exact (Complex.continuous_ofReal.mul continuous_const).mul continuous_const
    exact (isClosed_le (continuous_norm.comp hα_cont) (continuous_norm.comp hβ_cont)).closure_subset
      (closure_mono (fun t (ht : t ∈ Set.Ico 0 1) => hle_t t ht.1 ht.2)
        (by rw [closure_Ico (show (0 : ℝ) ≠ 1 from one_ne_zero.symm)]
            exact Set.right_mem_Icc.mpr zero_le_one))

/-- **Harcos/Ruelle theorem**: For an `n × n` Hermitian matrix `A` with `|a_{ij}| ≤ 1`,
the Lee-Yang polynomial `f_A` does not vanish on the open unit polydisk.

Proof by induction on `n`:
- `n = 0`: `f_A = 1 ≠ 0`
- `n + 1`: Separate the last variable. Using `a_{ji} = conj(a_{ij})`, decompose
  `f_A(z) = f_B(a·z) + (∏z_k) · conj(f_B(a/conj(z)))`.
  First term ≠ 0 by induction. Ratio of second/first has modulus ≤ 1 by the
  maximum modulus principle (on |z_k| = 1, the ratio is exactly 1).

Reference: Harcos, "The Lee-Yang Circle Theorem",
  based on Ruelle, Ann. of Math. 171 (2010), 589–603. -/
theorem leeYangPoly_nonvanishing {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian)
    (hbound : ∀ i j, ‖A i j‖ ≤ 1)
    (z : Fin n → ℂ) (hz : ∀ k, ‖z k‖ < 1) :
    (leeYangPoly A).eval z ≠ 0 := by
  induction n with
  | zero =>
    -- f_A(z) = 1 ≠ 0 (Fin 0 is empty, only subset is ∅, all products are empty = 1)
    unfold MultilinPoly.eval leeYangPoly
    rw [Fintype.sum_eq_single (∅ : Finset (Fin 0)) (fun S hS => by
      exfalso; exact hS (Finset.eq_empty_of_isEmpty S))]
    simp
  | succ m ih =>
    -- Let B = upper m×m block of A, last = Fin.last m, aᵢ = A i last
    let B : Matrix (Fin m) (Fin m) ℂ := A.submatrix Fin.castSucc Fin.castSucc
    -- B is Hermitian since A is
    have hB : B.IsHermitian := hA.submatrix Fin.castSucc
    -- |B i j| ≤ 1
    have hBbound : ∀ i j, ‖B i j‖ ≤ 1 := fun i j => hbound _ _
    -- Key decomposition (Harcos):
    -- f_A(z) = f_B(a_{0,n}·z_0,...,a_{m-1,n}·z_{m-1})
    --        + (z_0···z_n) · conj(f_B(a_{0,n}/conj(z_0),...))
    -- where aᵢ = A (Fin.castSucc i) (Fin.last m)
    -- First term ≠ 0 by ih (since |aᵢ·zᵢ| ≤ |aᵢ|·|zᵢ| < 1)
    have h_first_nonzero : (leeYangPoly B).eval
        (fun i => A (Fin.castSucc i) (Fin.last m) * z (Fin.castSucc i)) ≠ 0 := by
      apply ih B hB hBbound
      intro k
      calc ‖A (Fin.castSucc k) (Fin.last m) * z (Fin.castSucc k)‖
          = ‖A (Fin.castSucc k) (Fin.last m)‖ * ‖z (Fin.castSucc k)‖ := norm_mul _ _
        _ ≤ 1 * ‖z (Fin.castSucc k)‖ := by
            exact mul_le_mul_of_nonneg_right (hbound _ _) (norm_nonneg _)
        _ < 1 := by linarith [hz (Fin.castSucc k)]
    -- f_A is linear in z_last: f_A(z) = β + z_last · α
    -- where β = firstTerm = f_B(a·z) and α is the z_last coefficient.
    let β := (leeYangPoly B).eval
        (fun i => A (Fin.castSucc i) (Fin.last m) * z (Fin.castSucc i))
    -- α = ∑_{S : last ∈ S} coeff(S) · ∏_{k ∈ S \ {last}} z_k
    let α := ∑ S ∈ (Finset.univ : Finset (Finset (Fin (m + 1)))).filter
        (fun S => Fin.last m ∈ S),
        leeYangPoly A S * ∏ k ∈ S.erase (Fin.last m), z k
    -- Step 1: eval = β + z_last · α (sum splitting + factoring z_last from monomial)
    have hdecomp : (leeYangPoly A).eval z = β + z (Fin.last m) * α := by
      -- Split ∑_S into ∑_{last∉S} + ∑_{last∈S}, factor z_last from the second sum
      change (∑ S : Finset (Fin (m + 1)), leeYangPoly A S * ∏ k ∈ S, z k) = β + _
      rw [show (∑ S : Finset (Fin (m + 1)), leeYangPoly A S * ∏ k ∈ S, z k) =
        ∑ S ∈ Finset.univ.filter (fun S => Fin.last m ∈ S),
          leeYangPoly A S * ∏ k ∈ S, z k +
        ∑ S ∈ Finset.univ.filter (fun S => Fin.last m ∉ S),
          leeYangPoly A S * ∏ k ∈ S, z k from
        (Finset.sum_filter_add_sum_filter_not _ _ _).symm]
      rw [add_comm]; congr 1
      · -- Σ_{last∉S} = β (bijection with Finset (Fin m))
        symm
        apply Finset.sum_nbij (fun T =>
          T.map ⟨Fin.castSucc, Fin.castSucc_injective m⟩)
        · intro T _
          simp [Finset.mem_filter, Finset.mem_map, Fin.castSucc_ne_last]
        · intro T₁ _ T₂ _ h
          exact Finset.map_injective ⟨Fin.castSucc, Fin.castSucc_injective m⟩ h
        · intro S hS
          rw [Set.mem_image]
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hS
          refine ⟨S.preimage Fin.castSucc
            (Fin.castSucc_injective m |>.injOn),
            Finset.mem_coe.mpr (Finset.mem_univ _), ?_⟩
          ext j; simp only [Finset.mem_map, Finset.mem_preimage,
            Function.Embedding.coeFn_mk]
          constructor
          · rintro ⟨k, hk, rfl⟩; exact hk
          · intro hj
            induction j using Fin.lastCases with
            | last => exact absurd hj hS
            | cast i => exact ⟨i, hj, rfl⟩
        · intro T _; exact (leeYangPoly_coeff_notin A T z).symm
      · -- Σ_{last∈S} factor: ∏_{k∈S} z_k = z_last * ∏_{k∈S\{last}} z_k
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro S hS
        rw [Finset.mem_filter] at hS
        rw [← Finset.mul_prod_erase S z hS.2]
        ring
    -- Step 2: ‖α‖ ≤ ‖β‖ (maximum modulus principle + Hermitian structure)
    -- On |z_k| = 1: α = (∏_{k<m} z_k) · conj(β), so |α| = |β|.
    -- By max modulus (iterated 1-variable): |α/β| ≤ 1 on |z_k| < 1.
    -- Uses: when |a_{k,n}| < 1, β ≠ 0 on closed polydisk (ih), so α/β holomorphic.
    -- Extends to |a_{k,n}| ≤ 1 by continuity.
    have hbound : ‖α‖ ≤ ‖β‖ :=
      leeYangPoly_ratio_bound A hA hbound z hz ih
    -- Step 3: Conclude f_A ≠ 0
    rw [hdecomp]
    intro h
    -- β + z_last · α = 0 → β = -(z_last · α)
    -- |β| = |z_last| · |α| ≤ |z_last| · |β|
    -- If β ≠ 0: 1 ≤ |z_last| < 1, contradiction.
    have hβ : β ≠ 0 := h_first_nonzero
    have : ‖β‖ ≤ ‖z (Fin.last m)‖ * ‖β‖ := by
      have heq : β = -(z (Fin.last m) * α) := by linear_combination h
      calc ‖β‖ = ‖z (Fin.last m) * α‖ := by rw [heq, norm_neg]
        _ = ‖z (Fin.last m)‖ * ‖α‖ := norm_mul _ _
        _ ≤ ‖z (Fin.last m)‖ * ‖β‖ := by
            exact mul_le_mul_of_nonneg_left hbound (norm_nonneg _)
    have hβ_pos : 0 < ‖β‖ := norm_pos_iff.mpr hβ
    have : 1 ≤ ‖z (Fin.last m)‖ := by
      by_contra h
      push Not at h
      linarith [mul_lt_of_lt_one_left hβ_pos h]
    linarith [hz (Fin.last m)]

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
