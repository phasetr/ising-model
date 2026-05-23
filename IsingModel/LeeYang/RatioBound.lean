import IsingModel.LeeYang.Poly

/-!
# Lee-Yang circle theorem split — iterated ratio bound for the Lee-Yang polynomial

Part of the split Lee-Yang circle-theorem layer (Issue #1850).
-/

namespace IsingModel

open Finset Complex

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

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
If `‖f v‖ ≤ ‖g v‖` on the torus and `g ≠ 0` on the closed polydisk,
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
lemma leeYangPoly_ratio_bound {m : ℕ}
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
      exact Finset.map_injective ⟨Fin.castSucc, Fin.castSucc_injective m⟩ this
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
    -- ‖αfun w‖ ≤ ‖βfun w‖ by approximation (t < 1) + iterated max modulus + limit.
    -- Uses standalone lemmas: torus_identity, one_var_max_ratio, iterated_ratio,
    -- alphaT/betaT (private defs to avoid let-binding heartbeat timeout).
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


end IsingModel
