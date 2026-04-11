/-
Scratch file: test the Harcos decomposition identity for leeYangPoly.
This is completely separate from the main codebase.

Goal: For A : Matrix (Fin (m+1)) (Fin (m+1)) ℂ with A Hermitian,
show f_A(z) = f_B(a·z) + (∏z) · conj(f_B(a/conj(z)))
where B is the upper m×m block and aᵢ = A (castSucc i) (last m).
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian

open Finset Complex

variable {m : ℕ}

/-- The Lee-Yang polynomial for an n×n matrix. -/
noncomputable def leeYangPoly {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    Finset (Fin n) → ℂ :=
  fun S => ∏ i ∈ S, ∏ j ∈ Finset.univ \ S, A i j

/-- Evaluate: f_A(z) = Σ_S coeff(S) · ∏_{k∈S} z_k -/
noncomputable def leeYangEval {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (z : Fin n → ℂ) : ℂ :=
  ∑ S : Finset (Fin n), leeYangPoly A S * ∏ k ∈ S, z k

-- Test: for n=0, f_A = 1
example (A : Matrix (Fin 0) (Fin 0) ℂ) : leeYangEval A (Fin.elim0) = 1 := by
  unfold leeYangEval leeYangPoly
  rw [Fintype.sum_eq_single (∅ : Finset (Fin 0)) (fun S hS => by
    exfalso; exact hS (Finset.eq_empty_of_isEmpty S))]
  simp

-- Now the decomposition. Let's define the pieces.
variable (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
variable (hA : A.IsHermitian)
variable (z : Fin (m + 1) → ℂ)

/-- The upper m×m block -/
noncomputable def B : Matrix (Fin m) (Fin m) ℂ := A.submatrix Fin.castSucc Fin.castSucc

/-- The coupling: aᵢ = A (castSucc i) (last m) -/
noncomputable def avec (i : Fin m) : ℂ := A (Fin.castSucc i) (Fin.last m)

/-- First term: f_B evaluated at (aᵢ · zᵢ) -/
noncomputable def firstTerm : ℂ :=
  leeYangEval (B A) (fun i => avec A i * z (Fin.castSucc i))

/-- Second term: (∏ z_k) · conj(f_B(aᵢ/conj(zᵢ))) -/
noncomputable def secondTerm : ℂ :=
  (∏ k : Fin (m + 1), z k) *
    starRingEnd ℂ (leeYangEval (B A) (fun i => avec A i / starRingEnd ℂ (z (Fin.castSucc i))))

-- The decomposition identity to prove:
-- leeYangEval A z = firstTerm A z + secondTerm A hA z

-- Let's first understand what leeYangEval A z looks like when we split by Fin.last m ∈ S.
-- S ⊂ Fin (m+1). Either Fin.last m ∈ S or not.

-- For S with last ∉ S: S ⊂ Fin m (embedded via castSucc).
-- coeff(S) = ∏_{i∈S, j∉S} A i j
-- where j ranges over (Fin.univ \ S) which includes Fin.last m.
-- So coeff(S) = (∏_{i∈S, j∈Fin.univ\S, j≠last} A i j) · (∏_{i∈S} A i last)
-- The first part is the B-coefficient of S (restricted to Fin m indices).
-- The second part is ∏_{i∈S} aᵢ.

-- For S with last ∈ S: S = T ∪ {last} for T ⊂ Fin m (embedded).
-- coeff(S) = ∏_{i∈T∪{last}, j∈Fin.univ\(T∪{last})} A i j
-- = (∏_{i∈T, j∈Fin m\T} A(castSucc i)(castSucc j)) · (∏_{j∈Fin m\T} A(last)(castSucc j))
--   · (∏_{i∈T} A(castSucc i)(castSucc ... wait the complement doesn't include last)
-- This is getting complex. Let me just try to prove it.

-- Actually, let me try a simpler approach: just verify the identity computationally for m=1.

-- For m=1 (so n=2), A is 2×2:
-- f_A(z0, z1) = A 0 1 · A 1 0 · 1  (S=∅... wait no)
-- Actually wait. leeYangPoly A S = ∏_{i∈S} ∏_{j∉S} A i j
-- For S=∅: empty product = 1. Monomial = 1.
-- For S={0}: ∏_{i∈{0}} ∏_{j∈{1}} A i j = A 0 1. Monomial = z 0.
-- For S={1}: ∏_{i∈{1}} ∏_{j∈{0}} A i j = A 1 0. Monomial = z 1.
-- For S={0,1}: ∏_{i∈{0,1}} ∏_{j∈∅} A i j = 1. Monomial = z 0 · z 1.
-- So f_A(z0,z1) = 1 + A01·z0 + A10·z1 + z0·z1.

-- The Harcos decomposition with last = 1:
-- B = (A 0 0) = 1×1 matrix, avec = A 0 1
-- f_B(w) = Σ_{S⊂{0}} ... For S=∅: 1. For S={0}: w. So f_B(w) = 1 + w.
-- firstTerm = f_B(A01·z0) = 1 + A01·z0
-- secondTerm = z0·z1 · conj(f_B(A01/conj(z0))) = z0·z1 · conj(1 + A01/conj(z0))
--            = z0·z1 · (1 + conj(A01)·z0) [since conj(1/conj(z0)) = z0 when simplified... hmm]
-- Wait: conj(A01/conj(z0)) = conj(A01) / conj(conj(z0)) = conj(A01) / z0 = A10 / z0
-- (using Hermitian: conj(A01) = A10)
-- So secondTerm = z0·z1 · (1 + A10/z0) = z0·z1 + A10·z1 = z1·(z0 + A10)

-- firstTerm + secondTerm = (1 + A01·z0) + z1·(z0 + A10)
--                        = 1 + A01·z0 + z0·z1 + A10·z1
-- This matches f_A! ✓

-- Great, the identity works for m=1. Now let me try to prove it in general.

-- The key Finset operation: split ∑_{S : Finset (Fin (m+1))} into
-- ∑_{S : last ∉ S} + ∑_{S : last ∈ S}

-- Let's try the splitting first.
-- Key experiment: split sum by Fin.last m ∈ S
-- This is the first step of the Harcos decomposition.
noncomputable example (f : Finset (Fin (m + 1)) → ℂ) :
    ∑ S : Finset (Fin (m + 1)), f S =
    ∑ S ∈ (Finset.univ : Finset (Finset (Fin (m + 1)))).filter (fun S => Fin.last m ∉ S), f S +
    ∑ S ∈ (Finset.univ : Finset (Finset (Fin (m + 1)))).filter (fun S => Fin.last m ∈ S), f S := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun S => Fin.last m ∈ S)]
  ring

-- Now: can we biject {S : Fin.last ∉ S} with Finset (Fin m)?
-- A subset S of Fin (m+1) not containing last is essentially a subset of Fin m.
-- The bijection: S ↦ S.map Fin.castSucc.toEmbedding (embed Fin m → Fin (m+1))
-- or rather S ↦ S.preimage Fin.castSucc (injective)

-- Let's try the "image under castSucc" approach:
-- Given T : Finset (Fin m), map to T.map ⟨Fin.castSucc, Fin.castSucc_injective m⟩
-- This gives a Finset (Fin (m+1)) not containing Fin.last m.

-- And conversely: given S not containing last, S.preimage castSucc (or S.map Fin.castSucc⁻¹)

-- Test: the coefficient for S (last ∉ S) relates to B-coefficient.
-- leeYangPoly A S = ∏_{i∈S} ∏_{j∈univ\S} A i j
-- Since last ∉ S: univ \ S includes last.
-- = ∏_{i∈S} (A i last · ∏_{j∈univ\S, j≠last} A i j)
-- = (∏_{i∈S} A i last) · ∏_{i∈S} ∏_{j∈(univ\S)\{last}} A i j
-- The second factor: indices restricted to Fin m via castSucc.
-- = (∏_{i∈S} avec i) · leeYangPoly B (S restricted to Fin m)

-- And the monomial: ∏_{k∈S} z k = ∏_{k∈S} z (castSucc (preimage k))

-- Putting together: for last ∉ S:
-- leeYangPoly A S · ∏_{k∈S} z k
-- = leeYangPoly B (S') · ∏_{i∈S'} (avec i · z (castSucc i))
-- where S' = S restricted to Fin m.
-- This is exactly the firstTerm contribution!

-- For last ∈ S: S = T ∪ {last} for T not containing last.
-- leeYangPoly A S = ∏_{i∈T∪{last}} ∏_{j∈univ\(T∪{last})} A i j
-- univ \ (T ∪ {last}) = (univ \ T) \ {last} = {j ∈ Fin m | j ∉ T} (embedded)
-- So the product splits into:
-- (∏_{i∈T} ∏_{j∈Fin m\T} A(castSucc i)(castSucc j)) · (∏_{j∈Fin m\T} A(last)(castSucc j))
-- · ... hmm, i also runs over {last}:
-- ∏_{i∈T∪{last}} ... = (∏_{i∈T} ...) · (∏_{j∈compl} A last j)

-- This is getting messy. Let me just try to verify it compiles for m=1 concretely.

-- Actually, let me try a different, more Lean-friendly approach.
-- Instead of the full decomposition, use the fact that for the PROOF,
-- we only need: f_A(z) ≠ 0.
-- We know: f_A(z) = P(z) + Q(z) where P = firstTerm, Q = secondTerm.
-- We know: P ≠ 0.
-- We need: |Q| < |P| (then P + Q ≠ 0).
-- This follows if |Q/P| < 1.

-- The ratio Q/P is a meromorphic function. On |z_k| = 1, it equals 1.
-- By maximum modulus, |Q/P| ≤ 1 on |z_k| ≤ 1.
-- Since |z_k| < 1 (strict) and Q/P is holomorphic (P ≠ 0), |Q/P| < 1...
-- wait, maximum modulus gives ≤, not <. The strict inequality needs more.

-- Actually, the ratio |Q/P| = |∏z_k| · |f_B(a/conj(z))| / |f_B(a·z)|.
-- On |z_k| = 1: a/conj(z_k) = a·z_k (since conj(z_k) = 1/z_k on unit circle).
-- So f_B(a/conj(z)) = f_B(a·z), and |∏z_k| = 1. Ratio = 1.
-- Maximum modulus for |z_k| < 1 gives ratio ≤ 1.
-- If ratio = 1 at some interior point, then by max modulus it's constant = 1
-- everywhere, but that contradicts |∏z_k| < 1 at the interior point.
-- So ratio < 1. Hence |Q| < |P|, so P + Q ≠ 0. ✓

-- The proof doesn't need the FULL algebraic identity. It only needs:
-- 1. A way to express Q/P
-- 2. Q/P is holomorphic on the open polydisk (when P ≠ 0)
-- 3. |Q/P| = 1 on the boundary |z_k| = 1
-- 4. Maximum modulus principle

-- ACTUALLY, looking at Harcos more carefully:
-- He shows sup_{|a|≤1, |z|<1} |ratio| ≤ 1.
-- By continuity, replacing |a|≤1 with |a|<1 doesn't change the sup.
-- Then by max modulus, replacing |z|<1 with |z|=1 doesn't change the sup.
-- With |z|=1 and |a|<1: ratio = |(∏z) · conj(f_B(a/conj(z))) / f_B(a·z)|.
-- But on |z_k|=1: a_k/conj(z_k) = a_k · z_k. So both f_B arguments are the same!
-- ratio = |∏z_k| = 1. (Since |z_k| = 1.)
-- So sup = 1, meaning |ratio| ≤ 1 on the original domain.
-- Combined with P ≠ 0: |P + Q| ≥ |P| - |Q| ≥ |P| - |P| = 0.
-- But this only gives ≥ 0, not > 0!

-- Hmm wait, Harcos says it SUFFICES to show sup ≤ 1.
-- If |Q/P| ≤ 1, i.e., |Q| ≤ |P|, then P + Q = 0 would require Q = -P,
-- so |Q| = |P|, meaning |Q/P| = 1 at that point.
-- But we also need Q = -P, i.e., Q/P = -1.
-- On |z_k| = 1: Q/P = (∏z_k) · 1 = ∏z_k. (Since f_B cancels.)
-- So |Q/P| = 1 but Q/P = ∏z_k which is some unit complex number.
-- By max modulus, if |Q/P| achieves its max = 1 at an interior point,
-- then Q/P is constant. But Q/P = ∏z_k on the boundary, which is NOT constant.
-- So Q/P is not constant, hence |Q/P| < 1 at interior points.
-- Therefore |Q| < |P|, so P + Q ≠ 0. ✓

-- OK so the argument works, but it's subtle. The max modulus needs to be applied
-- to the MULTIVARIATE function, which is harder.

-- SIMPLIFICATION: Harcos actually fixes all z_k except one, say z_1,
-- and applies max modulus for that single variable. Then iterates.
-- This avoids multivariate max modulus.

-- Step by step for single variable z_1:
-- Fix z_2,...,z_{m+1} with |z_k| < 1.
-- g(z_1) = Q(z_1,...)/P(z_1,...) is meromorphic in z_1 (P ≠ 0 by ih).
-- On |z_1| = 1: |g| = ... hmm, this doesn't simplify to 1 unless ALL |z_k| = 1.

-- I think Harcos's proof DOES use multivariate max modulus in a single step.
-- But the key is: the function z ↦ (∏z_k) · f_B(a/conj(z))/f_B(a·z)
-- is holomorphic in each z_k separately (when |a| < 1, f_B ≠ 0 by ih).
-- And on the "torus" |z_k| = 1 for all k, the function has modulus 1.
-- By the multivariate max modulus (iterate single-variable max modulus),
-- |function| ≤ 1 on the polydisk.

-- The iterated max modulus: for f holomorphic in each variable separately
-- on the polydisk, sup_{D^n} |f| = sup_{T^n} |f| (achieved on the torus).
-- This is a well-known result and follows from iterating the 1-variable case.

-- In Lean, this would be:
-- 1. Fix z_2,...,z_n. Apply 1-variable max modulus to z_1.
-- 2. The bound on |z_1| = 1 depends on z_2,...,z_n.
-- 3. But we can take sup over z_2,...,z_n and iterate.

-- This requires showing the function is continuous and holomorphic in each variable.
-- For a polynomial (which f_A is), this is automatic.

-- CONCLUSION: The Harcos proof is doable but requires:
-- a) The algebraic identity f_A = P + Q (hard Finset manipulation)
-- b) Holomorphy of the ratio (polynomial ÷ nonzero polynomial)
-- c) Iterated 1-variable max modulus
-- d) Boundary evaluation (on torus, ratio has modulus 1)

-- Each step is individually feasible but the combination is 500+ lines.
-- The algebraic identity (a) is the hardest part.

-- Let me at least TRY to prove the algebraic identity for the "last ∉ S" part.
-- This is: ∑_{S : last ∉ S} leeYangPoly A S · ∏_{k∈S} z k = firstTerm A z

-- For this, I need to biject {S ⊆ Fin(m+1) : last ∉ S} with {T ⊆ Fin m}
-- and show the summands match.

-- The bijection: T ↦ T.map ⟨castSucc, castSucc_injective⟩
-- inverse: S ↦ S.preimage castSucc (works because last ∉ S means all elements are castSucc)

-- Let me try this bijection.

-- Step 1 attempt: the bijection between {S : last ∉ S} and Finset (Fin m)
-- Using Finset.map with castSucc embedding.
-- Instead of the filtered sum, let me try a direct Fintype.sum_equiv.

-- First, test: can we even state that T.map castSucc doesn't contain last?
example (T : Finset (Fin m)) : Fin.last m ∉ T.map ⟨Fin.castSucc, Fin.castSucc_injective m⟩ := by
  simp [Finset.mem_map, Fin.castSucc_ne_last]

-- Step 2: coefficient match for the "last ∉ S" part.
-- For S = T.map castSucc (last ∉ S):
-- leeYangPoly A S = ∏_{i∈S} ∏_{j∈univ\S} A i j
-- univ \ S includes last. Factor out last from the j-product:
-- = ∏_{i∈S} (A i last · ∏_{j∈(univ\S)\{last}} A i j)
-- = (∏_{i∈S} A i last) · (∏_{i∈S} ∏_{j∈(univ\S)\{last}} A i j)
-- The second factor: i ∈ S = T.map castSucc, j ∈ (univ\S)\{last} = (Fin m).map castSucc \ S
-- This corresponds to leeYangPoly B T.
-- The first factor: ∏_{i∈T} A (castSucc i) last = ∏_{i∈T} avec i.

-- So leeYangPoly A (T.map castSucc) · ∏_{k∈T.map castSucc} z k
-- = leeYangPoly B T · (∏_{i∈T} avec i) · (∏_{i∈T} z (castSucc i))
-- = leeYangPoly B T · ∏_{i∈T} (avec i · z (castSucc i))
-- = firstTerm summand at T.

-- This is the key coefficient identity. Let me try to prove it.
-- For now, just state it and sorry:
example (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (T : Finset (Fin m)) :
    let S := T.map ⟨Fin.castSucc, Fin.castSucc_injective m⟩
    leeYangPoly A S * ∏ k ∈ S, z k =
    leeYangPoly (A.submatrix Fin.castSucc Fin.castSucc) T *
    ∏ i ∈ T, (A (Fin.castSucc i) (Fin.last m) * z (Fin.castSucc i)) := by
  simp only
  -- leeYangPoly A S = ∏_{i∈S} ∏_{j∈univ\S} A i j
  -- S = T.map castSucc. univ \ S = (univ as Fin(m+1)) \ T.map castSucc
  -- This includes Fin.last m and the castSucc images of Fin m \ T.
  -- Factor the j-product: last + rest.
  unfold leeYangPoly
  -- LHS: (∏ i ∈ T.map e, ∏ j ∈ univ \ T.map e, A i j) * ∏ k ∈ T.map e, z k
  -- RHS: (∏ i ∈ T, ∏ j ∈ univ \ T, A (cs i) (cs j)) * ∏ i ∈ T, (A (cs i) last * z (cs i))
  -- where e = castSucc embedding, cs = Fin.castSucc
  -- Rewrite map products to T-indexed products:
  rw [Finset.prod_map, Finset.prod_map]
  -- Now LHS: (∏ i ∈ T, ∏ j ∈ univ \ T.map e, A (cs i) j) * ∏ i ∈ T, z (cs i)
  -- Factor the complement: univ \ T.map e = insert last ((univ\T).map e)
  have hcompl : ∀ T : Finset (Fin m),
      Finset.univ \ T.map ⟨Fin.castSucc, Fin.castSucc_injective m⟩ =
      insert (Fin.last m) ((Finset.univ \ T).map ⟨Fin.castSucc, Fin.castSucc_injective m⟩) := by
    intro T; ext j
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
  -- Combine the outer products: (∏ f) * (∏ g) = ∏ (f * g)
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  congr 1; ext i
  -- Factor the complement using hcompl
  rw [hcompl T]
  have hlast_nmem : Fin.last m ∉
      (Finset.univ \ T).map ⟨Fin.castSucc, Fin.castSucc_injective m⟩ := by
    simp [Finset.mem_map, Fin.castSucc_ne_last]
  rw [Finset.prod_insert hlast_nmem, Finset.prod_map]
  simp only [Matrix.submatrix_apply, Function.Embedding.coeFn_mk]
  ring

-- Hermitian conjugation lemma:
-- conj(leeYangPoly B T) = leeYangPoly B (univ \ T)
-- This uses A Hermitian ⇒ B Hermitian ⇒ conj(B i j) = B j i
-- Then swapping i,j products gives the complement.
private lemma hermitian_conj_entry {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (i j : Fin n) :
    starRingEnd ℂ (A i j) = A j i := by
  have h := congr_fun (congr_fun hA.eq j) i
  simp [Matrix.conjTranspose_apply] at h
  exact h

lemma leeYangPoly_conj_eq_compl {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (T : Finset (Fin n)) :
    starRingEnd ℂ (leeYangPoly A T) = leeYangPoly A (Finset.univ \ T) := by
  unfold leeYangPoly
  simp only [map_prod]
  simp_rw [hermitian_conj_entry A hA]
  -- LHS: ∏_{i∈T} ∏_{j∈univ\T} A j i
  -- RHS: ∏_{i∈univ\T} ∏_{j∈univ\(univ\T)} A i j
  rw [Finset.prod_comm]
  -- Now: ∏_{j∈univ\T} ∏_{i∈T} A j i
  -- Need: univ \ (univ \ T) = T
  congr 1; ext j; congr 1
  ext x; simp

-- "last ∈ S" coefficient identity.
-- For S = insert last (T.map castSucc):
-- leeYangPoly A S * ∏_{k∈S} z k
-- = leeYangPoly B T * (∏_{j∈univ\T} A last (cs j)) * z last * ∏_{i∈T} z(cs i)
-- We factor: S.complement = (univ\T).map castSucc (no last),
-- and split the i-product over insert.

-- First, the complement of insert last (T.map cs):
private lemma compl_insert_last (T : Finset (Fin m)) :
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

-- The coefficient for S = insert last (T.map cs):
example (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (T : Finset (Fin m)) :
    let e := ⟨Fin.castSucc, Fin.castSucc_injective m⟩
    leeYangPoly A (insert (Fin.last m) (T.map e)) =
    leeYangPoly (A.submatrix Fin.castSucc Fin.castSucc) T *
    ∏ j ∈ (Finset.univ \ T), A (Fin.last m) (Fin.castSucc j) := by
  simp only
  unfold leeYangPoly
  rw [compl_insert_last]
  -- LHS: ∏_{i ∈ insert last (T.map e)} ∏_{j ∈ (univ\T).map e} A i j
  have hlast_nmem : Fin.last m ∉ T.map ⟨Fin.castSucc, Fin.castSucc_injective m⟩ := by
    simp [Finset.mem_map, Fin.castSucc_ne_last]
  rw [Finset.prod_insert hlast_nmem]
  -- = (∏_{j ∈ (univ\T).map e} A last j) * ∏_{i ∈ T.map e} ∏_{j ∈ (univ\T).map e} A i j
  rw [Finset.prod_map, Finset.prod_map]
  simp_rw [Finset.prod_map]
  simp only [Matrix.submatrix_apply, Function.Embedding.coeFn_mk]
  ring
