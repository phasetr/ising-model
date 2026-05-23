import IsingModel.LeeYang.RatioBound

/-!
# Lee-Yang circle theorem split — Lee-Yang polynomial nonvanishing on the polydisk

Part of the split Lee-Yang circle-theorem layer (Issue #1850).
-/

namespace IsingModel

open Finset Complex

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

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


end IsingModel
