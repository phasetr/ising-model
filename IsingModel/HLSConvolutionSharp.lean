import IsingModel.PolyDecay
import IsingModel.Concrete.LatticeSphereCard
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Sharp distance-dependent Hardy–Littlewood–Sobolev convolution bound on ℤ^d

This module builds toward the **sharp** (distance-decaying) HLS convolution bound
needed by the proof of Glimm–Jaffe Theorem 17.5.1 (continuity of the mass,
2nd ed. pp.~311--312):
`∑_z (1 + |x − z|)^{-α} (1 + |y − z|)^{-α} ≤ C · (1 + |x − y|)^{-(2α − d)}`
for `d < 2α`, in contrast to the existing *constant* bound
`discrete_hls_convolution_constant` (`PolyDecay.lean`, `∑ ≤ C`, no decay).

The foundational step is the **shell reorganization**: a radial nonnegative
`ℝ≥0∞` kernel summed over `ℤ^d` equals the sum over radii of
`(sphere cardinality) × (kernel value)`.  Working in `ℝ≥0∞` keeps the
reindexing summability-free (`ENNReal.tsum_fiberwise`).

Tracking issue: <https://github.com/phasetr/ising-model/issues/4320>.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5, Theorem 17.5.1, pp.~311--312.
-/

namespace IsingModel

open scoped ENNReal
open Ambient

/-- **Shell reorganization of a radial `ℝ≥0∞` sum over `ℤ^d`**: for any kernel
`f : ℕ → ℝ≥0∞`, the sum of `f (latticeDistance d 0 z)` over `z : Fin d → ℤ`
equals the sum over radii `n` of `(latticeSphere d n).card · f n`.

Proof: fiber the lattice over the distance-to-origin map
(`ENNReal.tsum_fiberwise`); on the fiber `{z | dist 0 z = n}` the kernel is the
constant `f n`, so the fiber sum is `ENat.card · f n`
(`ENNReal.tsum_const`), and the fiber is exactly `latticeSphere d n`, finite, with
`ENat.card = (latticeSphere d n).card`. -/
theorem tsum_radial_eq_tsum_shell (d : ℕ) (f : ℕ → ℝ≥0∞) :
    ∑' z : Fin d → ℤ, f (IsingModel.latticeDistance d 0 z)
      = ∑' n : ℕ, ((latticeSphere d n).card : ℝ≥0∞) * f n := by
  classical
  rw [← ENNReal.tsum_fiberwise (fun z => f (IsingModel.latticeDistance d 0 z))
    (fun z => IsingModel.latticeDistance d 0 z)]
  refine tsum_congr (fun n => ?_)
  -- The fiber over `n` is `latticeSphere d n` (as a set), finite.
  have hfib_eq : (fun z => IsingModel.latticeDistance d 0 z) ⁻¹' {n}
      = ↑(latticeSphere d n) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff,
      Finset.mem_coe, mem_latticeSphere]
  -- On the fiber the kernel is constant `f n`.
  have hconst :
      ∑' b : (fun z => IsingModel.latticeDistance d 0 z) ⁻¹' {n},
          f (IsingModel.latticeDistance d 0 (b : Fin d → ℤ))
        = ∑' _b : (fun z => IsingModel.latticeDistance d 0 z) ⁻¹' {n}, f n := by
    refine tsum_congr (fun b => ?_)
    have hb : IsingModel.latticeDistance d 0 (b : Fin d → ℤ) = n := b.2
    rw [hb]
  rw [hconst, ENNReal.tsum_const]
  -- `ENat.card (fiber) = (latticeSphere d n).card`.
  have hcard : ENat.card ((fun z => IsingModel.latticeDistance d 0 z) ⁻¹' {n})
      = ((latticeSphere d n).card : ℕ∞) := by
    rw [hfib_eq]
    simp
  rw [hcard]
  simp

/-- **Shell reorganization centred at an arbitrary point** `x`: for any kernel
`f : ℕ → ℝ≥0∞`, the radial sum `∑'_z f (latticeDistance d x z)` equals the
shell sum `∑'_n (latticeSphere d n).card · f n`, independent of the centre `x`.

Proof: `latticeDistance d x z = latticeDistance d 0 (z - x)`
(`latticeDistance_translate_eq`), reindex `z ↦ z - x` by `Equiv.addRight (-x)`,
then apply the origin-centred `tsum_radial_eq_tsum_shell`. -/
theorem tsum_radial_eq_tsum_shell_center (d : ℕ) (x : Fin d → ℤ) (f : ℕ → ℝ≥0∞) :
    ∑' z : Fin d → ℤ, f (IsingModel.latticeDistance d x z)
      = ∑' n : ℕ, ((latticeSphere d n).card : ℝ≥0∞) * f n := by
  have hshift : ∑' z : Fin d → ℤ, f (IsingModel.latticeDistance d x z)
      = ∑' z : Fin d → ℤ, f (IsingModel.latticeDistance d 0 z) := by
    simp_rw [latticeDistance_translate_eq d x]
    exact (Equiv.addRight (-x)).tsum_eq
      (fun z => f (IsingModel.latticeDistance d 0 z))
  rw [hshift, tsum_radial_eq_tsum_shell d f]

/-- **Shell-cardinality power reduction**: for `d ≥ 1` and any real exponent `s`,
the shell-weighted kernel `(latticeSphere d n).card · (1 + n)^s` is dominated by
`2^d · (1 + n)^{(d-1) + s}`.

Proof: `(latticeSphere d n).card ≤ 2·(2n+1)^{d-1}` (`latticeSphere_card_le'`),
`2n+1 ≤ 2·(1+n)` gives `(2n+1)^{d-1} ≤ 2^{d-1}·(1+n)^{d-1}`, so the card is
`≤ 2^d·(1+n)^{d-1}`; multiplying by `(1+n)^s` and merging the powers
(`Real.rpow_natCast`, `Real.rpow_add`) yields the claim. -/
theorem latticeSphere_card_mul_rpow_le (d : ℕ) (hd : 1 ≤ d) (n : ℕ) (s : ℝ) :
    ((latticeSphere d n).card : ℝ) * (1 + (n : ℝ)) ^ s
      ≤ (2 : ℝ) ^ d * (1 + (n : ℝ)) ^ ((d : ℝ) - 1 + s) := by
  have h1n : (0 : ℝ) < 1 + (n : ℝ) := by positivity
  -- Cardinality bound, cast to ℝ.
  have hcard : ((latticeSphere d n).card : ℝ) ≤ (2 : ℝ) ^ d * (1 + (n : ℝ)) ^ ((d : ℝ) - 1) := by
    have hcard0 : (latticeSphere d n).card ≤ 2 * (2 * n + 1) ^ (d - 1) :=
      latticeSphere_card_le' d n hd
    have hcardR : ((latticeSphere d n).card : ℝ) ≤ 2 * ((2 * n + 1 : ℕ) : ℝ) ^ (d - 1) := by
      have := (Nat.cast_le (α := ℝ)).mpr hcard0
      push_cast at this ⊢
      convert this using 2
    -- `(2n+1) ≤ 2(1+n)`, so `(2n+1)^{d-1} ≤ (2(1+n))^{d-1} = 2^{d-1}(1+n)^{d-1}`.
    have hstep : ((2 * n + 1 : ℕ) : ℝ) ^ (d - 1) ≤ (2 : ℝ) ^ (d - 1) * (1 + (n : ℝ)) ^ (d - 1) := by
      have hb : ((2 * n + 1 : ℕ) : ℝ) ≤ 2 * (1 + (n : ℝ)) := by push_cast; linarith
      calc ((2 * n + 1 : ℕ) : ℝ) ^ (d - 1)
          ≤ (2 * (1 + (n : ℝ))) ^ (d - 1) :=
            pow_le_pow_left₀ (by positivity) hb _
        _ = (2 : ℝ) ^ (d - 1) * (1 + (n : ℝ)) ^ (d - 1) := by rw [mul_pow]
    -- Convert the natural-power `(1+n)^{d-1}` to the real-power `(1+n)^{(d:ℝ)-1}`.
    have hpow_cast : (1 + (n : ℝ)) ^ (d - 1) = (1 + (n : ℝ)) ^ ((d : ℝ) - 1) := by
      rw [← Real.rpow_natCast (1 + (n : ℝ)) (d - 1)]
      congr 1
      have : (1 : ℕ) ≤ d := hd
      push_cast [Nat.cast_sub this]
      ring
    have h2cast : (2 : ℝ) ^ d = 2 * (2 : ℝ) ^ (d - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    calc ((latticeSphere d n).card : ℝ)
        ≤ 2 * ((2 * n + 1 : ℕ) : ℝ) ^ (d - 1) := hcardR
      _ ≤ 2 * ((2 : ℝ) ^ (d - 1) * (1 + (n : ℝ)) ^ (d - 1)) := by
          exact mul_le_mul_of_nonneg_left hstep (by norm_num)
      _ = (2 * (2 : ℝ) ^ (d - 1)) * (1 + (n : ℝ)) ^ (d - 1) := by ring
      _ = (2 : ℝ) ^ d * (1 + (n : ℝ)) ^ ((d : ℝ) - 1) := by rw [← h2cast, hpow_cast]
  -- Multiply by `(1+n)^s ≥ 0` and merge the real powers.
  calc ((latticeSphere d n).card : ℝ) * (1 + (n : ℝ)) ^ s
      ≤ ((2 : ℝ) ^ d * (1 + (n : ℝ)) ^ ((d : ℝ) - 1)) * (1 + (n : ℝ)) ^ s :=
        mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg h1n.le s)
    _ = (2 : ℝ) ^ d * (1 + (n : ℝ)) ^ ((d : ℝ) - 1 + s) := by
        rw [mul_assoc, ← Real.rpow_add h1n]

/-- **Finite-interval integral comparison for the tail sum**: for `e < -1` and
`1 ≤ R ≤ M`, `∑_{j ∈ Ioc R M} j^e ≤ R^{e+1} / (-(e+1))`.

Proof: reindex `Ioc R M = Ico (R+1) (M+1)` to match `AntitoneOn.sum_le_integral_Ico`
(`t^e` antitone on `(0,∞)`), bounding the sum by `∫_R^M t^e`; evaluate the
interval integral by `integral_rpow` as `(M^{e+1} - R^{e+1})/(e+1)`, and drop the
nonnegative `M^{e+1}` term. -/
theorem sum_Ioc_nat_rpow_le {e : ℝ} (he : e < -1) {R M : ℕ} (hR : 1 ≤ R) (hRM : R ≤ M) :
    ∑ j ∈ Finset.Ioc R M, ((j : ℝ)) ^ e ≤ (R : ℝ) ^ (e + 1) / (-(e + 1)) := by
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have hMnat : 0 < M := lt_of_lt_of_le Nat.one_pos (le_trans hR hRM)
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hMnat
  have he0 : e ≤ 0 := by linarith
  have he1 : (0 : ℝ) < -(e + 1) := by linarith
  have hne1 : e + 1 ≠ 0 := by linarith
  -- Reindex `Ioc R M = Ico (R+1) (M+1)`, then `Ico (R+1)(M+1)` as a `+1`-shift of `Ico R M`.
  have hIoc : Finset.Ioc R M = Finset.Ico (R + 1) (M + 1) := by
    ext x; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega
  have hmap : ∑ j ∈ Finset.Ioc R M, ((j : ℝ)) ^ e
      = ∑ i ∈ Finset.Ico R M, (((i + 1 : ℕ) : ℝ)) ^ e := by
    rw [hIoc, ← Finset.map_add_right_Ico R M 1, Finset.sum_map]
    rfl
  rw [hmap]
  -- Antitone integral comparison.
  have hanti : AntitoneOn (fun t : ℝ => t ^ e) (Set.Icc (R : ℝ) (M : ℝ)) :=
    (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos he0).mono
      (fun t ht => lt_of_lt_of_le hRpos ht.1)
  have hsum_le_int :
      ∑ i ∈ Finset.Ico R M, (((i + 1 : ℕ) : ℝ)) ^ e
        ≤ ∫ x in (R : ℝ)..(M : ℝ), x ^ e :=
    AntitoneOn.sum_le_integral_Ico hRM hanti
  refine hsum_le_int.trans ?_
  -- Evaluate the interval integral.
  have hne : e ≠ -1 := ne_of_lt he
  have h0notmem : (0 : ℝ) ∉ Set.uIcc (R : ℝ) (M : ℝ) := by
    rw [Set.uIcc_of_le (by exact_mod_cast hRM), Set.mem_Icc]
    rintro ⟨h0, _⟩; linarith
  rw [integral_rpow (Or.inr ⟨hne, h0notmem⟩)]
  -- `(M^{e+1} - R^{e+1})/(e+1) ≤ R^{e+1}/(-(e+1))`.
  have hMe : (0 : ℝ) ≤ (M : ℝ) ^ (e + 1) := Real.rpow_nonneg hMpos.le _
  have heq : ((M : ℝ) ^ (e + 1) - (R : ℝ) ^ (e + 1)) / (e + 1)
      = ((R : ℝ) ^ (e + 1) - (M : ℝ) ^ (e + 1)) / (-(e + 1)) := by
    rw [div_neg, ← neg_div, neg_sub]
  rw [heq]
  gcongr
  linarith [hMe]

/-- **Finite head-sum integral comparison** (`e > -1`): for `1 ≤ N`,
`∑_{m ∈ Ioc 0 N} m^e ≤ (N+1)^{e+1}/(e+1) + 1`.

Two cases: for `e ≥ 0` (monotone) `∑_{m∈Ico 1 (N+1)} m^e ≤ ∫_1^{N+1} t^e`; for
`-1 < e < 0` (antitone, where `t^e` is antitone only on `(0,∞)`, NOT through 0)
split off the `m = 1` term and apply `AntitoneOn.sum_le_integral_Ico` on `Icc 1 N`,
`∫_1^N t^e`.  Both interval integrals are evaluated by `integral_rpow`. -/
theorem sum_Ioc_zero_nat_rpow_le {e : ℝ} (he : -1 < e) {N : ℕ} (hN : 1 ≤ N) :
    ∑ m ∈ Finset.Ioc 0 N, ((m : ℝ)) ^ e ≤ ((N : ℝ) + 1) ^ (e + 1) / (e + 1) + 1 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have he1 : (0 : ℝ) < e + 1 := by linarith
  have hNN1 : (N : ℝ) ^ (e + 1) ≤ ((N : ℝ) + 1) ^ (e + 1) :=
    Real.rpow_le_rpow hNpos.le (by linarith) he1.le
  by_cases he0 : 0 ≤ e
  · -- `e ≥ 0`: monotone on `Icc 1 (N+1)`.
    have hIoc : Finset.Ioc 0 N = Finset.Ico 1 (N + 1) := by
      ext x; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega
    rw [hIoc]
    have hmono : MonotoneOn (fun t : ℝ => t ^ e)
        (Set.Icc ((1 : ℕ) : ℝ) ((N + 1 : ℕ) : ℝ)) := by
      intro a ha b hb hab
      exact Real.rpow_le_rpow (le_trans (by norm_num) ha.1) hab he0
    have hle := MonotoneOn.sum_le_integral_Ico (f := fun t : ℝ => t ^ e)
      (by omega : (1 : ℕ) ≤ N + 1) hmono
    refine hle.trans ?_
    have h0notmem : (0 : ℝ) ∉ Set.uIcc ((1 : ℕ) : ℝ) ((N + 1 : ℕ) : ℝ) := by
      rw [Set.uIcc_of_le (by exact_mod_cast (by omega : (1 : ℕ) ≤ N + 1)), Set.mem_Icc]
      rintro ⟨h0, _⟩; norm_num at h0
    rw [integral_rpow (Or.inl he)]
    push_cast
    rw [Real.one_rpow]
    have : ((N : ℝ) + 1) ^ (e + 1) / (e + 1) - 1 / (e + 1)
        ≤ ((N : ℝ) + 1) ^ (e + 1) / (e + 1) + 1 := by
      have : (0 : ℝ) ≤ 1 / (e + 1) := by positivity
      linarith
    calc (((N : ℝ) + 1) ^ (e + 1) - 1) / (e + 1)
        = ((N : ℝ) + 1) ^ (e + 1) / (e + 1) - 1 / (e + 1) := by ring
      _ ≤ ((N : ℝ) + 1) ^ (e + 1) / (e + 1) + 1 := this
  · -- `-1 < e < 0`: split off `m = 1`, antitone on `Icc 1 N`.
    replace he0 : e < 0 := not_le.mp he0
    have hsplit : Finset.Ioc 0 N = insert 1 (Finset.Ioc 1 N) := by
      ext x; simp only [Finset.mem_Ioc, Finset.mem_insert]; omega
    have h1notin : (1 : ℕ) ∉ Finset.Ioc 1 N := by simp
    rw [hsplit, Finset.sum_insert h1notin, Nat.cast_one, Real.one_rpow]
    -- bound `∑_{m∈Ioc 1 N} m^e` by `∫_1^N`.
    have hmap : ∑ m ∈ Finset.Ioc 1 N, ((m : ℝ)) ^ e
        = ∑ i ∈ Finset.Ico 1 N, (((i + 1 : ℕ) : ℝ)) ^ e := by
      have hII : Finset.Ioc 1 N = Finset.Ico 2 (N + 1) := by
        ext x; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega
      rw [hII, show (2 : ℕ) = 1 + 1 from rfl, show N + 1 = N + 1 from rfl,
        ← Finset.map_add_right_Ico 1 N 1, Finset.sum_map]
      rfl
    have hanti : AntitoneOn (fun t : ℝ => t ^ e) (Set.Icc ((1 : ℕ) : ℝ) ((N : ℕ) : ℝ)) :=
      (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (le_of_lt he0)).mono
        (fun t ht => lt_of_lt_of_le (by norm_num) ht.1)
    have hle := AntitoneOn.sum_le_integral_Ico (f := fun t : ℝ => t ^ e) hN hanti
    rw [hmap] at *
    have hInt : ∫ x in ((1 : ℕ) : ℝ)..((N : ℕ) : ℝ), x ^ e
        = ((N : ℝ) ^ (e + 1) - 1) / (e + 1) := by
      have h0notmem : (0 : ℝ) ∉ Set.uIcc ((1 : ℕ) : ℝ) ((N : ℕ) : ℝ) := by
        rw [Set.uIcc_of_le (by exact_mod_cast hN), Set.mem_Icc]
        rintro ⟨h0, _⟩; norm_num at h0
      rw [integral_rpow (Or.inl he)]; push_cast; rw [Real.one_rpow]
    rw [hInt] at hle
    have hfrac : ((N : ℝ) ^ (e + 1) - 1) / (e + 1)
        ≤ ((N : ℝ) + 1) ^ (e + 1) / (e + 1) := by
      gcongr
      linarith [hNN1]
    linarith [hle, hfrac]

/-- **Radial shell-sum over a ball** (`α < d`, `d ≥ 1`): the shell-weighted
inverse-power sum over radii `0..K` is bounded by `2^d·((K+2)^{d-α}/(d-α) + 1)`.

Combines `latticeSphere_card_mul_rpow_le` (term-wise card→power reduction, with
`s = -α`) with the head-sum integral comparison `sum_Ioc_zero_nat_rpow_le` (at
`e = d-1-α > -1`), after reindexing `∑_{n ∈ range (K+1)} (1+n)^e = ∑_{m ∈ Ioc 0 (K+1)} m^e`. -/
theorem radial_shell_ball_sum_le {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : α < (d : ℝ))
    (K : ℕ) :
    ∑ n ∈ Finset.range (K + 1),
        ((latticeSphere d n).card : ℝ) * (1 + (n : ℝ)) ^ (-α)
      ≤ (2 : ℝ) ^ d * (((K : ℝ) + 2) ^ ((d : ℝ) - α) / ((d : ℝ) - α) + 1) := by
  set e : ℝ := (d : ℝ) - 1 - α with he_def
  have he : -1 < e := by rw [he_def]; linarith
  -- Term-wise card→power reduction.
  have hterm : ∀ n ∈ Finset.range (K + 1),
      ((latticeSphere d n).card : ℝ) * (1 + (n : ℝ)) ^ (-α)
        ≤ (2 : ℝ) ^ d * (1 + (n : ℝ)) ^ e := by
    intro n _
    have := latticeSphere_card_mul_rpow_le d hd n (-α)
    rwa [show (d : ℝ) - 1 + -α = e from by rw [he_def]; ring] at this
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  -- Reindex `∑_{range (K+1)} (1+n)^e = ∑_{Ioc 0 (K+1)} m^e`.
  have hreindex : ∑ n ∈ Finset.range (K + 1), (1 + (n : ℝ)) ^ e
      = ∑ m ∈ Finset.Ioc 0 (K + 1), ((m : ℝ)) ^ e := by
    have hIoc : Finset.Ioc 0 (K + 1) = Finset.Ico 1 (K + 2) := by
      ext x; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega
    rw [hIoc, show (1 : ℕ) = 0 + 1 from rfl, ← Finset.map_add_right_Ico 0 (K + 1) 1,
      Finset.sum_map, Finset.range_eq_Ico]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    simp only [addRightEmbedding_apply]
    congr 1
    push_cast
    ring
  rw [hreindex]
  -- Head-sum bound at `N = K+1`.
  have hhead := sum_Ioc_zero_nat_rpow_le he (N := K + 1) (by omega)
  have hee : e + 1 = (d : ℝ) - α := by rw [he_def]; ring
  have hNN : ((K : ℝ) + 1 + 1) = (K : ℝ) + 2 := by ring
  rw [hee] at hhead
  have hcast : (((K + 1 : ℕ) : ℝ)) = (K : ℝ) + 1 := by push_cast; ring
  rw [hcast] at hhead
  have h2d_pos : (0 : ℝ) < (2 : ℝ) ^ d := by positivity
  rw [hNN] at hhead
  exact mul_le_mul_of_nonneg_left hhead h2d_pos.le

end IsingModel
