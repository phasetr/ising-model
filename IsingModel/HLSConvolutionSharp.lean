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

/-- **Radial ball z-sum bound** (`α < d`, `d ≥ 1`): the `ℝ≥0∞` sum over the
lattice points `z` with `latticeDistance d x z ≤ K` of `(1+dist)^{−α}` is bounded
by `ENNReal.ofReal (2^d·((K+2)^{d−α}/(d−α)+1))`.

Bridges the shell-index `radial_shell_ball_sum_le` to a z-indexed `ℝ≥0∞` sum (the
form consumed by the convolution region split): the centre-arbitrary shell
reorganization turns the z-sum into `∑_n card·(if n≤K then …)`, every partial sum
of which is `≤ ∑_{n≤K} card·(1+n)^{−α} = ofReal(radial ball bound)`
(via `ENNReal.tsum_le_of_sum_range_le`). -/
theorem tsum_ball_radial_le {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : α < (d : ℝ))
    (x : Fin d → ℤ) (K : ℕ) :
    ∑' z : Fin d → ℤ,
        (if IsingModel.latticeDistance d x z ≤ K then
          ENNReal.ofReal ((1 + (IsingModel.latticeDistance d x z : ℝ)) ^ (-α)) else 0)
      ≤ ENNReal.ofReal ((2 : ℝ) ^ d * (((K : ℝ) + 2) ^ ((d : ℝ) - α) / ((d : ℝ) - α) + 1)) := by
  rw [tsum_radial_eq_tsum_shell_center d x
    (fun n => if n ≤ K then ENNReal.ofReal ((1 + (n : ℝ)) ^ (-α)) else 0)]
  -- Rewrite each shell term `card · (if …)` as `if … then ofReal(card·…) else 0`.
  have hkern : ∀ n : ℕ,
      ((latticeSphere d n).card : ℝ≥0∞) *
          (if n ≤ K then ENNReal.ofReal ((1 + (n : ℝ)) ^ (-α)) else 0)
        = (if n ≤ K then
            ENNReal.ofReal (((latticeSphere d n).card : ℝ) * (1 + (n : ℝ)) ^ (-α))
            else 0) := by
    intro n
    by_cases hn : n ≤ K
    · rw [if_pos hn, if_pos hn,
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
    · rw [if_neg hn, if_neg hn, mul_zero]
  simp_rw [hkern]
  refine ENNReal.tsum_le_of_sum_range_le (fun m => ?_)
  -- Bound the partial sum by the full ball shell-sum, then by `ofReal(bound)`.
  have hsub :
      ∑ n ∈ Finset.range m,
          (if n ≤ K then
            ENNReal.ofReal (((latticeSphere d n).card : ℝ) * (1 + (n : ℝ)) ^ (-α)) else 0)
        ≤ ∑ n ∈ Finset.range (K + 1),
            ENNReal.ofReal (((latticeSphere d n).card : ℝ) * (1 + (n : ℝ)) ^ (-α)) := by
    rw [← Finset.sum_filter]
    refine Finset.sum_le_sum_of_subset ?_
    intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    rw [Finset.mem_range]; omega
  refine hsub.trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun n _ => by positivity)]
  exact ENNReal.ofReal_le_ofReal (radial_shell_ball_sum_le hd hα K)

/-- **Radial shell-sum over a tail** (`d < 2α`, `d ≥ 1`): the shell-weighted
`(1+n)^{−2α}` sum over radii `n > K` (here as a finite `Ioc K m` partial sum) is
bounded by `2^d·(K+1)^{d−2α}/(2α−d)`, uniformly in `m`.

Combines `latticeSphere_card_mul_rpow_le` (term-wise, `s=−2α`) with the tail
integral comparison `sum_Ioc_nat_rpow_le` (at `e = d−1−2α < −1`), after reindexing
`∑_{n∈Ioc K m} (1+n)^e = ∑_{j∈Ioc (K+1) (m+1)} j^e`. -/
theorem radial_shell_tail_sum_le {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα2 : (d : ℝ) < 2 * α)
    (K m : ℕ) :
    ∑ n ∈ Finset.Ioc K m,
        ((latticeSphere d n).card : ℝ) * (1 + (n : ℝ)) ^ (-(2 * α))
      ≤ (2 : ℝ) ^ d * ((K : ℝ) + 1) ^ ((d : ℝ) - 2 * α) / (2 * α - (d : ℝ)) := by
  set e : ℝ := (d : ℝ) - 1 - 2 * α with he_def
  have he : e < -1 := by rw [he_def]; linarith
  -- Term-wise card→power reduction.
  have hterm : ∀ n ∈ Finset.Ioc K m,
      ((latticeSphere d n).card : ℝ) * (1 + (n : ℝ)) ^ (-(2 * α))
        ≤ (2 : ℝ) ^ d * (1 + (n : ℝ)) ^ e := by
    intro n _
    have := latticeSphere_card_mul_rpow_le d hd n (-(2 * α))
    rwa [show (d : ℝ) - 1 + -(2 * α) = e from by rw [he_def]; ring] at this
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  -- Reindex `∑_{Ioc K m} (1+n)^e = ∑_{Ioc (K+1) (m+1)} j^e`.
  have hreindex : ∑ n ∈ Finset.Ioc K m, (1 + (n : ℝ)) ^ e
      = ∑ j ∈ Finset.Ioc (K + 1) (m + 1), ((j : ℝ)) ^ e := by
    have hIoc : Finset.Ioc (K + 1) (m + 1) = Finset.Ico (K + 2) (m + 2) := by
      ext x; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega
    have hIoc2 : Finset.Ioc K m = Finset.Ico (K + 1) (m + 1) := by
      ext x; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega
    rw [hIoc, hIoc2, show K + 2 = (K + 1) + 1 from rfl,
      show m + 2 = (m + 1) + 1 from rfl,
      ← Finset.map_add_right_Ico (K + 1) (m + 1) 1, Finset.sum_map]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    simp only [addRightEmbedding_apply]
    congr 1
    push_cast
    ring
  rw [hreindex]
  -- Tail integral comparison at `R = K+1`, `M = m+1`.
  by_cases hKm : K + 1 ≤ m + 1
  · have htail := sum_Ioc_nat_rpow_le he (R := K + 1) (M := m + 1) (by omega) hKm
    have hee : -(e + 1) = 2 * α - (d : ℝ) := by rw [he_def]; ring
    have hcast : (((K + 1 : ℕ) : ℝ)) = (K : ℝ) + 1 := by push_cast; ring
    rw [hee, hcast] at htail
    have h2d_pos : (0 : ℝ) < (2 : ℝ) ^ d := by positivity
    calc (2 : ℝ) ^ d * ∑ j ∈ Finset.Ioc (K + 1) (m + 1), ((j : ℝ)) ^ e
        ≤ (2 : ℝ) ^ d * (((K : ℝ) + 1) ^ (e + 1) / (2 * α - (d : ℝ))) :=
          mul_le_mul_of_nonneg_left htail h2d_pos.le
      _ = (2 : ℝ) ^ d * ((K : ℝ) + 1) ^ ((d : ℝ) - 2 * α) / (2 * α - (d : ℝ)) := by
          rw [show e + 1 = (d : ℝ) - 2 * α from by rw [he_def]; ring]; ring
  · have hempty : Finset.Ioc (K + 1) (m + 1) = ∅ := Finset.Ioc_eq_empty (by omega)
    rw [hempty, Finset.sum_empty, mul_zero]
    apply div_nonneg
    · positivity
    · linarith

/-- **Radial tail z-sum bound** (`d < 2α`, `d ≥ 1`): the `ℝ≥0∞` sum over lattice
points `z` with `K < latticeDistance d x z` of `(1+dist)^{−2α}` is bounded by
`ENNReal.ofReal (2^d·(K+1)^{d−2α}/(2α−d))`.

The far-region engine bridge: centre-arbitrary shell reorganization +
`ENNReal.tsum_le_of_sum_range_le`, each partial sum bounded by `radial_shell_tail_sum_le`. -/
theorem tsum_tail_radial_le {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα2 : (d : ℝ) < 2 * α)
    (x : Fin d → ℤ) (K : ℕ) :
    ∑' z : Fin d → ℤ,
        (if K < IsingModel.latticeDistance d x z then
          ENNReal.ofReal ((1 + (IsingModel.latticeDistance d x z : ℝ)) ^ (-(2 * α))) else 0)
      ≤ ENNReal.ofReal
          ((2 : ℝ) ^ d * ((K : ℝ) + 1) ^ ((d : ℝ) - 2 * α) / (2 * α - (d : ℝ))) := by
  rw [tsum_radial_eq_tsum_shell_center d x
    (fun n => if K < n then ENNReal.ofReal ((1 + (n : ℝ)) ^ (-(2 * α))) else 0)]
  have hkern : ∀ n : ℕ,
      ((latticeSphere d n).card : ℝ≥0∞) *
          (if K < n then ENNReal.ofReal ((1 + (n : ℝ)) ^ (-(2 * α))) else 0)
        = (if K < n then
            ENNReal.ofReal (((latticeSphere d n).card : ℝ) * (1 + (n : ℝ)) ^ (-(2 * α)))
            else 0) := by
    intro n
    by_cases hn : K < n
    · rw [if_pos hn, if_pos hn,
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
    · rw [if_neg hn, if_neg hn, mul_zero]
  simp_rw [hkern]
  refine ENNReal.tsum_le_of_sum_range_le (fun m => ?_)
  have hsub :
      ∑ n ∈ Finset.range m,
          (if K < n then
            ENNReal.ofReal (((latticeSphere d n).card : ℝ) * (1 + (n : ℝ)) ^ (-(2 * α)))
            else 0)
        ≤ ∑ n ∈ Finset.Ioc K m,
            ENNReal.ofReal (((latticeSphere d n).card : ℝ) * (1 + (n : ℝ)) ^ (-(2 * α))) := by
    rw [← Finset.sum_filter]
    refine Finset.sum_le_sum_of_subset ?_
    intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    rw [Finset.mem_Ioc]; omega
  refine hsub.trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun n _ => by positivity)]
  exact ENNReal.ofReal_le_ofReal (radial_shell_tail_sum_le hd hα2 K m)

/-- **Near-x region bound** of the sharp HLS convolution (`α < d`, `d ≥ 1`): the
sum over `z` with `2·dist(x,z) ≤ D := dist(x,y)` of
`ofReal((1+dist x z)^{−α})·ofReal((1+dist y z)^{−α})` is bounded by
`ofReal((1+K)^{−α}) · ofReal(2^d·((K+2)^{d−α}/(d−α)+1))` with `K := D/2`.

In this region `dist(y,z) ≥ D − dist(x,z) ≥ K` (triangle inequality), so the
`y`-factor is `≤ ofReal((1+K)^{−α})`; factoring it out (`ENNReal.tsum_mul_right`)
leaves the radial ball sum `tsum_ball_radial_le`. -/
theorem tsum_nearx_region_le {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hαnn : 0 ≤ α) (hα : α < (d : ℝ))
    (x y : Fin d → ℤ) :
    ∑' z : Fin d → ℤ,
        (if 2 * IsingModel.latticeDistance d x z ≤ IsingModel.latticeDistance d x y then
          ENNReal.ofReal ((1 + (IsingModel.latticeDistance d x z : ℝ)) ^ (-α)) *
            ENNReal.ofReal ((1 + (IsingModel.latticeDistance d y z : ℝ)) ^ (-α)) else 0)
      ≤ ENNReal.ofReal ((1 + ((IsingModel.latticeDistance d x y / 2 : ℕ) : ℝ)) ^ (-α)) *
          ENNReal.ofReal ((2 : ℝ) ^ d *
            ((((IsingModel.latticeDistance d x y / 2 : ℕ) : ℝ) + 2) ^ ((d : ℝ) - α) /
              ((d : ℝ) - α) + 1)) := by
  have hα0 : (-α) ≤ 0 := by linarith
  set D := IsingModel.latticeDistance d x y with hD
  set K := D / 2 with hK
  set C : ℝ≥0∞ := ENNReal.ofReal ((1 + (K : ℝ)) ^ (-α)) with hC
  -- Pointwise: near-x term ≤ (ball indicator)·C.
  have hcover : ∀ z : Fin d → ℤ,
      (if 2 * IsingModel.latticeDistance d x z ≤ D then
        ENNReal.ofReal ((1 + (IsingModel.latticeDistance d x z : ℝ)) ^ (-α)) *
          ENNReal.ofReal ((1 + (IsingModel.latticeDistance d y z : ℝ)) ^ (-α)) else 0)
        ≤ (if IsingModel.latticeDistance d x z ≤ K then
            ENNReal.ofReal ((1 + (IsingModel.latticeDistance d x z : ℝ)) ^ (-α)) else 0) * C := by
    intro z
    by_cases hz : 2 * IsingModel.latticeDistance d x z ≤ D
    · rw [if_pos hz, if_pos (by omega : IsingModel.latticeDistance d x z ≤ K)]
      -- y-factor ≤ C.
      have hyge : K ≤ IsingModel.latticeDistance d y z := by
        have htri := IsingModel.latticeDistance_triangle d x z y
        rw [IsingModel.latticeDistance_comm d z y] at htri
        omega
      have hyle : ENNReal.ofReal ((1 + (IsingModel.latticeDistance d y z : ℝ)) ^ (-α)) ≤ C := by
        rw [hC]
        apply ENNReal.ofReal_le_ofReal
        apply Real.rpow_le_rpow_of_nonpos (by positivity) _ hα0
        have : (K : ℝ) ≤ (IsingModel.latticeDistance d y z : ℝ) := by exact_mod_cast hyge
        linarith
      exact mul_le_mul' le_rfl hyle
    · rw [if_neg hz]
      exact zero_le _
  refine (ENNReal.tsum_le_tsum hcover).trans ?_
  rw [ENNReal.tsum_mul_right, mul_comm]
  exact mul_le_mul' le_rfl (tsum_ball_radial_le hd hα x K)

/-- **Far region bound** of the sharp HLS convolution (`d < 2α`, `0 ≤ α`,
`d ≥ 1`): the sum over `z` with `D < 2·dist(x,z)` and `D < 2·dist(y,z)`
(`D := dist(x,y)`) of `ofReal((1+dist x z)^{−α})·ofReal((1+dist y z)^{−α})` is
bounded by `ofReal(3^α) · ofReal(2^d·(K+1)^{d−2α}/(2α−d))` with `K := D/2`.

In this region `dist(x,z) ≤ D + dist(y,z) < 3·dist(y,z)` (triangle + `D<2·dist(y,z)`),
so `1+dist(x,z) ≤ 3(1+dist(y,z))`, hence the product is
`≤ ofReal(3^α)·ofReal((1+dist x z)^{−2α})`; restricting to `K < dist(x,z)` and
applying `tsum_tail_radial_le` closes it. -/
theorem tsum_far_region_le {d : ℕ} (hd : 1 ≤ d) {α : ℝ}
    (hα2 : (d : ℝ) < 2 * α) (x y : Fin d → ℤ) :
    ∑' z : Fin d → ℤ,
        (if IsingModel.latticeDistance d x y < 2 * IsingModel.latticeDistance d x z ∧
            IsingModel.latticeDistance d x y < 2 * IsingModel.latticeDistance d y z then
          ENNReal.ofReal ((1 + (IsingModel.latticeDistance d x z : ℝ)) ^ (-α)) *
            ENNReal.ofReal ((1 + (IsingModel.latticeDistance d y z : ℝ)) ^ (-α)) else 0)
      ≤ ENNReal.ofReal ((3 : ℝ) ^ α) *
          ENNReal.ofReal ((2 : ℝ) ^ d *
            ((IsingModel.latticeDistance d x y / 2 : ℕ) + 1 : ℝ) ^ ((d : ℝ) - 2 * α) /
              (2 * α - (d : ℝ))) := by
  set D := IsingModel.latticeDistance d x y with hD
  set K := D / 2 with hK
  have hcover : ∀ z : Fin d → ℤ,
      (if D < 2 * IsingModel.latticeDistance d x z ∧
          D < 2 * IsingModel.latticeDistance d y z then
        ENNReal.ofReal ((1 + (IsingModel.latticeDistance d x z : ℝ)) ^ (-α)) *
          ENNReal.ofReal ((1 + (IsingModel.latticeDistance d y z : ℝ)) ^ (-α)) else 0)
        ≤ ENNReal.ofReal ((3 : ℝ) ^ α) *
            (if K < IsingModel.latticeDistance d x z then
              ENNReal.ofReal ((1 + (IsingModel.latticeDistance d x z : ℝ)) ^ (-(2 * α)))
              else 0) := by
    intro z
    by_cases hz : D < 2 * IsingModel.latticeDistance d x z ∧
        D < 2 * IsingModel.latticeDistance d y z
    · obtain ⟨hzx, hzy⟩ := hz
      rw [if_pos ⟨hzx, hzy⟩, if_pos (show K < IsingModel.latticeDistance d x z by
        rw [hK]; exact Nat.div_lt_of_lt_mul (by omega))]
      set a : ℝ := 1 + (IsingModel.latticeDistance d x z : ℝ) with ha_def
      set b : ℝ := 1 + (IsingModel.latticeDistance d y z : ℝ) with hb_def
      have ha_pos : 0 < a := by rw [ha_def]; positivity
      have hb_pos : 0 < b := by rw [hb_def]; positivity
      -- comparability `a ≤ 3*b`.
      have hab : a ≤ 3 * b := by
        have htri := IsingModel.latticeDistance_triangle d x y z
        have h1 : (IsingModel.latticeDistance d x z : ℝ)
            ≤ 3 * (IsingModel.latticeDistance d y z : ℝ) := by
          have : IsingModel.latticeDistance d x z ≤ 3 * IsingModel.latticeDistance d y z := by omega
          exact_mod_cast this
        rw [ha_def, hb_def]; linarith
      -- `b^{-α} ≤ 3^α · a^{-α}`.
      have hble : b ^ (-α) ≤ (3 : ℝ) ^ α * a ^ (-α) := by
        have h3b : ((3 : ℝ) * b) ^ (-α) ≤ a ^ (-α) :=
          Real.rpow_le_rpow_of_nonpos ha_pos hab (by linarith)
        rw [Real.mul_rpow (by norm_num) hb_pos.le] at h3b
        have h3 : (3 : ℝ) ^ (-α) = ((3 : ℝ) ^ α)⁻¹ := by
          rw [← Real.rpow_neg (by norm_num)]
        rw [h3] at h3b
        have h3pos : (0 : ℝ) < (3 : ℝ) ^ α := by positivity
        rw [inv_mul_le_iff₀ h3pos] at h3b
        linarith [h3b]
      -- product bound, in ℝ then lifted via ofReal.
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have ha2 : a ^ (-α) * a ^ (-α) = a ^ (-(2 * α)) := by
        rw [← Real.rpow_add ha_pos]; congr 1; ring
      calc a ^ (-α) * b ^ (-α)
          ≤ a ^ (-α) * ((3 : ℝ) ^ α * a ^ (-α)) :=
            mul_le_mul_of_nonneg_left hble (by positivity)
        _ = (3 : ℝ) ^ α * (a ^ (-α) * a ^ (-α)) := by ring
        _ = (3 : ℝ) ^ α * a ^ (-(2 * α)) := by rw [ha2]
    · rw [if_neg hz]
      exact zero_le _
  refine (ENNReal.tsum_le_tsum hcover).trans ?_
  rw [ENNReal.tsum_mul_left]
  exact mul_le_mul' le_rfl (tsum_tail_radial_le hd hα2 x K)

end IsingModel
