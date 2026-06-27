import IsingModel.PolyDecay
import IsingModel.Concrete.LatticeSphereCard

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

end IsingModel
