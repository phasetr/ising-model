import IsingModel.Concrete.LatticeGraphCorrelation.Lemma_17_5_2.MassContinuityLatticeMassContinuityGated

/-!
# GJ Theorem 17.5.1 — reduce the gate to GJ p.312's literal per-pair log-Lipschitz estimate

`latticeMass_continuousOn_window_of_uniform_lipschitz` (#4402) gates true-mass continuity on a
Lipschitz bound for the *Fekete-limit* directional rate `directionalRateFn`.  This file relocates
that gate onto the **book-faithful per-pair estimate** of GJ p.312:

`hLogLip : |log⟨φ₀ φ_{n·v}⟩(β') − log⟨φ₀ φ_{n·v}⟩(β)| ≤ K · (n · d(0,v)) · |β'−β|`

— i.e. the β-log-derivative of the two-point function is bounded **linearly in the separation**,
uniformly over all ray points `n·v`.  `latticeMass_continuousOn_window_of_uniform_log_lipschitz`
proves `hLogLip ⟹` full continuity.

This is pure axiom-free analysis: dividing `hLogLip` by `n` and using `d(0,n·v) = n·d(0,v)`, the
`n`-family `β ↦ −log⟨φ₀φ_{nv}⟩/n` is `(K·d(0,v))`-Lipschitz uniformly in `n`, so its infimum (the
directional rate × `d(0,v)`) is too (`abs_csInf_range_sub_csInf_range_le`); dividing by `d(0,v) ≥ 1`
gives the directional rate `K`-Lipschitz uniformly in `v`, discharging `hLip`.

`hLogLip` does **not** discharge anything — it is the genuine remaining Ornstein–Zernike ingredient,
now stated in its literal GJ p.312 form (the natural target for a §18 random-walk path-sum
representation of `∂_β log⟨φ₀φ_x⟩`, which bounds the log-derivative by the path length
`∼ d(0,x)` directly).  It is a hypothesis, not an axiom; the theorem is axiom-free.

References:

* Glimm--Jaffe, *Quantum Physics* (2nd ed.), §17.5 Theorem 17.5.1, p.~312.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems* (2017), §3.7.3.
-/

namespace IsingModel
namespace Ambient

open Set

variable {d : ℕ}

/-- Boundedness below (by `0`) of the `n`-family `n ↦ −log⟨φ₀φ_{nv}⟩/n` at positive `β`. -/
theorem directionalLogCorr_div_range_bddBelow {J γ : ℝ} (hJ : 0 < J) (hγ : 0 < γ)
    (v : Fin d → ℤ) :
    BddBelow (Set.range fun n : ↥(Set.Ici (1 : ℕ)) =>
      directionalLogCorr J γ v (n : ℕ) / ((n : ℕ) : ℝ)) := by
  refine ⟨0, ?_⟩
  rintro x ⟨n, rfl⟩
  exact div_nonneg (directionalLogCorr_nonneg hJ hγ v _) (Nat.cast_nonneg _)

/-- **GJ Theorem 17.5.1 (continuity of the true mass), gated on the literal GJ p.312 per-pair
log-Lipschitz estimate.**  Given `hLogLip` — on each compact subinterval `[β₁,β₂]` of the window, a
single constant `K` such that for **every** ray point `n·v` (`v ≠ 0`, `n ≥ 1`) the two-point
log-correlation is `(K · n · d(0,v))`-Lipschitz in `β` (the β-log-derivative bounded linearly in the
separation `d(0,n·v) = n·d(0,v)`, GJ p.312) — the true mass `β ↦ latticeMass d (cubicExhaustion d)
⟨J,0,β⟩` is `ContinuousOn` the window.

This relocates the gate of #4402 from the Fekete-limit directional rate onto the book-faithful
per-pair estimate; `hLogLip` is the genuine remaining Ornstein–Zernike ingredient (a hypothesis, not
an axiom).  Proof: divide by `n` and by `d(0,v) ≥ 1`, then `abs_csInf_range_sub_csInf_range_le`. -/
theorem latticeMass_continuousOn_window_of_uniform_log_lipschitz {J : ℝ} (hJ : 0 < J) {d : ℕ}
    (hd : 1 ≤ d)
    (hLogLip : ∀ β₁ β₂ : ℝ, 0 < β₁ → β₁ ≤ β₂ → β₂ < 1 / (J * ↑(2 * d)) →
      ∃ K : ℝ, ∀ v : {v : Fin d → ℤ // v ≠ 0}, ∀ n : ↥(Set.Ici (1 : ℕ)),
        ∀ β ∈ Set.Icc β₁ β₂, ∀ β' ∈ Set.Icc β₁ β₂,
        |directionalLogCorr J β' v.1 (n : ℕ) - directionalLogCorr J β v.1 (n : ℕ)|
          ≤ K * (((n : ℕ) : ℝ) * (latticeDistance d 0 v.1 : ℝ)) * |β' - β|) :
    ContinuousOn (fun β => latticeMass d (Ambient.cubicExhaustion d) (⟨J, 0, β⟩ : IsingParams ℝ))
      (Set.Ioo (0 : ℝ) (1 / (J * ↑(2 * d)))) := by
  haveI : Nonempty ↥(Set.Ici (1 : ℕ)) := ⟨⟨1, le_refl 1⟩⟩
  refine latticeMass_continuousOn_window_of_uniform_lipschitz hJ hd (fun β₁ β₂ h1 h12 h2 => ?_)
  obtain ⟨K, hK⟩ := hLogLip β₁ β₂ h1 h12 h2
  refine ⟨K, fun v β hβ β' hβ' => ?_⟩
  have hβ0 : 0 < β := lt_of_lt_of_le h1 hβ.1
  have hβ'0 : 0 < β' := lt_of_lt_of_le h1 hβ'.1
  have hd0 : (0 : ℝ) < (latticeDistance d 0 v.1 : ℝ) := by
    have hne : latticeDistance d 0 v.1 ≠ 0 := fun h =>
      v.2 (((latticeDistance_eq_zero_iff d 0 v.1).mp h).symm)
    exact_mod_cast Nat.pos_of_ne_zero hne
  -- the `n`-family is `(K · d(0,v))`-Lipschitz uniformly in `n`.
  have hper : ∀ n : ↥(Set.Ici (1 : ℕ)),
      |directionalLogCorr J β' v.1 (n : ℕ) / ((n : ℕ) : ℝ)
          - directionalLogCorr J β v.1 (n : ℕ) / ((n : ℕ) : ℝ)|
        ≤ K * (latticeDistance d 0 v.1 : ℝ) * |β' - β| := by
    intro n
    have hn1 : (1 : ℝ) ≤ ((n : ℕ) : ℝ) := by exact_mod_cast n.2
    have hn0 : (0 : ℝ) < ((n : ℕ) : ℝ) := lt_of_lt_of_le one_pos hn1
    rw [div_sub_div_same, abs_div, abs_of_pos hn0, div_le_iff₀ hn0]
    calc |directionalLogCorr J β' v.1 (n : ℕ) - directionalLogCorr J β v.1 (n : ℕ)|
        ≤ K * (((n : ℕ) : ℝ) * (latticeDistance d 0 v.1 : ℝ)) * |β' - β| := hK v n β hβ β' hβ'
      _ = K * (latticeDistance d 0 v.1 : ℝ) * |β' - β| * ((n : ℕ) : ℝ) := by ring
  have hinf := abs_csInf_range_sub_csInf_range_le
    (fa := fun n : ↥(Set.Ici (1 : ℕ)) => directionalLogCorr J β v.1 (n : ℕ) / ((n : ℕ) : ℝ))
    (fb := fun n : ↥(Set.Ici (1 : ℕ)) => directionalLogCorr J β' v.1 (n : ℕ) / ((n : ℕ) : ℝ))
    (directionalLogCorr_div_range_bddBelow hJ hβ0 v.1)
    (directionalLogCorr_div_range_bddBelow hJ hβ'0 v.1) hper
  -- divide the infimum bound by `d(0,v)`.
  rw [directionalRateFn, directionalRateFn, div_sub_div_same, abs_div, abs_of_pos hd0,
    div_le_iff₀ hd0]
  refine hinf.trans (le_of_eq ?_)
  ring

end Ambient
end IsingModel
