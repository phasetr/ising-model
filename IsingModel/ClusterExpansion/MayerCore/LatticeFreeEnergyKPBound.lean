import IsingModel.ClusterExpansion.MayerCore.MayerIdentityPersiteKP
import IsingModel.ClusterExpansion.MayerTsumPerSiteAmbient
import IsingModel.ClusterExpansion.MayerTermTailSummability

/-!
# Volume-uniform per-site free-energy bound on the lattice (GJ §18.6)

This is PR-D1 of issue #4149 (§18.6).  It composes two volume-uniform ingredients:

* the **per-site Kotecky--Preiss Mayer--Montroll identity**
  `polymerFreeEnergy_eq_tsum_mayerExpansionTerm_of_persite_kp` (#4152), which rewrites the
  polymer free energy of a finite graph as the convergent Mayer series on the volume-uniform
  Kotecky--Preiss interval `Ico 0 T`;
* the **volume-uniform per-site Mayer bound** `latticeGraph_kp_tsum_per_site_le` (#4148), which
  bounds the per-site total absolute Mayer expansion sum by `kpBound (2 d) t`, a constant
  independent of the finite volume `Λ`.

The free-energy decomposition `freeEnergy_eq_polymerFreeEnergy` (Step 612) writes the lattice
free energy as `log 2 + (|E|/|Λ|)·log cosh(βJ) + polymerFreeEnergy G (tanh βJ) / |Λ|`.  Shifting
the Mayer series to drop its vanishing `n = 0` term (`mayerExpansionTerm_zero`) and bounding the
norm of the tsum by the tsum of norms (`norm_tsum_le_tsum_norm`), the deviation of the free
energy from the explicit `log 2 + (|E|/|Λ|)·log cosh(βJ)` part is bounded by
`kpBound (2 d) (tanh βJ)`, a constant **independent of the volume** `Λ`.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.5--§18.6, pp.~335--340.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems*, §5.4
  (Theorem 5.4, the Kotecky--Preiss criterion).
-/

namespace IsingModel

open Finset

/-- **Volume-uniform per-site free-energy deviation bound on the lattice** (GJ §18.6).  For the
lattice graph `latticeGraph d` induced on an arbitrary finite volume `Λ`, at zero external field
with ferromagnetic coupling `0 ≤ J` and inverse temperature `0 < β`, the deviation of the free
energy from its explicit `log 2 + (|E|/|Λ|)·log cosh(βJ)` part is bounded by
`kpBound (2 d) (tanh βJ)`, a constant **independent of the volume** `Λ`.

The Kotecky--Preiss hypotheses are stated at a volume-uniform radius `T` with `tanh(βJ) < T`:
`(2d)²·e·T < 1` and `4·(2d)²eT/(1−(2d)²eT)² < 1`.  Since `tanh(βJ) ∈ Ico 0 T`, the per-site
Mayer--Montroll identity (#4152) rewrites `polymerFreeEnergy G (tanh βJ)` as the convergent Mayer
series, whose shifted (`n ≥ 1`) tail is bounded per site by `kpBound (2 d) (tanh βJ)` (#4148).

Proof outline: discharge the identity's and bound's Kotecky--Preiss hypotheses (stated at
`G.maxDegree` resp. `t = tanh βJ`) from the `2 d` resp. `T` ones via
`induced_latticeGraph_maxDegree_le` and the downward closure `kpRegion_downward_closed`; rewrite
the free energy via `freeEnergy_eq_polymerFreeEnergy`; replace the polymer free energy by the
Mayer tsum, shift away the vanishing `n = 0` term (`Summable.tsum_eq_zero_add`,
`mayerExpansionTerm_zero`), and bound `‖∑'‖ ≤ ∑'‖·‖` (`norm_tsum_le_tsum_norm`) before dividing
by the positive site count. -/
theorem latticeGraph_freeEnergy_deviation_le_kpBound
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) [Nonempty (↑Λ : Type _)]
    {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    {T : ℝ} (hT : 0 < T)
    (hkp2dT : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T) < 1)
    (hρ2dT : 4 * (((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T))
        / (1 - ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T)) ^ 2 < 1)
    (htanh : Real.tanh (β * J) < T) :
    |freeEnergy (Ambient.inducedGraph (latticeGraph d) Λ) (⟨J, 0, β⟩ : IsingParams ℝ)
        - (Real.log 2
            + ((Ambient.inducedGraph (latticeGraph d) Λ).edgeFinset.card : ℝ)
                / Fintype.card (↑Λ : Type _) * Real.log (Real.cosh (β * J)))|
      ≤ kpBound (2 * d) (Real.tanh (β * J)) := by
  classical
  set G := Ambient.inducedGraph (latticeGraph d) Λ with hG
  set t : ℝ := Real.tanh (β * J) with ht
  -- Basic positivity / membership facts.
  have hβJ : 0 ≤ β * J := mul_nonneg hβ.le hJ
  have htnn : 0 ≤ t := by rw [ht]; exact real_tanh_nonneg hβJ
  have htabs : |t| = t := abs_of_nonneg htnn
  have hne : 0 < Fintype.card (↑Λ : Type _) := Fintype.card_pos
  have hcardpos : (0 : ℝ) < (Fintype.card (↑Λ : Type _) : ℝ) := by exact_mod_cast hne
  have ht_mem : t ∈ Set.Ico 0 T := ⟨htnn, by rw [ht]; exact htanh⟩
  -- `e·T ≥ 0`.
  have heT : (0 : ℝ) ≤ Real.exp 1 * T := by positivity
  -- STEP A: discharge the identity's KP hypotheses (stated at `G.maxDegree`, radius `T`).
  have hΔ : G.maxDegree ≤ 2 * d := induced_latticeGraph_maxDegree_le d Λ
  have hΔcast : (G.maxDegree : ℝ) ≤ ((2 * d : ℕ) : ℝ) := by exact_mod_cast hΔ
  have h12T : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * T)
      ≤ ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T) := by
    apply mul_le_mul_of_nonneg_right _ heT
    gcongr
  have h0T : (0 : ℝ) ≤ (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * T) := by positivity
  obtain ⟨hkpG_T, hρG_T⟩ := kpRegion_downward_closed h0T h12T hkp2dT hρ2dT
  have hid : polymerFreeEnergy G t = ∑' n : ℕ, mayerExpansionTerm G n t :=
    polymerFreeEnergy_eq_tsum_mayerExpansionTerm_of_persite_kp G hT hkpG_T hρG_T ht_mem
  -- STEP B: discharge #4148's KP hypotheses at `t` from the `T` ones (via `|t| = t < T`).
  have h12t : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * |t|)
      ≤ ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T) := by
    rw [htabs]
    have : Real.exp 1 * t ≤ Real.exp 1 * T :=
      mul_le_mul_of_nonneg_left (le_of_lt ht_mem.2) (Real.exp_pos 1).le
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have h0t : (0 : ℝ) ≤ ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * |t|) := by positivity
  obtain ⟨hkp2dt, hρ2dt⟩ := kpRegion_downward_closed h0t h12t hkp2dT hρ2dT
  have hbound :
      (∑' n : ℕ, |mayerExpansionTerm G (n + 1) t|) / (Fintype.card (↑Λ : Type _) : ℝ)
        ≤ kpBound (2 * d) t :=
    latticeGraph_kp_tsum_per_site_le d Λ hkp2dt hρ2dt
  -- STEP C: the per-graph (maxDegree) KP hypotheses at `t`, for the summability lemmas.
  have h12tG : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)
      ≤ ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * |t|) := by
    have habs : (0 : ℝ) ≤ Real.exp 1 * |t| := by positivity
    apply mul_le_mul_of_nonneg_right _ habs
    gcongr
  have h0tG : (0 : ℝ) ≤ (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) := by positivity
  obtain ⟨hkpGt, hρGt⟩ := kpRegion_downward_closed h0tG h12tG hkp2dt hρ2dt
  -- Summability of the shifted absolute series and of the full series.
  have hsucc : Summable fun n : ℕ => |mayerExpansionTerm G (n + 1) t| :=
    summable_abs_mayerExpansionTerm_succ_of_tail_condition G hkpGt hρGt
  have hsum : Summable fun n : ℕ => mayerExpansionTerm G n t :=
    (summable_abs_mayerExpansionTerm_of_tail_condition G hkpGt hρGt).of_abs
  -- STEP D: shift the Mayer series to drop the vanishing `n = 0` term.
  have hshift : (∑' n : ℕ, mayerExpansionTerm G n t)
      = ∑' n : ℕ, mayerExpansionTerm G (n + 1) t := by
    rw [hsum.tsum_eq_zero_add, mayerExpansionTerm_zero, zero_add]
  -- STEP E: bound the norm of the tsum by the tsum of norms.
  have habs : |∑' n : ℕ, mayerExpansionTerm G n t|
      ≤ ∑' n : ℕ, |mayerExpansionTerm G (n + 1) t| := by
    rw [hshift]
    have hnorm := norm_tsum_le_tsum_norm
      (f := fun n : ℕ => mayerExpansionTerm G (n + 1) t)
      (by simpa only [Real.norm_eq_abs] using hsucc)
    simpa only [Real.norm_eq_abs] using hnorm
  -- STEP F: rewrite the free energy and isolate the polymer-free-energy summand.
  rw [freeEnergy_eq_polymerFreeEnergy G J β hβJ hne, ← ht]
  rw [show Real.log 2
        + ((G.edgeFinset.card : ℝ) / Fintype.card (↑Λ : Type _) * Real.log (Real.cosh (β * J)))
        + polymerFreeEnergy G t / (Fintype.card (↑Λ : Type _) : ℝ)
        - (Real.log 2
            + (G.edgeFinset.card : ℝ) / Fintype.card (↑Λ : Type _)
                * Real.log (Real.cosh (β * J)))
      = polymerFreeEnergy G t / (Fintype.card (↑Λ : Type _) : ℝ) by ring]
  rw [hid, abs_div, abs_of_pos hcardpos]
  -- `|∑'| / card ≤ (∑' |·(n+1)|) / card ≤ kpBound`.
  refine le_trans ?_ hbound
  gcongr

end IsingModel
