import IsingModel.ClusterExpansion.MayerCore.CubicMayerClusterFreeEnergyComplex
import IsingModel.ClusterExpansion.MayerCore.MayerIdentityPersiteKP
import IsingModel.ClusterExpansion.MayerCore.PolymerFreeEnergy
import IsingModel.ClusterExpansion.MayerCore.LatticeFreeEnergyInfiniteKPBound
import Mathlib.Analysis.SpecialFunctions.Artanh

/-!
# Real-axis convergence of the per-site complex cluster free energy (GJ §18.6)

This is PR-D2.3c of issue #4149 (§18.6).  We show that, along the cubic exhaustion of `ℤ^d`,
the per-site complex cluster free energy `cubicMayerClusterFreeEnergyComplex d n` evaluated at a
**real** activity `t ∈ Ioo 0 T` converges to a real limit
`cubicInfiniteClusterFreeEnergyReal d t`.  This pins the interval-wise real-axis values of the
Montel limit (the holomorphic limit of the locally bounded family from PR-D2.3b), which is the
input to the identity-theorem step (PR-D2.3d).

The chain of identifications is:

* On the real axis `↑t`, the complex per-site cluster free energy equals (the cast of) the real
  per-site polymer free energy `polymerFreeEnergy G_n t / (cubicBox d n).card`, via
  `Complex.ofReal_tsum`, `mayerExpansionTermComplex_ofReal`, and the volume-uniform per-site
  Kotecky--Preiss Mayer--Montroll identity
  `polymerFreeEnergy_eq_tsum_mayerExpansionTerm_of_persite_kp`
  (#4152) with the actual maximum degree KP hypotheses discharged from the `2d` ones.
* Setting the coupling `J := artanh t` (with `β = 1`, `h = 0`), the high-temperature free-energy
  decomposition `freeEnergy_eq_polymerFreeEnergy` (with `tanh (1 · artanh t) = t`,
  `Real.tanh_artanh`)
  rewrites `polymerFreeEnergy G_n t / card` as
  `freeEnergy G_n ⟨artanh t, 0, 1⟩ − log 2 − (edge density)_n · log (cosh (artanh t))`.
* `freeEnergy G_n ⟨artanh t, 0, 1⟩` converges to the infinite-volume free energy
  (`freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_tendsto`, ferromagnetic since
  `0 ≤ artanh t`); the edge density converges to `d`
  (`tendsto_inducedLatticeGraph_cubicBox_edgeDensity`).

## Main definitions and results

* `cubicInfiniteClusterFreeEnergyReal` — the real limit.
* `cubicMayerClusterFreeEnergyComplex_ofReal_eq` — real-axis evaluation as a cast of the per-site
  polymer free energy.
* `cubicMayerClusterFreeEnergyComplex_tendsto_realAxis` — the headline real-axis convergence.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.6 (cluster expansion, analyticity).
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems*, §5.4 (Kotecky--Preiss criterion).
-/

namespace IsingModel

open Ambient Filter Topology

/-- **Real-axis limit of the per-site cluster free energy (GJ §18.6).**
At a real activity `t`, the infinite-volume per-site cluster free energy is the infinite-volume
free-energy density with coupling `J = artanh t` (field `h = 0`, inverse temperature `β = 1`)
minus the trivial single-site contribution `log 2` and the bond contribution
`d · log (cosh (artanh t))`.  Here `tanh (1 · artanh t) = t` for `t ∈ Ioo (-1) 1`, so the
underlying activity is exactly `t`. -/
noncomputable def cubicInfiniteClusterFreeEnergyReal (d : ℕ) (t : ℝ) : ℝ :=
  Ambient.freeEnergyInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
      (⟨Real.artanh t, 0, 1⟩ : IsingParams ℝ)
    - Real.log 2 - (d : ℝ) * Real.log (Real.cosh (Real.artanh t))

/-- **Real-axis evaluation of the per-site complex cluster free energy (GJ §18.6).**
For a real activity `t ∈ Ico 0 T` in the per-site Kotecky--Preiss region at radius `T`
(`(2d)²eT < 1` and `4·(2d)²eT/(1−(2d)²eT)² < 1`),
`cubicMayerClusterFreeEnergyComplex d n (↑t)` equals the cast of the per-site real polymer free
energy `polymerFreeEnergy G_n t / (cubicBox d n).card`, where
`G_n = inducedGraph (latticeGraph d) (cubicBox d n)`.

Proof: push `Complex.ofReal_tsum` and `mayerExpansionTermComplex_ofReal` through the numerator to
land on `↑(∑'_k mayerExpansionTerm G_n k t)`, then apply the volume-uniform per-site KP identity
`polymerFreeEnergy_eq_tsum_mayerExpansionTerm_of_persite_kp` (#4152) — its actual maximum-degree
KP hypotheses are discharged from the `2d` ones via `induced_latticeGraph_maxDegree_le` and
`kpRegion_downward_closed`.  Finally `↑x / ↑card = ↑(x / card)` (`Complex.ofReal_div`,
`Complex.ofReal_natCast`, `Fintype.card_coe`). -/
theorem cubicMayerClusterFreeEnergyComplex_ofReal_eq (d n : ℕ) {T : ℝ} (hT : 0 < T)
    (hkp2dT : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T) < 1)
    (hρ2dT : 4 * (((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T))
        / (1 - ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T)) ^ 2 < 1)
    {t : ℝ} (ht : t ∈ Set.Ico 0 T) :
    cubicMayerClusterFreeEnergyComplex d n (↑t)
      = ((polymerFreeEnergy
          (Ambient.inducedGraph (latticeGraph d) (cubicBox d n)) t
          / ((cubicBox d n).card : ℝ) : ℝ) : ℂ) := by
  classical
  haveI : Nonempty (↑(cubicBox d n) : Type _) := (cubicBox_nonempty d n).to_subtype
  set G := Ambient.inducedGraph (latticeGraph d) (cubicBox d n) with hG
  -- Discharge the actual-maximum-degree KP hypotheses from the `2d` ones.
  have hΔ : G.maxDegree ≤ 2 * d := induced_latticeGraph_maxDegree_le d (cubicBox d n)
  have heT : (0 : ℝ) ≤ Real.exp 1 * T := by positivity
  have h0 : (0 : ℝ) ≤ (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * T) := by positivity
  have h12 : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * T)
      ≤ ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T) := by
    apply mul_le_mul_of_nonneg_right _ heT
    have hcast : (G.maxDegree : ℝ) ≤ ((2 * d : ℕ) : ℝ) := by exact_mod_cast hΔ
    gcongr
  obtain ⟨hkpG, hρG⟩ := kpRegion_downward_closed h0 h12 hkp2dT hρ2dT
  -- The volume-uniform per-site KP Mayer--Montroll identity (#4152) at `t`.
  have hident : polymerFreeEnergy G t = ∑' k : ℕ, mayerExpansionTerm G k t :=
    polymerFreeEnergy_eq_tsum_mayerExpansionTerm_of_persite_kp G hT hkpG hρG ht
  -- Cast the real numerator into the complex Mayer numerator.
  have hnum : (∑' k : ℕ, mayerExpansionTermComplex G k (↑t))
      = ((polymerFreeEnergy G t : ℝ) : ℂ) := by
    rw [hident, Complex.ofReal_tsum]
    exact tsum_congr fun k => mayerExpansionTermComplex_ofReal G k t
  -- Unfold the per-site complex free energy and push the cast through the division.
  unfold cubicMayerClusterFreeEnergyComplex
  rw [hnum, ← Complex.ofReal_natCast (cubicBox d n).card, ← Complex.ofReal_div]

/-- **Real-axis convergence of the per-site complex cluster free energy (GJ §18.6).**
For a real activity `t ∈ Ioo 0 T` with `T ≤ 1` in the per-site Kotecky--Preiss region at radius
`T`, the per-site complex cluster free energy evaluated at `↑t` converges, as the cubic box grows,
to the real limit `cubicInfiniteClusterFreeEnergyReal d t` (cast to `ℂ`).

Proof: first establish the **real** convergence of
`polymerFreeEnergy G_n t / (cubicBox d n).card`.  Using
`freeEnergy_eq_polymerFreeEnergy` with `J = artanh t`, `β = 1` (so `0 ≤ 1 · artanh t` since
`0 ≤ artanh t` by `Real.artanh_nonneg`, and `tanh (1 · artanh t) = t` by `Real.tanh_artanh`,
valid because `t ∈ Ioo 0 T ⊆ Ioo (-1) 1` using `T ≤ 1`), this per-site polymer free energy equals
`freeEnergy G_n ⟨artanh t, 0, 1⟩ − log 2 − (edge density)_n · log (cosh (artanh t))`.
The free energy converges to the infinite-volume value
(`freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_tendsto`, ferromagnetic), and the edge
density to `d` (`tendsto_inducedLatticeGraph_cubicBox_edgeDensity`), so the combination converges
to `cubicInfiniteClusterFreeEnergyReal d t`.  Finally push through `Complex.continuous_ofReal` and
rewrite the complex sequence by `cubicMayerClusterFreeEnergyComplex_ofReal_eq`. -/
theorem cubicMayerClusterFreeEnergyComplex_tendsto_realAxis (d : ℕ) {T : ℝ} (hT : 0 < T)
    (hT1 : T ≤ 1)
    (hkp2dT : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T) < 1)
    (hρ2dT : 4 * (((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T))
        / (1 - ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T)) ^ 2 < 1)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 T) :
    Filter.Tendsto (fun n => cubicMayerClusterFreeEnergyComplex d n (↑t : ℂ))
      Filter.atTop (nhds ((cubicInfiniteClusterFreeEnergyReal d t : ℝ) : ℂ)) := by
  classical
  rw [Set.mem_Ioo] at ht
  -- `t ∈ Ico 0 T` (for the real-axis evaluation lemma) and `t ∈ Ioo (-1) 1` (for `tanh_artanh`).
  have htIco : t ∈ Set.Ico 0 T := Set.mem_Ico.mpr ⟨ht.1.le, ht.2⟩
  have htIoo11 : t ∈ Set.Ioo (-1 : ℝ) 1 :=
    Set.mem_Ioo.mpr ⟨by linarith [ht.1], by linarith [ht.2, hT1]⟩
  -- Coupling `J = artanh t`, with `0 ≤ J` (ferromagnetic) and `tanh (1 · J) = t`.
  set J := Real.artanh t with hJdef
  have hJnn : 0 ≤ J := Real.artanh_nonneg ht.1.le
  have htanh : Real.tanh (1 * J) = t := by
    rw [one_mul, hJdef]; exact Real.tanh_artanh htIoo11
  set c := Real.log (Real.cosh J) with hcdef
  -- Stage rewrite of the per-site real polymer free energy.
  -- `polymerFreeEnergy G_n t / card = freeEnergy G_n ⟨J,0,1⟩ − log 2 − (edge density)_n · c`.
  have hstage : ∀ n : ℕ,
      polymerFreeEnergy (Ambient.inducedGraph (latticeGraph d) (cubicBox d n)) t
          / ((cubicBox d n).card : ℝ)
        = IsingModel.freeEnergy
            (Ambient.inducedGraph (latticeGraph d) (cubicBox d n)) ⟨J, 0, 1⟩
          - Real.log 2
          - (((Ambient.inducedGraph (latticeGraph d) (cubicBox d n)).edgeFinset.card : ℝ)
              / ((cubicBox d n).card : ℝ)) * c := by
    intro n
    haveI : Nonempty (↑(cubicBox d n) : Type _) := (cubicBox_nonempty d n).to_subtype
    set G := Ambient.inducedGraph (latticeGraph d) (cubicBox d n) with hG
    have hne : 0 < Fintype.card (↑(cubicBox d n) : Type _) := Fintype.card_pos
    have hcard : (Fintype.card (↑(cubicBox d n) : Type _) : ℝ) = ((cubicBox d n).card : ℝ) := by
      rw [Fintype.card_coe]
    -- The high-temperature decomposition with `J`, `β = 1`.
    have hdecomp := freeEnergy_eq_polymerFreeEnergy G J 1 (by simpa using hJnn) hne
    rw [htanh, one_mul] at hdecomp
    -- Solve for `polymerFreeEnergy G t / card`.
    rw [hcard] at hdecomp
    rw [hcdef]
    -- `freeEnergy = log2 + edgeDensity·c + polymerFreeEnergy/card`  ⟹  rearrange.
    linarith [hdecomp]
  -- REAL tendsto of the per-site polymer free energy.
  have hfreeTendsto :
      Filter.Tendsto (fun n => IsingModel.freeEnergy
          (Ambient.inducedGraph (latticeGraph d) (cubicBox d n)) ⟨J, 0, 1⟩)
        Filter.atTop
        (nhds (Ambient.freeEnergyInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
          (⟨J, 0, 1⟩ : IsingParams ℝ))) := by
    have hferro : Ferromagnetic (⟨J, 0, 1⟩ : IsingParams ℝ) :=
      ⟨hJnn, le_refl 0, one_pos⟩
    have htend := freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_tendsto d
      (⟨J, 0, 1⟩ : IsingParams ℝ) hferro
    -- Rewrite the stage sequence to `freeEnergy (inducedGraph ...)`.
    refine htend.congr ?_
    intro n
    rw [freeEnergyAlongExhaustion_apply, freeEnergyΛ_apply]
    rfl
  have hdensTendsto :
      Filter.Tendsto (fun n =>
        ((Ambient.inducedGraph (latticeGraph d) (cubicBox d n)).edgeFinset.card : ℝ)
          / ((cubicBox d n).card : ℝ))
        Filter.atTop (nhds (d : ℝ)) :=
    tendsto_inducedLatticeGraph_cubicBox_edgeDensity d
  -- Combine into the real per-site polymer free-energy convergence.
  have hrealTendsto :
      Filter.Tendsto (fun n =>
        polymerFreeEnergy (Ambient.inducedGraph (latticeGraph d) (cubicBox d n)) t
          / ((cubicBox d n).card : ℝ))
        Filter.atTop (nhds (cubicInfiniteClusterFreeEnergyReal d t)) := by
    have hcomb := ((hfreeTendsto.sub (tendsto_const_nhds (x := Real.log 2))).sub
      (hdensTendsto.mul_const c))
    -- `cubicInfiniteClusterFreeEnergyReal d t = freeEnergyInfinite − log2 − d·c`
    -- holds definitionally (`J`, `c` are the `set` abbreviations).
    have hlim : cubicInfiniteClusterFreeEnergyReal d t
        = Ambient.freeEnergyInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
            (⟨J, 0, 1⟩ : IsingParams ℝ) - Real.log 2 - (d : ℝ) * c := rfl
    rw [hlim]
    refine hcomb.congr ?_
    intro n
    rw [hstage n]
  -- Push through `Complex.ofReal` and rewrite the complex sequence on the real axis.
  have hcomplexTendsto :
      Filter.Tendsto (fun n =>
        ((polymerFreeEnergy (Ambient.inducedGraph (latticeGraph d) (cubicBox d n)) t
          / ((cubicBox d n).card : ℝ) : ℝ) : ℂ))
        Filter.atTop (nhds ((cubicInfiniteClusterFreeEnergyReal d t : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.continuousAt.tendsto).comp hrealTendsto
  refine hcomplexTendsto.congr ?_
  intro n
  exact (cubicMayerClusterFreeEnergyComplex_ofReal_eq d n hT hkp2dT hρ2dT htIco).symm

end IsingModel
