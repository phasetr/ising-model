import IsingModel.ClusterExpansion.MayerCore.CubicMayerClusterLimit
import IsingModel.ClusterExpansion.RegularityHZero
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Artanh

/-!
# Infinite-volume coupling analyticity at high temperature (GJ §18.6 capstone)

The capstone of the Glimm--Jaffe §18.6 cluster-expansion programme: the infinite-volume
free-energy density of the ferromagnetic Ising model on the cubic lattice `ℤ^d`, viewed as a
function of the inverse temperature `β` (equivalently the coupling at fixed temperature), is
**real-analytic** at high temperature (small `tanh (β J)`).

## Strategy

* **P1 — scaling** (`freeEnergyInfinite_scaling`): at zero external field the Boltzmann weight
  depends on `(J, β)` only through the product `β · J`, hence
  `freeEnergyInfinite G Λ ⟨J, 0, β⟩ = freeEnergyInfinite G Λ ⟨β J, 0, 1⟩`.
* **P2 — bridge identity** (`freeEnergyInfinite_latticeGraph_cubicExhaustion_eq_cluster_of_tanh`):
  rewriting the definition of `cubicInfiniteClusterFreeEnergyReal` via `Real.artanh_tanh`,
  `freeEnergyInfinite ⟨c, 0, 1⟩ = log 2 + d · log (cosh c) + cubicInfiniteClusterFreeEnergyReal d
  (tanh c)`.
* **P3 — `f_∞` real-analyticity** (`cubicInfiniteClusterFreeEnergyReal_analyticOnNhd`): the real
  cluster free energy is real-analytic on `Ioo 0 T`, obtained as the real part of the holomorphic
  whole-sequence limit `F_∞` (D2.3d) restricted to the real axis.
* **P4 — capstone**: compose P1, P2, P3 with the analyticity of `log ∘ cosh` and `tanh`.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.6 (cluster expansion, analyticity).
-/

namespace IsingModel

open Ambient Filter Topology

/-! ## P1 — Zero-field `β · J` scaling -/

/-- **Boltzmann-weight scaling at zero field**: with `h = 0` the Boltzmann weight depends on the
coupling `J` and inverse temperature `β` only through their product `β · J`, so
`boltzmannWeight G ⟨J, 0, β⟩ σ = boltzmannWeight G ⟨β J, 0, 1⟩ σ`.  Both equal
`exp (β J · ∑_{e} σ_e)` since `-β · H_{⟨J,0,β⟩}(σ) = β J · (edge spin sum)` and
`-1 · H_{⟨βJ,0,1⟩}(σ) = β J · (edge spin sum)`, the field terms vanishing at `h = 0`. -/
theorem boltzmannWeight_scaling {ι : Type*} [Fintype ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℝ) (σ : Config ι) :
    boltzmannWeight G (⟨J, 0, β⟩ : IsingParams ℝ) σ
      = boltzmannWeight G (⟨β * J, 0, 1⟩ : IsingParams ℝ) σ := by
  simp only [boltzmannWeight, hamiltonian, interactionEnergy, externalFieldEnergy]
  congr 1
  ring

/-- **Partition-function scaling at zero field**: summing `boltzmannWeight_scaling` over all
configurations, `partitionFunction G ⟨J, 0, β⟩ = partitionFunction G ⟨β J, 0, 1⟩`. -/
theorem partitionFunction_scaling {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℝ) :
    partitionFunction G (⟨J, 0, β⟩ : IsingParams ℝ)
      = partitionFunction G (⟨β * J, 0, 1⟩ : IsingParams ℝ) := by
  unfold partitionFunction
  exact Finset.sum_congr rfl fun σ _ => boltzmannWeight_scaling G J β σ

/-- **Free-energy scaling at zero field** (finite graph): since the partition function is unchanged
and the per-site normalisation `(card ι)⁻¹` does not depend on the parameters,
`freeEnergy G ⟨J, 0, β⟩ = freeEnergy G ⟨β J, 0, 1⟩`. -/
theorem freeEnergy_scaling {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℝ) :
    freeEnergy G (⟨J, 0, β⟩ : IsingParams ℝ)
      = freeEnergy G (⟨β * J, 0, 1⟩ : IsingParams ℝ) := by
  unfold freeEnergy
  rw [partitionFunction_scaling G J β]

/-- **`freeEnergyΛ` scaling at zero field**: lift of `freeEnergy_scaling` through
`freeEnergyΛ = freeEnergy (inducedGraph G Λ)`. -/
theorem freeEnergyΛ_scaling {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (Ambient.inducedGraph G Λ).edgeSet] (J β : ℝ) :
    Ambient.freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      = Ambient.freeEnergyΛ G Λ (⟨β * J, 0, 1⟩ : IsingParams ℝ) := by
  simp only [Ambient.freeEnergyΛ_apply]
  exact freeEnergy_scaling (Ambient.inducedGraph G Λ) J β

/-- **`freeEnergyAlongExhaustion` scaling at zero field** (pointwise): each stage of the exhaustion
sequence satisfies the `β · J` scaling. -/
theorem freeEnergyAlongExhaustion_scaling {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (Λ : Ambient.Exhaustion V)
    [∀ n, Fintype (Ambient.inducedGraph G (Λ.volume n)).edgeSet] (J β : ℝ) :
    Ambient.freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      = Ambient.freeEnergyAlongExhaustion G Λ (⟨β * J, 0, 1⟩ : IsingParams ℝ) := by
  funext n
  simp only [Ambient.freeEnergyAlongExhaustion_apply]
  exact freeEnergyΛ_scaling G (Λ.volume n) J β

/-- **P1 — infinite-volume free-energy scaling at zero field**: the limsup of the scaled stage
sequences agrees, so `freeEnergyInfinite G Λ ⟨J, 0, β⟩ = freeEnergyInfinite G Λ ⟨β J, 0, 1⟩`.

At `h = 0` the Boltzmann weight depends only on `β · J`, so each finite-volume free energy is
invariant under `(J, β) ↦ (β J, 1)` (`freeEnergyAlongExhaustion_scaling`); the `limsup` defining
the infinite-volume free energy then coincides. -/
theorem freeEnergyInfinite_scaling {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (Λ : Ambient.Exhaustion V)
    [∀ n, Fintype (Ambient.inducedGraph G (Λ.volume n)).edgeSet] (J β : ℝ) :
    Ambient.freeEnergyInfinite G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
      = Ambient.freeEnergyInfinite G Λ (⟨β * J, 0, 1⟩ : IsingParams ℝ) := by
  simp only [Ambient.freeEnergyInfinite_apply]
  rw [freeEnergyAlongExhaustion_scaling G Λ J β]

/-! ## P2 — Bridge to the cluster free energy -/

/-- **P2 — bridge identity**: for any real coupling `c`, the infinite-volume free energy of the
cubic Ising model at `⟨c, 0, 1⟩` decomposes as the trivial single-site term `log 2`, the bond term
`d · log (cosh c)`, and the per-site cluster free energy `cubicInfiniteClusterFreeEnergyReal d
(tanh c)`.

Unfolding `cubicInfiniteClusterFreeEnergyReal d (tanh c)` (which is
`freeEnergyInfinite ⟨artanh (tanh c), 0, 1⟩ − log 2 − d · log (cosh (artanh (tanh c)))`) and
applying `Real.artanh_tanh : artanh (tanh c) = c` gives the claim by rearrangement. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_eq_cluster_of_tanh (d : ℕ) (c : ℝ) :
    Ambient.freeEnergyInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨c, 0, 1⟩ : IsingParams ℝ)
      = Real.log 2 + (d : ℝ) * Real.log (Real.cosh c)
        + cubicInfiniteClusterFreeEnergyReal d (Real.tanh c) := by
  unfold cubicInfiniteClusterFreeEnergyReal
  rw [Real.artanh_tanh]
  ring

/-! ## P3 — Real-analyticity of the cluster free energy on `Ioo 0 T` -/

/-- **P3 — real-analyticity of `f_∞`**: the per-site real cluster free energy
`cubicInfiniteClusterFreeEnergyReal d` is real-analytic on the open interval `Ioo 0 T`.

Proof.  The whole-sequence Vitali limit `F_∞` (D2.3d,
`exists_cubicMayerClusterFreeEnergyComplex_limit`)
is holomorphic on `ball 0 R`, hence `AnalyticOnNhd ℂ F_∞ (ball 0 R)`
(`DifferentiableOn.analyticOnNhd` on the open ball).  Its real part along the real axis,
`fun t => (F_∞ ↑t).re`, is therefore `AnalyticOnNhd ℝ` on `Ioo (-R) R` via `AnalyticOnNhd.re_ofReal`
(using `ofReal '' Ioo (-R) R ⊆ ball 0 R`).  Restricting (`.mono`) to `Ioo 0 T ⊆ Ioo (-R) R`
(from `0 < T ≤ R`) and rewriting `(F_∞ ↑t).re = cubicInfiniteClusterFreeEnergyReal d t` on the open
`Ioo 0 T` (where `F_∞ ↑t = ↑(cubicInfiniteClusterFreeEnergyReal d t)`) via `AnalyticOnNhd.congr`
gives the result. -/
theorem cubicInfiniteClusterFreeEnergyReal_analyticOnNhd (d : ℕ) {R T : ℝ}
    (hR : 0 < R) (hT : 0 < T) (hTR : T ≤ R) (hT1 : T ≤ 1)
    (hkp2dR : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R) < 1)
    (hρ2dR : 4 * (((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R))
        / (1 - ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R)) ^ 2 < 1)
    (hkp2dT : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T) < 1)
    (hρ2dT : 4 * (((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T))
        / (1 - ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T)) ^ 2 < 1) :
    AnalyticOnNhd ℝ (fun t : ℝ => cubicInfiniteClusterFreeEnergyReal d t) (Set.Ioo 0 T) := by
  -- The whole-sequence Vitali limit `F_∞`.
  obtain ⟨F, hFdiff, _, hFreal⟩ :=
    exists_cubicMayerClusterFreeEnergyComplex_limit d hR hT hTR hT1 hkp2dR hρ2dR hkp2dT hρ2dT
  -- `F` is `AnalyticOnNhd ℂ` on the open ball.
  have hFanal : AnalyticOnNhd ℂ F (Metric.ball (0 : ℂ) R) :=
    hFdiff.analyticOnNhd Metric.isOpen_ball
  -- The image of `Ioo (-R) R` under `ofReal` lies in `ball 0 R`.
  have hsub : (Complex.ofReal '' Set.Ioo (-R) R) ⊆ Metric.ball (0 : ℂ) R := by
    rintro z ⟨t, ht, rfl⟩
    rw [Set.mem_Ioo] at ht
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_lt]
    exact ht
  -- The real part along the real axis is `AnalyticOnNhd ℝ` on `Ioo (-R) R`.
  have hRe : AnalyticOnNhd ℝ (fun t : ℝ => (F ↑t).re) (Set.Ioo (-R) R) :=
    (hFanal.mono hsub).re_ofReal
  -- `Ioo 0 T ⊆ Ioo (-R) R`.
  have hIooSub : Set.Ioo (0 : ℝ) T ⊆ Set.Ioo (-R) R := by
    intro t ht
    rw [Set.mem_Ioo] at ht ⊢
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  -- Restrict to `Ioo 0 T` and rewrite the real part as the real cluster free energy.
  refine ((hRe.mono hIooSub).congr isOpen_Ioo ?_)
  intro t ht
  have hval : F (↑t) = ((cubicInfiniteClusterFreeEnergyReal d t : ℝ) : ℂ) := hFreal t ht
  simp only [hval, Complex.ofReal_re]

/-! ## P4 — Capstone -/

/-- **P4 — GJ §18.6 infinite-volume coupling analyticity (capstone).**
At high temperature (`0 < β J` and `tanh (β J) < T` within the per-site Kotecky--Preiss radius `T`),
the infinite-volume free-energy density of the ferromagnetic cubic Ising model at zero external
field is real-analytic in the inverse temperature `β` (at coupling `J`).

Proof.  By the zero-field scaling `freeEnergyInfinite ⟨J, 0, β'⟩ = freeEnergyInfinite ⟨β' J, 0, 1⟩`
(P1) and the bridge identity (P2), the free energy equals
`log 2 + d · log (cosh (β' J)) + cubicInfiniteClusterFreeEnergyReal d (tanh (β' J))` as a function
of `β'`.  Each summand is `AnalyticAt ℝ` near `β`: the constant `log 2`; `d · log (cosh (β' J))` via
`Real.analyticAt_cosh`, `AnalyticAt.log` (using `Real.cosh_pos`), and the linear `β' ↦ β' J`; and
`cubicInfiniteClusterFreeEnergyReal d (tanh (β' J))` via P3 evaluated at `tanh (β J) ∈ Ioo 0 T`
(`0 < tanh (β J)` from `0 < β J`, `< T` from the hypothesis) composed with `analyticAt_real_tanh`
and `β' ↦ β' J`.  An `AnalyticAt.congr` rewrites back to the free-energy function. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_analyticAt_beta_h_zero
    (d : ℕ) {R T J β : ℝ}
    (hR : 0 < R) (hT : 0 < T) (hTR : T ≤ R) (hT1 : T ≤ 1)
    (hkp2dR : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R) < 1)
    (hρ2dR : 4 * (((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R))
        / (1 - ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R)) ^ 2 < 1)
    (hkp2dT : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T) < 1)
    (hρ2dT : 4 * (((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T))
        / (1 - ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T)) ^ 2 < 1)
    (hβJ_pos : 0 < β * J) (hβJ_tanh : Real.tanh (β * J) < T) :
    AnalyticAt ℝ (fun β' : ℝ => Ambient.freeEnergyInfinite (latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, 0, β'⟩ : IsingParams ℝ)) β := by
  -- The model function obtained from P1 + P2.
  set g : ℝ → ℝ := fun β' => Real.log 2 + (d : ℝ) * Real.log (Real.cosh (β' * J))
    + cubicInfiniteClusterFreeEnergyReal d (Real.tanh (β' * J)) with hg
  -- The free-energy function equals `g` everywhere (P1 + P2).
  have hcongr : (fun β' : ℝ => Ambient.freeEnergyInfinite (latticeGraph d)
      (Ambient.cubicExhaustion d) (⟨J, 0, β'⟩ : IsingParams ℝ)) = g := by
    funext β'
    rw [freeEnergyInfinite_scaling (latticeGraph d) (Ambient.cubicExhaustion d) J β',
      freeEnergyInfinite_latticeGraph_cubicExhaustion_eq_cluster_of_tanh d (β' * J)]
  rw [hcongr]
  -- The linear map `β' ↦ β' * J` is analytic at `β`, with value `β * J`.
  have hmul : AnalyticAt ℝ (fun β' : ℝ => β' * J) β := analyticAt_id.mul (analyticAt_const)
  have hmulval : (fun β' : ℝ => β' * J) β = β * J := rfl
  -- `log 2` is a constant.
  have h1 : AnalyticAt ℝ (fun _ : ℝ => Real.log 2) β := analyticAt_const
  -- `d * log (cosh (β' * J))` is analytic at `β`.
  have h2 : AnalyticAt ℝ (fun β' : ℝ => (d : ℝ) * Real.log (Real.cosh (β' * J))) β := by
    have hcosh : AnalyticAt ℝ (fun β' : ℝ => Real.cosh (β' * J)) β :=
      (Real.analyticAt_cosh (x := β * J)).comp_of_eq' hmul hmulval
    have hlog : AnalyticAt ℝ (fun β' : ℝ => Real.log (Real.cosh (β' * J))) β :=
      hcosh.log (Real.cosh_pos (β * J))
    exact analyticAt_const.mul hlog
  -- `tanh (β * J) ∈ Ioo 0 T`.
  have htanhpos : 0 < Real.tanh (β * J) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr hβJ_pos) (Real.cosh_pos (β * J))
  have htanhmem : Real.tanh (β * J) ∈ Set.Ioo (0 : ℝ) T :=
    Set.mem_Ioo.mpr ⟨htanhpos, hβJ_tanh⟩
  -- `f_∞` is analytic at `tanh (β * J)`.
  have hfinf : AnalyticAt ℝ (fun t : ℝ => cubicInfiniteClusterFreeEnergyReal d t)
      (Real.tanh (β * J)) :=
    cubicInfiniteClusterFreeEnergyReal_analyticOnNhd d hR hT hTR hT1 hkp2dR hρ2dR hkp2dT hρ2dT
      _ htanhmem
  -- `cubicInfiniteClusterFreeEnergyReal d (tanh (β' * J))` is analytic at `β`.
  have htanh : AnalyticAt ℝ (fun β' : ℝ => Real.tanh (β' * J)) β :=
    (analyticAt_real_tanh (β * J)).comp_of_eq' hmul hmulval
  have htanhval : (fun β' : ℝ => Real.tanh (β' * J)) β = Real.tanh (β * J) := rfl
  have h3 : AnalyticAt ℝ
      (fun β' : ℝ => cubicInfiniteClusterFreeEnergyReal d (Real.tanh (β' * J))) β :=
    hfinf.comp_of_eq' htanh htanhval
  rw [hg]
  exact (h1.add h2).add h3

/-- **GJ §18.6 capstone, unit coupling (`J = 1`).**  Specialisation of
`freeEnergyInfinite_latticeGraph_cubicExhaustion_analyticAt_beta_h_zero` to `J = 1`: the
infinite-volume cubic-Ising free-energy density at zero field and unit coupling is real-analytic in
`β` at high temperature (`0 < β`, `tanh β < T`). -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_analyticAt_beta_unitCoupling
    (d : ℕ) {R T β : ℝ}
    (hR : 0 < R) (hT : 0 < T) (hTR : T ≤ R) (hT1 : T ≤ 1)
    (hkp2dR : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R) < 1)
    (hρ2dR : 4 * (((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R))
        / (1 - ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * R)) ^ 2 < 1)
    (hkp2dT : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T) < 1)
    (hρ2dT : 4 * (((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T))
        / (1 - ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T)) ^ 2 < 1)
    (hβ : 0 < β) (htanh : Real.tanh β < T) :
    AnalyticAt ℝ (fun β' : ℝ => Ambient.freeEnergyInfinite (latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨1, 0, β'⟩ : IsingParams ℝ)) β := by
  have hβJ_pos : 0 < β * 1 := by rwa [mul_one]
  have hβJ_tanh : Real.tanh (β * 1) < T := by rwa [mul_one]
  exact freeEnergyInfinite_latticeGraph_cubicExhaustion_analyticAt_beta_h_zero d hR hT hTR hT1
    hkp2dR hρ2dR hkp2dT hρ2dT hβJ_pos hβJ_tanh

end IsingModel
