import IsingModel.Concrete.LatticeGraphBED
import IsingModel.PhaseTransition
import IsingModel.Inequalities.FKG

/-!
# Magnetization, susceptibility, and FKG inequality at ℤ^d

ℤ^d forwarders for:

1. **Magnetization / truncated-2 / susceptibility convergence** — `{J,h,β} → ∞`
   convergence and subgraph-monotone convergence from `PhaseTransition.lean`.
2. **Susceptibility (GJ §5.3)** — `susceptibility_apply`, nonneg, trivial slices,
   and `{J,h,β} → ∞` subsequence convergence.
3. **Site-level magnetization wrappers (GJ §5.3, pp. 77–80)** — bounds, vanishing
   slices, monotonicity, `HasNonnegCorrelations` helpers.
4. **GKS-I / GKS-II / FKG inequality (GJ §4.4)** — `gks_first`, `gks_second`,
   `boltzmannWeight_log_supermodular`, `fkg_ising`.

## References

* Glimm–Jaffe, *Quantum Physics* 2nd ed., §4.4, §5.3, §17.7.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-! ### Magnetization / truncated-2 / susceptibility convergence wrappers

Direct ℤ^d forwarders for `magnetization_convergent_{J,h,beta}`,
`truncated2_convergent_{J,h,beta,subgraph}`, and
`susceptibility_convergent_subgraph` /
`magnetization_total_convergent_subgraph` (`IsingModel/PhaseTransition.lean`). -/

/-- **ℤ^d magnetization_convergent_J direct** (Λ-induced, ferromagnetic):
`n ↦ M_i(J = n, h, β)` converges for `h ≥ 0`, `β > 0`. Thin pass-through
of `IsingModel.magnetization_convergent_J`. -/
theorem magnetization_convergent_J_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h : ℝ) (hh : 0 ≤ h) (β : ℝ) (hβ : 0 < β)
    (i : (↑Λ : Type _)) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => IsingModel.magnetization
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        ⟨(n : ℝ), h, β⟩ i)
      Filter.atTop (nhds L) :=
  IsingModel.magnetization_convergent_J
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h hh β hβ i

/-- **ℤ^d magnetization_convergent_h direct** (Λ-induced, ferromagnetic):
`n ↦ M_i(J, h = n, β)` converges for `J ≥ 0`, `β > 0`. Thin pass-through
of `IsingModel.magnetization_convergent_h`. -/
theorem magnetization_convergent_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J : ℝ) (hJ : 0 ≤ J) (β : ℝ) (hβ : 0 < β)
    (i : (↑Λ : Type _)) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => IsingModel.magnetization
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        ⟨J, (n : ℝ), β⟩ i)
      Filter.atTop (nhds L) :=
  IsingModel.magnetization_convergent_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J hJ β hβ i

/-- **ℤ^d magnetization_convergent_beta direct** (Λ-induced, ferromagnetic):
`n ↦ M_i(J, h, β = n+1)` converges for `J ≥ 0`, `h ≥ 0`. Thin
pass-through of `IsingModel.magnetization_convergent_beta`. -/
theorem magnetization_convergent_beta_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J : ℝ) (hJ : 0 ≤ J) (h : ℝ) (hh : 0 ≤ h)
    (i : (↑Λ : Type _)) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => IsingModel.magnetization
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        ⟨J, h, (n + 1 : ℝ)⟩ i)
      Filter.atTop (nhds L) :=
  IsingModel.magnetization_convergent_beta
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J hJ h hh i

/-- **ℤ^d truncated2_convergent_J direct** (Λ-induced, ferromagnetic):
`n ↦ ⟨σ_i; σ_j⟩_{(n, h, β)}` converges for `h ≥ 0`, `β > 0`. Thin
pass-through of `IsingModel.truncated2_convergent_J`. -/
theorem truncated2_convergent_J_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h : ℝ) (hh : 0 ≤ h) (β : ℝ) (hβ : 0 < β)
    (i j : (↑Λ : Type _)) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => IsingModel.truncated2
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        ⟨(n : ℝ), h, β⟩ i j)
      Filter.atTop (nhds L) :=
  IsingModel.truncated2_convergent_J
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h hh β hβ i j

/-- **ℤ^d truncated2_convergent_h direct** (Λ-induced, ferromagnetic):
`n ↦ ⟨σ_i; σ_j⟩_{(J, n, β)}` converges for `J ≥ 0`, `β > 0`. Thin
pass-through of `IsingModel.truncated2_convergent_h`. -/
theorem truncated2_convergent_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J : ℝ) (hJ : 0 ≤ J) (β : ℝ) (hβ : 0 < β)
    (i j : (↑Λ : Type _)) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => IsingModel.truncated2
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        ⟨J, (n : ℝ), β⟩ i j)
      Filter.atTop (nhds L) :=
  IsingModel.truncated2_convergent_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J hJ β hβ i j

/-- **ℤ^d truncated2_convergent_beta direct** (Λ-induced, ferromagnetic):
`n ↦ ⟨σ_i; σ_j⟩_{(J, h, n+1)}` converges for `J ≥ 0`, `h ≥ 0`. Thin
pass-through of `IsingModel.truncated2_convergent_beta`. -/
theorem truncated2_convergent_beta_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J : ℝ) (hJ : 0 ≤ J) (h : ℝ) (hh : 0 ≤ h)
    (i j : (↑Λ : Type _)) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => IsingModel.truncated2
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        ⟨J, h, (n + 1 : ℝ)⟩ i j)
      Filter.atTop (nhds L) :=
  IsingModel.truncated2_convergent_beta
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J hJ h hh i j

/-- **ℤ^d truncated2_convergent_subgraph direct** (Λ-induced,
ferromagnetic): `n ↦ ⟨σ_i; σ_j⟩_{Gₙ}` converges along any increasing
subgraph sequence `Gₙ : ℕ → SimpleGraph (↑Λ)` (note: `Gₙ` is arbitrary
on the Λ-induced vertex type; this wrapper only fixes `ι = ↑Λ`, not the
graph itself). Thin pass-through of
`IsingModel.truncated2_convergent_subgraph`. -/
theorem truncated2_convergent_subgraph_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (Gn : ℕ → SimpleGraph (↑Λ : Type _)) [∀ n, Fintype (Gn n).edgeSet]
    (hmono : Monotone Gn) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (i j : (↑Λ : Type _)) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => IsingModel.truncated2 (Gn n) p i j)
      Filter.atTop (nhds L) :=
  IsingModel.truncated2_convergent_subgraph Gn hmono p hf i j

/-- **ℤ^d susceptibility_convergent_subgraph direct** (Λ-induced,
ferromagnetic): `n ↦ χ_i(Gₙ)` converges along any increasing subgraph
sequence `Gₙ : ℕ → SimpleGraph (↑Λ)` (note: `Gₙ` is arbitrary on the
Λ-induced vertex type; this wrapper only fixes `ι = ↑Λ`, not the graph
itself). Thin pass-through of
`IsingModel.susceptibility_convergent_subgraph`. -/
theorem susceptibility_convergent_subgraph_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (Gn : ℕ → SimpleGraph (↑Λ : Type _)) [∀ n, Fintype (Gn n).edgeSet]
    (hmono : Monotone Gn) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (i : (↑Λ : Type _)) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => IsingModel.susceptibility (Gn n) p i)
      Filter.atTop (nhds L) :=
  IsingModel.susceptibility_convergent_subgraph Gn hmono p hf i

/-- **ℤ^d magnetization_total_convergent_subgraph direct** (Λ-induced,
ferromagnetic): `n ↦ Σ_i M_i(Gₙ)` converges along any increasing
subgraph sequence `Gₙ : ℕ → SimpleGraph (↑Λ)` (note: `Gₙ` is arbitrary on
the Λ-induced vertex type; this wrapper only fixes `ι = ↑Λ`, not the
graph itself). Thin pass-through of
`IsingModel.magnetization_total_convergent_subgraph`. -/
theorem magnetization_total_convergent_subgraph_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (Gn : ℕ → SimpleGraph (↑Λ : Type _)) [∀ n, Fintype (Gn n).edgeSet]
    (hmono : Monotone Gn) (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => ∑ i : (↑Λ : Type _), IsingModel.magnetization (Gn n) p i)
      Filter.atTop (nhds L) :=
  IsingModel.magnetization_total_convergent_subgraph Gn hmono p hf

/-! ### Susceptibility (GJ §5.3) and eta critical-exponent wrappers

Direct ℤ^d forwarders for the `susceptibility` family (apply, nonneg,
trivial slices at `J=0` / `β=0`, and `{J,h,β} → ∞` subsequence
convergence) and the GJ §17.7 finite-volume `η ≥ 0` slice
`eta_nonneg_finite_vol`. -/

/-- **ℤ^d susceptibility_apply direct** (Λ-induced):
`susceptibility ι = ∑ j, truncated2 ι j`. Thin pass-through of
`IsingModel.susceptibility_apply`. -/
theorem susceptibility_apply_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (i : (↑Λ : Type _)) :
    IsingModel.susceptibility
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p i
      = ∑ j : (↑Λ : Type _), IsingModel.truncated2
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p i j :=
  IsingModel.susceptibility_apply
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p i

/-- **ℤ^d susceptibility_nonneg direct** (Λ-induced, ferromagnetic):
`0 ≤ χ_i`. Thin pass-through of `IsingModel.susceptibility_nonneg`
(GKS-II summed over `j`). -/
theorem susceptibility_nonneg_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (hf : Ferromagnetic p) (i : (↑Λ : Type _)) :
    0 ≤ IsingModel.susceptibility
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p i :=
  IsingModel.susceptibility_nonneg
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p hf i

/-- **ℤ^d susceptibility_J_zero direct** (Λ-induced): at `J = 0`,
`χ_i = t · (1 - t)` with `t = tanh(β·h)`. Thin pass-through of
`IsingModel.susceptibility_J_zero`. Note: uses the Finset-based
`truncated2` so the diagonal `{i, i} = {i}` term is `t - t²`, not
the physical `1 - t²` — see the base theorem's doc comment. -/
theorem susceptibility_J_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ) (i : (↑Λ : Type _)) :
    IsingModel.susceptibility
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨0, h, β⟩ : IsingParams ℝ) i
      = Real.tanh (β * h) * (1 - Real.tanh (β * h)) :=
  IsingModel.susceptibility_J_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β i

/-- **ℤ^d truncated2 h=0 direct** (Λ-induced): at `h = 0`,
`truncated2 i j = correlation {i, j}`. Thin pass-through of
`IsingModel.truncated2_h_zero`. -/
theorem truncated2_h_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (i j : (↑Λ : Type _)) :
    IsingModel.truncated2
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, 0, β⟩ : IsingParams ℝ) i j
      = IsingModel.correlation
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, 0, β⟩ : IsingParams ℝ) {i, j} :=
  IsingModel.truncated2_h_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β i j

/-- **ℤ^d susceptibility_h_zero direct** (Λ-induced): at `h = 0`,
`χ_i = ∑_j correlation {i, j}`. Thin pass-through of
`IsingModel.susceptibility_h_zero`. -/
theorem susceptibility_h_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (i : (↑Λ : Type _)) :
    IsingModel.susceptibility
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, 0, β⟩ : IsingParams ℝ) i
      = ∑ j : (↑Λ : Type _),
          IsingModel.correlation
            (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
            (⟨J, 0, β⟩ : IsingParams ℝ) {i, j} :=
  IsingModel.susceptibility_h_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β i

/-- **ℤ^d susceptibility_neg_h direct** (Λ-induced):
`χ(-h) = χ(h) - 2·M(h)`. Concrete wrapper for
`IsingModel.susceptibility_neg_h` (#767). -/
theorem susceptibility_neg_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h β : ℝ) (i : (↑Λ : Type _)) :
    IsingModel.susceptibility
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, -h, β⟩ : IsingParams ℝ) i
      = IsingModel.susceptibility
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, h, β⟩ : IsingParams ℝ) i
        - 2 * IsingModel.magnetization
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, h, β⟩ : IsingParams ℝ) i :=
  IsingModel.susceptibility_neg_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β i

/-- **ℤ^d susceptibility_beta_zero direct** (Λ-induced): at `β = 0`,
`χ_i = 0` for any `J, h`. Thin pass-through of
`IsingModel.susceptibility_beta_zero`. -/
theorem susceptibility_beta_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h : ℝ) (i : (↑Λ : Type _)) :
    IsingModel.susceptibility
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, h, 0⟩ : IsingParams ℝ) i = 0 :=
  IsingModel.susceptibility_beta_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h i

/-- **ℤ^d susceptibility_convergent_J direct** (Λ-induced, ferromagnetic):
`n ↦ χ_i(n, h, β)` converges for `h ≥ 0`, `β > 0`. Thin pass-through of
`IsingModel.susceptibility_convergent_J`. -/
theorem susceptibility_convergent_J_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h : ℝ) (hh : 0 ≤ h) (β : ℝ) (hβ : 0 < β)
    (i : (↑Λ : Type _)) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => IsingModel.susceptibility
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        ⟨(n : ℝ), h, β⟩ i)
      Filter.atTop (nhds L) :=
  IsingModel.susceptibility_convergent_J
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h hh β hβ i

/-- **ℤ^d susceptibility_convergent_h direct** (Λ-induced, ferromagnetic):
`n ↦ χ_i(J, n, β)` converges for `J ≥ 0`, `β > 0`. Thin pass-through of
`IsingModel.susceptibility_convergent_h`. -/
theorem susceptibility_convergent_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J : ℝ) (hJ : 0 ≤ J) (β : ℝ) (hβ : 0 < β)
    (i : (↑Λ : Type _)) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => IsingModel.susceptibility
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        ⟨J, (n : ℝ), β⟩ i)
      Filter.atTop (nhds L) :=
  IsingModel.susceptibility_convergent_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J hJ β hβ i

/-- **ℤ^d susceptibility_convergent_beta direct** (Λ-induced,
ferromagnetic): `n ↦ χ_i(J, h, n+1)` converges for `J ≥ 0`, `h ≥ 0`.
Thin pass-through of `IsingModel.susceptibility_convergent_beta`. -/
theorem susceptibility_convergent_beta_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J : ℝ) (hJ : 0 ≤ J) (h : ℝ) (hh : 0 ≤ h)
    (i : (↑Λ : Type _)) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => IsingModel.susceptibility
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        ⟨J, h, (n + 1 : ℝ)⟩ i)
      Filter.atTop (nhds L) :=
  IsingModel.susceptibility_convergent_beta
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J hJ h hh i

/-- **ℤ^d eta_nonneg_finite_vol direct** (Λ-induced, GJ §17.7
Thm 17.7.1 finite-volume slice, ferromagnetic):
`0 ≤ ⟨σ_i; σ_j⟩` via GKS-II. Thin pass-through of
`IsingModel.eta_nonneg_finite_vol`. -/
theorem eta_nonneg_finite_vol_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (hf : Ferromagnetic p) (i j : (↑Λ : Type _)) :
    0 ≤ IsingModel.truncated2
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p i j :=
  IsingModel.eta_nonneg_finite_vol
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p hf i j

/-! ### Site-level magnetization wrappers (GJ §5.3, pp. 77–80)

Direct ℤ^d forwarders for `magnetization G p i = correlation G p {i}`
in `PhaseTransition.lean`. All pass through the abstract
`IsingModel.magnetization_*` theorems on
`Ambient.inducedGraph (latticeGraph d) Λ`. -/

/-- **ℤ^d magnetization_apply direct** (Λ-induced):
`magnetization = correlation … {i}`. -/
theorem magnetization_apply_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (i : (↑Λ : Type _)) :
    IsingModel.magnetization
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p i
      = IsingModel.correlation
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p {i} :=
  IsingModel.magnetization_apply
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p i

/-- **ℤ^d abs_magnetization_le_one direct** (Λ-induced):
`|M_i| ≤ 1` unconditionally. -/
theorem abs_magnetization_le_one_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (i : (↑Λ : Type _)) :
    |IsingModel.magnetization
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p i| ≤ 1 :=
  IsingModel.abs_magnetization_le_one
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p i

/-- **ℤ^d magnetization_le_one direct** (Λ-induced):
`M_i ≤ 1` unconditionally. -/
theorem magnetization_le_one_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (i : (↑Λ : Type _)) :
    IsingModel.magnetization
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p i ≤ 1 :=
  IsingModel.magnetization_le_one
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p i

/-- **ℤ^d neg_one_le_magnetization direct** (Λ-induced):
`-1 ≤ M_i` unconditionally. -/
theorem neg_one_le_magnetization_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (i : (↑Λ : Type _)) :
    -1 ≤ IsingModel.magnetization
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p i :=
  IsingModel.neg_one_le_magnetization
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p i

/-- **ℤ^d magnetization_nonneg direct** (Λ-induced, ferromagnetic):
`0 ≤ M_i` via GKS-I. -/
theorem magnetization_nonneg_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (hf : Ferromagnetic p) (i : (↑Λ : Type _)) :
    0 ≤ IsingModel.magnetization
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p i :=
  IsingModel.magnetization_nonneg
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p hf i

/-- **ℤ^d magnetization_sq_le_one direct** (Λ-induced):
`M_i² ≤ 1` unconditionally. -/
theorem magnetization_sq_le_one_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (i : (↑Λ : Type _)) :
    IsingModel.magnetization
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p i ^ 2 ≤ 1 :=
  IsingModel.magnetization_sq_le_one
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p i

/-- **ℤ^d magnetization_zero_at_h_zero direct** (Λ-induced):
`M_i(J, 0, β) = 0` — Z₂ symmetry at `h = 0`. -/
theorem magnetization_zero_at_h_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (i : (↑Λ : Type _)) :
    IsingModel.magnetization
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        ⟨J, 0, β⟩ i = 0 :=
  IsingModel.magnetization_zero_at_h_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β i

/-- **ℤ^d magnetization_beta_zero direct** (Λ-induced):
`M_i(J, h, 0) = 0` — infinite-temperature slice. -/
theorem magnetization_beta_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h : ℝ) (i : (↑Λ : Type _)) :
    IsingModel.magnetization
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        ⟨J, h, 0⟩ i = 0 :=
  IsingModel.magnetization_beta_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h i

/-- **ℤ^d magnetization_J_zero direct** (Λ-induced):
`M_i(0, h, β) = tanh(β·h)` — non-interacting slice. -/
theorem magnetization_J_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ) (i : (↑Λ : Type _)) :
    IsingModel.magnetization
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨0, h, β⟩ : IsingParams ℝ) i = Real.tanh (β * h) :=
  IsingModel.magnetization_J_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β i

/-- **ℤ^d magnetization_monotone_h direct** (Λ-induced, ferromagnetic):
`h ↦ M_i(J, h, β)` is `MonotoneOn (Set.Ici 0)` for `J ≥ 0`, `β > 0`. -/
theorem magnetization_monotone_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    (i : (↑Λ : Type _)) :
    MonotoneOn
      (fun h : ℝ => IsingModel.magnetization
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) ⟨J, h, β⟩ i)
      (Set.Ici 0) :=
  IsingModel.magnetization_monotone_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β hJ hβ i

/-- **ℤ^d magnetization_monotone_beta direct** (Λ-induced, ferromagnetic):
`β ↦ M_i(J, h, β)` is `MonotoneOn (Set.Ioi 0)` for `J, h ≥ 0`. -/
theorem magnetization_monotone_beta_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J : ℝ) (hJ : 0 ≤ J) (h : ℝ) (hh : 0 ≤ h)
    (i : (↑Λ : Type _)) :
    MonotoneOn
      (fun β : ℝ => IsingModel.magnetization
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) ⟨J, h, β⟩ i)
      (Set.Ioi 0) :=
  IsingModel.magnetization_monotone_beta
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J hJ h hh i

/-- **ℤ^d abs_correlation_le_one direct** (Λ-induced): `|⟨σ^A⟩| ≤ 1`. -/
theorem abs_correlation_le_one_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (A : Finset (↑Λ : Type _)) :
    |IsingModel.correlation
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p A| ≤ 1 :=
  IsingModel.abs_correlation_le_one
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p A

/-- **ℤ^d correlation_le_one direct** (Λ-induced): `⟨σ^A⟩ ≤ 1`. -/
theorem correlation_le_one_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (A : Finset (↑Λ : Type _)) :
    IsingModel.correlation
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p A ≤ 1 :=
  IsingModel.correlation_le_one
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p A

/-- **ℤ^d neg_one_le_correlation direct** (Λ-induced): `-1 ≤ ⟨σ^A⟩`. -/
theorem neg_one_le_correlation_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (A : Finset (↑Λ : Type _)) :
    -1 ≤ IsingModel.correlation
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p A :=
  IsingModel.neg_one_le_correlation
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p A

/-- **ℤ^d correlation_sq_le_one direct** (Λ-induced): `⟨σ^A⟩² ≤ 1`. -/
theorem correlation_sq_le_one_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (A : Finset (↑Λ : Type _)) :
    IsingModel.correlation
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p A ^ 2 ≤ 1 :=
  IsingModel.correlation_sq_le_one
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p A

/-- **ℤ^d correlation_beta_zero_vanish_of_nonempty_A direct** (Λ-induced):
`⟨σ^A⟩ at ⟨J, h, 0⟩ = 0` for nonempty `A`. -/
theorem correlation_beta_zero_vanish_of_nonempty_A_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h : ℝ)
    (A : Finset (↑Λ : Type _)) (hA : A.Nonempty) :
    IsingModel.correlation
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, h, 0⟩ : IsingParams ℝ) A = 0 :=
  IsingModel.correlation_beta_zero_vanish_of_nonempty_A
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h A hA

/-- **ℤ^d correlation_zero_params_vanish_of_nonempty_A direct** (Λ-induced):
`⟨σ^A⟩ at ⟨0, 0, β⟩ = 0` for nonempty `A`. -/
theorem correlation_zero_params_vanish_of_nonempty_A_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (β : ℝ)
    (A : Finset (↑Λ : Type _)) (hA : A.Nonempty) :
    IsingModel.correlation
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨0, 0, β⟩ : IsingParams ℝ) A = 0 :=
  IsingModel.correlation_zero_params_vanish_of_nonempty_A
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) β A hA

/-- **ℤ^d correlation_J_zero direct at Λ-induced**:
`⟨σ^A⟩ at ⟨0, h, β⟩ = tanh(βh)^|A|`. -/
theorem correlation_J_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ)
    (A : Finset (↑Λ : Type _)) :
    IsingModel.correlation
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨0, h, β⟩ : IsingParams ℝ) A
      = Real.tanh (β * h) ^ A.card :=
  IsingModel.correlation_J_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β A

/-- **ℤ^d correlation_empty at Λ-induced**: `⟨σ^∅⟩_Λ = 1`. -/
theorem correlation_empty_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    IsingModel.correlation
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p ∅ = 1 :=
  IsingModel.correlation_empty
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p

/-- **ℤ^d hasNonnegCorrelations_one direct** (Λ-induced):
the constant function `1` has HNC. -/
theorem hasNonnegCorrelations_one_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) :
    IsingModel.HasNonnegCorrelations
      (ι := (↑Λ : Type _)) (fun _ => 1) :=
  IsingModel.hasNonnegCorrelations_one

/-- **ℤ^d hasNonnegCorrelations_finset_prod direct** (Λ-induced):
a product of `(a + b · σ^C)` factors over a Finset has HNC. -/
theorem hasNonnegCorrelations_finset_prod_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {α : Type*}
    (S : Finset α)
    (g : α → IsingModel.Config (↑Λ : Type _) → ℝ)
    (hg : ∀ a ∈ S, ∃ c e : ℝ, ∃ C : Finset (↑Λ : Type _), 0 ≤ c ∧ 0 ≤ e ∧
      ∀ σ, g a σ = c + e * IsingModel.spinProduct C σ) :
    IsingModel.HasNonnegCorrelations fun σ : IsingModel.Config (↑Λ : Type _) =>
      ∏ a ∈ S, g a σ := by
  classical
  exact IsingModel.hasNonnegCorrelations_finset_prod S g hg

/-- **ℤ^d hasNonnegCorrelations_mul_prod direct** (Λ-induced):
multiplying an HNC function by a product of `(a + b · σ^C)` factors
preserves HNC. -/
theorem hasNonnegCorrelations_mul_prod_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {α : Type*}
    (S : Finset α) {f : IsingModel.Config (↑Λ : Type _) → ℝ}
    (hf : IsingModel.HasNonnegCorrelations f)
    (g : α → IsingModel.Config (↑Λ : Type _) → ℝ)
    (hg : ∀ a ∈ S, ∃ c e : ℝ, ∃ C : Finset (↑Λ : Type _), 0 ≤ c ∧ 0 ≤ e ∧
      ∀ σ, g a σ = c + e * IsingModel.spinProduct C σ) :
    IsingModel.HasNonnegCorrelations fun σ : IsingModel.Config (↑Λ : Type _) =>
      f σ * ∏ a ∈ S, g a σ := by
  classical
  exact IsingModel.hasNonnegCorrelations_mul_prod S hf g hg

/-- **ℤ^d hasNonnegCorrelations_mul direct** (Λ-induced): if `f` has HNC
then so does `f · (a + b · σ^C)` for `a, b ≥ 0`. -/
theorem hasNonnegCorrelations_mul_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {f : IsingModel.Config (↑Λ : Type _) → ℝ}
    (hf : IsingModel.HasNonnegCorrelations f)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (C : Finset (↑Λ : Type _)) :
    IsingModel.HasNonnegCorrelations fun σ : IsingModel.Config (↑Λ : Type _) =>
      f σ * (a + b * IsingModel.spinProduct C σ) :=
  IsingModel.hasNonnegCorrelations_mul hf ha hb C

/-- **ℤ^d hasNonnegCorrelations_general_coupling direct** (Λ-induced):
general non-negative couplings give HNC product. -/
theorem hasNonnegCorrelations_general_coupling_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (couplings : Finset (Finset (↑Λ : Type _)))
    (K : Finset (↑Λ : Type _) → ℝ)
    (hK : ∀ C ∈ couplings, 0 ≤ K C) :
    IsingModel.HasNonnegCorrelations fun σ : IsingModel.Config (↑Λ : Type _) =>
      ∏ C ∈ couplings, Real.exp (K C * IsingModel.spinProduct C σ) :=
  IsingModel.hasNonnegCorrelations_general_coupling couplings K hK

/-- **ℤ^d hasNonnegCorrelations_edge_site_product direct** (Λ-induced):
the edge × site product weight has HNC on `Config ↑Λ`. -/
theorem hasNonnegCorrelations_edge_site_product_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (edgeK : Sym2 (↑Λ : Type _) → ℝ) (siteK : (↑Λ : Type _) → ℝ)
    (hedgeK : ∀ e ∈ (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset,
      0 ≤ edgeK e)
    (hsiteK : ∀ i, 0 ≤ siteK i) :
    IsingModel.HasNonnegCorrelations fun σ : IsingModel.Config (↑Λ : Type _) =>
      (∏ e ∈ (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset,
        Real.exp (edgeK e * IsingModel.edgeSpin (K := ℝ) σ e)) *
      (∏ i : (↑Λ : Type _),
        Real.exp (siteK i * IsingModel.Spin.sign ℝ (σ i))) :=
  IsingModel.hasNonnegCorrelations_edge_site_product
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) edgeK siteK hedgeK hsiteK

/-- **ℤ^d GKS numerator nonneg** at Λ-induced: for ferromagnetic `p`,
`0 ≤ numerator (spinProduct A)`. -/
theorem gks_numerator_nonneg_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset (↑Λ : Type _)) :
    0 ≤ IsingModel.numerator
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p
          (IsingModel.spinProduct A) :=
  IsingModel.gks_numerator_nonneg
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p hf A

/-- **ℤ^d boltzmannWeight has non-negative correlations** at Λ-induced
(ferromagnetic). -/
theorem boltzmannWeight_hasNonnegCorrelations_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    IsingModel.HasNonnegCorrelations (IsingModel.boltzmannWeight
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p) :=
  IsingModel.boltzmannWeight_hasNonnegCorrelations
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p hf

/-- **ℤ^d GKS-I at Λ-induced subgraph** (Griffiths 1967):
`0 ≤ ⟨σ^A⟩_Λ` for ferromagnetic `p`. -/
theorem gks_first_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A : Finset (↑Λ)) :
    0 ≤ IsingModel.correlation
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p A :=
  IsingModel.gks_first
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p hf A

/-- **ℤ^d GKS-II at Λ-induced subgraph** (Griffiths 1967):
`⟨σ^A⟩_Λ · ⟨σ^B⟩_Λ ≤ ⟨σ^{A Δ B}⟩_Λ` for ferromagnetic `p`. -/
theorem gks_second_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (A B : Finset (↑Λ)) :
    IsingModel.correlation
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p A
      * IsingModel.correlation
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p B
      ≤ IsingModel.correlation
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p (symmDiff A B) :=
  IsingModel.gks_second
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p hf A B

/-- **ℤ^d boltzmannWeight log-supermodularity** (Λ-induced,
ferromagnetic): `w(σ) · w(σ') ≤ w(σ ⊔ σ') · w(σ ⊓ σ')`. Thin
pass-through of `IsingModel.boltzmannWeight_log_supermodular`; the
technical input to `fkg_ising`. -/
theorem boltzmannWeight_log_supermodular_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (σ σ' : IsingModel.Config (↑Λ : Type _)) :
    IsingModel.boltzmannWeight
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p σ
      * IsingModel.boltzmannWeight
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p σ'
      ≤ IsingModel.boltzmannWeight
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p (σ ⊔ σ')
        * IsingModel.boltzmannWeight
            (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p (σ ⊓ σ') :=
  IsingModel.boltzmannWeight_log_supermodular
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p hf σ σ'

/-- **ℤ^d FKG inequality** (Λ-induced, ferromagnetic, GJ §4.4): for
nonneg monotone `f, g : Config (↑Λ) → ℝ`,
`⟨f⟩ · ⟨g⟩ ≤ ⟨f · g⟩`. Thin pass-through of
`IsingModel.fkg_ising`. -/
theorem fkg_ising_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (f g : IsingModel.Config (↑Λ : Type _) → ℝ)
    (hf_nn : 0 ≤ f) (hg_nn : 0 ≤ g)
    (hf_mono : Monotone f) (hg_mono : Monotone g) :
    IsingModel.gibbsExpectation
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p f
      * IsingModel.gibbsExpectation
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p g
      ≤ IsingModel.gibbsExpectation
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p (f * g) :=
  IsingModel.fkg_ising
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p hf
    f g hf_nn hg_nn hf_mono hg_mono

end Ambient
end IsingModel
