import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Concrete.IntLattice
import IsingModel.PhaseTransition
import IsingModel.AmbientLattice.MagnetizationInfinite

/-!
# Concrete correlation symmetry wrappers

Narrow child module for concrete `latticeGraph` correlation, magnetization, and
susceptibility h-symmetry / absolute-field wrappers, including finite-volume,
along-exhaustion, and infinite-volume forms. The theorem names are the same as
the former legacy declarations, but callers can now avoid importing the
monolithic concrete legacy module.
-/

namespace IsingModel
namespace Ambient

/-! ### ℤ^d direct finite-volume correlation symmetry wrappers -/

/-- **ℤ^d correlation_neg_h direct** at Λ-induced: Z₂ odd-symmetry
under `h → -h`. `correlation ⟨J,-h,β⟩ A = (-1)^|A| · correlation ⟨J,h,β⟩ A`.
Concrete wrapper for `IsingModel.correlation_neg_h` (#754). -/
theorem correlation_neg_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h β : ℝ) (A : Finset (↑Λ : Type _)) :
    IsingModel.correlation
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, -h, β⟩ : IsingParams ℝ) A
      = (-1) ^ A.card * IsingModel.correlation
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, h, β⟩ : IsingParams ℝ) A :=
  IsingModel.correlation_neg_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β A

/-- **ℤ^d magnetization_neg_h direct** at Λ-induced.
Concrete wrapper for `IsingModel.magnetization_neg_h` (#755). -/
theorem magnetization_neg_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h β : ℝ) (i : (↑Λ : Type _)) :
    IsingModel.magnetization
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, -h, β⟩ : IsingParams ℝ) i
      = -IsingModel.magnetization
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, h, β⟩ : IsingParams ℝ) i :=
  IsingModel.magnetization_neg_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β i

/-- **ℤ^d truncated2_neg_h direct** at Λ-induced (i ≠ j).
Concrete wrapper for `IsingModel.truncated2_neg_h` (#756). -/
theorem truncated2_neg_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h β : ℝ)
    {i j : (↑Λ : Type _)} (hij : i ≠ j) :
    IsingModel.truncated2
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, -h, β⟩ : IsingParams ℝ) i j
      = IsingModel.truncated2
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, h, β⟩ : IsingParams ℝ) i j :=
  IsingModel.truncated2_neg_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β hij

/-- **ℤ^d truncated3_neg_h direct** at Λ-induced (pairwise distinct):
antisymmetric, `U_3(-h) = -U_3(h)`. Concrete wrapper for
`IsingModel.truncated3_neg_h` (#758). -/
theorem truncated3_neg_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h β : ℝ)
    {i j k : (↑Λ : Type _)} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    IsingModel.truncated3
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, -h, β⟩ : IsingParams ℝ) i j k
      = -IsingModel.truncated3
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, h, β⟩ : IsingParams ℝ) i j k :=
  IsingModel.truncated3_neg_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β hij hjk hik

/-- **ℤ^d truncated4_neg_h direct** at Λ-induced (pairwise distinct):
invariant under `h → -h`. Concrete wrapper for
`IsingModel.truncated4_neg_h` (#757). -/
theorem truncated4_neg_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h β : ℝ)
    {i j k l : (↑Λ : Type _)}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    IsingModel.truncated4
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, -h, β⟩ : IsingParams ℝ) i j k l
      = IsingModel.truncated4
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, h, β⟩ : IsingParams ℝ) i j k l :=
  IsingModel.truncated4_neg_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β hij hik hil hjk hjl hkl

/-- **ℤ^d correlation_eq_abs_h_of_even_card direct** at Λ-induced:
for `|A|` even, `correlation ⟨J, h, β⟩ A = correlation ⟨J, |h|, β⟩ A`.
Concrete wrapper for `IsingModel.correlation_eq_abs_h_of_even_card`
(#760). -/
theorem correlation_eq_abs_h_of_even_card_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h β : ℝ)
    (A : Finset (↑Λ : Type _)) (heven : Even A.card) :
    IsingModel.correlation
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, h, β⟩ : IsingParams ℝ) A
      = IsingModel.correlation
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, |h|, β⟩ : IsingParams ℝ) A :=
  IsingModel.correlation_eq_abs_h_of_even_card
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β A heven

/-! ### ℤ^d infinite-volume even-card correlation symmetry wrappers -/

/-- **ℤ^d correlationInfinite invariance under `h → -h`** (even `|A|`):
`correlationInfinite ⟨J,-h,β⟩ A = correlationInfinite ⟨J,h,β⟩ A`.
Concrete wrapper for `correlationInfinite_neg_h_of_even_card` (#765). -/
theorem correlationInfinite_neg_h_of_even_card_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J h β : ℝ) (A : Finset (Fin d → ℤ)) (heven : Even A.card) :
    correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, -h, β⟩ : IsingParams ℝ) A
      = correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, h, β⟩ : IsingParams ℝ) A :=
  correlationInfinite_neg_h_of_even_card (IsingModel.latticeGraph d) Λ J h β A heven

/-- **ℤ^d correlationInfinite equals value at `|h|`** (even `|A|`):
concrete wrapper for `correlationInfinite_eq_abs_h_of_even_card` (#765). -/
theorem correlationInfinite_eq_abs_h_of_even_card_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J h β : ℝ) (A : Finset (Fin d → ℤ)) (heven : Even A.card) :
    correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ) A
      = correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, |h|, β⟩ : IsingParams ℝ) A :=
  correlationInfinite_eq_abs_h_of_even_card (IsingModel.latticeGraph d) Λ J h β A heven

/-! ### ℤ^d magnetization and susceptibility absolute-field wrappers -/

/-- **ℤ^d `|M_Λ(h)| = M_Λ(|h|)`** under ferromagnetism at `|h|`.
Concrete `latticeGraph d` wrapper for PR #772's
`abs_magnetizationΛ_eq_magnetizationΛ_abs_h`. -/
theorem abs_magnetizationΛ_latticeGraph_eq_magnetizationΛ_latticeGraph_abs_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (J h β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (i : ↑Λ) :
    |magnetizationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ) i|
      = magnetizationΛ (IsingModel.latticeGraph d) Λ
          (⟨J, |h|, β⟩ : IsingParams ℝ) i :=
  abs_magnetizationΛ_eq_magnetizationΛ_abs_h
    (IsingModel.latticeGraph d) Λ J h β hJ hβ i

/-- **ℤ^d `M_along(-h) n = -M_along(h) n`** (any parameters). Concrete
`latticeGraph d` wrapper for PR #773's
`magnetizationAlongExhaustion_neg_h`. -/
theorem magnetizationAlongExhaustion_latticeGraph_neg_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J h β : ℝ) (i : Fin d → ℤ) (n : ℕ) :
    magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, -h, β⟩ : IsingParams ℝ) i n
      = -magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h, β⟩ : IsingParams ℝ) i n :=
  magnetizationAlongExhaustion_neg_h (IsingModel.latticeGraph d) Λ J h β i n

/-- **ℤ^d `|M_along(h) n| = M_along(|h|) n`** under ferromagnetism at
`|h|`. Concrete `latticeGraph d` wrapper for PR #773's
`abs_magnetizationAlongExhaustion_eq_magnetizationAlongExhaustion_abs_h`. -/
theorem abs_magnetizationAlongExhaustion_latticeGraph_eq_abs_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J h β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (i : Fin d → ℤ) (n : ℕ) :
    |magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ) i n|
      = magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, |h|, β⟩ : IsingParams ℝ) i n :=
  abs_magnetizationAlongExhaustion_eq_magnetizationAlongExhaustion_abs_h
    (IsingModel.latticeGraph d) Λ J h β hJ hβ i n

/-- **ℤ^d ∞-volume one-sided `|M_∞(h)| ≤ M_∞(|h|)`** under ferromagnetism
at `|h|`. Concrete `latticeGraph d` wrapper for PR #773's
`abs_magnetizationInfinite_le_magnetizationInfinite_abs_h`. -/
theorem abs_magnetizationInfinite_latticeGraph_le_magnetizationInfinite_latticeGraph_abs_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J h β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (i : Fin d → ℤ) :
    |magnetizationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ) i|
      ≤ magnetizationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, |h|, β⟩ : IsingParams ℝ) i :=
  abs_magnetizationInfinite_le_magnetizationInfinite_abs_h
    (IsingModel.latticeGraph d) Λ J h β hJ hβ i

/-- **ℤ^d `M_∞ ≤ 0` at `h ≤ 0`** under ferromagnetism. Concrete
`latticeGraph d` wrapper for PR #774's
`magnetizationInfinite_nonpos_of_nonpos_h`. -/
theorem magnetizationInfinite_latticeGraph_nonpos_of_nonpos_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J h β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hh : h ≤ 0)
    (i : Fin d → ℤ) :
    magnetizationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ) i ≤ 0 :=
  magnetizationInfinite_nonpos_of_nonpos_h
    (IsingModel.latticeGraph d) Λ J h β hJ hβ hh i

/-- **ℤ^d `M_∞ = 0` at `h ≤ 0` when some stage misses `i`**.
Concrete `latticeGraph d` wrapper for PR #774's
`magnetizationInfinite_eq_zero_of_exists_stage_not_mem`. -/
theorem magnetizationInfinite_latticeGraph_eq_zero_of_exists_stage_not_mem
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J h β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hh : h ≤ 0)
    (i : Fin d → ℤ) (hmiss : ∃ n, i ∉ Λ.volume n) :
    magnetizationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ) i = 0 :=
  magnetizationInfinite_eq_zero_of_exists_stage_not_mem
    (IsingModel.latticeGraph d) Λ J h β hJ hβ hh i hmiss

/-! ## Moved: susceptibility h-symmetry wrappers

The four wrappers `susceptibility*_latticeGraph_*_abs_h` now live in
`CorrelationSymmetrySusceptibility.lean`. -/

end Ambient
end IsingModel
