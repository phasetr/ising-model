import IsingModel.AmbientLattice.Defs.Core
import IsingModel.ClusterExpansion.AlternatingCompleteGraph.MayerConnectedFilter
import IsingModel.ClusterExpansion.StrictPositivity.CycleSeven
import IsingModel.ClusterExpansion.StrictPositivity.MayerPartialFerro

/-!
# Sign, zero set and strict growth of the polymer free energy on a finite volume (§18.4)

Statements for an ambient graph `G : SimpleGraph V` and a finite volume `Λ : Finset V`, read
on the induced subgraph `inducedGraph G Λ`. Two sums recur and neither has a definition of
its own, so a statement that mentions one carries the summation written out; most statements
here mention neither and are phrased through `polymerFreeEnergy`, `mayerPartialSum` or
`mayerExpansionTerm`. Write `Ξ t` for `∑ Γ ∈ vdCompatiblePolymerFamilies (inducedGraph G Λ),
∏ P ∈ Γ, t ^ P.card`, which the theorem names abbreviate to `vdPolymerFamilies_sum_Λ`, and
`ε t` for the same sum over `(vdCompatiblePolymerFamilies (inducedGraph G Λ)).erase ∅`, which
they abbreviate to `eps`. Then `polymerFreeEnergy (inducedGraph G Λ) t = Real.log (Ξ t)` by
definition, and `E` below is `(inducedGraph G Λ).edgeFinset`. The declaration comments below
write `vdSum` for `Ξ` and `ε(t)` for `ε t`; both are prose shorthands of this file and
neither is a name in the library.

Growth in the activity is strict once a polymer exists: assuming
`(allPolymers (inducedGraph G Λ)).Nonempty`, the polymer free energy at `t` exceeds the one
at `s` whenever `0 ≤ s < t`, and it is `StrictMonoOn` over `Set.Ici 0`.

On `0 ≤ t` its sign and its zero set are settled exactly, and the two conditions are
complementary there: it is positive precisely when `0 < t` and
`(allPolymers (inducedGraph G Λ)).Nonempty`, and it is `0` precisely when `t = 0` or
`allPolymers (inducedGraph G Λ) = ∅`. The same alternative is recorded on `Ξ` through `ε`:
under `0 ≤ t`, `1 < Ξ t` exactly when `0 < ε t`; and `Ξ t = 1` exactly when `ε t = 0`, this
last one for every real `t`.

Upper bounds for the polymer free energy are `ε t` under `0 ≤ t`, sharpened to a strict
`< ε t` under `0 < ε t` alone, then `(1 + t) ^ E.card - 1` under `0 ≤ t`, and `Real.log 2`
under `0 ≤ t` together with the high-temperature hypothesis `(1 + t) ^ E.card < 2`.

On the Mayer side, `mayerExpansionTerm (inducedGraph G Λ)` vanishes at every order and every
activity when `allPolymers (inducedGraph G Λ) = ∅`, and `mayerPartialSum (inducedGraph G Λ)`
vanishes at order `0` for every activity; at order `1` it is nonnegative under `0 ≤ t` and
strictly positive under `0 < t` with a polymer present. Both are also rewritten as sums
restricted to the length-`n` polymer sequences whose `polymerSeqIncompatibilityGraph` is
`Connected`, with `ursellCoefficient` and `clusterSeqActivity` as the summand.

Every statement takes exactly two instance binders, `DecidableEq V` and
`Fintype (inducedGraph G Λ).edgeSet`. The Prop-valued hypotheses occurring anywhere in the
file are exactly `(allPolymers (inducedGraph G Λ)).Nonempty`,
`allPolymers (inducedGraph G Λ) = ∅`, `0 ≤ t`, `0 < t`, `0 ≤ s`, `s < t`, `0 < ε t` and
`(1 + t) ^ E.card < 2`. The statements carrying none are `Ξ t = 1 ↔ ε t = 0`, the
order-`0` vanishing of `mayerPartialSum`, and the connected-form rewrites of
`mayerExpansionTerm` and `mayerPartialSum`.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Λ-layer: `polymerFreeEnergy` strictly increasing under polymers
exist** (§18.4 strict-mono Λ wrap). -/
theorem polymerFreeEnergy_Λ_lt_of_lt_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h_poly : (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) s <
      IsingModel.polymerFreeEnergy (inducedGraph G Λ) t :=
  IsingModel.polymerFreeEnergy_lt_of_lt_of_polymers_nonempty
    (inducedGraph G Λ) h_poly hs hst

/-- **Λ-layer: `polymerFreeEnergy_strictMonoOn (Set.Ici 0)` under
polymers exist** (§18.4 strict-mono Λ wrap). -/
theorem polymerFreeEnergy_Λ_strictMonoOn_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h_poly : (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty) :
    StrictMonoOn (fun t : ℝ => IsingModel.polymerFreeEnergy (inducedGraph G Λ) t)
      (Set.Ici 0) :=
  IsingModel.polymerFreeEnergy_strictMonoOn_of_polymers_nonempty
    (inducedGraph G Λ) h_poly

/-- **Λ-layer: `polymerFreeEnergy > 0 ↔ 0 < t ∧ polymers exist`** (§18.4 Λ wrap). -/
theorem polymerFreeEnergy_Λ_pos_iff
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    0 < IsingModel.polymerFreeEnergy (inducedGraph G Λ) t ↔
      0 < t ∧ (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty :=
  IsingModel.polymerFreeEnergy_pos_iff (inducedGraph G Λ) ht

/-- **Λ-layer: `polymerFreeEnergy = 0 ↔ t = 0 ∨ no polymers`** (§18.4 Λ wrap). -/
theorem polymerFreeEnergy_Λ_eq_zero_iff
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) t = 0 ↔
      t = 0 ∨ IsingModel.allPolymers (inducedGraph G Λ) = ∅ :=
  IsingModel.polymerFreeEnergy_eq_zero_iff (inducedGraph G Λ) ht

/-- **Λ-layer: `polymerFreeEnergy ≤ ε(t)` under `0 ≤ t`** (§18.4 Λ wrap). -/
theorem polymerFreeEnergy_Λ_le_eps_of_nonneg
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) t ≤
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ)).erase ∅,
        ∏ P ∈ Γ, t ^ P.card :=
  IsingModel.polymerFreeEnergy_le_eps_of_nonneg (inducedGraph G Λ) ht

/-- **Λ-layer: `polymerFreeEnergy < ε(t)` when `ε(t) > 0`** (§18.4 Λ wrap). -/
theorem polymerFreeEnergy_Λ_lt_eps_of_eps_pos
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (h_eps_pos : 0 < ∑ Γ ∈
      (IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ)).erase ∅,
      ∏ P ∈ Γ, t ^ P.card) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) t <
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ)).erase ∅,
        ∏ P ∈ Γ, t ^ P.card :=
  IsingModel.polymerFreeEnergy_lt_eps_of_eps_pos (inducedGraph G Λ) h_eps_pos

/-- **Λ-layer: `polymerFreeEnergy ≤ (1+t)^|E| - 1` under `0 ≤ t`** (§18.4 Λ wrap). -/
theorem polymerFreeEnergy_Λ_le_pow_sub_one_of_nonneg
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) t ≤
      (1 + t) ^ (inducedGraph G Λ).edgeFinset.card - 1 :=
  IsingModel.polymerFreeEnergy_le_pow_sub_one_of_nonneg (inducedGraph G Λ) ht

/-- **Λ-layer: `polymerFreeEnergy < log 2` under `(1+t)^|E| < 2` and
`0 ≤ t`** (§18.4 Λ wrap). -/
theorem polymerFreeEnergy_Λ_lt_log_two_of_pow_lt_two
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t)
    (h_pow : (1 + t) ^ (inducedGraph G Λ).edgeFinset.card < 2) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) t < Real.log 2 :=
  IsingModel.polymerFreeEnergy_lt_log_two_of_pow_lt_two (inducedGraph G Λ) ht h_pow

/-- **Λ-layer: `vdSum > 1 ↔ ε > 0` under `0 ≤ t`** (§18.4 Λ wrap). -/
theorem vdPolymerFamilies_sum_Λ_gt_one_iff_eps_pos
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    1 < (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
            ∏ P ∈ Γ, t ^ P.card) ↔
      0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ)).erase ∅,
        ∏ P ∈ Γ, t ^ P.card :=
  IsingModel.vdPolymerFamilies_sum_gt_one_iff_eps_pos (inducedGraph G Λ) ht

/-- **Λ-layer: `vdSum = 1 ↔ ε = 0`** (§18.4 Λ wrap). -/
theorem vdPolymerFamilies_sum_Λ_eq_one_iff_eps_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (t : ℝ) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
        ∏ P ∈ Γ, t ^ P.card) = 1 ↔
      (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ)).erase ∅,
        ∏ P ∈ Γ, t ^ P.card) = 0 :=
  IsingModel.vdPolymerFamilies_sum_eq_one_iff_eps_eq_zero (inducedGraph G Λ) t

/-! ### §18.4 mayerExpansionTerm / mayerPartialSum Λ-layer wrappers -/

/-- **Λ-layer: `mayerExpansionTerm = 0` for graphs with no polymers** (§18.4 Λ wrap). -/
theorem mayerExpansionTerm_Λ_eq_zero_of_no_polymers
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (h_no : IsingModel.allPolymers (inducedGraph G Λ) = ∅) (n : ℕ) (t : ℝ) :
    IsingModel.mayerExpansionTerm (inducedGraph G Λ) n t = 0 :=
  IsingModel.mayerExpansionTerm_eq_zero_of_no_polymers (inducedGraph G Λ) h_no n t

/-- **Λ-layer: `mayerPartialSum G 0 t = 0`** (§18.4 Λ wrap). -/
theorem mayerPartialSum_Λ_zero_eq_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (t : ℝ) :
    IsingModel.mayerPartialSum (inducedGraph G Λ) 0 t = 0 :=
  IsingModel.mayerPartialSum_zero_eq_zero (inducedGraph G Λ) t

/-- **Λ-layer: `mayerPartialSum G 1 t > 0` under `0 < t` and polymers exist**
(§18.4 Λ wrap). -/
theorem mayerPartialSum_Λ_one_pos_of_t_pos_of_polymers_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (h_t_pos : 0 < t)
    (h_poly : (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty) :
    0 < IsingModel.mayerPartialSum (inducedGraph G Λ) 1 t :=
  IsingModel.mayerPartialSum_one_pos_of_t_pos_of_polymers_nonempty
    (inducedGraph G Λ) h_t_pos h_poly

/-- **Λ-layer: `mayerPartialSum G 1 t ≥ 0` under `0 ≤ t`** (§18.4 Λ wrap). -/
theorem mayerPartialSum_Λ_one_nonneg_of_nonneg
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ IsingModel.mayerPartialSum (inducedGraph G Λ) 1 t :=
  IsingModel.mayerPartialSum_one_nonneg_of_nonneg (inducedGraph G Λ) ht

/-- **Λ-layer: `mayerExpansionTerm` filter to connected polymer
sequences** (§18.4 Λ wrap of PR #1521). -/
theorem mayerExpansionTerm_Λ_filter_connected
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (n : ℕ) (t : ℝ) :
    IsingModel.mayerExpansionTerm (inducedGraph G Λ) n t =
      ∑ ω ∈ (Fintype.piFinset
          (fun _ : Fin n => IsingModel.allPolymers (inducedGraph G Λ))).filter
        (fun ω => (IsingModel.polymerSeqIncompatibilityGraph ω).Connected),
        IsingModel.ursellCoefficient ω * IsingModel.clusterSeqActivity t ω :=
  IsingModel.mayerExpansionTerm_filter_connected (inducedGraph G Λ) n t

/-- **Λ-layer: `mayerPartialSum` filter to connected polymer sequences**
(§18.4 Λ wrap of PR #1522). -/
theorem mayerPartialSum_Λ_filter_connected
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (N : ℕ) (t : ℝ) :
    IsingModel.mayerPartialSum (inducedGraph G Λ) N t =
      ∑ n ∈ Finset.range (N + 1),
        ∑ ω ∈ (Fintype.piFinset
            (fun _ : Fin n => IsingModel.allPolymers (inducedGraph G Λ))).filter
          (fun ω => (IsingModel.polymerSeqIncompatibilityGraph ω).Connected),
          IsingModel.ursellCoefficient ω * IsingModel.clusterSeqActivity t ω :=
  IsingModel.mayerPartialSum_filter_connected (inducedGraph G Λ) N t

end Ambient

end IsingModel
