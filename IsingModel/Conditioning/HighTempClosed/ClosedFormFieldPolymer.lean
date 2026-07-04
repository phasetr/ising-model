import IsingModel.ClusterExpansion.Families.FieldConnectedPolymers

/-!
# Field-dependent high-temperature closed form as a polymer gas (GJ §17.6.1, brick 2a)

Capstone of brick 2a: substituting the field-dependent polymer factorization
identity `allSubgraphs_sum_eq_vdConnectedPolymerFamilies_sum`
(`ClusterExpansion/Families/FieldConnectedPolymers.lean`) into the first-brick
closed form `partitionFunction_high_temp_expansion_field_closed`
(`Conditioning/HighTempClosed/ClosedFormField.lean`) exhibits the finite-volume
Ising partition function as a hard-core (vertex-disjoint) polymer gas with the
field-dependent activity `w(P) = tanh(βJ)^|P|·tanh(βh)^{#odd(P)}`:
\[
Z(G;J,h,\beta)=2^{|\iota|}\cosh(\beta J)^{|E|}\cosh(\beta h)^{|\iota|}
  \sum_{\Gamma\in\mathtt{vdConnectedPolymerFamilies}\ G}
    \prod_{P\in\Gamma} w_{\beta J,\beta h}(P).
\]
The field enters only through `tanh(βh)^{#odd(P)}`; the polymers still live on
`G` with bounded degree, so no maximum-degree blow-up occurs. This is a purely
finite combinatorial identity; convergence content (Kotecky–Preiss activity
bounds, `h`-analyticity) is brick 2b onward.

References: Friedli–Velenik §3.7.3, eq. (3.45), p. 117 (2017 ed.) (`h = 0`
template); Friedli–Velenik §5.7 (polymer gas); Glimm–Jaffe §18.4 (lattice
cluster expansion, field version).
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Field-dependent high-temperature closed form as a polymer gas**
(GJ §17.6.1, brick 2a capstone):
`Z(G;J,h,β) = 2^|ι|·cosh(βJ)^|E|·cosh(βh)^|ι| ·
  ∑_{Γ ∈ vdConnectedPolymerFamilies G} ∏_{P ∈ Γ} fieldPolymerWeight (βJ) (βh) P`.

Obtained by rewriting the first-brick closed form
`partitionFunction_high_temp_expansion_field_closed` with the polymer
factorization identity `allSubgraphs_sum_eq_vdConnectedPolymerFamilies_sum`.
No axiom, no `sorry`, no new analytic input.

References: Friedli–Velenik §3.7.3, eq. (3.45), p. 117 (2017 ed.); Glimm–Jaffe
§18.4 (lattice cluster expansion, field version). -/
theorem partitionFunction_high_temp_expansion_field_polymer_family
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J h β : ℝ) :
    partitionFunction G ⟨J, h, β⟩ =
      (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card *
        Real.cosh (β * h) ^ Fintype.card ι *
      ∑ Γ ∈ vdConnectedPolymerFamilies G,
        ∏ P ∈ Γ, fieldPolymerWeight (β * J) (β * h) P := by
  rw [partitionFunction_high_temp_expansion_field_closed G J h β,
      allSubgraphs_sum_eq_vdConnectedPolymerFamilies_sum G (β * J) (β * h)]


end IsingModel
