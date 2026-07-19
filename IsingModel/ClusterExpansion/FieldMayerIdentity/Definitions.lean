import IsingModel.ClusterExpansion.FieldMayerTerm
import IsingModel.ClusterExpansion.Families.FieldConnectedPolymers
import IsingModel.ClusterExpansion.MayerCore.LogTaylor
import IsingModel.ClusterExpansion.MayerCore.MayerMontroll.ProperColorings

/-!
# Field Mayer–Montroll identity: base definitions and the `log(1 + ε)` side
(GJ §17.6.1, brick 4 — child 1 of 4)

Base definitions (`fieldPolymerZ`, `fieldPolymerFreeEnergy`, the shared colour-degree
hub `fieldColorDegreeTerm`) plus the analytic `log(1 + ε_{a,b})` side (L1) of the
split `FieldMayerIdentity` umbrella.  See `FieldMayerIdentity.lean` for the full
module overview.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## New definitions: field polymer partition function, free energy, colour term -/

/-- **Field polymer partition function**
`fieldPolymerZ G a b := ∑_{Γ ∈ vdConnectedPolymerFamilies G} ∏_{P ∈ Γ} w_{a,b}(P)`,
the hard-core gas of the connected field polymers.  By brick 2a
(`allSubgraphs_sum_eq_vdConnectedPolymerFamilies_sum`) this equals the reduced
field partition function `Z/(2^|ι|·cosh(a)^|E|·cosh(b)^|ι|)` at `a = βJ, b = βh`.
Field mirror of the `h = 0` reduced sum in `polymerFreeEnergy`. -/
noncomputable def fieldPolymerZ (G : SimpleGraph ι) [Fintype G.edgeSet]
    (a b : ℝ) : ℝ :=
  ∑ Γ ∈ vdConnectedPolymerFamilies G, ∏ P ∈ Γ, fieldPolymerWeight a b P

/-- **Field polymer free energy** `fieldPolymerFreeEnergy G a b := log(fieldPolymerZ G a b)`,
the field mirror of `polymerFreeEnergy G t := log(∑_Γ ∏ t^|P|)`
(`MayerCore/PolymerFreeEnergy.lean`).  The Mayer–Montroll identity below reads
`fieldPolymerFreeEnergy G a b = ∑' n, fieldMayerExpansionTerm G n a b`. -/
noncomputable def fieldPolymerFreeEnergy (G : SimpleGraph ι) [Fintype G.edgeSet]
    (a b : ℝ) : ℝ :=
  Real.log (fieldPolymerZ G a b)

/-- **`fieldPolymerZ` equals the reduced field partition sum** (brick 2a landing):
`fieldPolymerZ G a b = ∑_{X ⊆ E} tanh(a)^|X|·tanh(b)^{#odd(X)}`.  A definitional
restatement of `allSubgraphs_sum_eq_vdConnectedPolymerFamilies_sum`, confirming
`fieldPolymerFreeEnergy` is genuinely the log of the reduced field partition
function (needed by the non-vanishing bricks). -/
theorem fieldPolymerZ_eq_allSubgraphs_sum (G : SimpleGraph ι) [Fintype G.edgeSet]
    (a b : ℝ) :
    fieldPolymerZ G a b =
      ∑ X ∈ G.edgeFinset.powerset,
        Real.tanh a ^ X.card *
          Real.tanh b ^
            (Finset.univ.filter
              (fun v => Odd ((X.filter (v ∈ ·)).card))).card := by
  rw [fieldPolymerZ, ← allSubgraphs_sum_eq_vdConnectedPolymerFamilies_sum]

/-- **Field colour-degree term** `fC(r,k)`: the `(r,k)` contribution of the field
Mayer expansion,
`(-1)^(k-1)/k · ∑_ω #properSurjectiveColorings(G(ω),k)/r! · fieldClusterSeqActivity a b ω`.
Field mirror of `colorDegreeTerm` (`MayerMontroll.lean`) with the activity
`clusterSeqActivity t ω ⤳ fieldClusterSeqActivity a b ω` and the reference
species `allPolymers G ⤳ allConnectedPolymers G`; the combinatorial prefactor is
identical.  Summing over `k ∈ Icc 1 r` gives `fieldMayerExpansionTerm G r a b`;
over `r ≤ k·|allConnectedPolymers G|` gives the `k`-th log-Taylor term. -/
noncomputable def fieldColorDegreeTerm (G : SimpleGraph ι) [Fintype G.edgeSet]
    (a b : ℝ) (r k : ℕ) : ℝ :=
  ((-1 : ℝ) ^ (k - 1) / (k : ℝ)) *
    ∑ ω ∈ Fintype.piFinset (fun _ : Fin r => allConnectedPolymers G),
      ((properSurjectiveColorings (polymerSeqIncompatibilityGraph ω) k).card : ℝ) /
        (r.factorial : ℝ) * fieldClusterSeqActivity a b ω

/-! ## L1: the analytic `log(1 + ε_{a,b})` side -/

/-- **`fieldPolymerZ` split as `1 + ε_{a,b}`**: peeling off the empty family
(whose product is `1`), `fieldPolymerZ G a b = 1 + ∑_{Γ ≠ ∅} ∏_{P ∈ Γ} w_{a,b}(P)`.
Field mirror of `vdPolymerFamilies_sum_eq_one_add` (`PolymerFreeEnergy.lean`). -/
theorem fieldPolymerZ_eq_one_add (G : SimpleGraph ι) [Fintype G.edgeSet] (a b : ℝ) :
    fieldPolymerZ G a b =
      1 + ∑ Γ ∈ (vdConnectedPolymerFamilies G).erase ∅,
            ∏ P ∈ Γ, fieldPolymerWeight a b P := by
  classical
  have h_empty_in :
      (∅ : Finset (Finset (Sym2 ι))) ∈ vdConnectedPolymerFamilies G := by
    rw [mem_vdConnectedPolymerFamilies]
    refine ⟨Finset.empty_subset _, ?_⟩
    simp only [Finset.coe_empty, Set.pairwise_empty]
  rw [fieldPolymerZ,
    show vdConnectedPolymerFamilies G =
        insert (∅ : Finset (Finset (Sym2 ι)))
          ((vdConnectedPolymerFamilies G).erase ∅) from
        (Finset.insert_erase h_empty_in).symm,
    Finset.sum_insert (Finset.notMem_erase _ _),
    Finset.prod_empty,
    Finset.erase_insert (Finset.notMem_erase _ _)]

/-- **`fieldPolymerFreeEnergy = log(1 + ε_{a,b})`**: rewrite via
`fieldPolymerZ_eq_one_add`, the entry to the `log(1 + x)` Taylor series.  Field
mirror of `polymerFreeEnergy_eq_log_one_add_eps` (`LogTaylor.lean`). -/
theorem fieldPolymerFreeEnergy_eq_log_one_add_eps (G : SimpleGraph ι)
    [Fintype G.edgeSet] (a b : ℝ) :
    fieldPolymerFreeEnergy G a b =
      Real.log (1 + ∑ Γ ∈ (vdConnectedPolymerFamilies G).erase ∅,
        ∏ P ∈ Γ, fieldPolymerWeight a b P) := by
  rw [fieldPolymerFreeEnergy, fieldPolymerZ_eq_one_add]

/-- **Field polymer free energy log-Taylor series**: when `|ε_{a,b}| < 1`,
`fieldPolymerFreeEnergy G a b = ∑_n (-1)^n · ε_{a,b}^(n+1)/(n+1)` as a `HasSum`.
Applies the weight-agnostic real-analytic `log(1 + x)` Taylor lemma
`hasSum_real_log_one_add_of_abs_lt_one` (`LogTaylor.lean`, reused verbatim) to
`x = ε_{a,b}`.  Field mirror of `polymerFreeEnergy_hasSum_via_log`. -/
theorem fieldPolymerFreeEnergy_hasSum_via_log (G : SimpleGraph ι) [Fintype G.edgeSet]
    {a b : ℝ}
    (h_abs : |∑ Γ ∈ (vdConnectedPolymerFamilies G).erase ∅,
                ∏ P ∈ Γ, fieldPolymerWeight a b P| < 1) :
    HasSum (fun n : ℕ =>
        (-1 : ℝ) ^ n *
          (∑ Γ ∈ (vdConnectedPolymerFamilies G).erase ∅,
            ∏ P ∈ Γ, fieldPolymerWeight a b P) ^ (n + 1) /
          (n + 1))
      (fieldPolymerFreeEnergy G a b) := by
  rw [fieldPolymerFreeEnergy_eq_log_one_add_eps]
  exact hasSum_real_log_one_add_of_abs_lt_one h_abs

end IsingModel
