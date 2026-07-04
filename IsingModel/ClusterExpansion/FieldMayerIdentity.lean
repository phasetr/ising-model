import IsingModel.ClusterExpansion.FieldMayerTerm
import IsingModel.ClusterExpansion.Families.FieldConnectedPolymers
import IsingModel.ClusterExpansion.MayerCore.MayerMontroll
import IsingModel.ClusterExpansion.MayerCore.LogTaylor

/-!
# Field-dependent Mayer–Montroll identity `log Ξ_{a,b} = ∑ₙ fieldMayerExpansionTerm`
(GJ §17.6.1, brick 4)

Brick 4 of the on-book programme toward Glimm–Jaffe (GJ) Theorem 17.6.1
(`∂/∂h` infinite-volume differentiability / `h`-analyticity of the two-point
function in the high-temperature window).  This file supplies the **algebraic
Mayer–Montroll identity** for the field-dependent hard-core polymer gas: the
field polymer free energy (the log of the field polymer partition function)
equals the field Mayer series,
`fieldPolymerFreeEnergy G a b = ∑' n, fieldMayerExpansionTerm G n a b`.

This is the field generalisation of the already-formalised `h = 0` identity
`mayer_identity_general_t` (`MayerCore/MayerMontroll.lean`, PR #3998), obtained by
carrying the multiplicative field weight
`w_{a,b}(P) = tanh(a)^|P|·tanh(b)^{#odd(P)}` (`fieldPolymerWeight`,
`Families/FieldConnectedPolymers.lean`) through the identical colour-degree /
log-Taylor / Fubini tower over the *connected* species `allConnectedPolymers G`.
The combinatorial coefficients (`ursellCoefficient`, `properSurjectiveColorings`
counts, the incompatibility graph) are weight-agnostic and reused *verbatim* from
`MayerMontroll.lean`; the genuinely new content is re-running the weight-carrying
`Finset` regroupings with `w_{a,b}` in place of the monomial `t^|P|`, and
supplying the analytic `log(1 + ε)` side over the field `ε`.  Convergence is
imported from brick 3 (`summable_fieldMayerExpansionTerm`, the
domination `|fieldClusterSeqActivity a b ω| ≤ clusterSeqActivity |tanh a| ω`).

Real `h` only; complex `h` (where `|tanh b|` need not be `≤ 1`) is deferred to the
later non-vanishing brick.  Regression at `b = 0`: `tanh 0 = 0`, so
`fieldPolymerWeight a 0 P = tanh(a)^|P|·0^{#odd(P)}` collapses to `tanh(a)^|P|` on
even polymers and vanishes otherwise, so `fieldPolymerZ G a 0` reduces to the
even-species reduced partition sum and the identity lands on the `h = 0`
`mayer_identity_general_t` up to the species relabelling `allPolymers ⤳
allConnectedPolymers`.

## References
- Glimm–Jaffe, *Quantum Physics*, 2nd ed., §18.4–§18.5, pp. 378–386
  (lattice cluster expansion, field version).
- Friedli–Velenik, *Statistical Mechanics of Lattice Systems* (2017), §5.7.3
  (Mayer–Montroll) and §3.7.3, eqs. (3.48)–(3.49) (magnetic-field expansion).
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

/-! ## L2: species / colour-class ports (connected species) -/

/-- **Colour classes of a proper surjective colouring are nonempty vertex-disjoint
connected families**: for `ω` valued in `allConnectedPolymers G` and a proper
colouring of its incompatibility graph, each colour class lies in
`(vdConnectedPolymerFamilies G).erase ∅`.  Field mirror of
`colorClass_mem_vdCompatiblePolymerFamilies`; simpler since the connected
membership carries no `IsPolymer` clause. -/
theorem fieldColorClass_mem_vdConnectedPolymerFamilies
    (G : SimpleGraph ι) [Fintype G.edgeSet] {r : ℕ} {ω : Fin r → Finset (Sym2 ι)}
    (hω : ∀ i, ω i ∈ allConnectedPolymers G) {k : ℕ} {c : Fin r → Fin k}
    (hproper : IsProperColoring (polymerSeqIncompatibilityGraph ω) k c)
    (hsurj : Function.Surjective c) (x : Fin k) :
    colorClass ω c x ∈ (vdConnectedPolymerFamilies G).erase ∅ := by
  rw [Finset.mem_erase]
  refine ⟨(colorClass_nonempty hsurj x).ne_empty, ?_⟩
  rw [mem_vdConnectedPolymerFamilies]
  refine ⟨?_, ?_⟩
  · intro Q hQ
    obtain ⟨i, _, rfl⟩ := mem_colorClass.mp hQ
    exact hω i
  · intro P hP Q hQ hPQ
    obtain ⟨i, hi, rfl⟩ := mem_colorClass.mp (Finset.mem_coe.mp hP)
    obtain ⟨j, hj, rfl⟩ := mem_colorClass.mp (Finset.mem_coe.mp hQ)
    have hij : i ≠ j := fun h => hPQ (by rw [h])
    have hnotadj : ¬ (polymerSeqIncompatibilityGraph ω).Adj i j := fun hadj =>
      hproper i j hadj (hi.trans hj.symm)
    rw [polymerSeqIncompatibilityGraph_adj] at hnotadj
    have hcompat : ¬ PolymersIncompatible (ω i) (ω j) := fun hinc => hnotadj ⟨hij, hinc⟩
    rwa [PolymersIncompatible.iff_not_isPolymerVertexDisjoint, not_not] at hcompat

/-- **A polymer sequence over `allConnectedPolymers` is injective on each colour
class**: two equal-coloured indices with equal polymers coincide (same-colour
indices are non-adjacent, hence vertex-disjoint, and a nonempty polymer is not
vertex-disjoint from itself).  Field mirror of `seq_injective_on_colorClass`. -/
theorem fieldSeq_injective_on_colorClass
    (G : SimpleGraph ι) [Fintype G.edgeSet] {r : ℕ} {ω : Fin r → Finset (Sym2 ι)}
    (hω : ∀ i, ω i ∈ allConnectedPolymers G) {m : ℕ} {c : Fin r → Fin m}
    (hproper : IsProperColoring (polymerSeqIncompatibilityGraph ω) m c)
    {i j : Fin r} (hc : c i = c j) (hωij : ω i = ω j) : i = j := by
  by_contra hij
  have hnotadj : ¬ (polymerSeqIncompatibilityGraph ω).Adj i j := fun hadj => hproper i j hadj hc
  rw [polymerSeqIncompatibilityGraph_adj] at hnotadj
  have hvd : IsPolymerVertexDisjoint (ω i) (ω j) := by
    by_contra hinc
    exact hnotadj ⟨hij, (PolymersIncompatible.iff_not_isPolymerVertexDisjoint).mpr hinc⟩
  rw [hωij] at hvd
  exact not_isPolymerVertexDisjoint_self_of_nonempty
    (mem_allConnectedPolymers.mp (hω j)).nonempty hvd

/-- **Field activity factor as a product over colour classes**: for `ω` valued in
`allConnectedPolymers G` and a proper colouring `c` of its incompatibility graph,
`fieldClusterSeqActivity a b ω = ∏_x ∏_{P ∈ colorClass ω c x} w_{a,b}(P)`.  Group
the sequence indices by colour and use injectivity of `ω` on each class (the field
weight is a per-polymer multiplicative label).  Field mirror of
`clusterSeqActivity_eq_prod_colorClass`. -/
theorem fieldClusterSeqActivity_eq_prod_colorClass
    (G : SimpleGraph ι) [Fintype G.edgeSet] (a b : ℝ) {r : ℕ}
    {ω : Fin r → Finset (Sym2 ι)}
    (hω : ∀ i, ω i ∈ allConnectedPolymers G) {m : ℕ} {c : Fin r → Fin m}
    (hproper : IsProperColoring (polymerSeqIncompatibilityGraph ω) m c) :
    fieldClusterSeqActivity a b ω =
      ∏ x : Fin m, ∏ P ∈ colorClass ω c x, fieldPolymerWeight a b P := by
  classical
  rw [fieldClusterSeqActivity,
    ← Finset.prod_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ) (g := c)
      (f := fun i => fieldPolymerWeight a b (ω i)) (fun i _ => Finset.mem_univ (c i))]
  refine Finset.prod_congr rfl (fun x _ => ?_)
  have hinj : ∀ i ∈ Finset.univ.filter (fun i => c i = x),
      ∀ j ∈ Finset.univ.filter (fun i => c i = x), ω i = ω j → i = j := by
    intro i hi j hj hij
    rw [Finset.mem_filter] at hi hj
    exact fieldSeq_injective_on_colorClass G hω hproper (hi.2.trans hj.2.symm) hij
  have hcc : colorClass ω c x = (Finset.univ.filter (fun i => c i = x)).image ω := rfl
  rw [hcc, Finset.prod_image hinj]

/-- **Forward map is injective** (connected species): distinct indices give
distinct labelled polymers, via `fieldSeq_injective_on_colorClass`.  Field mirror
of `seqColoringForward_injective` (`seqColoringForward` itself is species-agnostic
and reused verbatim). -/
theorem fieldSeqColoringForward_injective {r m : ℕ} (G : SimpleGraph ι)
    [Fintype G.edgeSet] {Ω : Fin m → Finset (Finset (Sym2 ι))}
    {ω : Fin r → Finset (Sym2 ι)} {c : Fin r → Fin m}
    (hω : ∀ i, ω i ∈ allConnectedPolymers G)
    (hproper : IsProperColoring (polymerSeqIncompatibilityGraph ω) m c)
    (hcolor : ∀ x, colorClass ω c x = Ω x) :
    Function.Injective (seqColoringForward hcolor) := by
  intro i j hij
  simp only [seqColoringForward, Subtype.mk.injEq, Sigma.mk.injEq, heq_eq_eq] at hij
  exact fieldSeq_injective_on_colorClass G hω hproper hij.1 hij.2

/-- **Inverse colouring is proper** (connected species): the colouring induced by
a bijection `e : Fin r ≃ labelledPolymers Ω` is proper for the incompatibility
graph, using pairwise vertex-disjointness of each family `Ω x`.  Field mirror of
`invProper` with the `IsCompatiblePolymerFamilyVertexDisjoint` hypothesis replaced
by the bare pairwise clause carried by connected families. -/
theorem fieldInvProper {r m : ℕ}
    {Ω : Fin m → Finset (Finset (Sym2 ι))}
    (hΩ : ∀ x, (↑(Ω x) : Set (Finset (Sym2 ι))).Pairwise IsPolymerVertexDisjoint)
    (e : Fin r ≃ ↥(labelledPolymers Ω)) :
    IsProperColoring (polymerSeqIncompatibilityGraph (fun i => (e i).val.2)) m
      (fun i => (e i).val.1) := by
  intro i j hadj hc
  rw [polymerSeqIncompatibilityGraph_adj] at hadj
  dsimp only at hc
  have hne : (e i).val.2 ≠ (e j).val.2 := by
    intro hP
    apply hadj.1
    apply e.injective
    apply Subtype.ext
    apply Sigma.ext hc
    rw [heq_eq_eq]; exact hP
  have hmi := mem_labelledPolymers.mp (e i).property
  have hmj := mem_labelledPolymers.mp (e j).property
  have hmj' : (e j).val.2 ∈ Ω ((e i).val.1) := by rw [hc]; exact hmj
  have hvd : IsPolymerVertexDisjoint (e i).val.2 (e j).val.2 :=
    (hΩ ((e i).val.1)) (Finset.mem_coe.mpr hmi) (Finset.mem_coe.mpr hmj') hne
  exact (PolymersIncompatible.iff_not_isPolymerVertexDisjoint.mp hadj.2) hvd

/-- **Colour-class fibre cardinality is `r!`** (connected species): the pairs
`(ω, c)` — a polymer sequence over `allConnectedPolymers G` and a proper colouring
whose colour classes are exactly `Ω` — number `r!` (they biject with the orderings
`Fin r ≃ labelledPolymers Ω`).  Field mirror of `card_proper_colorClass_fiber`. -/
theorem fieldCard_proper_colorClass_fiber {r m : ℕ} (G : SimpleGraph ι)
    [Fintype G.edgeSet] {Ω : Fin m → Finset (Finset (Sym2 ι))}
    (hΩ : ∀ x, Ω x ∈ vdConnectedPolymerFamilies G)
    (hr : r = (labelledPolymers Ω).card) :
    Fintype.card {p : (Fin r → Finset (Sym2 ι)) × (Fin r → Fin m) //
        (∀ i, p.1 i ∈ allConnectedPolymers G) ∧
        IsProperColoring (polymerSeqIncompatibilityGraph p.1) m p.2 ∧
        (∀ x, colorClass p.1 p.2 x = Ω x)} = r.factorial := by
  classical
  have hsub : ∀ x, Ω x ⊆ allConnectedPolymers G :=
    fun x => (mem_vdConnectedPolymerFamilies.mp (hΩ x)).1
  have hvd : ∀ x, (↑(Ω x) : Set (Finset (Sym2 ι))).Pairwise IsPolymerVertexDisjoint :=
    fun x => (mem_vdConnectedPolymerFamilies.mp (hΩ x)).2
  have E : {p : (Fin r → Finset (Sym2 ι)) × (Fin r → Fin m) //
        (∀ i, p.1 i ∈ allConnectedPolymers G) ∧
        IsProperColoring (polymerSeqIncompatibilityGraph p.1) m p.2 ∧
        (∀ x, colorClass p.1 p.2 x = Ω x)} ≃ (Fin r ≃ ↥(labelledPolymers Ω)) :=
    { toFun := fun q => Equiv.ofBijective (seqColoringForward q.2.2.2)
        ⟨fieldSeqColoringForward_injective G q.2.1 q.2.2.1 q.2.2.2,
          seqColoringForward_surjective q.2.2.2⟩
      invFun := fun e => ⟨(fun i => (e i).val.2, fun i => (e i).val.1),
        fun i => hsub _ (mem_labelledPolymers.mp (e i).property), fieldInvProper hvd e,
        invColorClass e⟩
      left_inv := fun q => by apply Subtype.ext; rfl
      right_inv := fun e => by
        apply Equiv.ext; intro i; apply Subtype.ext; rfl }
  rw [Fintype.card_congr E]
  have hcard : Fintype.card (Fin r) = Fintype.card ↥(labelledPolymers Ω) := by
    rw [Fintype.card_fin, Fintype.card_coe, ← hr]
  rw [Fintype.card_equiv (Fintype.equivOfCardEq hcard), Fintype.card_fin]

/-- **Fibre activity sum is `r! · W_{a,b}(Ω)`**: summing the field activity over all
`(ω, c)` whose colour classes are `Ω` gives `r!` copies of the family field weight
`∏_x ∏_{P ∈ Ω x} w_{a,b}(P)`.  Field mirror of `fiber_sum_clusterSeqActivity`. -/
theorem fieldFiber_sum_fieldClusterSeqActivity {r m : ℕ} (G : SimpleGraph ι)
    [Fintype G.edgeSet] (a b : ℝ) {Ω : Fin m → Finset (Finset (Sym2 ι))}
    (hΩ : ∀ x, Ω x ∈ vdConnectedPolymerFamilies G)
    (hr : r = (labelledPolymers Ω).card) :
    ∑ q : {p : (Fin r → Finset (Sym2 ι)) × (Fin r → Fin m) //
        (∀ i, p.1 i ∈ allConnectedPolymers G) ∧
        IsProperColoring (polymerSeqIncompatibilityGraph p.1) m p.2 ∧
        (∀ x, colorClass p.1 p.2 x = Ω x)}, fieldClusterSeqActivity a b q.1.1 =
      (r.factorial : ℝ) * ∏ x : Fin m, ∏ P ∈ Ω x, fieldPolymerWeight a b P := by
  classical
  have hconst : ∀ q : {p : (Fin r → Finset (Sym2 ι)) × (Fin r → Fin m) //
        (∀ i, p.1 i ∈ allConnectedPolymers G) ∧
        IsProperColoring (polymerSeqIncompatibilityGraph p.1) m p.2 ∧
        (∀ x, colorClass p.1 p.2 x = Ω x)},
      fieldClusterSeqActivity a b q.1.1 =
        ∏ x : Fin m, ∏ P ∈ Ω x, fieldPolymerWeight a b P := by
    intro q
    rw [fieldClusterSeqActivity_eq_prod_colorClass G a b q.2.1 q.2.2.1]
    exact Finset.prod_congr rfl (fun x _ => by rw [q.2.2.2 x])
  rw [Finset.sum_congr rfl (fun q _ => hconst q), Finset.sum_const, Finset.card_univ,
    fieldCard_proper_colorClass_fiber G hΩ hr, nsmul_eq_mul]

open Classical in
/-- **Fibre activity sum as a `Finset`-filter sum**: the product-subtype fibre sum
rewritten as a sum over the `Finset` of `(ω, c)` satisfying the fibre predicate.
Field mirror of `fiber_filter_sum`. -/
theorem fieldFiber_filter_sum {r m : ℕ} (G : SimpleGraph ι) [Fintype G.edgeSet]
    (a b : ℝ) {Ω : Fin m → Finset (Finset (Sym2 ι))}
    (hΩ : ∀ x, Ω x ∈ vdConnectedPolymerFamilies G)
    (hr : r = (labelledPolymers Ω).card) :
    ∑ p ∈ (Finset.univ : Finset ((Fin r → Finset (Sym2 ι)) × (Fin r → Fin m))).filter
        (fun p => (∀ i, p.1 i ∈ allConnectedPolymers G) ∧
          IsProperColoring (polymerSeqIncompatibilityGraph p.1) m p.2 ∧
          (∀ x, colorClass p.1 p.2 x = Ω x)), fieldClusterSeqActivity a b p.1 =
      (r.factorial : ℝ) * ∏ x : Fin m, ∏ P ∈ Ω x, fieldPolymerWeight a b P := by
  classical
  rw [Finset.sum_subtype (Finset.univ.filter
        (fun p : (Fin r → Finset (Sym2 ι)) × (Fin r → Fin m) =>
          (∀ i, p.1 i ∈ allConnectedPolymers G) ∧
            IsProperColoring (polymerSeqIncompatibilityGraph p.1) m p.2 ∧
            (∀ x, colorClass p.1 p.2 x = Ω x)))
      (p := fun p => (∀ i, p.1 i ∈ allConnectedPolymers G) ∧
        IsProperColoring (polymerSeqIncompatibilityGraph p.1) m p.2 ∧
        (∀ x, colorClass p.1 p.2 x = Ω x))
      (fun x => by simp only [Finset.mem_filter, Finset.mem_univ, true_and])
      (fun p => fieldClusterSeqActivity a b p.1)]
  exact fieldFiber_sum_fieldClusterSeqActivity G a b hΩ hr

open Classical in
/-- **Colour-count sum as a product-`Finset` sum**: the field activity weighted by
the proper-surjective-colouring count over polymer sequences equals the field
activity summed over the `Finset` of `(ω, c)` pairs with `ω` valued in
`allConnectedPolymers` and `c` a proper surjective colouring.  Field mirror of
`seq_count_eq_product_sum`. -/
theorem fieldSeq_count_eq_product_sum {r m : ℕ} (G : SimpleGraph ι)
    [Fintype G.edgeSet] (a b : ℝ) :
    ∑ ω ∈ Fintype.piFinset (fun _ : Fin r => allConnectedPolymers G),
        ((properSurjectiveColorings (polymerSeqIncompatibilityGraph ω) m).card : ℝ) *
          fieldClusterSeqActivity a b ω =
      ∑ p ∈ (Finset.univ : Finset ((Fin r → Finset (Sym2 ι)) × (Fin r → Fin m))).filter
          (fun p => (∀ i, p.1 i ∈ allConnectedPolymers G) ∧
            IsProperColoring (polymerSeqIncompatibilityGraph p.1) m p.2 ∧
            Function.Surjective p.2), fieldClusterSeqActivity a b p.1 := by
  classical
  have hps : ∀ ω : Fin r → Finset (Sym2 ι),
      properSurjectiveColorings (polymerSeqIncompatibilityGraph ω) m =
      Finset.univ.filter (fun c : Fin r → Fin m =>
        IsProperColoring (polymerSeqIncompatibilityGraph ω) m c ∧ Function.Surjective c) := by
    intro ω
    ext c
    simp only [mem_properSurjectiveColorings, Finset.mem_filter, Finset.mem_univ, true_and]
  have hcount : ∀ ω : Fin r → Finset (Sym2 ι),
      ((properSurjectiveColorings (polymerSeqIncompatibilityGraph ω) m).card : ℝ) *
        fieldClusterSeqActivity a b ω =
      ∑ _c ∈ properSurjectiveColorings (polymerSeqIncompatibilityGraph ω) m,
        fieldClusterSeqActivity a b ω := by
    intro ω
    rw [Finset.sum_const, nsmul_eq_mul]
  simp_rw [hcount, hps]
  refine (Finset.sum_finset_product
    (Finset.univ.filter (fun p : (Fin r → Finset (Sym2 ι)) × (Fin r → Fin m) =>
      (∀ i, p.1 i ∈ allConnectedPolymers G) ∧
        IsProperColoring (polymerSeqIncompatibilityGraph p.1) m p.2 ∧ Function.Surjective p.2))
    (Fintype.piFinset (fun _ : Fin r => allConnectedPolymers G))
    (fun ω => Finset.univ.filter (fun c : Fin r → Fin m =>
      IsProperColoring (polymerSeqIncompatibilityGraph ω) m c ∧ Function.Surjective c))
    (fun p => ?_) (f := fun p => fieldClusterSeqActivity a b p.1)).symm
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]

open Classical in
/-- **Colour-count sum regrouped by colour classes** (fixed `r`): the field
activity-weighted proper-surjective-colouring count over length-`r` sequences
equals, summed over connected family-tuples `Ω`, the field activity over the fibre
of `(ω, c)` with colour classes `Ω`.  Field mirror of `seq_count_eq_fiberwise`. -/
theorem fieldSeq_count_eq_fiberwise {r m : ℕ} (G : SimpleGraph ι) [Fintype G.edgeSet]
    (a b : ℝ) :
    ∑ ω ∈ Fintype.piFinset (fun _ : Fin r => allConnectedPolymers G),
        ((properSurjectiveColorings (polymerSeqIncompatibilityGraph ω) m).card : ℝ) *
          fieldClusterSeqActivity a b ω =
      ∑ Ω ∈ Fintype.piFinset (fun _ : Fin m => (vdConnectedPolymerFamilies G).erase ∅),
        ∑ p ∈ (Finset.univ : Finset ((Fin r → Finset (Sym2 ι)) × (Fin r → Fin m))).filter
            (fun p => (∀ i, p.1 i ∈ allConnectedPolymers G) ∧
              IsProperColoring (polymerSeqIncompatibilityGraph p.1) m p.2 ∧
              (∀ x, colorClass p.1 p.2 x = Ω x)), fieldClusterSeqActivity a b p.1 := by
  classical
  rw [fieldSeq_count_eq_product_sum]
  have hmaps : ∀ p ∈ (Finset.univ :
        Finset ((Fin r → Finset (Sym2 ι)) × (Fin r → Fin m))).filter
      (fun p => (∀ i, p.1 i ∈ allConnectedPolymers G) ∧
        IsProperColoring (polymerSeqIncompatibilityGraph p.1) m p.2 ∧ Function.Surjective p.2),
      (fun x => colorClass p.1 p.2 x) ∈
        Fintype.piFinset (fun _ : Fin m => (vdConnectedPolymerFamilies G).erase ∅) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    rw [Fintype.mem_piFinset]
    exact fun x => fieldColorClass_mem_vdConnectedPolymerFamilies G hp.1 hp.2.1 hp.2.2 x
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun p => fieldClusterSeqActivity a b p.1)]
  refine Finset.sum_congr rfl (fun Ω hΩ => ?_)
  rw [Fintype.mem_piFinset] at hΩ
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, funext_iff]
  constructor
  · rintro ⟨⟨hap, hpr, _⟩, hcol⟩; exact ⟨hap, hpr, hcol⟩
  · rintro ⟨hap, hpr, hcol⟩
    refine ⟨⟨hap, hpr, fun x => ?_⟩, hcol⟩
    obtain ⟨P, hPmem⟩ := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp (hΩ x)).1
    rw [← hcol x] at hPmem
    obtain ⟨i, hci, _⟩ := mem_colorClass.mp hPmem
    exact ⟨i, hci⟩

open Classical in
/-- **Inner fibre sum evaluated**: for a connected family-tuple `Ω` of nonempty
vertex-disjoint families, the field activity over the `(ω, c)` fibre with colour
classes `Ω` is `r!·∏_x∏_{P∈Ω x} w_{a,b}(P)` when the total polymer count is `r`,
and `0` otherwise.  Field mirror of `fiber_filter_sum_eval`. -/
theorem fieldFiber_filter_sum_eval {r m : ℕ} (G : SimpleGraph ι) [Fintype G.edgeSet]
    (a b : ℝ) {Ω : Fin m → Finset (Finset (Sym2 ι))}
    (hΩ : ∀ x, Ω x ∈ (vdConnectedPolymerFamilies G).erase ∅) :
    ∑ p ∈ (Finset.univ : Finset ((Fin r → Finset (Sym2 ι)) × (Fin r → Fin m))).filter
        (fun p => (∀ i, p.1 i ∈ allConnectedPolymers G) ∧
          IsProperColoring (polymerSeqIncompatibilityGraph p.1) m p.2 ∧
          (∀ x, colorClass p.1 p.2 x = Ω x)), fieldClusterSeqActivity a b p.1 =
      if (labelledPolymers Ω).card = r then
        (r.factorial : ℝ) * ∏ x : Fin m, ∏ P ∈ Ω x, fieldPolymerWeight a b P else 0 := by
  classical
  have hΩ' : ∀ x, Ω x ∈ vdConnectedPolymerFamilies G :=
    fun x => (Finset.mem_erase.mp (hΩ x)).2
  by_cases hcard : (labelledPolymers Ω).card = r
  · rw [if_pos hcard]
    exact fieldFiber_filter_sum G a b hΩ' hcard.symm
  · rw [if_neg hcard]
    refine Finset.sum_eq_zero (fun p hp => ?_)
    exfalso
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨hap, hpr, hcol⟩ := hp
    apply hcard
    have e : Fin r ≃ ↥(labelledPolymers Ω) :=
      Equiv.ofBijective (seqColoringForward hcol)
        ⟨fieldSeqColoringForward_injective G hap hpr hcol, seqColoringForward_surjective hcol⟩
    have hc := Fintype.card_congr e
    rw [Fintype.card_fin, Fintype.card_coe] at hc
    exact hc.symm

open Classical in
/-- **Field family-tuple sum as a polymer-sequence colouring sum** (per-`m`
Mayer–Montroll identity): the connected family-tuple field-weight sum equals the
field activity-weighted proper-surjective-colouring count over polymer sequences
of all lengths, normalised by `1/r!`.  Field mirror of
`vdFamilyTuple_sum_eq_seq_coloring_sum`. -/
theorem fieldVdFamilyTuple_sum_eq_seq_coloring_sum {m : ℕ} (G : SimpleGraph ι)
    [Fintype G.edgeSet] (a b : ℝ) :
    (∑ Ω ∈ Fintype.piFinset (fun _ : Fin m => (vdConnectedPolymerFamilies G).erase ∅),
        ∏ i : Fin m, ∏ P ∈ Ω i, fieldPolymerWeight a b P) =
      ∑ r ∈ Finset.range (m * (allConnectedPolymers G).card + 1),
        ∑ ω ∈ Fintype.piFinset (fun _ : Fin r => allConnectedPolymers G),
          ((properSurjectiveColorings (polymerSeqIncompatibilityGraph ω) m).card : ℝ) /
            (r.factorial : ℝ) * fieldClusterSeqActivity a b ω := by
  classical
  have hr : ∀ r : ℕ,
      ∑ ω ∈ Fintype.piFinset (fun _ : Fin r => allConnectedPolymers G),
          ((properSurjectiveColorings (polymerSeqIncompatibilityGraph ω) m).card : ℝ) /
            (r.factorial : ℝ) * fieldClusterSeqActivity a b ω =
      ∑ Ω ∈ Fintype.piFinset (fun _ : Fin m => (vdConnectedPolymerFamilies G).erase ∅),
        (if (labelledPolymers Ω).card = r then
          ∏ x : Fin m, ∏ P ∈ Ω x, fieldPolymerWeight a b P else 0) := by
    intro r
    have key : ∑ ω ∈ Fintype.piFinset (fun _ : Fin r => allConnectedPolymers G),
        ((properSurjectiveColorings (polymerSeqIncompatibilityGraph ω) m).card : ℝ) *
          fieldClusterSeqActivity a b ω =
        ∑ Ω ∈ Fintype.piFinset (fun _ : Fin m => (vdConnectedPolymerFamilies G).erase ∅),
          (if (labelledPolymers Ω).card = r then
            (r.factorial : ℝ) *
              ∏ x : Fin m, ∏ P ∈ Ω x, fieldPolymerWeight a b P else 0) := by
      rw [fieldSeq_count_eq_fiberwise]
      refine Finset.sum_congr rfl (fun Ω hΩ => ?_)
      rw [Fintype.mem_piFinset] at hΩ
      exact fieldFiber_filter_sum_eval G a b hΩ
    rw [show (∑ ω ∈ Fintype.piFinset (fun _ : Fin r => allConnectedPolymers G),
          ((properSurjectiveColorings (polymerSeqIncompatibilityGraph ω) m).card : ℝ) /
            (r.factorial : ℝ) * fieldClusterSeqActivity a b ω) =
        (∑ ω ∈ Fintype.piFinset (fun _ : Fin r => allConnectedPolymers G),
          ((properSurjectiveColorings (polymerSeqIncompatibilityGraph ω) m).card : ℝ) *
            fieldClusterSeqActivity a b ω) / (r.factorial : ℝ) from by
        rw [Finset.sum_div]; exact Finset.sum_congr rfl (fun ω _ => by ring),
      key, Finset.sum_div]
    refine Finset.sum_congr rfl (fun Ω _ => ?_)
    split_ifs with h
    · rw [mul_div_cancel_left₀ _ (by positivity : (r.factorial : ℝ) ≠ 0)]
    · rw [zero_div]
  simp_rw [hr]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun Ω hΩ => ?_)
  rw [Fintype.mem_piFinset] at hΩ
  have hsub : ∀ x, Ω x ⊆ allConnectedPolymers G :=
    fun x => (mem_vdConnectedPolymerFamilies.mp (Finset.mem_erase.mp (hΩ x)).2).1
  have hlt : (labelledPolymers Ω).card < m * (allConnectedPolymers G).card + 1 := by
    rw [card_labelledPolymers]
    calc ∑ x : Fin m, (Ω x).card
        ≤ ∑ _x : Fin m, (allConnectedPolymers G).card :=
          Finset.sum_le_sum (fun x _ => Finset.card_le_card (hsub x))
      _ = m * (allConnectedPolymers G).card := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      _ < m * (allConnectedPolymers G).card + 1 := Nat.lt_succ_self _
  rw [Finset.sum_eq_single_of_mem ((labelledPolymers Ω).card) (Finset.mem_range.mpr hlt)
      (fun r _ hr => if_neg (fun h => hr h.symm)), if_pos rfl]

/-- **No proper surjective colouring of an over-long connected sequence**: for `ω`
valued in `allConnectedPolymers G`, if `r > m·|allConnectedPolymers G|` there is
no proper surjective `m`-colouring of its incompatibility graph.  Field mirror of
`properSurjectiveColorings_empty_of_card_lt`. -/
theorem fieldProperSurjectiveColorings_empty_of_card_lt {r m : ℕ} (G : SimpleGraph ι)
    [Fintype G.edgeSet] {ω : Fin r → Finset (Sym2 ι)}
    (hω : ∀ i, ω i ∈ allConnectedPolymers G)
    (hr : m * (allConnectedPolymers G).card < r) :
    properSurjectiveColorings (polymerSeqIncompatibilityGraph ω) m = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro c hc
  obtain ⟨hproper, hsurj⟩ := (mem_properSurjectiveColorings _).mp hc
  have e : Fin r ≃ ↥(labelledPolymers (colorClass ω c)) :=
    Equiv.ofBijective (seqColoringForward (fun x => rfl))
      ⟨fieldSeqColoringForward_injective G hω hproper (fun x => rfl),
        seqColoringForward_surjective (fun x => rfl)⟩
  have hcard : r = ∑ x : Fin m, (colorClass ω c x).card := by
    have hc := Fintype.card_congr e
    rw [Fintype.card_fin, Fintype.card_coe, card_labelledPolymers] at hc
    exact hc
  have hsub : ∀ x, colorClass ω c x ⊆ allConnectedPolymers G := by
    intro x P hP
    obtain ⟨i, _, rfl⟩ := mem_colorClass.mp hP
    exact hω i
  have hle : (∑ x : Fin m, (colorClass ω c x).card) ≤ m * (allConnectedPolymers G).card := by
    calc ∑ x : Fin m, (colorClass ω c x).card
        ≤ ∑ _x : Fin m, (allConnectedPolymers G).card :=
          Finset.sum_le_sum (fun x _ => Finset.card_le_card (hsub x))
      _ = m * (allConnectedPolymers G).card := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  omega

/-! ## L2 / L3: log-Taylor and Mayer bridges to `fieldColorDegreeTerm` -/

/-- **`ε_{a,b}^n` expansion as a sum over connected family-tuples**: applying
`Finset.sum_pow'`, `ε_{a,b}^n = ∑_ω ∏_i ∏_{P ∈ ω i} w_{a,b}(P)` over `n`-tuples of
nonempty vd connected families.  Field mirror of
`vdPolymerFamilies_sum_minus_one_pow`. -/
theorem fieldVdPolymerFamilies_sum_minus_one_pow (G : SimpleGraph ι) [Fintype G.edgeSet]
    (a b : ℝ) (n : ℕ) :
    (∑ Γ ∈ (vdConnectedPolymerFamilies G).erase ∅,
      ∏ P ∈ Γ, fieldPolymerWeight a b P) ^ n =
      ∑ ω ∈ Fintype.piFinset
              (fun _ : Fin n => (vdConnectedPolymerFamilies G).erase ∅),
        ∏ i : Fin n, ∏ P ∈ ω i, fieldPolymerWeight a b P :=
  Finset.sum_pow' _ _ n

/-- **Log-Taylor term as a connected family-tuple sum**: the `n`-th term
`(-1)^n · ε_{a,b}^(n+1)/(n+1)` expands into a sum over `(n+1)`-tuples of nonempty
vd connected families with the scalar coefficient pulled inside.  Field mirror of
`logTaylor_eps_term_eq_sum_vdFamilyTuples`. -/
theorem fieldLogTaylor_eps_term_eq_sum_vdFamilyTuples (G : SimpleGraph ι)
    [Fintype G.edgeSet] (a b : ℝ) (n : ℕ) :
    (-1 : ℝ) ^ n *
        (∑ Γ ∈ (vdConnectedPolymerFamilies G).erase ∅,
          ∏ P ∈ Γ, fieldPolymerWeight a b P) ^ (n + 1) / (n + 1) =
      ∑ Ω ∈ Fintype.piFinset
            (fun _ : Fin (n + 1) => (vdConnectedPolymerFamilies G).erase ∅),
        ((-1 : ℝ) ^ n / (n + 1)) *
          ∏ i : Fin (n + 1), ∏ P ∈ Ω i, fieldPolymerWeight a b P := by
  rw [fieldVdPolymerFamilies_sum_minus_one_pow G a b (n + 1), Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl (fun Ω _ => ?_)
  ring

/-- **Field Mayer term in colouring form**: substituting
`ursellCoefficient_eq_coloring_sum` (reused verbatim) into
`fieldMayerExpansionTerm`, the `r`-th field term is the field activity-weighted sum
over polymer sequences of the alternating proper-surjective-colouring count,
normalised by `r!`.  Field mirror of `mayerExpansionTerm_eq_coloring_form`. -/
theorem fieldMayerExpansionTerm_eq_coloring_form (G : SimpleGraph ι) [Fintype G.edgeSet]
    (r : ℕ) (a b : ℝ) :
    fieldMayerExpansionTerm G r a b =
      ∑ ω ∈ Fintype.piFinset (fun _ : Fin r => allConnectedPolymers G),
        (∑ k ∈ Finset.Icc 1 r, ((-1 : ℝ) ^ (k - 1) / (k : ℝ)) *
            ((properSurjectiveColorings (polymerSeqIncompatibilityGraph ω) k).card : ℝ)) /
          (r.factorial : ℝ) * fieldClusterSeqActivity a b ω := by
  unfold fieldMayerExpansionTerm
  exact Finset.sum_congr rfl (fun ω _ => by rw [ursellCoefficient_eq_coloring_sum])

/-- **Field Mayer term as a colour-degree double sum**: distributing the
colour-degree sum out of the sequence sum.  Field mirror of
`mayerExpansionTerm_eq_double_sum`. -/
theorem fieldMayerExpansionTerm_eq_double_sum (G : SimpleGraph ι) [Fintype G.edgeSet]
    (r : ℕ) (a b : ℝ) :
    fieldMayerExpansionTerm G r a b =
      ∑ k ∈ Finset.Icc 1 r, ((-1 : ℝ) ^ (k - 1) / (k : ℝ)) *
        ∑ ω ∈ Fintype.piFinset (fun _ : Fin r => allConnectedPolymers G),
          ((properSurjectiveColorings (polymerSeqIncompatibilityGraph ω) k).card : ℝ) /
            (r.factorial : ℝ) * fieldClusterSeqActivity a b ω := by
  rw [fieldMayerExpansionTerm_eq_coloring_form]
  simp_rw [Finset.sum_div, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun ω _ => by ring)

/-- **Log-Taylor term as a field colouring sum**: combining
`fieldLogTaylor_eps_term_eq_sum_vdFamilyTuples` with the per-`m` identity
`fieldVdFamilyTuple_sum_eq_seq_coloring_sum` (`m = n+1`).  Field mirror of
`logTaylor_term_eq_coloring`. -/
theorem fieldLogTaylor_term_eq_coloring (G : SimpleGraph ι) [Fintype G.edgeSet]
    (a b : ℝ) (n : ℕ) :
    (-1 : ℝ) ^ n *
        (∑ Γ ∈ (vdConnectedPolymerFamilies G).erase ∅,
          ∏ P ∈ Γ, fieldPolymerWeight a b P) ^ (n + 1) / (n + 1) =
      ∑ r ∈ Finset.range ((n + 1) * (allConnectedPolymers G).card + 1),
        ((-1 : ℝ) ^ n / (n + 1)) *
          ∑ ω ∈ Fintype.piFinset (fun _ : Fin r => allConnectedPolymers G),
            ((properSurjectiveColorings (polymerSeqIncompatibilityGraph ω) (n + 1)).card : ℝ) /
              (r.factorial : ℝ) * fieldClusterSeqActivity a b ω := by
  rw [fieldLogTaylor_eps_term_eq_sum_vdFamilyTuples, ← Finset.mul_sum,
    fieldVdFamilyTuple_sum_eq_seq_coloring_sum, Finset.mul_sum]

/-- **`fieldColorDegreeTerm` vanishes for `k > r`**: no surjective `k`-colouring of
`Fin r`.  Field mirror of `colorDegreeTerm_eq_zero_of_lt`. -/
theorem fieldColorDegreeTerm_eq_zero_of_lt (G : SimpleGraph ι) [Fintype G.edgeSet]
    (a b : ℝ) {r k : ℕ} (hrk : r < k) : fieldColorDegreeTerm G a b r k = 0 := by
  rw [fieldColorDegreeTerm]
  refine mul_eq_zero.mpr (Or.inr (Finset.sum_eq_zero (fun ω _ => ?_)))
  rw [properSurjectiveColorings_eq_empty_of_card_lt _ hrk, Finset.card_empty, Nat.cast_zero,
    zero_div, zero_mul]

/-- **`fieldColorDegreeTerm` vanishes at `k = 0`**: the `1/k = 1/0 = 0` factor.
Field mirror of `colorDegreeTerm_zero_right`. -/
theorem fieldColorDegreeTerm_zero_right (G : SimpleGraph ι) [Fintype G.edgeSet]
    (a b : ℝ) (r : ℕ) : fieldColorDegreeTerm G a b r 0 = 0 := by
  rw [fieldColorDegreeTerm, Nat.cast_zero, div_zero, zero_mul]

/-- **`fieldColorDegreeTerm` vanishes when `m·|allConnectedPolymers G| < r`**: no
surjective `m`-colouring of a graph on `Fin r` from `r` connected polymers.  Field
mirror of `colorDegreeTerm_eq_zero_of_card_lt`. -/
theorem fieldColorDegreeTerm_eq_zero_of_card_lt (G : SimpleGraph ι) [Fintype G.edgeSet]
    (a b : ℝ) {r m : ℕ} (hr : m * (allConnectedPolymers G).card < r) :
    fieldColorDegreeTerm G a b r m = 0 := by
  classical
  rw [fieldColorDegreeTerm]
  refine mul_eq_zero.mpr (Or.inr (Finset.sum_eq_zero (fun ω hω => ?_)))
  have hω' : ∀ i, ω i ∈ allConnectedPolymers G := fun i => Fintype.mem_piFinset.mp hω i
  rw [fieldProperSurjectiveColorings_empty_of_card_lt G hω' hr, Finset.card_empty,
    Nat.cast_zero, zero_div, zero_mul]

/-- **Field Mayer term as the `tsum` of its colour-degree row**:
`fieldMayerExpansionTerm G r a b = ∑'_k fieldColorDegreeTerm G a b r k`.  The row is
finitely supported in `Icc 1 r`.  Field mirror of
`mayerExpansionTerm_eq_tsum_colorDegreeTerm`. -/
theorem fieldMayerExpansionTerm_eq_tsum_fieldColorDegreeTerm (G : SimpleGraph ι)
    [Fintype G.edgeSet] (r : ℕ) (a b : ℝ) :
    fieldMayerExpansionTerm G r a b = ∑' k, fieldColorDegreeTerm G a b r k := by
  classical
  rw [fieldMayerExpansionTerm_eq_double_sum,
    tsum_eq_sum (s := Finset.Icc 1 r) (fun k hk => by
      rw [Finset.mem_Icc, not_and_or, not_le, not_le, Nat.lt_one_iff] at hk
      rcases hk with hk0 | hkr
      · rw [hk0, fieldColorDegreeTerm_zero_right]
      · exact fieldColorDegreeTerm_eq_zero_of_lt G a b hkr)]
  rfl

/-- **Log-Taylor term as the `tsum` of its colour-degree column**: the `n`-th
log-Taylor term equals `∑'_r fieldColorDegreeTerm G a b r (n+1)`.  The column is
finitely supported (`r ≤ (n+1)·|allConnectedPolymers G|`).  Field mirror of
`logTaylorTerm_eq_tsum_colorDegreeTerm`. -/
theorem fieldLogTaylorTerm_eq_tsum_fieldColorDegreeTerm (G : SimpleGraph ι)
    [Fintype G.edgeSet] (a b : ℝ) (n : ℕ) :
    (-1 : ℝ) ^ n *
        (∑ Γ ∈ (vdConnectedPolymerFamilies G).erase ∅,
          ∏ P ∈ Γ, fieldPolymerWeight a b P) ^ (n + 1) / (n + 1) =
      ∑' r, fieldColorDegreeTerm G a b r (n + 1) := by
  classical
  rw [fieldLogTaylor_term_eq_coloring,
    tsum_eq_sum (s := Finset.range ((n + 1) * (allConnectedPolymers G).card + 1)) (fun r hr => by
      rw [Finset.mem_range, not_lt] at hr
      exact fieldColorDegreeTerm_eq_zero_of_card_lt G a b
        (by omega : (n + 1) * (allConnectedPolymers G).card < r))]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [fieldColorDegreeTerm, Nat.add_sub_cancel]
  push_cast
  ring

/-! ## L4: double summability of `fieldColorDegreeTerm` via brick-3 domination -/

/-- **Per-`(r,k)` field colour-degree bound**: `|fieldColorDegreeTerm G a b r k| ≤
(k^(r-1)/r!)·A_C^r`, `A_C = ∑_{P ∈ allConnectedPolymers G} |tanh a|^|P|`.  Combines
`card_properSurjectiveColorings_le` (verbatim), the brick-3 domination
`abs_fieldClusterSeqActivity_le`, and the factorised total activity
`sum_clusterSeqActivity_piFinset_connected`.  Field/connected mirror of
`abs_colorDegreeTerm_le`. -/
theorem abs_fieldColorDegreeTerm_le (G : SimpleGraph ι) [Fintype G.edgeSet] (a b : ℝ)
    (r k : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) :
    |fieldColorDegreeTerm G a b r k| ≤
      ((k : ℝ) ^ (r - 1) / (r.factorial : ℝ)) *
        (∑ P ∈ allConnectedPolymers G, |Real.tanh a| ^ P.card) ^ r := by
  classical
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  rw [fieldColorDegreeTerm, abs_mul, abs_div, abs_pow, abs_neg, abs_one, one_pow,
    abs_of_pos hkpos, one_div]
  have hsum : |∑ ω ∈ Fintype.piFinset (fun _ : Fin r => allConnectedPolymers G),
        ((properSurjectiveColorings (polymerSeqIncompatibilityGraph ω) k).card : ℝ) /
          (r.factorial : ℝ) * fieldClusterSeqActivity a b ω| ≤
      ((k : ℝ) ^ r / (r.factorial : ℝ)) *
        (∑ P ∈ allConnectedPolymers G, |Real.tanh a| ^ P.card) ^ r := by
    calc |∑ ω ∈ _, _|
        ≤ ∑ ω ∈ Fintype.piFinset (fun _ : Fin r => allConnectedPolymers G),
            |((properSurjectiveColorings (polymerSeqIncompatibilityGraph ω) k).card : ℝ) /
              (r.factorial : ℝ) * fieldClusterSeqActivity a b ω| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ ω ∈ Fintype.piFinset (fun _ : Fin r => allConnectedPolymers G),
            ((k : ℝ) ^ r / (r.factorial : ℝ)) * clusterSeqActivity |Real.tanh a| ω := by
          refine Finset.sum_le_sum (fun ω _ => ?_)
          rw [abs_mul, abs_div, Nat.abs_cast, Nat.abs_cast]
          refine mul_le_mul ?_ (abs_fieldClusterSeqActivity_le a b ω) (abs_nonneg _)
            (by positivity)
          gcongr
          exact_mod_cast card_properSurjectiveColorings_le
            (polymerSeqIncompatibilityGraph ω) k
      _ = ((k : ℝ) ^ r / (r.factorial : ℝ)) *
            (∑ P ∈ allConnectedPolymers G, |Real.tanh a| ^ P.card) ^ r := by
          rw [← Finset.mul_sum, sum_clusterSeqActivity_piFinset_connected]
  have hkr : (k : ℝ)⁻¹ * (k : ℝ) ^ r = (k : ℝ) ^ (r - 1) := by
    have h1 : (k : ℝ) ^ r = (k : ℝ) * (k : ℝ) ^ (r - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hr]
    rw [h1, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hkpos), one_mul]
  calc (k : ℝ)⁻¹ * |∑ ω ∈ _, _|
      ≤ (k : ℝ)⁻¹ * (((k : ℝ) ^ r / (r.factorial : ℝ)) *
          (∑ P ∈ allConnectedPolymers G, |Real.tanh a| ^ P.card) ^ r) := by gcongr
    _ = ((k : ℝ) ^ (r - 1) / (r.factorial : ℝ)) *
          (∑ P ∈ allConnectedPolymers G, |Real.tanh a| ^ P.card) ^ r := by
        rw [← mul_assoc, ← mul_div_assoc, hkr]

/-- **Field colour-degree row bound**: `∑_{k=1}^r |fieldColorDegreeTerm G a b r k| ≤
(r^r/r!)·A_C^r`, summing `abs_fieldColorDegreeTerm_le` over `k ∈ Icc 1 r`.  Field
mirror of `sum_abs_colorDegreeTerm_le`. -/
theorem sum_abs_fieldColorDegreeTerm_le (G : SimpleGraph ι) [Fintype G.edgeSet]
    (a b : ℝ) (r : ℕ) (hr : 1 ≤ r) :
    ∑ k ∈ Finset.Icc 1 r, |fieldColorDegreeTerm G a b r k| ≤
      ((r : ℝ) ^ r / (r.factorial : ℝ)) *
        (∑ P ∈ allConnectedPolymers G, |Real.tanh a| ^ P.card) ^ r := by
  calc ∑ k ∈ Finset.Icc 1 r, |fieldColorDegreeTerm G a b r k|
      ≤ ∑ k ∈ Finset.Icc 1 r,
          ((r : ℝ) ^ (r - 1) / (r.factorial : ℝ)) *
            (∑ P ∈ allConnectedPolymers G, |Real.tanh a| ^ P.card) ^ r := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        rw [Finset.mem_Icc] at hk
        refine (abs_fieldColorDegreeTerm_le G a b r k hk.1 hr).trans ?_
        gcongr
        exact_mod_cast hk.2
    _ = ((r : ℝ) ^ r / (r.factorial : ℝ)) *
          (∑ P ∈ allConnectedPolymers G, |Real.tanh a| ^ P.card) ^ r := by
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
        have hrr : (r : ℝ) * (r : ℝ) ^ (r - 1) = (r : ℝ) ^ r := by
          rw [← pow_succ', Nat.sub_add_cancel hr]
        rw [← mul_assoc, ← mul_div_assoc, hrr]

/-- **Field row absolute `tsum` bound**: `∑'_k |fieldColorDegreeTerm G a b r k| ≤
(r^r/r!)·A_C^r`.  Each row is finitely supported (`Icc 1 r`).  Field mirror of
`tsum_abs_colorDegreeTerm_le`. -/
theorem tsum_abs_fieldColorDegreeTerm_le (G : SimpleGraph ι) [Fintype G.edgeSet]
    (a b : ℝ) (r : ℕ) :
    ∑' k, |fieldColorDegreeTerm G a b r k| ≤
      ((r : ℝ) ^ r / (r.factorial : ℝ)) *
        (∑ P ∈ allConnectedPolymers G, |Real.tanh a| ^ P.card) ^ r := by
  classical
  rw [tsum_eq_sum (s := Finset.range (r + 1)) (fun k hk => by
    rw [Finset.mem_range, not_lt] at hk
    rw [fieldColorDegreeTerm_eq_zero_of_lt G a b (by omega : r < k), abs_zero])]
  rcases Nat.eq_zero_or_pos r with hr0 | hr1
  · subst hr0
    simp [fieldColorDegreeTerm_zero_right]
  · rw [show Finset.range (r + 1) = insert 0 (Finset.Icc 1 r) from by
        ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega,
      Finset.sum_insert (by simp), fieldColorDegreeTerm_zero_right, abs_zero, zero_add]
    exact sum_abs_fieldColorDegreeTerm_le G a b r hr1

/-- **Double summability of the field colour-degree term**:
`(r,k) ↦ fieldColorDegreeTerm G a b r k` is summable over `ℕ × ℕ` when
`e·A_C < 1` (`A_C = ∑_{P ∈ allConnectedPolymers G} |tanh a|^|P|`, the brick-3
window).  Rows finitely supported, row absolute sums majorised by the summable
`(r^r/r!)·A_C^r` (`summable_pow_self_div_factorial_mul_abs_pow`, verbatim).  Field
mirror of `summable_uncurry_colorDegreeTerm`; enables the capstone `tsum_comm`. -/
theorem summable_uncurry_fieldColorDegreeTerm (G : SimpleGraph ι) [Fintype G.edgeSet]
    (a b : ℝ)
    (hact : Real.exp 1 * (∑ P ∈ allConnectedPolymers G, |Real.tanh a| ^ P.card) < 1) :
    Summable (fun p : ℕ × ℕ => fieldColorDegreeTerm G a b p.1 p.2) := by
  classical
  have hsumnn : (0 : ℝ) ≤ ∑ P ∈ allConnectedPolymers G, |Real.tanh a| ^ P.card :=
    Finset.sum_nonneg (fun P _ => by positivity)
  have hAabs : Real.exp 1 *
      |∑ P ∈ allConnectedPolymers G, |Real.tanh a| ^ P.card| < 1 := by
    rwa [abs_of_nonneg hsumnn]
  rw [← summable_abs_iff, summable_prod_of_nonneg (fun p => abs_nonneg _)]
  refine ⟨fun r => ?_, ?_⟩
  · refine summable_of_ne_finset_zero (s := Finset.range (r + 1)) (fun k hk => ?_)
    rw [Finset.mem_range, not_lt] at hk
    rw [fieldColorDegreeTerm_eq_zero_of_lt G a b (by omega : r < k), abs_zero]
  · refine Summable.of_nonneg_of_le (fun r => tsum_nonneg (fun k => abs_nonneg _))
      (fun r => tsum_abs_fieldColorDegreeTerm_le G a b r) ?_
    have hpow : ∀ r : ℕ, ((r : ℝ) ^ r / (r.factorial : ℝ)) *
        (∑ P ∈ allConnectedPolymers G, |Real.tanh a| ^ P.card) ^ r =
        ((r : ℝ) ^ r / (r.factorial : ℝ)) *
          |∑ P ∈ allConnectedPolymers G, |Real.tanh a| ^ P.card| ^ r := by
      intro r; rw [abs_of_nonneg hsumnn]
    simp_rw [hpow]
    exact summable_pow_self_div_factorial_mul_abs_pow _ hAabs

/-! ## L5: the field Mayer–Montroll capstone -/

/-- **Field Mayer–Montroll identity** (GJ §17.6.1, brick 4): in the high-temperature
convergence regime, the field polymer free energy equals the sum of the field Mayer
expansion terms,
`fieldPolymerFreeEnergy G a b = ∑'_n fieldMayerExpansionTerm G n a b`.

Proof (Fubini swap of the colour-degree double sum, exactly as the `h = 0`
`mayer_identity_general_t`).  The analytic side `fieldPolymerFreeEnergy_hasSum_via_log`
gives `fieldPolymerFreeEnergy = ∑'_n logTaylorTerm n`, and each
`logTaylorTerm n = ∑'_r fieldColorDegreeTerm G a b r (n+1)` (column), while
`fieldMayerExpansionTerm G r a b = ∑'_k fieldColorDegreeTerm G a b r k` (row).
Double-summability (`summable_uncurry_fieldColorDegreeTerm`, valid for `e·A_C < 1`)
licenses `tsum_comm`; the `k = 0` column vanishes, giving the `n ↔ n+1` shift.

The two hypotheses are the genuine analytic convergence conditions: `h_abs`
(`|ε_{a,b}| < 1`) for the `log(1+ε)` series over the erase-`∅` connected family sum,
and `hact` (`e·A_C < 1`, `A_C = ∑_P |tanh a|^|P|`, the brick-3 window) for the
double-sum Fubini swap. -/
theorem field_mayer_identity_general (G : SimpleGraph ι) [Fintype G.edgeSet] {a b : ℝ}
    (h_abs : |∑ Γ ∈ (vdConnectedPolymerFamilies G).erase ∅,
                ∏ P ∈ Γ, fieldPolymerWeight a b P| < 1)
    (hact : Real.exp 1 * (∑ P ∈ allConnectedPolymers G, |Real.tanh a| ^ P.card) < 1) :
    fieldPolymerFreeEnergy G a b = ∑' n, fieldMayerExpansionTerm G n a b := by
  classical
  have hsum : Summable (Function.uncurry fun r k => fieldColorDegreeTerm G a b r k) :=
    summable_uncurry_fieldColorDegreeTerm G a b hact
  have hlog := fieldPolymerFreeEnergy_hasSum_via_log G h_abs
  have hg : Summable (fun k => ∑' r, fieldColorDegreeTerm G a b r k) := hsum.prod_symm.prod
  have hg0 : (∑' r, fieldColorDegreeTerm G a b r 0) = 0 := by
    simp_rw [fieldColorDegreeTerm_zero_right]; exact tsum_zero
  have hshift : ∑' n, ∑' r, fieldColorDegreeTerm G a b r (n + 1) =
      ∑' k, ∑' r, fieldColorDegreeTerm G a b r k := by
    rw [hg.tsum_eq_zero_add]; simp only [hg0, zero_add]
  have hcomm : ∑' k, ∑' r, fieldColorDegreeTerm G a b r k =
      ∑' r, ∑' k, fieldColorDegreeTerm G a b r k := hsum.tsum_comm
  calc fieldPolymerFreeEnergy G a b
      = ∑' n, ∑' r, fieldColorDegreeTerm G a b r (n + 1) := by
        rw [← hlog.tsum_eq]
        exact tsum_congr (fun n => fieldLogTaylorTerm_eq_tsum_fieldColorDegreeTerm G a b n)
    _ = ∑' k, ∑' r, fieldColorDegreeTerm G a b r k := hshift
    _ = ∑' r, ∑' k, fieldColorDegreeTerm G a b r k := hcomm
    _ = ∑' r, fieldMayerExpansionTerm G r a b :=
        tsum_congr (fun r => (fieldMayerExpansionTerm_eq_tsum_fieldColorDegreeTerm G r a b).symm)

/-- **Field Mayer–Montroll identity, eventual form near `a = 0`** (GJ §17.6.1,
brick 4): for fixed `b`, in some neighbourhood of `a = 0`,
`fieldPolymerFreeEnergy G a b = ∑'_n fieldMayerExpansionTerm G n a b`.

Both convergence hypotheses of `field_mayer_identity_general` hold as `a → 0`:
`ε_{a,b} → 0` since every nonempty connected polymer `P` contributes a factor
`tanh(a)^|P| → 0` (`|P| ≥ 1`), and `A_C(a) = ∑_P |tanh a|^|P| → 0` likewise, so
`e·A_C(a) < 1`.  Field mirror of `mayer_identity_general_t_eventually`. -/
theorem field_mayer_identity_general_eventually (G : SimpleGraph ι) [Fintype G.edgeSet]
    (b : ℝ) :
    ∀ᶠ a : ℝ in nhds 0,
      fieldPolymerFreeEnergy G a b = ∑' n, fieldMayerExpansionTerm G n a b := by
  classical
  -- `|ε_{a,b}| < 1` eventually.
  have hε0 : (∑ Γ ∈ (vdConnectedPolymerFamilies G).erase ∅,
      ∏ P ∈ Γ, fieldPolymerWeight (0 : ℝ) b P) = 0 := by
    refine Finset.sum_eq_zero (fun Γ hΓ => ?_)
    rw [Finset.mem_erase] at hΓ
    obtain ⟨hne, hin⟩ := hΓ
    obtain ⟨P, hP⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    rw [mem_vdConnectedPolymerFamilies] at hin
    have hpos : 0 < P.card :=
      (mem_allConnectedPolymers.mp (hin.1 hP)).nonempty.card_pos
    refine Finset.prod_eq_zero hP ?_
    rw [fieldPolymerWeight, Real.tanh_zero, zero_pow hpos.ne', zero_mul]
  have hε_cont : Continuous (fun a : ℝ =>
      ∑ Γ ∈ (vdConnectedPolymerFamilies G).erase ∅,
        ∏ P ∈ Γ, fieldPolymerWeight a b P) := by
    refine continuous_finset_sum _ (fun Γ _ => continuous_finset_prod _ (fun P _ => ?_))
    simp only [fieldPolymerWeight]
    exact (continuous_real_tanh.pow _).mul continuous_const
  have h_abs_ev : ∀ᶠ a : ℝ in nhds 0,
      |∑ Γ ∈ (vdConnectedPolymerFamilies G).erase ∅,
        ∏ P ∈ Γ, fieldPolymerWeight a b P| < 1 := by
    have h := (continuous_abs.comp hε_cont).tendsto 0
    rw [Function.comp_apply, hε0, abs_zero] at h
    exact h.eventually_lt_const zero_lt_one
  -- `e·A_C(a) < 1` eventually.
  have hA0 : Real.exp 1 * ∑ P ∈ allConnectedPolymers G, |Real.tanh (0 : ℝ)| ^ P.card = 0 :=
    mul_eq_zero.mpr (Or.inr (Finset.sum_eq_zero (fun P hP => by
      rw [Real.tanh_zero, abs_zero,
        zero_pow (Finset.card_ne_zero.mpr (mem_allConnectedPolymers.mp hP).nonempty)])))
  have hA_cont : Continuous
      (fun a : ℝ => Real.exp 1 * ∑ P ∈ allConnectedPolymers G, |Real.tanh a| ^ P.card) :=
    continuous_const.mul
      (continuous_finset_sum _ (fun P _ => (continuous_abs.comp continuous_real_tanh).pow P.card))
  have hact_ev : ∀ᶠ a : ℝ in nhds 0,
      Real.exp 1 * (∑ P ∈ allConnectedPolymers G, |Real.tanh a| ^ P.card) < 1 := by
    have h := hA_cont.tendsto 0
    rw [hA0] at h
    exact h.eventually_lt_const zero_lt_one
  exact (h_abs_ev.and hact_ev).mono
    (fun a ha => field_mayer_identity_general G ha.1 ha.2)

end IsingModel
