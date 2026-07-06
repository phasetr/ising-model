import IsingModel.ClusterExpansion.FieldExpIdentityDegreeWindow
import IsingModel.ClusterExpansion.FieldMayerTermPerOrderBound
import IsingModel.ClusterExpansion.MayerSumDiffSupportBound

/-!
# Avoiding-graph field partition ratio bound
(GJ §17.6.1, field cluster expansion, brick F3)

Brick F3 of the minimal (pair-only) field cluster-expansion route toward
Glimm–Jaffe (GJ) *Quantum Physics*, 2nd ed., §17.6.1, pp. 313–314 (the `∂/∂h`
infinite-volume differentiability / `h`-analyticity of the two-point function in
the high-temperature window).  This is the field/connected mirror of the
`β`-only avoiding-ratio unit `AvoidingRatioExp.lean` +
`MayerSumDiffSupportBound.lean`.

Fix a finite graph `G`, a real coupling `a ≥ 0` and a complex field `b`.  Write
`Zᶠ(G) = fieldPolymerZℂ G a b` and `F_G = ∑' n, fieldMayerExpansionTermℂ G n a b`.
For a set `C` of edges, `Gavoid G C = G.deleteEdges (touchEdges G C)` is `G` with
every edge touching `polymerSupport C` deleted.  With
`M = max 1 ‖Complex.tanh b‖`, the inflated per-site activity is
`t_∗ = M²·|tanh a|`, `r_∗ = Δ²·e·t_∗` (`Δ = G.maxDegree`), and the local
Kotecký–Preiss constant is `κ_Δ = (1−r_∗)⁻¹·(1−ρ_∗)⁻²` with the connected-gas
ratio `ρ_∗ = 8 r_∗/(1−r_∗)²` (support constant `c = 2`).

The headline (`fieldPolymerZℂ_Gavoid_div_norm_le_exp`) is the volume-uniform
ratio bound `‖Zᶠ(Gavoid G C)/Zᶠ(G)‖ ≤ exp(κ_Δ·|polymerSupport C|)`.  The
assembly follows the `β` template:

* **(a)/(b)** `IsConnectedPolymer_Gavoid_iff` / `allConnectedPolymers_Gavoid` —
  the connected-polymer characterizations of the delete-edges graph (mirror of
  `IsPolymer_Gavoid_iff` / `allPolymers_Gavoid`).
* **(c)** the field Mayer difference touching decomposition and its norm bound
  (`fieldMayerExpansionTermℂ_sub_Gavoid_eq_touching_sum`,
  `norm_fieldMayerExpansionTermℂ_sub_Gavoid_le`), passing to the inflated real
  activity `t_∗` via `norm_fieldClusterSeqActivityℂ_le`.
* **(d)** `field_gavoid_degree_window` (and its arithmetic core
  `kpRegion8_downward_closed`) — the `c = 2` degree-window transfer from `G` to
  `Gavoid G C`.
* the difference-support bound
  `norm_fieldMayerExpansionTermℂ_tsum_sub_Gavoid_le_support_card` (F3-pre
  `fixedVertexGasTouching_tsum_le` at `connectedPolymerGasData G`, `c = 2`) and
  the exp-ratio capstone `fieldPolymerZℂ_Gavoid_div_norm_le_exp`.

Both partitions are non-vanishing on the window
(`fieldPolymerZℂ_ne_zero_of_degree_window`, immediate from the `exp` identities
`fieldPolymerZℂ_eq_exp_tsum_of_degree_window` used here), so the ratio is a
genuine quotient.  `κ_Δ` depends only on `Δ`, `t_∗`, `c = 2`, **not** on the
volume `|ι|`, which is what makes the ratio bound survive the infinite-volume
limit and feed the §17.6.1 derivative-existence argument.

## References
- Glimm–Jaffe, *Quantum Physics*, 2nd ed., §17.6.1, pp. 313–314, and §18.4–§18.6,
  pp. 378–386 (lattice cluster expansion, analytic continuation in the fugacity).
- Friedli–Velenik, *Statistical Mechanics of Lattice Systems* (2017), §5.7,
  Theorem 5.4 (Kotecký–Preiss criterion).
- Kotecký–Preiss, Comm. Math. Phys. **103** (1986) 491–498, Theorem 1.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## (a)/(b): connected-polymer characterizations of the avoiding graph -/

/-- **(a) Connected polymers of the avoiding graph** (GJ §17.6.1, brick F3).  A connected
polymer of `Gavoid G C` is exactly a connected polymer of `G` whose edge set is contained in
the surviving edge finset (equivalently, vertex-disjoint from `C`).  Edge-connectivity and
nonemptiness are inherited unchanged; only the ambient edge-set clause shrinks, via
`subset_edgeFinset_Gavoid_iff`.  Connected/field mirror of `IsPolymer_Gavoid_iff`. -/
theorem IsConnectedPolymer_Gavoid_iff (G : SimpleGraph ι) [Fintype G.edgeSet]
    (C P : Finset (Sym2 ι)) :
    IsConnectedPolymer (Gavoid G C) P ↔
      IsConnectedPolymer G P ∧ P ⊆ (Gavoid G C).edgeFinset := by
  classical
  constructor
  · intro hP
    have hsub := (subset_edgeFinset_Gavoid_iff G C P).mp hP.subset
    exact
      ⟨{ nonempty := hP.nonempty
         subset := hsub.1
         connected := hP.connected },
       hP.subset⟩
  · rintro ⟨hP, hsub⟩
    exact
      { nonempty := hP.nonempty
        subset := hsub
        connected := hP.connected }

/-- **(b) The connected-polymer universe of the avoiding graph** (GJ §17.6.1, brick F3).  The
connected polymers of `Gavoid G C` are the connected polymers of `G` contained in the surviving
edge finset.  Connected/field mirror of `allPolymers_Gavoid`. -/
theorem allConnectedPolymers_Gavoid (G : SimpleGraph ι) [Fintype G.edgeSet]
    (C : Finset (Sym2 ι)) :
    allConnectedPolymers (Gavoid G C) =
      (allConnectedPolymers G).filter (fun P => P ⊆ (Gavoid G C).edgeFinset) := by
  classical
  ext P
  rw [mem_allConnectedPolymers, Finset.mem_filter, mem_allConnectedPolymers,
    IsConnectedPolymer_Gavoid_iff]

/-- **Connected polymers of the avoiding graph form a sub-finset** (GJ §17.6.1, brick F3).
Connected/field mirror of `allPolymers_Gavoid_subset`. -/
theorem allConnectedPolymers_Gavoid_subset
    (G : SimpleGraph ι) [Fintype G.edgeSet] (C : Finset (Sym2 ι)) :
    allConnectedPolymers (Gavoid G C) ⊆ allConnectedPolymers G := by
  classical
  letI : Fintype (Gavoid G C).edgeSet := instFintypeGavoidEdgeSet G C
  intro P hP
  rw [allConnectedPolymers_Gavoid G C] at hP
  exact (Finset.mem_filter.mp hP).1

/-- **The avoiding connected cluster sequences embed** (GJ §17.6.1, brick F3).  Connected/field
mirror of `piFinset_allPolymers_Gavoid_subset`. -/
theorem piFinset_allConnectedPolymers_Gavoid_subset
    (G : SimpleGraph ι) [Fintype G.edgeSet] (C : Finset (Sym2 ι)) (n : ℕ) :
    Fintype.piFinset (fun _ : Fin n => allConnectedPolymers (Gavoid G C)) ⊆
      Fintype.piFinset (fun _ : Fin n => allConnectedPolymers G) := by
  classical
  letI : Fintype (Gavoid G C).edgeSet := instFintypeGavoidEdgeSet G C
  exact Fintype.piFinset_subset _ _ (fun _ => allConnectedPolymers_Gavoid_subset G C)

/-! ## (c): the field Mayer difference touching decomposition and its norm bound -/

/-- **Field Mayer difference as a product-finset complement sum** (GJ §17.6.1, brick F3).  The
`n`-th field Mayer term difference equals the sum over connected cluster sequences of `G` not
already sequences of `Gavoid G C`.  Connected/field mirror of
`mayerExpansionTermComplex_sub_Gavoid_eq_sdiff_sum`. -/
theorem fieldMayerExpansionTermℂ_sub_Gavoid_eq_sdiff_sum
    (G : SimpleGraph ι) [Fintype G.edgeSet] (C : Finset (Sym2 ι)) (n : ℕ) (a : ℝ) (b : ℂ) :
    fieldMayerExpansionTermℂ G n a b - fieldMayerExpansionTermℂ (Gavoid G C) n a b =
      ∑ ω ∈
        (Fintype.piFinset (fun _ : Fin n => allConnectedPolymers G)) \
          (Fintype.piFinset (fun _ : Fin n => allConnectedPolymers (Gavoid G C))),
        (ursellCoefficient ω : ℂ) * fieldClusterSeqActivityℂ a b ω := by
  classical
  letI : Fintype (Gavoid G C).edgeSet := instFintypeGavoidEdgeSet G C
  let sG : Finset (Fin n → Finset (Sym2 ι)) :=
    Fintype.piFinset (fun _ : Fin n => allConnectedPolymers G)
  let sA : Finset (Fin n → Finset (Sym2 ι)) :=
    Fintype.piFinset (fun _ : Fin n => allConnectedPolymers (Gavoid G C))
  let f : (Fin n → Finset (Sym2 ι)) → ℂ :=
    fun ω => (ursellCoefficient ω : ℂ) * fieldClusterSeqActivityℂ a b ω
  have hsub : sA ⊆ sG := by
    dsimp [sA, sG]
    exact piFinset_allConnectedPolymers_Gavoid_subset G C n
  have hsum := Finset.sum_sdiff (s₁ := sA) (s₂ := sG) (f := f) hsub
  unfold fieldMayerExpansionTermℂ
  change (∑ ω ∈ sG, f ω) - (∑ ω ∈ sA, f ω) = ∑ ω ∈ sG \ sA, f ω
  rw [← hsum]
  ring

/-- **Membership in the connected product-finset complement** (GJ §17.6.1, brick F3).
A sequence lies in the complement iff all its coordinates are connected polymers of `G` and at
least one touches `polymerSupport C`.  Connected/field mirror of
`mem_piFinset_sdiff_iff_exists_touching`. -/
theorem mem_piFinset_sdiff_iff_exists_touching_connected
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {C : Finset (Sym2 ι)} {n : ℕ} {ω : Fin n → Finset (Sym2 ι)} :
    ω ∈
        (Fintype.piFinset (fun _ : Fin n => allConnectedPolymers G)) \
          (Fintype.piFinset (fun _ : Fin n => allConnectedPolymers (Gavoid G C))) ↔
      (∀ i, ω i ∈ allConnectedPolymers G) ∧
        ∃ i : Fin n, ¬ IsPolymerVertexDisjoint C (ω i) := by
  classical
  letI : Fintype (Gavoid G C).edgeSet := instFintypeGavoidEdgeSet G C
  constructor
  · intro h
    rw [Finset.mem_sdiff] at h
    have hG : ∀ i, ω i ∈ allConnectedPolymers G := Fintype.mem_piFinset.mp h.1
    have hnotA : ¬ ∀ i, ω i ∈ allConnectedPolymers (Gavoid G C) := by
      intro hA
      exact h.2 (Fintype.mem_piFinset.mpr hA)
    obtain ⟨i, hi⟩ := not_forall.mp hnotA
    refine ⟨hG, i, ?_⟩
    intro hdisj
    apply hi
    rw [allConnectedPolymers_Gavoid G C, Finset.mem_filter]
    refine ⟨hG i, ?_⟩
    exact (subset_edgeFinset_Gavoid_iff G C (ω i)).mpr
      ⟨(mem_allConnectedPolymers.mp (hG i)).subset, hdisj⟩
  · rintro ⟨hG, ⟨i, htouch⟩⟩
    rw [Finset.mem_sdiff]
    refine ⟨Fintype.mem_piFinset.mpr hG, ?_⟩
    intro hA
    have hiA : ω i ∈ allConnectedPolymers (Gavoid G C) := Fintype.mem_piFinset.mp hA i
    rw [allConnectedPolymers_Gavoid G C, Finset.mem_filter] at hiA
    have hsubAvoid : ω i ⊆ (Gavoid G C).edgeFinset := hiA.2
    have hdisj : IsPolymerVertexDisjoint C (ω i) :=
      ((subset_edgeFinset_Gavoid_iff G C (ω i)).mp hsubAvoid).2
    exact htouch hdisj

open Classical in
/-- **Field Mayer difference as a touching-cluster sum** (GJ §17.6.1, brick F3).  The `n`-th
field Mayer term difference is the sum over connected cluster sequences with at least one
polymer touching `polymerSupport C`.  Connected/field mirror of
`mayerExpansionTermComplex_sub_Gavoid_eq_touching_sum`. -/
theorem fieldMayerExpansionTermℂ_sub_Gavoid_eq_touching_sum
    (G : SimpleGraph ι) [Fintype G.edgeSet] (C : Finset (Sym2 ι)) (n : ℕ) (a : ℝ) (b : ℂ) :
    fieldMayerExpansionTermℂ G n a b - fieldMayerExpansionTermℂ (Gavoid G C) n a b =
      ∑ ω ∈
        (Fintype.piFinset (fun _ : Fin n => allConnectedPolymers G)).filter
          (fun ω => ∃ i : Fin n, ¬ IsPolymerVertexDisjoint C (ω i)),
        (ursellCoefficient ω : ℂ) * fieldClusterSeqActivityℂ a b ω := by
  classical
  letI : Fintype (Gavoid G C).edgeSet := instFintypeGavoidEdgeSet G C
  rw [fieldMayerExpansionTermℂ_sub_Gavoid_eq_sdiff_sum
    (G := G) (C := C) (n := n) (a := a) (b := b)]
  apply Finset.sum_congr
  · ext ω
    rw [Finset.mem_filter]
    constructor
    · intro h
      have ht :=
        (mem_piFinset_sdiff_iff_exists_touching_connected
          (G := G) (C := C) (n := n) (ω := ω)).mp h
      exact ⟨(Finset.mem_sdiff.mp h).1, ht.2⟩
    · rintro ⟨hG, htouch⟩
      exact
        (mem_piFinset_sdiff_iff_exists_touching_connected
          (G := G) (C := C) (n := n) (ω := ω)).mpr
          ⟨Fintype.mem_piFinset.mp hG, htouch⟩
  · intro ω _hω
    rfl

open Classical in
/-- **Norm of the field Mayer difference by the inflated touching sum** (GJ §17.6.1, brick F3).
The norm of the `n`-th field Mayer term difference is bounded by the touching-cluster sum at
the inflated real activity `t_∗ = M²·|tanh a|` (`M = max 1 ‖Complex.tanh b‖`), via
`norm_fieldClusterSeqActivityℂ_le`.  Connected/field mirror of
`norm_mayerExpansionTermComplex_sub_Gavoid_le`. -/
theorem norm_fieldMayerExpansionTermℂ_sub_Gavoid_le
    (G : SimpleGraph ι) [Fintype G.edgeSet] (C : Finset (Sym2 ι)) (n : ℕ) (a : ℝ) (b : ℂ) :
    ‖fieldMayerExpansionTermℂ G n a b - fieldMayerExpansionTermℂ (Gavoid G C) n a b‖
      ≤ ∑ ω ∈
        (Fintype.piFinset (fun _ : Fin n => allConnectedPolymers G)).filter
          (fun ω => ∃ i : Fin n, ¬ IsPolymerVertexDisjoint C (ω i)),
        |ursellCoefficient ω|
          * clusterSeqActivity ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|) ω := by
  classical
  rw [fieldMayerExpansionTermℂ_sub_Gavoid_eq_touching_sum
    (G := G) (C := C) (n := n) (a := a) (b := b)]
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum fun ω _hω => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (norm_fieldClusterSeqActivityℂ_le a b ω) (abs_nonneg _)

open Classical in
/-- **Connected touching clusters bounded by a support-vertex union** (GJ §17.6.1, brick F3).
If a connected cluster sequence contains a polymer not vertex-disjoint from `C`, some vertex of
`polymerSupport C` lies in the support of one of its coordinates.  Connected mirror of
`touchingCluster_termAbsSum_le_support_vertex_sum`. -/
theorem touchingConnectedCluster_termAbsSum_le_support_vertex_sum
    (G : SimpleGraph ι) [Fintype G.edgeSet] (C : Finset (Sym2 ι)) (n : ℕ) {t : ℝ}
    (ht : 0 ≤ t) :
    (∑ ω ∈ (Fintype.piFinset (fun _ : Fin n => allConnectedPolymers G)).filter
          (fun ω => ∃ i : Fin n, ¬ IsPolymerVertexDisjoint C (ω i)),
        |ursellCoefficient ω| * clusterSeqActivity t ω)
      ≤ ∑ v ∈ polymerSupport C,
        ∑ ω ∈ (Fintype.piFinset (fun _ : Fin n => allConnectedPolymers G)).filter
          (fun ω => ∃ i : Fin n, v ∈ polymerSupport (ω i)),
        |ursellCoefficient ω| * clusterSeqActivity t ω := by
  classical
  set S := Fintype.piFinset (fun _ : Fin n => allConnectedPolymers G) with hS
  set a : (Fin n → Finset (Sym2 ι)) → ℝ :=
    fun ω => |ursellCoefficient ω| * clusterSeqActivity t ω with ha
  have hanonneg : ∀ ω, 0 ≤ a ω := by
    intro ω
    exact mul_nonneg (abs_nonneg _) (clusterSeqActivity_nonneg ht ω)
  have hvertexNonneg : ∀ ω, 0 ≤ ∑ v ∈ polymerSupport C,
      if (∃ i : Fin n, v ∈ polymerSupport (ω i)) then a ω else 0 := by
    intro ω
    refine Finset.sum_nonneg fun v _ => ?_
    split_ifs with h
    · exact hanonneg ω
    · exact le_refl 0
  have hRHS : (∑ v ∈ polymerSupport C,
        ∑ ω ∈ S.filter (fun ω => ∃ i : Fin n, v ∈ polymerSupport (ω i)), a ω)
      = ∑ ω ∈ S, ∑ v ∈ polymerSupport C,
          if (∃ i : Fin n, v ∈ polymerSupport (ω i)) then a ω else 0 := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
  refine le_trans ?_ (ge_of_eq hRHS)
  refine le_trans (Finset.sum_le_sum (fun ω hω => ?_))
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun ω _ _ => hvertexNonneg ω))
  rw [Finset.mem_filter] at hω
  obtain ⟨i, hi⟩ := hω.2
  have hshared : ∃ v : ι, v ∈ polymerSupport C ∧ v ∈ polymerSupport (ω i) :=
    PolymersIncompatible.iff_exists_shared_vertex.mp hi
  obtain ⟨v, hvC, hvω⟩ := hshared
  calc a ω = if (∃ i : Fin n, v ∈ polymerSupport (ω i)) then a ω else 0 := by
        rw [if_pos ⟨i, hvω⟩]
    _ ≤ ∑ v ∈ polymerSupport C,
        if (∃ i : Fin n, v ∈ polymerSupport (ω i)) then a ω else 0 :=
        Finset.single_le_sum
          (f := fun v => if (∃ i : Fin n, v ∈ polymerSupport (ω i)) then a ω else 0)
          (fun v _ => by
            change (0 : ℝ) ≤ if (∃ i : Fin n, v ∈ polymerSupport (ω i)) then a ω else 0
            split_ifs with h; exacts [hanonneg ω, le_refl 0])
          hvC

/-! ## (d): the `c = 2` degree-window transfer -/

/-- **Downward closure of the `c = 2` Kotecký–Preiss region** (GJ §17.6.1, brick F3).  If
`0 ≤ r₁ ≤ r₂`, `r₂ < 1` and `8 r₂/(1−r₂)² < 1`, then `r₁ < 1` and `8 r₁/(1−r₁)² < 1`.  The
connected-gas (`c = 2`, ratio `8 r/(1−r)²`) mirror of `kpRegion_downward_closed`; the
monotonicity `8 r₁/(1−r₁)² ≤ 8 r₂/(1−r₂)²` is proved by the cross-multiplied form. -/
theorem kpRegion8_downward_closed {r₁ r₂ : ℝ} (h0 : 0 ≤ r₁) (h12 : r₁ ≤ r₂)
    (hr2 : r₂ < 1) (hρ2 : 8 * r₂ / (1 - r₂) ^ 2 < 1) :
    r₁ < 1 ∧ 8 * r₁ / (1 - r₁) ^ 2 < 1 := by
  have hr1 : r₁ < 1 := lt_of_le_of_lt h12 hr2
  refine ⟨hr1, ?_⟩
  have hq1 : (0 : ℝ) < 1 - r₁ := by linarith
  have hq2 : (0 : ℝ) < 1 - r₂ := by linarith
  have hmono : 8 * r₁ / (1 - r₁) ^ 2 ≤ 8 * r₂ / (1 - r₂) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg (r₂ - r₁), mul_nonneg h0 (le_of_lt hq2), mul_pos hq1 hq2]
  linarith

/-- **(d) `c = 2` degree-window transfer to the avoiding graph** (GJ §17.6.1, brick F3).  For a
non-negative real activity `A`, the field degree window (`hkp`, `hρwin` at maximum degree
`G.maxDegree`) transfers to `Gavoid G C`, since `(Gavoid G C).maxDegree ≤ G.maxDegree`
(`maxDegree_Gavoid_le`) shrinks `r = Δ²·e·A` and the connected-gas region is downward closed
(`kpRegion8_downward_closed`).  Used both for the F2c `exp` identity on `Gavoid G C`
(`A = M²·ρ`) and for F1 summability on `Gavoid G C` (`A = t_∗`).  The `c = 2` mirror of
`gavoid_kp_conditions`. -/
theorem field_gavoid_degree_window
    (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet]
    (C : Finset (Sym2 ι)) {A : ℝ} (hA : 0 ≤ A)
    (hkp : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * A) < 1)
    (hρwin : 8 * ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * A))
        / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * A)) ^ 2 < 1) :
    ((Gavoid G C).maxDegree : ℝ) ^ 2 * (Real.exp 1 * A) < 1 ∧
      8 * (((Gavoid G C).maxDegree : ℝ) ^ 2 * (Real.exp 1 * A))
        / (1 - ((Gavoid G C).maxDegree : ℝ) ^ 2 * (Real.exp 1 * A)) ^ 2 < 1 := by
  classical
  have hfactor : (0 : ℝ) ≤ Real.exp 1 * A := by positivity
  have h0 : 0 ≤ ((Gavoid G C).maxDegree : ℝ) ^ 2 * (Real.exp 1 * A) := by positivity
  have h12 : ((Gavoid G C).maxDegree : ℝ) ^ 2 * (Real.exp 1 * A)
      ≤ (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * A) := by
    have hcast : (((Gavoid G C).maxDegree : ℝ) ≤ (G.maxDegree : ℝ)) := by
      exact_mod_cast maxDegree_Gavoid_le G C
    gcongr
  exact kpRegion8_downward_closed h0 h12 hkp hρwin

/-! ## The difference-support bound and the exp-ratio capstone -/

/-- **Local KP bound for the field Mayer-sum difference caused by avoiding a support**
(GJ §17.6.1, brick F3).  On the connected-gas degree window at the inflated activity
`t_∗ = M²·|tanh a|` (`M = max 1 ‖Complex.tanh b‖`, `r_∗ = Δ²·e·t_∗`), the norm of the
difference of the full field Mayer sums of `G` and `Gavoid G C` is bounded by the local KP
constant `κ_Δ = (1−r_∗)⁻¹(1−ρ_∗)⁻²` (`ρ_∗ = 8 r_∗/(1−r_∗)²`) times `|polymerSupport C|`.
Connected/field mirror of `norm_mayerExpansionTermComplex_tsum_sub_Gavoid_le_support_card`,
with the even gas (`c = 1`) replaced by the connected gas (`c = 2`, `connectedPolymerGasData`);
the volume `|ι|` does not enter `κ_Δ`. -/
theorem norm_fieldMayerExpansionTermℂ_tsum_sub_Gavoid_le_support_card
    (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet]
    (C : Finset (Sym2 ι)) {a : ℝ} {b : ℂ}
    (hkp : (G.maxDegree : ℝ) ^ 2 *
        (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|)) < 1)
    (hρ : 8 * ((G.maxDegree : ℝ) ^ 2 *
          (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|)))
        / (1 - (G.maxDegree : ℝ) ^ 2 *
            (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|))) ^ 2 < 1) :
    ‖(∑' n : ℕ, fieldMayerExpansionTermℂ G n a b)
        - (∑' n : ℕ, fieldMayerExpansionTermℂ (Gavoid G C) n a b)‖
      ≤ ((1 / (1 - (G.maxDegree : ℝ) ^ 2 *
            (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|))))
          * (1 - 8 * ((G.maxDegree : ℝ) ^ 2 *
                (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|)))
              / (1 - (G.maxDegree : ℝ) ^ 2 *
                  (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|))) ^ 2)⁻¹ ^ 2)
        * (polymerSupport C).card := by
  classical
  letI : Fintype (Gavoid G C).edgeSet := instFintypeGavoidEdgeSet G C
  letI : DecidableRel (Gavoid G C).Adj := instDecidableRelGavoidAdj G C
  set t : ℝ := (max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a| with ht
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have habs : |t| = t := abs_of_nonneg ht0
  set κ : ℝ := (1 / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * t)))
          * (1 - 8 * ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * t))
            / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * t)) ^ 2)⁻¹ ^ 2 with hκ
  -- The `|t|`-form window hypotheses feeding the F3-pre moment machinery (`c = 2`).
  have hkp' : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1 := by rw [habs]; exact hkp
  have hρ' : 4 * 2 * ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|))
      / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ 2 < 1 := by
    have h8 : (4 : ℝ) * 2 = 8 := by norm_num
    rw [habs, h8]; exact hρ
  have hsupp : ∀ P ∈ allConnectedPolymers G,
      ((polymerSupport P).card : ℝ) ≤ 2 * (P.card : ℝ) := fun P hP =>
    polymerSupport_card_le_two_mul_of_mem_allConnectedPolymers G hP
  -- Field-window window transfer to `Gavoid G C` (for its F1 summability).
  obtain ⟨hkpAvoid, hρAvoid⟩ :=
    field_gavoid_degree_window G C (A := (max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|)
      (by positivity) (by rw [← ht]; exact hkp) (by rw [← ht]; exact hρ)
  -- Summability of both field Mayer series (F1).
  have hsumG : Summable fun n : ℕ => fieldMayerExpansionTermℂ G n a b :=
    (summable_norm_fieldMayerExpansionTermℂ_of_tail_condition G hkp hρ).of_norm
  have hsumA : Summable fun n : ℕ => fieldMayerExpansionTermℂ (Gavoid G C) n a b :=
    (summable_norm_fieldMayerExpansionTermℂ_of_tail_condition (Gavoid G C)
      hkpAvoid hρAvoid).of_norm
  have hdiffNorm : Summable fun n : ℕ =>
      ‖fieldMayerExpansionTermℂ G n a b - fieldMayerExpansionTermℂ (Gavoid G C) n a b‖ :=
    summable_norm_iff.mpr (hsumG.sub hsumA)
  have hnorm_tsum :
      ‖(∑' n : ℕ, fieldMayerExpansionTermℂ G n a b)
          - (∑' n : ℕ, fieldMayerExpansionTermℂ (Gavoid G C) n a b)‖
        ≤ ∑' n : ℕ,
          ‖fieldMayerExpansionTermℂ G n a b - fieldMayerExpansionTermℂ (Gavoid G C) n a b‖ := by
    rw [← hsumG.tsum_sub hsumA]
    exact norm_tsum_le_tsum_norm hdiffNorm
  -- Per-order: bounded by the support-vertex touching sum at activity `t`.
  have hper : ∀ n : ℕ,
      ‖fieldMayerExpansionTermℂ G n a b - fieldMayerExpansionTermℂ (Gavoid G C) n a b‖
      ≤ ∑ v ∈ polymerSupport C,
        ∑ ω ∈ (Fintype.piFinset (fun _ : Fin n => allConnectedPolymers G)).filter
          (fun ω => ∃ i : Fin n, v ∈ polymerSupport (ω i)),
        |ursellCoefficient ω| * clusterSeqActivity t ω := by
    intro n
    refine (norm_fieldMayerExpansionTermℂ_sub_Gavoid_le G C n a b).trans ?_
    rw [← ht]
    exact touchingConnectedCluster_termAbsSum_le_support_vertex_sum G C n ht0
  have hper0 : (∑ v ∈ polymerSupport C,
        ∑ ω ∈ (Fintype.piFinset (fun _ : Fin 0 => allConnectedPolymers G)).filter
          (fun ω => ∃ i : Fin 0, v ∈ polymerSupport (ω i)),
        |ursellCoefficient ω| * clusterSeqActivity t ω) = 0 := by
    refine Finset.sum_eq_zero fun v hv => ?_
    refine Finset.sum_eq_zero fun ω hω => ?_
    rw [Finset.mem_filter] at hω
    obtain ⟨i, _hi⟩ := hω.2
    exact Fin.elim0 i
  -- Per-vertex summability (F3-pre) and the fixed-vertex KP constant `κ`.
  have hsupportSumm : ∀ v : ι, Summable fun n : ℕ =>
      ∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allConnectedPolymers G)).filter
          (fun ω => ∃ i : Fin (n + 1), v ∈ polymerSupport (ω i)),
        |ursellCoefficient ω| * clusterSeqActivity t ω := by
    intro v
    exact summable_fixedVertexGasTouching_termAbsSum_succ G (connectedPolymerGasData G)
      (by norm_num) hsupp v ht0 hkp' hρ'
  have hsupportShiftSumm : Summable fun n : ℕ => ∑ v ∈ polymerSupport C,
      ∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allConnectedPolymers G)).filter
          (fun ω => ∃ i : Fin (n + 1), v ∈ polymerSupport (ω i)),
        |ursellCoefficient ω| * clusterSeqActivity t ω := by
    classical
    induction polymerSupport C using Finset.induction_on with
    | empty => simp
    | insert v s hvs ih =>
        have hvSumm : Summable fun n : ℕ =>
            ∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allConnectedPolymers G)).filter
                (fun ω => ∃ i : Fin (n + 1), v ∈ polymerSupport (ω i)),
              |ursellCoefficient ω| * clusterSeqActivity t ω := hsupportSumm v
        simpa [Finset.sum_insert, hvs] using hvSumm.add ih
  have hsupportFullSumm : Summable fun n : ℕ => ∑ v ∈ polymerSupport C,
      ∑ ω ∈ (Fintype.piFinset (fun _ : Fin n => allConnectedPolymers G)).filter
          (fun ω => ∃ i : Fin n, v ∈ polymerSupport (ω i)),
        |ursellCoefficient ω| * clusterSeqActivity t ω :=
    (summable_nat_add_iff 1).mp hsupportShiftSumm
  have hsupportTsum :
      (∑' n : ℕ, ∑ v ∈ polymerSupport C,
        ∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allConnectedPolymers G)).filter
          (fun ω => ∃ i : Fin (n + 1), v ∈ polymerSupport (ω i)),
        |ursellCoefficient ω| * clusterSeqActivity t ω)
      = ∑ v ∈ polymerSupport C,
          ∑' n : ℕ,
            ∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allConnectedPolymers G)).filter
              (fun ω => ∃ i : Fin (n + 1), v ∈ polymerSupport (ω i)),
            |ursellCoefficient ω| * clusterSeqActivity t ω :=
    Summable.tsum_finsetSum (fun v _hv => hsupportSumm v)
  have hshiftSupport :
      (∑' n : ℕ, ∑ v ∈ polymerSupport C,
        ∑ ω ∈ (Fintype.piFinset (fun _ : Fin n => allConnectedPolymers G)).filter
          (fun ω => ∃ i : Fin n, v ∈ polymerSupport (ω i)),
        |ursellCoefficient ω| * clusterSeqActivity t ω)
      = ∑' n : ℕ, ∑ v ∈ polymerSupport C,
        ∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allConnectedPolymers G)).filter
          (fun ω => ∃ i : Fin (n + 1), v ∈ polymerSupport (ω i)),
        |ursellCoefficient ω| * clusterSeqActivity t ω := by
    rw [hsupportFullSumm.tsum_eq_zero_add, hper0, zero_add]
  have hsupport_bound :
      (∑' n : ℕ, ∑ v ∈ polymerSupport C,
        ∑ ω ∈ (Fintype.piFinset (fun _ : Fin n => allConnectedPolymers G)).filter
          (fun ω => ∃ i : Fin n, v ∈ polymerSupport (ω i)),
        |ursellCoefficient ω| * clusterSeqActivity t ω)
      ≤ κ * (polymerSupport C).card := by
    calc
      (∑' n : ℕ, ∑ v ∈ polymerSupport C,
        ∑ ω ∈ (Fintype.piFinset (fun _ : Fin n => allConnectedPolymers G)).filter
          (fun ω => ∃ i : Fin n, v ∈ polymerSupport (ω i)),
        |ursellCoefficient ω| * clusterSeqActivity t ω)
        = ∑' n : ℕ, ∑ v ∈ polymerSupport C,
          ∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allConnectedPolymers G)).filter
            (fun ω => ∃ i : Fin (n + 1), v ∈ polymerSupport (ω i)),
          |ursellCoefficient ω| * clusterSeqActivity t ω := hshiftSupport
      _ = ∑ v ∈ polymerSupport C,
          ∑' n : ℕ,
            ∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allConnectedPolymers G)).filter
              (fun ω => ∃ i : Fin (n + 1), v ∈ polymerSupport (ω i)),
            |ursellCoefficient ω| * clusterSeqActivity t ω := hsupportTsum
      _ ≤ ∑ _v ∈ polymerSupport C, κ := by
          refine Finset.sum_le_sum fun v hv => ?_
          refine (fixedVertexGasTouching_tsum_le G (connectedPolymerGasData G)
            (by norm_num) hsupp v ht0 hkp' hρ').trans_eq ?_
          rw [hκ, habs, show (4 : ℝ) * 2 = 8 from by norm_num]
      _ = κ * (polymerSupport C).card := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
  calc
    ‖(∑' n : ℕ, fieldMayerExpansionTermℂ G n a b)
        - (∑' n : ℕ, fieldMayerExpansionTermℂ (Gavoid G C) n a b)‖
      ≤ ∑' n : ℕ,
          ‖fieldMayerExpansionTermℂ G n a b
            - fieldMayerExpansionTermℂ (Gavoid G C) n a b‖ := hnorm_tsum
    _ ≤ ∑' n : ℕ, ∑ v ∈ polymerSupport C,
        ∑ ω ∈ (Fintype.piFinset (fun _ : Fin n => allConnectedPolymers G)).filter
          (fun ω => ∃ i : Fin n, v ∈ polymerSupport (ω i)),
        |ursellCoefficient ω| * clusterSeqActivity t ω :=
        hdiffNorm.tsum_le_tsum hper hsupportFullSumm
    _ ≤ κ * (polymerSupport C).card := hsupport_bound
    _ = ((1 / (1 - (G.maxDegree : ℝ) ^ 2 *
            (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|))))
          * (1 - 8 * ((G.maxDegree : ℝ) ^ 2 *
                (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|)))
              / (1 - (G.maxDegree : ℝ) ^ 2 *
                  (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|))) ^ 2)⁻¹ ^ 2)
        * (polymerSupport C).card := by rw [hκ, ht]

/-- **Avoiding-graph field partition ratio bound** (GJ §17.6.1, brick F3, capstone).  Fix a
target coupling `a ∈ Set.Ico 0 A` and a field `b` in the `π/2`-ball `Metric.ball 0 r` with a
uniform bound `‖Complex.tanh z‖ ≤ Mr` (`Mr ≥ 1`), on the field degree window at radius `ρ`
(`hρ0`, `htanhA`, `hkp`, `hρwin`).  Then
`‖fieldPolymerZℂ (Gavoid G C) a b / fieldPolymerZℂ G a b‖ ≤ exp(κ_Δ·|polymerSupport C|)`,
with the **volume-uniform** local KP constant `κ_Δ = (1−r_∗)⁻¹(1−ρ_∗)⁻²`
(`r_∗ = Δ²·e·t_∗`, `t_∗ = (max 1 ‖Complex.tanh b‖)²·|tanh a|`, `ρ_∗ = 8 r_∗/(1−r_∗)²`).

Assembly: F2c (`fieldPolymerZℂ_eq_exp_tsum_of_degree_window`) writes both partitions as
`exp` of their field Mayer sums (on `Gavoid G C` via `field_gavoid_degree_window`); both are
non-vanishing (`fieldPolymerZℂ_ne_zero_of_degree_window`, immediate from those identities).
The ratio is `exp(F_av − F_G)`, whose norm is `exp((F_av − F_G).re) ≤ exp‖F_G − F_av‖`, and
`‖F_G − F_av‖ ≤ κ_Δ·|polymerSupport C|` by
`norm_fieldMayerExpansionTermℂ_tsum_sub_Gavoid_le_support_card` (the `t_∗` window is derived
from the `ρ`-window since `|tanh a| ≤ tanh A < ρ`, via `kpRegion8_downward_closed`).
Connected/field mirror of `norm_htSubgraphSumAvoiding_div_htSubgraphSum_empty_le`. -/
theorem fieldPolymerZℂ_Gavoid_div_norm_le_exp (G : SimpleGraph ι)
    [DecidableRel G.Adj] [Fintype G.edgeSet] (C : Finset (Sym2 ι)) {a A r Mr ρ : ℝ} {b : ℂ}
    (ha : a ∈ Set.Ico 0 A) (hr0 : 0 < r) (hrpi : r < Real.pi / 2) (hMr1 : 1 ≤ Mr)
    (hMr : ∀ z : ℂ, ‖z‖ ≤ r → ‖Complex.tanh z‖ ≤ Mr) (hbr : b ∈ Metric.ball 0 r)
    (hρ0 : 0 < ρ) (htanhA : Real.tanh A < ρ)
    (hkp : (G.maxDegree : ℝ) ^ 2 *
        (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * ρ)) < 1)
    (hρwin : 8 * ((G.maxDegree : ℝ) ^ 2 *
          (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * ρ)))
        / (1 - (G.maxDegree : ℝ) ^ 2 *
            (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * ρ))) ^ 2 < 1) :
    ‖fieldPolymerZℂ (Gavoid G C) a b / fieldPolymerZℂ G a b‖
      ≤ Real.exp (((1 / (1 - (G.maxDegree : ℝ) ^ 2 *
            (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|))))
          * (1 - 8 * ((G.maxDegree : ℝ) ^ 2 *
                (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|)))
              / (1 - (G.maxDegree : ℝ) ^ 2 *
                  (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|))) ^ 2)⁻¹ ^ 2)
        * (polymerSupport C).card) := by
  classical
  letI : Fintype (Gavoid G C).edgeSet := instFintypeGavoidEdgeSet G C
  letI : DecidableRel (Gavoid G C).Adj := instDecidableRelGavoidAdj G C
  -- `t_∗ ≤ M²·ρ`, hence the `t_∗` window for `G` from the `ρ`-window.
  have htanh_le : |Real.tanh a| ≤ ρ := by
    rw [abs_of_nonneg (real_tanh_nonneg ha.1)]
    exact le_of_lt (lt_of_le_of_lt (real_tanh_le_tanh (le_of_lt ha.2)) htanhA)
  have h12 : (G.maxDegree : ℝ) ^ 2 *
        (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|))
      ≤ (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * ρ)) := by
    gcongr
  have hstar0 : 0 ≤ (G.maxDegree : ℝ) ^ 2 *
      (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|)) := by positivity
  obtain ⟨hkp_star, hρ_star⟩ := kpRegion8_downward_closed hstar0 h12 hkp hρwin
  -- The `ρ`-window transfers to `Gavoid G C` (for its F2c `exp` identity).
  obtain ⟨hkp_av, hρwin_av⟩ :=
    field_gavoid_degree_window G C (A := (max 1 ‖Complex.tanh b‖) ^ 2 * ρ)
      (by positivity) hkp hρwin
  -- Open both partitions as exponentials of their field Mayer sums.
  have hZG : fieldPolymerZℂ G a b
      = Complex.exp (∑' n, fieldMayerExpansionTermℂ G n a b) :=
    fieldPolymerZℂ_eq_exp_tsum_of_degree_window G ha hr0 hrpi hMr1 hMr hbr hρ0 htanhA hkp hρwin
  have hZA : fieldPolymerZℂ (Gavoid G C) a b
      = Complex.exp (∑' n, fieldMayerExpansionTermℂ (Gavoid G C) n a b) :=
    fieldPolymerZℂ_eq_exp_tsum_of_degree_window (Gavoid G C) ha hr0 hrpi hMr1 hMr hbr hρ0 htanhA
      hkp_av hρwin_av
  set FG : ℂ := ∑' n, fieldMayerExpansionTermℂ G n a b with hFG
  set FA : ℂ := ∑' n, fieldMayerExpansionTermℂ (Gavoid G C) n a b with hFA
  have hdiff := norm_fieldMayerExpansionTermℂ_tsum_sub_Gavoid_le_support_card G C hkp_star hρ_star
  calc
    ‖fieldPolymerZℂ (Gavoid G C) a b / fieldPolymerZℂ G a b‖
        = ‖Complex.exp FA / Complex.exp FG‖ := by rw [hZA, hZG]
    _ = ‖Complex.exp (FA - FG)‖ := by rw [← Complex.exp_sub]
    _ = Real.exp (FA - FG).re := by rw [Complex.norm_exp]
    _ ≤ Real.exp ‖FG - FA‖ := by
        apply Real.exp_le_exp.mpr
        calc (FA - FG).re ≤ ‖FA - FG‖ := Complex.re_le_norm _
          _ = ‖FG - FA‖ := norm_sub_rev FA FG
    _ ≤ Real.exp (((1 / (1 - (G.maxDegree : ℝ) ^ 2 *
            (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|))))
          * (1 - 8 * ((G.maxDegree : ℝ) ^ 2 *
                (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|)))
              / (1 - (G.maxDegree : ℝ) ^ 2 *
                  (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|))) ^ 2)⁻¹ ^ 2)
        * (polymerSupport C).card) := Real.exp_le_exp.mpr hdiff

end IsingModel
