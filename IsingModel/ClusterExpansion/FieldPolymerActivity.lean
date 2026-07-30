import IsingModel.ClusterExpansion.Families.FieldConnectedPolymers
import IsingModel.Conditioning.EdgeWalkCounting

/-!
# Field-dependent per-vertex / total / per-site polymer activity bound (GJ §17.6.1)

Brick 2b of the on-book programme toward Glimm–Jaffe (GJ) Theorem 17.6.1
(`∂/∂h` infinite-volume differentiability / `h`-analyticity of the two-point
function in the high-temperature window).  Brick 2a
(`allSubgraphs_sum_eq_vdConnectedPolymerFamilies_sum`,
`Families/FieldConnectedPolymers.lean`) exhibited the finite-volume partition
function as a hard-core gas of the field-dependent *connected* polymers with
activity `w_{a,b}(P) = tanh(a)^|P|·tanh(b)^{#odd(P)}`.  This brick supplies the
**volume-uniform** activity bounds for that gas.

In the high-temperature window `Δ²·|tanh a| < 1` (`Δ = G.maxDegree`, `= 2d` on
the lattice), the per-vertex activity sum satisfies the geometric bound
`∑_{P ∋ v} |w_{a,b}(P)| ≤ (1 − Δ²|tanh a|)⁻¹`, uniformly in the volume and in
the field.  This is the field-dependent, parity-*free* mirror of the `h = 0`
per-vertex / total / per-site bounds `rootedPolymerActivity_le_geometric`,
`allPolymersActivity_le_card_mul_geometric`,
`allPolymersActivity_div_card_le_geometric` (`PolymerActivity.lean`).

The field enters only through the factor `|tanh(b)|^{#odd(P)} ≤ 1` (real `b`,
`Real.abs_tanh_lt_one`), which *helps* the bound and never breaks it, so **no
field hypothesis** on `b` is needed.  The geometric summation core is factored
out as the generic helper `sum_pow_card_le_geometric_of_count_le`, shared by the
connected species here (the pre-existing even version stays untouched).

**Honest scope.**  The right-hand constant `(1 − Δ²|tanh a|)⁻¹ ≥ 1` always
(since `Δ²|tanh a| ≥ 0`), so this is *never* a literal `∑ < 1`: it is a
volume-uniform *finiteness input* for Kotecky–Preiss, **not** the KP smallness
criterion (which is the `e·|t|`-loaded field Mayer bound, a later brick).
Complex `h` (where `|tanh b|` need not be `≤ 1`) is deferred to a later
non-vanishing brick; this file is for real `h` only.

## References

* Friedli–Velenik §3.7.3, eqs. (3.48)–(3.49), and §5.7.3 are the `h = 0`
  templates. Exercise 5.8, p. 238, with its Appendix C solution, p. 531, gives
  the exact real-field weight.
* Friedli–Velenik §§5.2–5.3, including Proposition 5.3, give the abstract model
  and formal expansion; §5.4, Theorem 5.4, p. 224, gives convergence. The
  activity count is a project extension.
-/

namespace IsingModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **Generic geometric activity bound from a per-cardinality count.**  For a
finset `S` of edge subsets of `G` such that every member is contained in
`G.edgeFinset` and the `ℓ`-cardinality slice has at most `Δ^{2ℓ}` members
(`Δ = G.maxDegree`), the activity sum `∑_{P ∈ S} t^{|P|}` is bounded by the
geometric series `(1 − Δ²t)⁻¹` under `0 ≤ t` and `Δ²t < 1`.  This is the
volume-independent summation core shared by the `h = 0` even polymers and the
field-dependent connected polymers; only the count hypothesis differs. -/
theorem sum_pow_card_le_geometric_of_count_le (G : SimpleGraph ι)
    [DecidableRel G.Adj] [Fintype G.edgeSet] (S : Finset (Finset (Sym2 ι)))
    (hsub : ∀ P ∈ S, P ⊆ G.edgeFinset)
    (hcount : ∀ ℓ : ℕ,
      (S.filter (fun P => P.card = ℓ)).card ≤ G.maxDegree ^ (2 * ℓ))
    {t : ℝ} (ht0 : 0 ≤ t) (ht : (G.maxDegree : ℝ) ^ 2 * t < 1) :
    (∑ P ∈ S, t ^ P.card) ≤ (1 - (G.maxDegree : ℝ) ^ 2 * t)⁻¹ := by
  have hr0 : (0 : ℝ) ≤ (G.maxDegree : ℝ) ^ 2 * t := mul_nonneg (by positivity) ht0
  have hmaps : ∀ P ∈ S, P.card ∈ Finset.range (G.edgeFinset.card + 1) := by
    intro P hP
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.card_le_card (hsub P hP)))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun P => t ^ P.card)]
  have hfiber : ∀ ℓ ∈ Finset.range (G.edgeFinset.card + 1),
      (∑ P ∈ S.filter (fun P => P.card = ℓ), t ^ P.card)
        ≤ ((G.maxDegree : ℝ) ^ 2 * t) ^ ℓ := by
    intro ℓ _
    have hconst : (∑ P ∈ S.filter (fun P => P.card = ℓ), t ^ P.card)
        = ((S.filter (fun P => P.card = ℓ)).card : ℝ) * t ^ ℓ := by
      rw [Finset.sum_congr rfl fun P hP => by rw [(Finset.mem_filter.mp hP).2]]
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [hconst]
    have hc : ((S.filter (fun P => P.card = ℓ)).card : ℝ)
        ≤ (G.maxDegree : ℝ) ^ (2 * ℓ) := by
      exact_mod_cast hcount ℓ
    calc ((S.filter (fun P => P.card = ℓ)).card : ℝ) * t ^ ℓ
        ≤ (G.maxDegree : ℝ) ^ (2 * ℓ) * t ^ ℓ :=
          mul_le_mul_of_nonneg_right hc (pow_nonneg ht0 ℓ)
      _ = ((G.maxDegree : ℝ) ^ 2 * t) ^ ℓ := by rw [mul_pow, pow_mul]
  refine le_trans (Finset.sum_le_sum hfiber) ?_
  refine le_trans ((summable_geometric_of_lt_one hr0 ht).sum_le_tsum _
    (fun ℓ _ => pow_nonneg hr0 ℓ)) ?_
  rw [tsum_geometric_of_lt_one hr0 ht]

/-- The connected polymers of `G` whose support contains the vertex `v`. -/
noncomputable def rootedConnectedPolymers (G : SimpleGraph ι) [Fintype G.edgeSet]
    (v : ι) : Finset (Finset (Sym2 ι)) :=
  (allConnectedPolymers G).filter fun P => v ∈ polymerSupport P

/-- The connected polymers of `G` of size `ℓ` whose support contains `v`. -/
noncomputable def rootedConnectedPolymersOfCard (G : SimpleGraph ι)
    [Fintype G.edgeSet] (v : ι) (ℓ : ℕ) : Finset (Finset (Sym2 ι)) :=
  (rootedConnectedPolymers G v).filter fun P => P.card = ℓ

/-- **Max-degree bound on rooted connected-polymer counts (volume-uniform).**
The number of size-`ℓ` connected polymers through `v` is at most `Δ^{2ℓ}`,
`Δ = G.maxDegree`.  Parity-free mirror of
`rootedPolymersOfCard_card_le_maxDegree_pow`: the counting injection
`card_connected_edge_sets_le` uses only that each member is a size-`ℓ`
edge-connected subset of `G.edgeFinset` touching `v`, supplied here by
`IsConnectedPolymer.subset`, `.connected`, the cardinality filter, and
`mem_polymerSupport`. -/
theorem rootedConnectedPolymersOfCard_card_le_maxDegree_pow (G : SimpleGraph ι)
    [DecidableRel G.Adj] [Fintype G.edgeSet] (v : ι) (ℓ : ℕ) :
    (rootedConnectedPolymersOfCard G v ℓ).card ≤ G.maxDegree ^ (2 * ℓ) := by
  refine le_trans (card_connected_edge_sets_le (G := G) v ℓ _ (fun C hC => ?_)) ?_
  · rw [rootedConnectedPolymersOfCard, Finset.mem_filter, rootedConnectedPolymers,
      Finset.mem_filter] at hC
    obtain ⟨⟨hCmem, hCv⟩, hCcard⟩ := hC
    have hpoly : IsConnectedPolymer G C := mem_allConnectedPolymers.mp hCmem
    exact ⟨hpoly.subset, hpoly.connected, hCcard, mem_polymerSupport.mp hCv⟩
  · refine le_trans ?_
      (walksFromCount_le_pow G (fun w => G.degree_le_maxDegree w) (2 * ℓ) v)
    rw [walksFromCount]
    exact Finset.single_le_sum
      (f := fun u => (G.finsetWalkLength (2 * ℓ) v u).card)
      (fun u _ => Nat.zero_le _) (Finset.mem_univ v)

/-- **Term-wise field reduction.**  For real `a, b` and every `P`,
`|fieldPolymerWeight a b P| = |tanh a|^|P|·|tanh b|^{#odd(P)} ≤ |tanh a|^|P|`,
since `|tanh b| < 1` (`Real.abs_tanh_lt_one`) forces `|tanh b|^{#odd(P)} ≤ 1`.
No hypothesis on `b` is used: the field factor can only lower the weight. -/
theorem abs_fieldPolymerWeight_le (a b : ℝ) (P : Finset (Sym2 ι)) :
    |fieldPolymerWeight a b P| ≤ |Real.tanh a| ^ P.card := by
  rw [fieldPolymerWeight, abs_mul, abs_pow, abs_pow]
  refine le_trans (mul_le_mul_of_nonneg_left
    (pow_le_one₀ (abs_nonneg _) (Real.abs_tanh_lt_one b).le)
    (pow_nonneg (abs_nonneg _) _)) ?_
  rw [mul_one]

/-- The field-dependent polymer activity through a vertex `v`:
`∑_{P ∋ v} |fieldPolymerWeight a b P|` over the connected polymers rooted at
`v`. -/
noncomputable def fieldRootedPolymerActivity (G : SimpleGraph ι)
    [Fintype G.edgeSet] (v : ι) (a b : ℝ) : ℝ :=
  ∑ P ∈ rootedConnectedPolymers G v, |fieldPolymerWeight a b P|

/-- **Field per-vertex activity bound (volume-uniform, real `h`).**  Under the
high-temperature hypothesis `Δ²·|tanh a| < 1` (`Δ = G.maxDegree`), the
field-dependent activity through `v` is bounded by `(1 − Δ²|tanh a|)⁻¹`,
independently of the volume `|ι|` and of the field `b`.  Applied with `a = βJ`,
`b = βh`, this is the volume-uniform per-vertex Kotecky–Preiss finiteness input.
It is **not** the KP smallness criterion: the bound is always `≥ 1`. -/
theorem fieldRootedPolymerActivity_le_geometric (G : SimpleGraph ι)
    [DecidableRel G.Adj] [Fintype G.edgeSet] (v : ι) {a b : ℝ}
    (ha : (G.maxDegree : ℝ) ^ 2 * |Real.tanh a| < 1) :
    fieldRootedPolymerActivity G v a b
      ≤ (1 - (G.maxDegree : ℝ) ^ 2 * |Real.tanh a|)⁻¹ := by
  rw [fieldRootedPolymerActivity]
  refine le_trans
    (Finset.sum_le_sum (fun P _ => abs_fieldPolymerWeight_le a b P)) ?_
  refine sum_pow_card_le_geometric_of_count_le G (rootedConnectedPolymers G v)
    (fun P hP => ?_) (fun ℓ => ?_) (abs_nonneg _) ha
  · rw [rootedConnectedPolymers, Finset.mem_filter] at hP
    exact (mem_allConnectedPolymers.mp hP.1).subset
  · exact rootedConnectedPolymersOfCard_card_le_maxDegree_pow G v ℓ

/-- **A connected polymer touches at least one vertex.**  Its support is
nonempty, since it is a nonempty edge set and every edge contains a vertex. -/
theorem one_le_card_polymerSupport_of_mem_allConnectedPolymers (G : SimpleGraph ι)
    [Fintype G.edgeSet] {P : Finset (Sym2 ι)} (hP : P ∈ allConnectedPolymers G) :
    1 ≤ (polymerSupport P).card := by
  obtain ⟨e, he⟩ := (mem_allConnectedPolymers.mp hP).nonempty
  refine Finset.card_pos.mpr ?_
  induction e using Sym2.ind with
  | _ a b => exact ⟨a, mem_polymerSupport.mpr ⟨_, he, Sym2.mem_mk_left a b⟩⟩

/-- **Summed per-vertex activity equals the support-weighted total activity.**
`∑_v ∑_{P ∋ v} |w(P)| = ∑_{P ∈ allConnectedPolymers} |supp P|·|w(P)|`, by
exchanging the order of summation.  Parity-free mirror of
`sum_rootedPolymerActivity_eq`. -/
theorem sum_fieldRootedPolymerActivity_eq (G : SimpleGraph ι) [Fintype G.edgeSet]
    (a b : ℝ) :
    (∑ v : ι, fieldRootedPolymerActivity G v a b)
      = ∑ P ∈ allConnectedPolymers G,
          (polymerSupport P).card • |fieldPolymerWeight a b P| := by
  simp only [fieldRootedPolymerActivity, rootedConnectedPolymers]
  rw [Finset.sum_congr rfl fun v _ => Finset.sum_filter _ _, Finset.sum_comm]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const]

/-- The total field-dependent polymer activity of `G`:
`∑_{P ∈ allConnectedPolymers G} |fieldPolymerWeight a b P|`. -/
noncomputable def fieldAllPolymersActivity (G : SimpleGraph ι) [Fintype G.edgeSet]
    (a b : ℝ) : ℝ :=
  ∑ P ∈ allConnectedPolymers G, |fieldPolymerWeight a b P|

/-- **Field total activity bound (vertices × per-vertex geometric bound).**
Under `Δ²·|tanh a| < 1`, the total field-dependent polymer activity is at most
`|ι|·(1 − Δ²|tanh a|)⁻¹`.  Each connected polymer is counted at least once in the
vertex sum (its support is nonempty), so the total activity is dominated by the
summed per-vertex activity, itself at most `|ι|` copies of the geometric
bound. -/
theorem fieldAllPolymersActivity_le_card_mul_geometric (G : SimpleGraph ι)
    [DecidableRel G.Adj] [Fintype G.edgeSet] {a b : ℝ}
    (ha : (G.maxDegree : ℝ) ^ 2 * |Real.tanh a| < 1) :
    fieldAllPolymersActivity G a b
      ≤ (Fintype.card ι : ℝ) * (1 - (G.maxDegree : ℝ) ^ 2 * |Real.tanh a|)⁻¹ := by
  have hle : fieldAllPolymersActivity G a b
      ≤ ∑ v : ι, fieldRootedPolymerActivity G v a b := by
    rw [fieldAllPolymersActivity, sum_fieldRootedPolymerActivity_eq]
    refine Finset.sum_le_sum fun P hP => ?_
    have h1 : (1 : ℝ) ≤ ((polymerSupport P).card : ℝ) := by
      exact_mod_cast one_le_card_polymerSupport_of_mem_allConnectedPolymers G hP
    calc |fieldPolymerWeight a b P|
        = 1 * |fieldPolymerWeight a b P| := (one_mul _).symm
      _ ≤ ((polymerSupport P).card : ℝ) * |fieldPolymerWeight a b P| :=
          mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ = (polymerSupport P).card • |fieldPolymerWeight a b P| :=
          (nsmul_eq_mul _ _).symm
  refine hle.trans ?_
  calc (∑ v : ι, fieldRootedPolymerActivity G v a b)
      ≤ ∑ _v : ι, (1 - (G.maxDegree : ℝ) ^ 2 * |Real.tanh a|)⁻¹ :=
        Finset.sum_le_sum fun v _ => fieldRootedPolymerActivity_le_geometric G v ha
    _ = (Fintype.card ι : ℝ) * (1 - (G.maxDegree : ℝ) ^ 2 * |Real.tanh a|)⁻¹ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **Field per-site activity bound (volume-uniform, real `h`).**  For a
nonempty vertex type and `Δ²·|tanh a| < 1`, the per-site total field-dependent
polymer activity `(1/|ι|)·∑_P |w(P)|` is bounded by the volume-uniform constant
`(1 − Δ²|tanh a|)⁻¹`, `Δ = G.maxDegree`. -/
theorem fieldAllPolymersActivity_div_card_le_geometric (G : SimpleGraph ι)
    [DecidableRel G.Adj] [Fintype G.edgeSet] [Nonempty ι] {a b : ℝ}
    (ha : (G.maxDegree : ℝ) ^ 2 * |Real.tanh a| < 1) :
    fieldAllPolymersActivity G a b / (Fintype.card ι : ℝ)
      ≤ (1 - (G.maxDegree : ℝ) ^ 2 * |Real.tanh a|)⁻¹ := by
  have hcard : (0 : ℝ) < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  rw [div_le_iff₀ hcard, mul_comm]
  exact fieldAllPolymersActivity_le_card_mul_geometric G ha

end IsingModel
