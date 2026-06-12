import IsingModel.Concrete.LatticeGraphCorrelation.TheoremEtaLe1.BallDefs
import IsingModel.BallBoundarySimonLieb.Tight
import IsingModel.AmbientLatticeSum.PerStageIncrement
import IsingModel.Concrete.LatticeGraphCorrelation.TheoremEtaLe1.Disconnection
import IsingModel.Inequalities.HighTemp.SimonLiebInfinite

/-!
# Infinite-volume tight ball-boundary Simon–Lieb inequality (GJ §17.8)

This file discharges the former `ball_boundary_tight_infinite` axiom
(`BallDefs.lean`) by taking the infinite-volume limit of the finite-stage tight
ball-boundary inequality `ball_boundary_simon_lieb_tight`.

## Correctness finding (hypothesis correction)

The original axiom was stated for every `r` and every `x` with
`r < latticeDistance d 0 x`. This is **false as stated**:

* **`r = 0`**: the boundary edges run from the origin to its nearest neighbours,
  so the origin lies on every boundary edge and the finite-stage separation
  hypothesis `0 ∉ e` fails; concretely the RHS lift hits the Finset `{0,0}`,
  which collapses to the singleton `{0}` giving `⟨σ₀⟩ = 0` (instead of the
  intended `⟨σ₀²⟩ = 1`), and the resulting bound fails at high temperature.
* **`latticeDistance d 0 x = r + 1`**: the endpoint `x` sits on the outer
  boundary shell, hence lies on a boundary edge, again breaking the separation.

The honest, provable statement (and the one the downstream consumer
`shellSup_contraction` actually uses, where `latticeDistance ≥ r + 2`) requires
`1 ≤ r` and `r + 1 < latticeDistance d 0 x`. Both hypotheses are exactly what is
needed for the source `0` and the sink `x` to avoid every boundary edge.

## Strategy

`ciSup_le` reduces to a per-stage bound: at each exhaustion stage `n` with
`{0, x} ⊆ Λ.volume n`, apply `ball_boundary_simon_lieb_tight` on the induced
graph with `E₀` the straddling cut edges (disconnection supplied by
`scaledCorrelation_at_zero_of_sep`), bound each finite-volume correlation by its
infinite-volume value, and reindex the subtype cut-edge sum into the ambient
`latticeBallBoundaryEdges` sum (the cut edges of any large enough stage are
confined to `cubicBox d (r+1)`).

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §17.8, (17.8.4)–(17.8.5),
  Theorem 17.8.1, pp. 316–318.
-/

namespace IsingModel.Ambient

open Finset Real IsingModel

/-- **Distance-to-box**: a point at lattice distance `≤ m` from the origin lies
in `cubicBox d m`. The `i`-th coordinate `|x i|` is a single summand of the ℓ¹
distance, hence `≤ m`. -/
theorem mem_cubicBox_of_latticeDistance_origin_le {d m : ℕ} {x : Fin d → ℤ}
    (h : IsingModel.latticeDistance d 0 x ≤ m) : x ∈ cubicBox d m := by
  rw [mem_cubicBox]
  intro i
  have hcoord : (x i).natAbs ≤ IsingModel.latticeDistance d 0 x := by
    unfold IsingModel.latticeDistance
    have heq : ((0 : Fin d → ℤ) i - x i).natAbs = (x i).natAbs := by
      simp only [Pi.zero_apply, zero_sub, Int.natAbs_neg]
    rw [← heq]
    exact Finset.single_le_sum (f := fun j => ((0 : Fin d → ℤ) j - x j).natAbs)
      (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  have hle : (x i).natAbs ≤ m := hcoord.trans h
  have habs : |x i| ≤ (m : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast hle
  rw [abs_le] at habs
  exact habs

/-- **Confinement of straddling edges**: if `k` and `l` are lattice-adjacent and
exactly one of them lies in the ball `B_r` (the straddle condition), then both
endpoints lie in `cubicBox d (r+1)`. Adjacency forces the outside endpoint to be
at distance exactly `r + 1`. -/
theorem latticeBallBoundary_confine {d r : ℕ} {k l : Fin d → ℤ}
    (hadj : (IsingModel.latticeGraph d).Adj k l)
    (hstr : (IsingModel.latticeDistance d 0 k ≤ r) ≠
      (IsingModel.latticeDistance d 0 l ≤ r)) :
    k ∈ cubicBox d (r + 1) ∧ l ∈ cubicBox d (r + 1) := by
  have hkl : IsingModel.latticeDistance d k l = 1 :=
    (latticeGraph_adj_iff_latticeDistance_eq_one d k l).mp hadj
  have hlk : IsingModel.latticeDistance d l k = 1 :=
    (latticeGraph_adj_iff_latticeDistance_eq_one d l k).mp hadj.symm
  have hkl1 : IsingModel.latticeDistance d 0 k ≤ IsingModel.latticeDistance d 0 l + 1 := by
    have := IsingModel.latticeDistance_triangle d 0 l k
    omega
  have hlk1 : IsingModel.latticeDistance d 0 l ≤ IsingModel.latticeDistance d 0 k + 1 := by
    have := IsingModel.latticeDistance_triangle d 0 k l
    omega
  by_cases hA : IsingModel.latticeDistance d 0 k ≤ r
  · exact ⟨mem_cubicBox_of_latticeDistance_origin_le (by omega),
      mem_cubicBox_of_latticeDistance_origin_le (by omega)⟩
  · have hB : IsingModel.latticeDistance d 0 l ≤ r := by
      by_contra hB
      exact hstr (propext ⟨fun h => absurd h hA, fun h => absurd h hB⟩)
    exact ⟨mem_cubicBox_of_latticeDistance_origin_le (by omega),
      mem_cubicBox_of_latticeDistance_origin_le (by omega)⟩

/-- **Membership characterization of `latticeBallBoundaryEdges`**: an edge
`s(k, l)` is a ball-boundary edge iff `k, l` are lattice-adjacent and exactly one
lies in the ball `B_r`. (The confinement to `cubicBox d (r+1)` is automatic from
adjacency and straddle.) -/
theorem mem_latticeBallBoundaryEdges {d r : ℕ} {k l : Fin d → ℤ} :
    s(k, l) ∈ latticeBallBoundaryEdges d r ↔
      (IsingModel.latticeGraph d).Adj k l ∧
        ((IsingModel.latticeDistance d 0 k ≤ r) ≠
          (IsingModel.latticeDistance d 0 l ≤ r)) := by
  classical
  unfold latticeBallBoundaryEdges
  rw [Finset.mem_filter, Finset.mem_image]
  simp only [Sym2.lift_mk]
  constructor
  · rintro ⟨⟨e', he', hmap⟩, hstr⟩
    refine ⟨?_, hstr⟩
    -- recover the subtype edge and its adjacency
    obtain ⟨⟨a, b⟩, rfl⟩ := Quot.exists_rep e'
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, inducedGraph_apply,
      SimpleGraph.induce_adj] at he'
    rw [Sym2.map_mk] at hmap
    -- hmap : s(a.val, b.val) = s(k, l), he' : (latticeGraph d).Adj a.val b.val
    rcases Sym2.eq_iff.mp hmap with ⟨hak, hbl⟩ | ⟨hal, hbk⟩
    · rw [hak, hbl] at he'; exact he'
    · rw [hal, hbk] at he'; exact he'.symm
  · rintro ⟨hadj, hstr⟩
    refine ⟨?_, hstr⟩
    obtain ⟨hk, hl⟩ := latticeBallBoundary_confine hadj hstr
    refine ⟨s(⟨k, hk⟩, ⟨l, hl⟩), ?_, ?_⟩
    · rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, inducedGraph_apply,
        SimpleGraph.induce_adj]
      exact hadj
    · rw [Sym2.map_mk]

set_option maxHeartbeats 1600000 in
-- The proof assembles a per-stage `ciSup_le` bound, a finite-volume tight
-- Simon–Lieb application, a per-edge product comparison, and a subtype-to-ambient
-- edge-sum reindex; the combined elaboration exceeds the default heartbeat limit.
/-- **Infinite-volume tight ball-boundary Simon–Lieb inequality** (GJ §17.8,
(17.8.4)–(17.8.5), pp. 316–318): for a ferromagnetic Ising model at `h = 0` on
`latticeGraph d`, with `1 ≤ r` and a point `x` with `r + 1 < latticeDistance d 0 x`,

`⟨σ_0 σ_x⟩_∞ ≤ β·J · ∑_{(k,l) ∈ ∂B_r}`
`  [⟨σ_0σ_k⟩_∞·⟨σ_lσ_x⟩_∞ + ⟨σ_0σ_l⟩_∞·⟨σ_kσ_x⟩_∞]`.

This discharges the former `ball_boundary_tight_infinite` axiom; see the
hypothesis-correctness discussion in the module docstring (`1 ≤ r` and
`r + 1 < latticeDistance` are required and are exactly what the downstream
`shellSup_contraction` uses).

Proof: `ciSup_le` reduces to per-stage bounds. At each stage with
`{0, x} ⊆ Λ.volume n`, `ball_boundary_simon_lieb_tight` applies to the induced
graph with the straddling cut edges (the source `0` and the sink `x` avoid every
cut edge by `1 ≤ r` and `r + 1 < dist`; disconnection via
`scaledCorrelation_at_zero_of_sep`); each finite-volume correlation is bounded by
its infinite-volume value and the subtype cut-edge sum reindexes into the ambient
`latticeBallBoundaryEdges` sum (cut edges are confined to `cubicBox d (r+1)`). -/
theorem ball_boundary_tight_infinite (d : ℕ) (_hd : 1 ≤ d)
    (r : ℕ) (hr : 1 ≤ r)
    (Λ : Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    (x : Fin d → ℤ) (hx : r + 1 < IsingModel.latticeDistance d 0 x) :
    correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), x}
      ≤ p.β * p.J * ∑ e ∈ latticeBallBoundaryEdges d r,
          Sym2.lift ⟨fun k l =>
            correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), k}
              * correlationInfinite (IsingModel.latticeGraph d) Λ p {l, x}
            + correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), l}
              * correlationInfinite (IsingModel.latticeGraph d) Λ p {k, x},
          fun k l => by ring⟩ e := by
  classical
  have hβJ : 0 ≤ p.β * p.J := mul_nonneg hf.hβ.le hf.hJ
  -- The ambient per-edge summand of the RHS.
  set Finf : Sym2 (Fin d → ℤ) → ℝ := fun e =>
    Sym2.lift ⟨fun k l =>
      correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), k}
        * correlationInfinite (IsingModel.latticeGraph d) Λ p {l, x}
      + correlationInfinite (IsingModel.latticeGraph d) Λ p {(0 : Fin d → ℤ), l}
        * correlationInfinite (IsingModel.latticeGraph d) Λ p {k, x},
    fun k l => by ring⟩ e with hFinf
  -- Each ambient summand is non-negative.
  have hFinf_nonneg : ∀ e, 0 ≤ Finf e := by
    intro e
    obtain ⟨⟨k, l⟩, rfl⟩ := Quot.exists_rep e
    simp only [hFinf, Sym2.lift_mk]
    have h1 := correlationInfinite_nonneg (IsingModel.latticeGraph d) Λ p hf
      {(0 : Fin d → ℤ), k}
    have h2 := correlationInfinite_nonneg (IsingModel.latticeGraph d) Λ p hf {l, x}
    have h3 := correlationInfinite_nonneg (IsingModel.latticeGraph d) Λ p hf
      {(0 : Fin d → ℤ), l}
    have h4 := correlationInfinite_nonneg (IsingModel.latticeGraph d) Λ p hf {k, x}
    positivity
  -- `x ≠ 0` (since `latticeDistance 0 x > r + 1 ≥ 0`).
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp only [IsingModel.latticeDistance_self] at hx
    omega
  rw [correlationInfinite_eq_ciSup]
  apply ciSup_le
  intro n
  by_cases hA : ({(0 : Fin d → ℤ), x} : Finset (Fin d → ℤ)) ⊆ Λ.volume n
  · -- Main case: both `0, x ∈ Λ.volume n`.
    have h0 : (0 : Fin d → ℤ) ∈ Λ.volume n := hA (Finset.mem_insert_self 0 {x})
    have hxn : x ∈ Λ.volume n :=
      hA (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self x)))
    rw [correlationAlongExhaustion_of_subset (IsingModel.latticeGraph d) Λ p hA,
      correlationΛ_apply]
    have h_lift : liftFinset ({(0 : Fin d → ℤ), x}) hA
        = ({⟨0, h0⟩, ⟨x, hxn⟩} : Finset ↑(Λ.volume n)) := by
      ext z
      simp only [mem_liftFinset, Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff]
    rw [h_lift]
    -- Abbreviations.
    set Gn := inducedGraph (IsingModel.latticeGraph d) (Λ.volume n) with hGn
    set C : Finset ↑(Λ.volume n) :=
      Finset.univ.filter (fun v => IsingModel.latticeDistance d 0 v.val ≤ r) with hC
    set E₀ : Finset (Sym2 ↑(Λ.volume n)) := Gn.edgeFinset.filter (straddlePred C) with hE₀
    -- Membership in the cut set `C`.
    have hCmem : ∀ v : ↑(Λ.volume n),
        v ∈ C ↔ IsingModel.latticeDistance d 0 v.val ≤ r := by
      intro v; simp [hC]
    -- The lifted source and sink.
    have h0C : (⟨0, h0⟩ : ↑(Λ.volume n)) ∈ C := by
      rw [hCmem]; simp only [IsingModel.latticeDistance_self]; omega
    have hxC : (⟨x, hxn⟩ : ↑(Λ.volume n)) ∉ C := by
      rw [hCmem]; simp only; omega
    have hrs : (⟨0, h0⟩ : ↑(Λ.volume n)) ≠ ⟨x, hxn⟩ := by
      simp only [ne_eq, Subtype.mk.injEq]; exact fun h => hx0 h.symm
    -- Edge-set side conditions.
    have hE₀_nd : ∀ e ∈ E₀, ¬e.IsDiag := by
      intro e he
      exact Gn.not_isDiag_of_mem_edgeFinset (Finset.mem_of_mem_filter e he)
    have hE₀_sub : E₀ ⊆ Gn.edgeFinset := Finset.filter_subset _ _
    -- Disconnection cut: every `Gn`-edge crossing `C` lies in `E₀`.
    have hcut : ∀ v ∈ C, ∀ w ∉ C, ∀ (e : Sym2 ↑(Λ.volume n)),
        e = s(v, w) → e ∉ E₀ → ¬Gn.Adj v w := by
      intro v hv w hw e he_eq he_not hadjvw
      apply he_not
      rw [he_eq, hE₀, Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]; exact hadjvw
      · simp only [straddlePred, Sym2.lift_mk]
        intro hiff; exact hw (hiff.mp hv)
    have h_s0 : scaledCorrelation Gn E₀ p 0 {⟨0, h0⟩, ⟨x, hxn⟩} = 0 :=
      scaledCorrelation_at_zero_of_sep Gn E₀ hE₀_sub p hf hh ⟨0, h0⟩ ⟨x, hxn⟩ hrs
        C h0C hxC hcut
    -- Separation: neither source nor sink lies on a cut edge.
    have hE₀_sep : ∀ e ∈ E₀,
        ¬ Sym2.Mem (⟨0, h0⟩ : ↑(Λ.volume n)) e ∧
          ¬ Sym2.Mem (⟨x, hxn⟩ : ↑(Λ.volume n)) e := by
      intro e he
      rw [hE₀, Finset.mem_filter] at he
      obtain ⟨he_edge, he_str⟩ := he
      have hadj_of_mem : ∀ (w : ↑(Λ.volume n)) (hw : w ∈ e),
          Gn.Adj w (Sym2.Mem.other hw) := by
        intro w hw
        have h_mem : s(w, Sym2.Mem.other hw) ∈ Gn.edgeSet :=
          (Sym2.other_spec hw).symm ▸ (SimpleGraph.mem_edgeFinset.mp he_edge)
        rwa [SimpleGraph.mem_edgeSet] at h_mem
      have hstr_pair : ∀ (v w : ↑(Λ.volume n)), e = s(v, w) → (v ∈ C ↔ w ∈ C) → False := by
        intro v w hvw hiff
        rw [hvw] at he_str
        simp only [straddlePred, Sym2.lift_mk] at he_str
        exact he_str hiff
      constructor
      · intro hmem0
        set u := Sym2.Mem.other hmem0 with hu
        have hadj0u : Gn.Adj ⟨0, h0⟩ u := hadj_of_mem _ hmem0
        have he_eq : e = s((⟨0, h0⟩ : ↑(Λ.volume n)), u) := (Sym2.other_spec hmem0).symm
        have huC : u ∉ C := by
          intro huC; exact hstr_pair _ _ he_eq ⟨fun _ => huC, fun _ => h0C⟩
        rw [hCmem, not_le] at huC
        have hadj_amb : (IsingModel.latticeGraph d).Adj 0 u.val := hadj0u
        have : IsingModel.latticeDistance d 0 u.val = 1 :=
          (latticeGraph_adj_iff_latticeDistance_eq_one d 0 u.val).mp hadj_amb
        omega
      · intro hmemx
        set u := Sym2.Mem.other hmemx with hu
        have hadjxu : Gn.Adj ⟨x, hxn⟩ u := hadj_of_mem _ hmemx
        have he_eq : e = s((⟨x, hxn⟩ : ↑(Λ.volume n)), u) := (Sym2.other_spec hmemx).symm
        have huC : u ∈ C := by
          by_contra huC
          exact hstr_pair _ _ he_eq ⟨fun h => absurd h hxC, fun h => absurd h huC⟩
        rw [hCmem] at huC
        have hadj_amb : (IsingModel.latticeGraph d).Adj x u.val := hadjxu
        have hdxu : IsingModel.latticeDistance d x u.val = 1 :=
          (latticeGraph_adj_iff_latticeDistance_eq_one d x u.val).mp hadj_amb
        have htri : IsingModel.latticeDistance d 0 x
            ≤ IsingModel.latticeDistance d 0 u.val + IsingModel.latticeDistance d u.val x :=
          IsingModel.latticeDistance_triangle d 0 u.val x
        have hdux : IsingModel.latticeDistance d u.val x = 1 := by
          have := (latticeGraph_adj_iff_latticeDistance_eq_one d u.val x).mp hadj_amb.symm
          exact this
        omega
    -- Apply the finite-stage tight inequality.
    have hfin := ball_boundary_simon_lieb_tight Gn E₀ hE₀_nd hE₀_sub p hf hh
      ⟨0, h0⟩ ⟨x, hxn⟩ hrs hE₀_sep h_s0
    refine le_trans hfin ?_
    -- Finite-to-infinite correlation comparison for a lifted pair.
    have hfin_le : ∀ (a b : ↑(Λ.volume n)),
        IsingModel.correlation Gn p {a, b}
          ≤ correlationInfinite (IsingModel.latticeGraph d) Λ p {a.val, b.val} := by
      intro a b
      have hsub : ({a.val, b.val} : Finset (Fin d → ℤ)) ⊆ Λ.volume n :=
        Finset.insert_subset_iff.mpr ⟨a.prop, Finset.singleton_subset_iff.mpr b.prop⟩
      have h_lift2 : liftFinset ({a.val, b.val}) hsub = ({a, b} : Finset ↑(Λ.volume n)) := by
        ext z
        simp only [mem_liftFinset, Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff]
      have heq : IsingModel.correlation Gn p {a, b}
          = correlationAlongExhaustion (IsingModel.latticeGraph d) Λ p {a.val, b.val} n := by
        rw [correlationAlongExhaustion_of_subset (IsingModel.latticeGraph d) Λ p hsub,
          correlationΛ_apply, h_lift2]
      rw [heq]
      exact correlationAlongExhaustion_le_correlationInfinite (IsingModel.latticeGraph d) Λ p
        {a.val, b.val} n
    -- Bound `derivBoundTight` by the ambient RHS.
    rw [derivBoundTight]
    refine mul_le_mul_of_nonneg_left ?_ hβJ
    -- per-edge bound, reindex, and inclusion into the boundary edge set.
    have h_each : ∀ e ∈ E₀,
        Sym2.lift ⟨fun u v =>
          IsingModel.correlation Gn p {(⟨0, h0⟩ : ↑(Λ.volume n)), u}
            * IsingModel.correlation Gn p {(⟨x, hxn⟩ : ↑(Λ.volume n)), v}
          + IsingModel.correlation Gn p {(⟨0, h0⟩ : ↑(Λ.volume n)), v}
            * IsingModel.correlation Gn p {(⟨x, hxn⟩ : ↑(Λ.volume n)), u},
        fun u v => by ring⟩ e
          ≤ Finf (Sym2.map Subtype.val e) := by
      intro e _
      obtain ⟨⟨a, b⟩, rfl⟩ := Quot.exists_rep e
      simp only [Sym2.lift_mk, Sym2.map_mk, hFinf]
      have ha0 : IsingModel.correlation Gn p {(⟨0, h0⟩ : ↑(Λ.volume n)), a}
          ≤ correlationInfinite (IsingModel.latticeGraph d) Λ p {0, a.val} := hfin_le _ a
      have hb0 : IsingModel.correlation Gn p {(⟨0, h0⟩ : ↑(Λ.volume n)), b}
          ≤ correlationInfinite (IsingModel.latticeGraph d) Λ p {0, b.val} := hfin_le _ b
      have hxa : IsingModel.correlation Gn p {(⟨x, hxn⟩ : ↑(Λ.volume n)), a}
          ≤ correlationInfinite (IsingModel.latticeGraph d) Λ p {a.val, x} := by
        rw [Finset.pair_comm (⟨x, hxn⟩ : ↑(Λ.volume n)) a]
        exact hfin_le a _
      have hxb : IsingModel.correlation Gn p {(⟨x, hxn⟩ : ↑(Λ.volume n)), b}
          ≤ correlationInfinite (IsingModel.latticeGraph d) Λ p {b.val, x} := by
        rw [Finset.pair_comm (⟨x, hxn⟩ : ↑(Λ.volume n)) b]
        exact hfin_le b _
      have hn_a0 : 0 ≤ IsingModel.correlation Gn p {(⟨0, h0⟩ : ↑(Λ.volume n)), a} :=
        gks_first Gn p hf _
      have hn_xb : 0 ≤ IsingModel.correlation Gn p {(⟨x, hxn⟩ : ↑(Λ.volume n)), b} :=
        gks_first Gn p hf _
      have hi_0a : 0 ≤ correlationInfinite (IsingModel.latticeGraph d) Λ p {0, a.val} :=
        correlationInfinite_nonneg (IsingModel.latticeGraph d) Λ p hf _
      have hi_0b : 0 ≤ correlationInfinite (IsingModel.latticeGraph d) Λ p {0, b.val} :=
        correlationInfinite_nonneg (IsingModel.latticeGraph d) Λ p hf _
      have hn_xa : 0 ≤ IsingModel.correlation Gn p {(⟨x, hxn⟩ : ↑(Λ.volume n)), a} :=
        gks_first Gn p hf _
      have hn_0b : 0 ≤ IsingModel.correlation Gn p {(⟨0, h0⟩ : ↑(Λ.volume n)), b} :=
        gks_first Gn p hf _
      exact add_le_add
        (mul_le_mul ha0 hxb hn_xb hi_0a)
        (mul_le_mul hb0 hxa hn_xa hi_0b)
    -- injectivity of the edge map and inclusion into the boundary edge set
    have hinj : ∀ e₁ ∈ E₀, ∀ e₂ ∈ E₀,
        Sym2.map Subtype.val e₁ = Sym2.map Subtype.val e₂ → e₁ = e₂ :=
      fun e₁ _ e₂ _ h => Sym2.map.injective Subtype.val_injective h
    have h_image_sub : E₀.image (Sym2.map Subtype.val) ⊆ latticeBallBoundaryEdges d r := by
      intro e' he'
      rw [Finset.mem_image] at he'
      obtain ⟨e, he, rfl⟩ := he'
      obtain ⟨⟨a, b⟩, rfl⟩ := Quot.exists_rep e
      rw [hE₀, Finset.mem_filter] at he
      obtain ⟨he_edge, he_str⟩ := he
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, hGn, inducedGraph_apply,
        SimpleGraph.induce_adj] at he_edge
      rw [Sym2.map_mk, mem_latticeBallBoundaryEdges]
      refine ⟨he_edge, ?_⟩
      simp only [straddlePred, Sym2.lift_mk] at he_str
      intro heq
      exact he_str (by rw [hCmem a, hCmem b, heq])
    calc ∑ e ∈ E₀,
          Sym2.lift ⟨fun u v =>
            IsingModel.correlation Gn p {(⟨0, h0⟩ : ↑(Λ.volume n)), u}
              * IsingModel.correlation Gn p {(⟨x, hxn⟩ : ↑(Λ.volume n)), v}
            + IsingModel.correlation Gn p {(⟨0, h0⟩ : ↑(Λ.volume n)), v}
              * IsingModel.correlation Gn p {(⟨x, hxn⟩ : ↑(Λ.volume n)), u},
          fun u v => by ring⟩ e
        ≤ ∑ e ∈ E₀, Finf (Sym2.map Subtype.val e) := Finset.sum_le_sum h_each
      _ = ∑ e' ∈ E₀.image (Sym2.map Subtype.val), Finf e' := (Finset.sum_image hinj).symm
      _ ≤ ∑ e' ∈ latticeBallBoundaryEdges d r, Finf e' :=
          Finset.sum_le_sum_of_subset_of_nonneg h_image_sub (fun e' _ _ => hFinf_nonneg e')
  · -- Not-subset case: LHS `= 0 ≤ RHS`.
    rw [correlationAlongExhaustion_of_not_subset (IsingModel.latticeGraph d) Λ p hA]
    refine mul_nonneg hβJ (Finset.sum_nonneg fun e _ => ?_)
    exact hFinf_nonneg e

end IsingModel.Ambient
