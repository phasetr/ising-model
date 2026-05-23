import IsingModel.Concrete.LatticeGraphBED.NeighborDegree

/-!
# Lattice graph bounded edge density split — weighted handshake identity

Part of the split lattice-graph bounded-edge-density layer (Issue #1850).
-/

/-! ## Weighted handshake identity (Step 159, GJ §17.5 prep)

Relates the sum over undirected edges of `f(u) + f(v)` to the degree-weighted
vertex sum `∑_v deg(v) · f(v)`. Used to bound the Lebowitz sum by the susceptibility.
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V]

/-- **Weighted handshake identity** (Step 159, GJ §17.5):
Summing `f u + f v` over undirected edges equals summing `degree(v) · f(v)` over vertices:
```
∑ e ∈ G.edgeFinset, Sym2.lift ⟨fun u v => f u + f v, _⟩ e = ∑ v, G.degree v * f v
```
Proof: edge sum = dart sum ∑_d f(d.fst) (via fiber {d, d.symm} per edge),
then group by d.fst to get ∑_v deg(v)*f(v).

Reference: Glimm–Jaffe §17.5 (bounds Lebowitz sum via susceptibility). -/
theorem sum_edgeFinset_sym2_lift_add_eq_sum_degree_mul
    (G : SimpleGraph V) [DecidableRel G.Adj] (φ : V → ℝ) :
    ∑ e ∈ G.edgeFinset, Sym2.lift ⟨fun u v => φ u + φ v, fun u v => by ring⟩ e
    = ∑ v : V, (G.degree v : ℝ) * φ v := by
  classical
  -- Step 1: edge sum = dart sum via fiber decomposition
  have h1 : ∑ e ∈ G.edgeFinset, Sym2.lift ⟨fun u v => φ u + φ v, fun u v => by ring⟩ e
      = ∑ d : G.Dart, φ d.fst := by
    -- Group dart sum by edge: ∑ d, φ(d.fst) = ∑ e ∈ E, ∑ d in fiber_e, φ(d.fst)
    conv_rhs =>
      rw [show ∑ d : G.Dart, φ d.fst
          = ∑ e ∈ G.edgeFinset,
              ∑ d ∈ Finset.univ.filter (fun d : G.Dart => d.edge = e), φ d.fst from
        (Finset.sum_fiberwise_of_maps_to (fun (d : G.Dart) _ => G.mem_edgeFinset.mpr d.edge_mem)
           (fun (d : G.Dart) => φ d.fst)).symm]
    apply Finset.sum_congr rfl
    intro e he
    induction e using Sym2.inductionOn
    rename_i u v
    have he' : s(u, v) ∈ G.edgeSet := G.mem_edgeFinset.mp he
    have hadj : G.Adj u v := G.mem_edgeSet.mp he'
    -- Dart fiber for s(u,v) = {⟨(u,v), hadj⟩, ⟨(v,u), hadj.symm⟩}
    have hfiber : Finset.univ.filter (fun d : G.Dart => d.edge = s(u, v)) =
                  {⟨(u, v), hadj⟩, ⟨(v, u), hadj.symm⟩} := by
      have hsym : (⟨(u, v), hadj⟩ : G.Dart).symm = ⟨(v, u), hadj.symm⟩ := rfl
      ext d
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
                 Finset.mem_insert, Finset.mem_singleton]
      rw [show s(u, v) = (⟨(u, v), hadj⟩ : G.Dart).edge from rfl,
          dart_edge_eq_iff d ⟨(u, v), hadj⟩, hsym]
    rw [hfiber]
    have hne : (⟨(u, v), hadj⟩ : G.Dart) ≠ ⟨(v, u), hadj.symm⟩ :=
      fun h => hadj.ne (congrArg (·.toProd.1) h)
    rw [Finset.sum_pair hne, Sym2.lift_mk]
  -- Step 2: dart sum = degree-weighted vertex sum via fst fiber
  -- ∑ d, φ(d.fst) = ∑ v, ∑_{d: d.fst=v} φ(v) = ∑ v, deg(v) * φ(v)
  rw [h1]
  rw [(Finset.sum_fiberwise_of_maps_to (fun (d : G.Dart) _ => Finset.mem_univ d.fst)
       (fun d => φ d.fst)).symm]
  apply Finset.sum_congr rfl
  intro v _
  have inner_eq : ∀ d ∈ Finset.univ.filter (fun d : G.Dart => d.fst = v),
      φ d.fst = φ v := by
    intro d hd; rw [(Finset.mem_filter.mp hd).2]
  rw [Finset.sum_congr rfl inner_eq, Finset.sum_const, nsmul_eq_mul]
  have hcard : (Finset.univ.filter (fun d : G.Dart => d.fst = v)).card = G.degree v :=
    G.dart_fst_fiber_card_eq_degree v
  rw [hcard]

/-- **Dart product sum identity** (Step 160 helper, GJ §17.5):
Summing `f(u)·g(v) + f(v)·g(u)` over undirected edges equals summing `f(d.fst)·g(d.snd)`
over oriented darts:
```
∑ e ∈ G.edgeFinset, Sym2.lift ⟨fun u v => f u * g v + f v * g u, _⟩ e = ∑ d, f d.fst * g d.snd
```
Proof: group darts by edge via fiber decomposition (same structure as
`sum_edgeFinset_sym2_lift_add_eq_sum_degree_mul`).

Reference: Glimm–Jaffe §17.5. -/
theorem sum_edgeFinset_sym2_lift_prod_eq_sum_dart
    (G : SimpleGraph V) [DecidableRel G.Adj] (f g : V → ℝ) :
    ∑ e ∈ G.edgeFinset, Sym2.lift ⟨fun u v => f u * g v + f v * g u, fun u v => by ring⟩ e
    = ∑ d : G.Dart, f d.fst * g d.snd := by
  classical
  conv_rhs =>
    rw [show ∑ d : G.Dart, f d.fst * g d.snd
        = ∑ e ∈ G.edgeFinset,
            ∑ d ∈ Finset.univ.filter (fun d : G.Dart => d.edge = e), f d.fst * g d.snd from
      (Finset.sum_fiberwise_of_maps_to (fun (d : G.Dart) _ => G.mem_edgeFinset.mpr d.edge_mem)
         (fun (d : G.Dart) => f d.fst * g d.snd)).symm]
  apply Finset.sum_congr rfl
  intro e he
  induction e using Sym2.inductionOn
  rename_i u v
  have he' : s(u, v) ∈ G.edgeSet := G.mem_edgeFinset.mp he
  have hadj : G.Adj u v := G.mem_edgeSet.mp he'
  have hfiber : Finset.univ.filter (fun d : G.Dart => d.edge = s(u, v)) =
                {⟨(u, v), hadj⟩, ⟨(v, u), hadj.symm⟩} := by
    have hsym : (⟨(u, v), hadj⟩ : G.Dart).symm = ⟨(v, u), hadj.symm⟩ := rfl
    ext d
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
               Finset.mem_insert, Finset.mem_singleton]
    rw [show s(u, v) = (⟨(u, v), hadj⟩ : G.Dart).edge from rfl,
        dart_edge_eq_iff d ⟨(u, v), hadj⟩, hsym]
  rw [hfiber]
  have hne : (⟨(u, v), hadj⟩ : G.Dart) ≠ ⟨(v, u), hadj.symm⟩ :=
    fun h => hadj.ne (congrArg (·.toProd.1) h)
  rw [Finset.sum_pair hne, Sym2.lift_mk]

end SimpleGraph
