import IsingModel.RandomCurrent.Switching.SupportGraph

/-!
# Support-graph constancy of the spin sign (Stage C2.1c)

For a fixed current `M : Current G Λ` and spin configuration `σ : ↑Λ → Spin`,
if the subcurrent generating polynomial
`P_M(σ) = ∏_e (1 + z_e(σ))^{M_e}` is nonzero
(`z_e(σ) = ∏_{v ∈ e} (σ v).toSign`), then the spin sign `(σ ·).toSign` is
constant along every edge of the support graph `M.toSimpleGraph`, hence along
every walk: `(M.toSimpleGraph G Λ).Reachable x y → (σ x).toSign = (σ y).toSign`.

This is the "genuinely new" third brick (C2.1c) of the discharge of the
switching gate `hswitch'` (random-current OZ, issue #4386, thread #4418). The
mechanism is: nonzero `P_M(σ)` forces every support-edge factor
`(1 + z_e)^{M_e} ≠ 0`, so `z_e = (σ u).toSign · (σ v).toSign ∈ {±1}` is not
`-1`, i.e. `z_e = +1`, i.e. the two endpoint signs agree; walk induction then
propagates the equality across each connected component. No analytic input, no
limit, axiom-free (textbook walk induction over `Spin = {±1}`).

## References

* Fernández–Fröhlich–Sokal, *Random Walks, Critical Phenomena, and
  Triviality in Quantum Field Theory* (1992), Ch. 12.
* Aizenman, M. (1982). Geometric analysis of φ⁴ fields.
* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §17.5, Theorem 17.5.1, p. 312.
-/

/-- **Walk constancy**: a vertex map `f : V → β` that is constant across every
edge of a `SimpleGraph G` is constant on each connected component. Concretely,
if `f u = f v` whenever `G.Adj u v`, then `G.Reachable x y → f x = f y`. Proved
by induction on the underlying walk: the `nil` base is reflexivity, and each
`cons` step chains the per-edge hypothesis with the induction hypothesis. There
is no ready-made mathlib lemma of this shape; this is the direct walk induction.
-/
theorem SimpleGraph.Reachable.eq_of_adj_imp_eq
    {V β : Type*} {G : SimpleGraph V} {f : V → β}
    (hf : ∀ {u v : V}, G.Adj u v → f u = f v)
    {x y : V} (h : G.Reachable x y) : f x = f y := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => rfl
  | cons hadj _ ih => exact (hf hadj).trans ih

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **Local constancy on a support edge**: if the generating polynomial
`P_M(σ) = ∏_e (1 + z_e(σ))^{M_e}` is nonzero and `u, v` are adjacent in the
support of `M` (`Current.Adj`), then `(σ u).toSign = (σ v).toSign` in `ℝ`. From
`M.Adj u v` extract a support edge `e ∈ M.support` with `u, v ∈ e`; the factor
at `e` is nonzero (`Finset.prod_ne_zero_iff`), and `M e ≠ 0` on the support
(`Current.mem_support_iff`) gives `1 + z_e(σ) ≠ 0` (`pow_ne_zero_iff`). The
two-element edge finset equals `{u, v}` (`edgeSet_toFinset_card_eq_two` +
`Finset.eq_of_subset_of_card_le`), so `z_e(σ) = (σ u).toSign · (σ v).toSign`
(`Finset.prod_pair`); since each sign is `±1`, `1 + z_e ≠ 0` rules out
`z_e = -1`, forcing the two signs equal (four-way `Spin` case split). -/
theorem Current.toSign_eq_of_adj_of_prod_ne_zero (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (M : Current G Λ) (σ : ↑Λ → Spin)
    (hP : (∏ e : (inducedGraph G Λ).edgeSet,
        (1 + (e : Sym2 ↑Λ).toFinset.prod (fun v => ((σ v).toSign : ℝ)))
          ^ (M e)) ≠ 0)
    {u v : ↑Λ} (hadj : M.Adj G Λ u v) :
    ((σ u).toSign : ℝ) = ((σ v).toSign : ℝ) := by
  classical
  obtain ⟨hne, e, he_supp, hu, hv⟩ := hadj
  have hfac :
      (1 + (e : Sym2 ↑Λ).toFinset.prod (fun v => ((σ v).toSign : ℝ)))
          ^ (M e) ≠ 0 :=
    Finset.prod_ne_zero_iff.mp hP e (Finset.mem_univ e)
  have hMe : M e ≠ 0 := (Current.mem_support_iff G Λ M e).mp he_supp
  have hbase :
      (1 + (e : Sym2 ↑Λ).toFinset.prod (fun v => ((σ v).toSign : ℝ))) ≠ 0 :=
    (pow_ne_zero_iff hMe).mp hfac
  have hsub : ({u, v} : Finset ↑Λ) ⊆ (e : Sym2 ↑Λ).toFinset := by
    intro w hw
    rcases Finset.mem_insert.mp hw with h | h
    · subst h; exact Sym2.mem_toFinset.mpr hu
    · rw [Finset.mem_singleton] at h; subst h; exact Sym2.mem_toFinset.mpr hv
  have hcard : (e : Sym2 ↑Λ).toFinset.card ≤ ({u, v} : Finset ↑Λ).card := by
    rw [Current.edgeSet_toFinset_card_eq_two G Λ e, Finset.card_pair hne]
  have hfin : (e : Sym2 ↑Λ).toFinset = {u, v} :=
    (Finset.eq_of_subset_of_card_le hsub hcard).symm
  rw [hfin, Finset.prod_pair hne] at hbase
  cases hu' : σ u <;> cases hv' : σ v <;>
    simp_all [Spin.toSign]

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **C2.1c: walk constancy of the spin sign**: if the generating polynomial
`P_M(σ) = ∏_e (1 + z_e(σ))^{M_e}` is nonzero and `x, y` are connected in the
support graph `M.toSimpleGraph`, then `(σ x).toSign = (σ y).toSign` in `ℝ`.
Apply the generic walk-constancy lemma `SimpleGraph.Reachable.eq_of_adj_imp_eq`
to `f = fun v => ((σ v).toSign : ℝ)`, whose per-edge hypothesis is the local
constancy `Current.toSign_eq_of_adj_of_prod_ne_zero` composed with the support
adjacency unfolding `Current.toSimpleGraph_adj_iff`. -/
theorem Current.toSign_eq_of_reachable_of_prod_ne_zero (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (M : Current G Λ) (σ : ↑Λ → Spin)
    (hP : (∏ e : (inducedGraph G Λ).edgeSet,
        (1 + (e : Sym2 ↑Λ).toFinset.prod (fun v => ((σ v).toSign : ℝ)))
          ^ (M e)) ≠ 0)
    {x y : ↑Λ} (hreach : (M.toSimpleGraph G Λ).Reachable x y) :
    ((σ x).toSign : ℝ) = ((σ y).toSign : ℝ) :=
  SimpleGraph.Reachable.eq_of_adj_imp_eq
    (f := fun v => ((σ v).toSign : ℝ))
    (fun {u v} huv =>
      Current.toSign_eq_of_adj_of_prod_ne_zero G Λ M σ hP
        ((Current.toSimpleGraph_adj_iff G Λ M u v).mp huv))
    hreach

end Ambient
end IsingModel
