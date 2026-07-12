import IsingModel.Inequalities.ClusterConditioningPivotal

/-!
# SL-D brick D1a: additive source/parity/degree split of a pinned pivotal fiber

This module implements ingredient **SL-D, brick D1a**: the pointwise-per-vertex
*additive* decomposition of the incident degree / parity / source set of a pinned
pivotal-fiber current `M` across the pinned edge partition
`E = E_int ⊔ E_cross ⊔ E_ext`, where
`E_int = interiorEdges C`, `E_ext = interiorEdges Cᶜ`,
`E_cross = (E_int ∪ E_ext)ᶜ` and `C = reachableCluster (M − 1_{e₀}) x` is the
decremented cluster of a pivotal edge `e₀ = s(a, b)`. The crossing block collapses
onto the single bridge `e₀` (which carries `M e₀ = 1`), so at every vertex `v`
\[
  \mathrm{degreeAt}\,M\,v
    = \mathrm{degreeOn}\,E_{\mathrm{int}}\,M\,v + \mathrm{degreeOn}\,E_{\mathrm{ext}}\,M\,v
      + [v = a] + [v = b],
\]
which, on `C` (where the exterior block is invisible) and on `Cᶜ` (where the
interior block is invisible), and after fixing the F1 labelling `a ∈ C, b ∉ C`,
becomes the two clauses `degreeAt M v = degreeOn E_int M v + [v = a]` (for `v ∈ C`)
and `degreeAt M v = degreeOn E_ext M v + [v = b]` (for `v ∉ C`); reducing mod 2
gives the parity clauses and, with `sources M = {x, y}`, the source-set split
`sourcesOn E_int M = {x, a}` and `sourcesOn E_ext M = {b, y}`.

**Scope.** D1a proves ONLY this per-vertex additive split and its source-set
corollary. It is `SL-D₁`'s (product Fubini) source/parity *foundation*: it does
**not** build the restriction/gluing bijection `Φ` nor the `Finset.sum_product`
Fubini (D1b), and does **not** touch the exterior → two-point collapse. The
genuine research core **SL-D₂ (conditioned-switching, Aizenman Lemma 4.1) awaits
explicit user authorisation** and is not started here.

**Tracked-ingredient status.** Like SL-A/SL-B/SL-C, D1a is a *tracked ingredient*
(Group 1a authorisation), buildable and axiom-free, with reference-count zero into
the live capstone until D1b / SL-D₂ / SL-E land. Its intended downstream position is
the (future) Lemma 5.1 → P2-ii → `hLogLip` → the explicitly-tracked
lower-semicontinuity half of GJ Theorem 17.5.1 (§17.5, issue #4386 / thread #4418).
The weight `Current.weight` is `∏_e (βJ)^{n_e}/n_e!`, the random-current weight of
FV, eq. (3.45); D1a itself uses only the source/parity combinatorics, not the
weight.

## References

* Friedli–Velenik, *Statistical Mechanics of Lattice Systems*, §3.7, eq. (3.45).
* Glimm–Jaffe, *Quantum Physics* (2nd ed.), Theorem 17.5.1, p. 312 (lsc half,
  issue #4386 / thread #4418).
* Aizenman (1982), Lemma 4.1; Fernández–Fröhlich–Sokal (1992), Ch. 12.
-/

namespace IsingModel

namespace Ambient

open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **`S`-restricted incident degree**: for an edge subset `S`, a current `n` and a
vertex `v`, the ℕ-valued sum of `n e` over edges `e ∈ S` incident to `v`,
`∑_{e ∈ S} [v ∈ e] · n e`. The global `Current.degreeAt` is `degreeOn` over the
full edge set (`Current.degreeOn_univ_eq_degreeAt`); `degreeOn` is additive over
disjoint edge subsets (`Current.degreeOn_union`). Part of ingredient **SL-D₁**
brick D1a (tracked ingredient, Group 1a; the SL-D₂ conditioned-switching core
awaits explicit user authorisation); weight source FV (3.45). -/
def Current.degreeOn (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (S : Finset (inducedGraph G Λ).edgeSet) (n : Current G Λ) (v : ↑Λ) : ℕ :=
  ∑ e ∈ S, if v ∈ (e : Sym2 ↑Λ) then n e else 0

/-- **`S`-restricted parity**: the `ZMod 2` reduction of the `S`-restricted
incident degree `Current.degreeOn`, `∑_{e ∈ S} [v ∈ e] · (n e mod 2)`. Equals
`(Current.degreeOn S n v mod 2)` (`Current.parityOn_eq_degreeOn`); the global
`Current.parity` is `parityOn` over the full edge set. Part of ingredient
**SL-D₁** brick D1a (tracked ingredient, Group 1a; the SL-D₂ conditioned-switching
core awaits explicit user authorisation); weight source FV (3.45). -/
def Current.parityOn (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (S : Finset (inducedGraph G Λ).edgeSet) (n : Current G Λ) (v : ↑Λ) : ZMod 2 :=
  ∑ e ∈ S, if v ∈ (e : Sym2 ↑Λ) then ((n e : ℕ) : ZMod 2) else 0

omit [DecidableEq V] in
/-- **`degreeOn` over the full edge set is `degreeAt`**: summing the incident
contributions over all induced-graph edges recovers the global incident degree
`Current.degreeAt`. Definitional. Part of ingredient **SL-D₁** brick D1a. -/
theorem Current.degreeOn_univ_eq_degreeAt (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (v : ↑Λ) :
    n.degreeOn G Λ Finset.univ v = n.degreeAt G Λ v := rfl

omit [DecidableEq V] in
/-- **`degreeOn` is additive over disjoint edge subsets**: for disjoint `S, T`,
`degreeOn (S ∪ T) n v = degreeOn S n v + degreeOn T n v` (a `Finset.sum_union`).
Part of ingredient **SL-D₁** brick D1a. -/
theorem Current.degreeOn_union (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    {S T : Finset (inducedGraph G Λ).edgeSet} (hST : Disjoint S T)
    (n : Current G Λ) (v : ↑Λ) :
    n.degreeOn G Λ (S ∪ T) v = n.degreeOn G Λ S v + n.degreeOn G Λ T v := by
  unfold Current.degreeOn
  exact Finset.sum_union hST

omit [DecidableEq V] in
/-- **`degreeOn` on `S` and on its complement recombine to `degreeAt`**:
`degreeOn S n v + degreeOn Sᶜ n v = degreeAt n v` (a `Finset.sum_add_sum_compl`).
Part of ingredient **SL-D₁** brick D1a. -/
theorem Current.degreeOn_add_compl (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (S : Finset (inducedGraph G Λ).edgeSet) (n : Current G Λ) (v : ↑Λ) :
    n.degreeOn G Λ S v + n.degreeOn G Λ Sᶜ v = n.degreeAt G Λ v := by
  unfold Current.degreeOn Current.degreeAt
  exact Finset.sum_add_sum_compl S _

omit [DecidableEq V] in
/-- **`parityOn` equals `degreeOn mod 2`**: the `ZMod 2` restricted parity is the
`ℕ → ZMod 2` cast of the restricted incident degree, mirroring
`Current.parity_eq_degreeAt`. Part of ingredient **SL-D₁** brick D1a. -/
theorem Current.parityOn_eq_degreeOn (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (S : Finset (inducedGraph G Λ).edgeSet) (n : Current G Λ) (v : ↑Λ) :
    n.parityOn G Λ S v = ((n.degreeOn G Λ S v : ℕ) : ZMod 2) := by
  unfold Current.parityOn Current.degreeOn
  rw [Nat.cast_sum]
  congr 1
  ext e
  by_cases hv : v ∈ (e : Sym2 ↑Λ) <;> simp [hv]

omit [DecidableEq V] in
/-- **A restricted degree vanishes when `v` lies on no edge of `S`**: if every edge
of `S` misses `v`, then `degreeOn S n v = 0` (every summand is `0`). Part of
ingredient **SL-D₁** brick D1a. -/
theorem Current.degreeOn_eq_zero_of_forall_not_mem (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (S : Finset (inducedGraph G Λ).edgeSet) (n : Current G Λ) (v : ↑Λ)
    (h : ∀ e ∈ S, v ∉ (e : Sym2 ↑Λ)) :
    n.degreeOn G Λ S v = 0 := by
  unfold Current.degreeOn
  apply Finset.sum_eq_zero
  intro e he
  rw [if_neg (h e he)]

set_option linter.unusedDecidableInType false in
/-- **The exterior block is invisible on `C`**: if `v ∈ C` then
`degreeOn (interiorEdges Cᶜ) M v = 0`, since every exterior edge has both endpoints
in `Cᶜ`, hence misses `v ∈ C`. Part of ingredient **SL-D₁** brick D1a. -/
theorem Current.degreeOn_interiorEdges_compl_eq_zero_of_mem (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (C : Finset ↑Λ) (n : Current G Λ) (v : ↑Λ) (hvC : v ∈ C) :
    n.degreeOn G Λ (Current.interiorEdges G Λ Cᶜ) v = 0 := by
  apply Current.degreeOn_eq_zero_of_forall_not_mem
  intro e he hve
  rw [Current.mem_interiorEdges_iff] at he
  exact (Finset.mem_compl.mp (he v hve)) hvC

set_option linter.unusedDecidableInType false in
/-- **The interior block is invisible off `C`**: if `v ∉ C` then
`degreeOn (interiorEdges C) M v = 0`, since every interior edge has both endpoints
in `C`, hence misses `v ∉ C`. Part of ingredient **SL-D₁** brick D1a. -/
theorem Current.degreeOn_interiorEdges_eq_zero_of_not_mem (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (C : Finset ↑Λ) (n : Current G Λ) (v : ↑Λ) (hvC : v ∉ C) :
    n.degreeOn G Λ (Current.interiorEdges G Λ C) v = 0 := by
  apply Current.degreeOn_eq_zero_of_forall_not_mem
  intro e he hve
  rw [Current.mem_interiorEdges_iff] at he
  exact hvC (he v hve)

set_option linter.unusedDecidableInType false in
/-- **The crossing block collapses onto the bridge `e₀`** (D1a.3). Under the
pivotal hypothesis, at every vertex `v`
\[
  \mathrm{degreeOn}\,E_{\mathrm{cross}}\,M\,v = [v = a] + [v = b],
\]
where `E_cross = (interiorEdges C ∪ interiorEdges Cᶜ)ᶜ` and
`C = reachableCluster (M − 1_{e₀}) x`. Proof: `e₀ ∈ E_cross` (F1 separates its
endpoints, so `e₀` is neither interior nor exterior); every other crossing edge
carries `M e = 0` (F3); so the sum collapses to the `e₀` term, equal to
`[v ∈ s(a,b)] · M e₀ = [v ∈ {a,b}]` (F2 gives `M e₀ = 1`), which is `[v = a] + [v = b]`
because `a ≠ b`. Part of ingredient **SL-D₁** brick D1a (tracked ingredient,
Group 1a; the SL-D₂ conditioned-switching core awaits explicit user authorisation);
weight source FV (3.45). -/
theorem Current.degreeOn_cross_eq (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (e₀ : (inducedGraph G Λ).edgeSet) (M : Current G Λ) (x y a b : ↑Λ)
    (C : Finset ↑Λ) (hab : (e₀ : Sym2 ↑Λ) = s(a, b))
    (hpiv : Current.EdgePivotal G Λ e₀ M x y)
    (hC : Current.reachableCluster G Λ (M - Current.fromEdgeFinset G Λ {e₀}) x = C)
    (v : ↑Λ) :
    M.degreeOn G Λ (Current.interiorEdges G Λ C ∪ Current.interiorEdges G Λ Cᶜ)ᶜ v
      = (if v = a then 1 else 0) + (if v = b then 1 else 0) := by
  have hMe0 : M e₀ = 1 :=
    Current.edgePivotal_dominant_edge_eq_one G Λ e₀ M x y a b hab hpiv
  have hab_ne : a ≠ b := by
    have hmem := e₀.2
    rw [hab, SimpleGraph.mem_edgeSet] at hmem
    exact hmem.ne
  have hamem : a ∈ (e₀ : Sym2 ↑Λ) := by rw [hab]; exact Sym2.mem_mk_left a b
  have hbmem : b ∈ (e₀ : Sym2 ↑Λ) := by rw [hab]; exact Sym2.mem_mk_right a b
  have hsplitC : (a ∈ C ∧ b ∉ C) ∨ (b ∈ C ∧ a ∉ C) := by
    have h := Current.edgePivotal_endpoint_split G Λ e₀ M x y a b hab hpiv
    rw [hC] at h; exact h
  have he0_int : e₀ ∉ Current.interiorEdges G Λ C := by
    rw [Current.mem_interiorEdges_iff]; push Not
    rcases hsplitC with ⟨_, hbC⟩ | ⟨_, haC⟩
    · exact ⟨b, hbmem, hbC⟩
    · exact ⟨a, hamem, haC⟩
  have he0_ext : e₀ ∉ Current.interiorEdges G Λ Cᶜ := by
    rw [Current.mem_interiorEdges_iff]; push Not
    rcases hsplitC with ⟨haC, _⟩ | ⟨hbC, _⟩
    · exact ⟨a, hamem, fun h => (Finset.mem_compl.mp h) haC⟩
    · exact ⟨b, hbmem, fun h => (Finset.mem_compl.mp h) hbC⟩
  have he0_cross :
      e₀ ∈ (Current.interiorEdges G Λ C ∪ Current.interiorEdges G Λ Cᶜ)ᶜ := by
    rw [Finset.mem_compl, Finset.mem_union]; push Not; exact ⟨he0_int, he0_ext⟩
  unfold Current.degreeOn
  rw [Finset.sum_eq_single_of_mem e₀ he0_cross ?_]
  · rw [hMe0, hab]
    by_cases hva : v = a <;> by_cases hvb : v = b <;>
      simp_all [Sym2.mem_iff]
  · intro e he hne
    rw [Finset.mem_compl, Finset.mem_union] at he
    push Not at he
    obtain ⟨he_notint, he_notext⟩ := he
    rw [Current.mem_interiorEdges_iff] at he_notint
    push Not at he_notint
    obtain ⟨w', hw'e, hw'C⟩ := he_notint
    rw [Current.mem_interiorEdges_iff] at he_notext
    push Not at he_notext
    obtain ⟨w, hwe, hwCc⟩ := he_notext
    have hwC : w ∈ C := by
      by_contra h; exact hwCc (Finset.mem_compl.mpr h)
    have hwne : w ≠ w' := by rintro rfl; exact hw'C hwC
    have hesym : (e : Sym2 ↑Λ) = s(w, w') :=
      (Sym2.mem_and_mem_iff hwne).mp ⟨hwe, hw'e⟩
    have hwmem :
        w ∈ Current.reachableCluster G Λ (M - Current.fromEdgeFinset G Λ {e₀}) x := by
      rw [hC]; exact hwC
    have hw'nmem :
        w' ∉ Current.reachableCluster G Λ (M - Current.fromEdgeFinset G Λ {e₀}) x := by
      rw [hC]; exact hw'C
    have hMe : M e = 0 :=
      Current.edgePivotal_no_spectator_crossing G Λ e₀ e M x w w'
        hwmem hw'nmem hesym hne
    rw [hMe]; simp

set_option linter.unusedDecidableInType false in
/-- **Symmetric interior degree split on `C`** (D1a.4, interior half, unlabelled).
For `v ∈ C`,
`degreeAt M v = degreeOn (interiorEdges C) M v + [v = a] + [v = b]`,
combining the edge-partition additivity (D1a.1), the vanishing of the exterior
block on `C` (D1a.2) and the crossing collapse (D1a.3). Part of ingredient
**SL-D₁** brick D1a. -/
theorem Current.degreeAt_eq_degreeOn_interior_add_bridge_of_mem (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (e₀ : (inducedGraph G Λ).edgeSet) (M : Current G Λ) (x y a b : ↑Λ)
    (C : Finset ↑Λ) (hab : (e₀ : Sym2 ↑Λ) = s(a, b))
    (hpiv : Current.EdgePivotal G Λ e₀ M x y)
    (hC : Current.reachableCluster G Λ (M - Current.fromEdgeFinset G Λ {e₀}) x = C)
    (v : ↑Λ) (hvC : v ∈ C) :
    M.degreeAt G Λ v
      = M.degreeOn G Λ (Current.interiorEdges G Λ C) v
        + ((if v = a then 1 else 0) + (if v = b then 1 else 0)) := by
  have hdisj := Current.interiorEdges_disjoint G Λ C
  have hsplit :
      M.degreeAt G Λ v
        = M.degreeOn G Λ (Current.interiorEdges G Λ C) v
          + M.degreeOn G Λ (Current.interiorEdges G Λ Cᶜ) v
          + M.degreeOn G Λ
              (Current.interiorEdges G Λ C ∪ Current.interiorEdges G Λ Cᶜ)ᶜ v := by
    have h1 := Current.degreeOn_add_compl G Λ
      (Current.interiorEdges G Λ C ∪ Current.interiorEdges G Λ Cᶜ) M v
    rw [Current.degreeOn_union G Λ hdisj] at h1
    omega
  have hext := Current.degreeOn_interiorEdges_compl_eq_zero_of_mem G Λ C M v hvC
  have hcross := Current.degreeOn_cross_eq G Λ e₀ M x y a b C hab hpiv hC v
  rw [hsplit, hext, hcross]
  ring

set_option linter.unusedDecidableInType false in
/-- **Symmetric exterior degree split off `C`** (D1a.4, exterior half, unlabelled).
For `v ∉ C`,
`degreeAt M v = degreeOn (interiorEdges Cᶜ) M v + [v = a] + [v = b]`. Part of
ingredient **SL-D₁** brick D1a. -/
theorem Current.degreeAt_eq_degreeOn_exterior_add_bridge_of_not_mem (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (e₀ : (inducedGraph G Λ).edgeSet) (M : Current G Λ) (x y a b : ↑Λ)
    (C : Finset ↑Λ) (hab : (e₀ : Sym2 ↑Λ) = s(a, b))
    (hpiv : Current.EdgePivotal G Λ e₀ M x y)
    (hC : Current.reachableCluster G Λ (M - Current.fromEdgeFinset G Λ {e₀}) x = C)
    (v : ↑Λ) (hvC : v ∉ C) :
    M.degreeAt G Λ v
      = M.degreeOn G Λ (Current.interiorEdges G Λ Cᶜ) v
        + ((if v = a then 1 else 0) + (if v = b then 1 else 0)) := by
  have hdisj := Current.interiorEdges_disjoint G Λ C
  have hsplit :
      M.degreeAt G Λ v
        = M.degreeOn G Λ (Current.interiorEdges G Λ C) v
          + M.degreeOn G Λ (Current.interiorEdges G Λ Cᶜ) v
          + M.degreeOn G Λ
              (Current.interiorEdges G Λ C ∪ Current.interiorEdges G Λ Cᶜ)ᶜ v := by
    have h1 := Current.degreeOn_add_compl G Λ
      (Current.interiorEdges G Λ C ∪ Current.interiorEdges G Λ Cᶜ) M v
    rw [Current.degreeOn_union G Λ hdisj] at h1
    omega
  have hint := Current.degreeOn_interiorEdges_eq_zero_of_not_mem G Λ C M v hvC
  have hcross := Current.degreeOn_cross_eq G Λ e₀ M x y a b C hab hpiv hC v
  rw [hsplit, hint, hcross]
  ring

omit [DecidableEq V] in
/-- **Mod-2 cast of a `degreeAt = degreeOn + [P]` clause** (D1a parity bridge). If
`degreeAt M v = degreeOn S M v + [P]` in ℕ (with `[P] = if P then 1 else 0`), then
reducing mod 2 (`Current.parity_eq_degreeAt`, `Current.parityOn_eq_degreeOn`) gives
`parity M v = parityOn S M v + [P]` in `ZMod 2`. Part of ingredient **SL-D₁**
brick D1a. -/
theorem Current.parity_eq_parityOn_add_ite (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (S : Finset (inducedGraph G Λ).edgeSet) (M : Current G Λ) (v : ↑Λ)
    (P : Prop) [Decidable P]
    (hdeg : M.degreeAt G Λ v = M.degreeOn G Λ S v + (if P then (1 : ℕ) else 0)) :
    M.parity G Λ v = M.parityOn G Λ S v + (if P then (1 : ZMod 2) else 0) := by
  rw [Current.parity_eq_degreeAt, hdeg, Nat.cast_add, ← Current.parityOn_eq_degreeOn]
  congr 1
  by_cases hP : P <;> simp [hP]

set_option linter.unusedDecidableInType false in
/-- **D1a per-vertex additive source/parity/degree split of a pinned pivotal fiber**
(main D1a statement, degree + parity form). Under the pivotal hypothesis with
`e₀ = s(a, b)` and decremented cluster `C = reachableCluster (M − 1_{e₀}) x`, the
F1 labelling (`edgePivotal_endpoint_split`) puts exactly one endpoint of `e₀` in
`C`; accordingly one of the two symmetric branches holds. In the branch
`a ∈ C, b ∉ C`:
* interior degree: `∀ v ∈ C, degreeAt M v = degreeOn (interiorEdges C) M v + [v = a]`;
* exterior degree: `∀ v ∉ C, degreeAt M v = degreeOn (interiorEdges Cᶜ) M v + [v = b]`;
* the two mod-2 parity clauses (`Current.parity`, `Current.parityOn`) with the same
  `[v = a]` / `[v = b]` bridge bumps.
The other branch `b ∈ C, a ∉ C` swaps `a ↔ b` in the bumps. Proof: from the
symmetric unlabelled splits
`Current.degreeAt_eq_degreeOn_interior_add_bridge_of_mem` /
`..._exterior_add_bridge_of_not_mem` (which package D1a.1–D1a.3), the off-cluster
bump vanishes (`v ∈ C, b ∉ C ⟹ v ≠ b`, resp. `v ∉ C, a ∈ C ⟹ v ≠ a`); the parity
clauses are the mod-2 casts (`Current.parity_eq_parityOn_add_ite`). This is the
D1a foundation of `SL-D₁` (product Fubini); **D1b (the restriction/gluing Fubini)
and the SL-D₂ conditioned-switching core (Aizenman Lemma 4.1) are follow-ups, the
latter awaiting explicit user authorisation.** Tracked ingredient (Group 1a),
downstream position: future Lemma 5.1 → `hLogLip` → lsc half of GJ Theorem 17.5.1
(§17.5, issue #4386 / thread #4418); weight source FV (3.45). -/
theorem Current.pivotalFiber_sources_split (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (e₀ : (inducedGraph G Λ).edgeSet) (M : Current G Λ) (x y a b : ↑Λ)
    (C : Finset ↑Λ) (hab : (e₀ : Sym2 ↑Λ) = s(a, b))
    (hpiv : Current.EdgePivotal G Λ e₀ M x y)
    (hC : Current.reachableCluster G Λ (M - Current.fromEdgeFinset G Λ {e₀}) x = C) :
    ((a ∈ C ∧ b ∉ C) ∧
      (∀ v ∈ C, M.degreeAt G Λ v
        = M.degreeOn G Λ (Current.interiorEdges G Λ C) v + (if v = a then 1 else 0)) ∧
      (∀ v ∉ C, M.degreeAt G Λ v
        = M.degreeOn G Λ (Current.interiorEdges G Λ Cᶜ) v + (if v = b then 1 else 0)) ∧
      (∀ v ∈ C, M.parity G Λ v
        = M.parityOn G Λ (Current.interiorEdges G Λ C) v + (if v = a then 1 else 0)) ∧
      (∀ v ∉ C, M.parity G Λ v
        = M.parityOn G Λ (Current.interiorEdges G Λ Cᶜ) v + (if v = b then 1 else 0)))
    ∨
    ((b ∈ C ∧ a ∉ C) ∧
      (∀ v ∈ C, M.degreeAt G Λ v
        = M.degreeOn G Λ (Current.interiorEdges G Λ C) v + (if v = b then 1 else 0)) ∧
      (∀ v ∉ C, M.degreeAt G Λ v
        = M.degreeOn G Λ (Current.interiorEdges G Λ Cᶜ) v + (if v = a then 1 else 0)) ∧
      (∀ v ∈ C, M.parity G Λ v
        = M.parityOn G Λ (Current.interiorEdges G Λ C) v + (if v = b then 1 else 0)) ∧
      (∀ v ∉ C, M.parity G Λ v
        = M.parityOn G Λ (Current.interiorEdges G Λ Cᶜ) v + (if v = a then 1 else 0))) := by
  have hsplitC : (a ∈ C ∧ b ∉ C) ∨ (b ∈ C ∧ a ∉ C) := by
    have h := Current.edgePivotal_endpoint_split G Λ e₀ M x y a b hab hpiv
    rw [hC] at h; exact h
  rcases hsplitC with ⟨haC, hbC⟩ | ⟨hbC, haC⟩
  · left
    refine ⟨⟨haC, hbC⟩, ?_, ?_, ?_, ?_⟩
    · intro v hv
      have h := Current.degreeAt_eq_degreeOn_interior_add_bridge_of_mem
        G Λ e₀ M x y a b C hab hpiv hC v hv
      have hvb : v ≠ b := fun h' => hbC (h' ▸ hv)
      rw [h, if_neg hvb]; ring
    · intro v hv
      have h := Current.degreeAt_eq_degreeOn_exterior_add_bridge_of_not_mem
        G Λ e₀ M x y a b C hab hpiv hC v hv
      have hva : v ≠ a := by rintro rfl; exact hv haC
      rw [h, if_neg hva]; ring
    · intro v hv
      apply Current.parity_eq_parityOn_add_ite
      have h := Current.degreeAt_eq_degreeOn_interior_add_bridge_of_mem
        G Λ e₀ M x y a b C hab hpiv hC v hv
      have hvb : v ≠ b := fun h' => hbC (h' ▸ hv)
      rw [h, if_neg hvb]; ring
    · intro v hv
      apply Current.parity_eq_parityOn_add_ite
      have h := Current.degreeAt_eq_degreeOn_exterior_add_bridge_of_not_mem
        G Λ e₀ M x y a b C hab hpiv hC v hv
      have hva : v ≠ a := by rintro rfl; exact hv haC
      rw [h, if_neg hva]; ring
  · right
    refine ⟨⟨hbC, haC⟩, ?_, ?_, ?_, ?_⟩
    · intro v hv
      have h := Current.degreeAt_eq_degreeOn_interior_add_bridge_of_mem
        G Λ e₀ M x y a b C hab hpiv hC v hv
      have hva : v ≠ a := fun h' => haC (h' ▸ hv)
      rw [h, if_neg hva]; ring
    · intro v hv
      have h := Current.degreeAt_eq_degreeOn_exterior_add_bridge_of_not_mem
        G Λ e₀ M x y a b C hab hpiv hC v hv
      have hvb : v ≠ b := by rintro rfl; exact hv hbC
      rw [h, if_neg hvb]; ring
    · intro v hv
      apply Current.parity_eq_parityOn_add_ite
      have h := Current.degreeAt_eq_degreeOn_interior_add_bridge_of_mem
        G Λ e₀ M x y a b C hab hpiv hC v hv
      have hva : v ≠ a := fun h' => haC (h' ▸ hv)
      rw [h, if_neg hva]; ring
    · intro v hv
      apply Current.parity_eq_parityOn_add_ite
      have h := Current.degreeAt_eq_degreeOn_exterior_add_bridge_of_not_mem
        G Λ e₀ M x y a b C hab hpiv hC v hv
      have hvb : v ≠ b := by rintro rfl; exact hv hbC
      rw [h, if_neg hvb]; ring

/-- **`S`-restricted source set** of a current `n`: the `Finset` of vertices `v`
with non-zero `S`-restricted parity (`Current.parityOn S n v ≠ 0`). The global
`Current.sources` is `sourcesOn` over the full edge set. Part of ingredient
**SL-D₁** brick D1a (tracked ingredient, Group 1a; the SL-D₂ conditioned-switching
core awaits explicit user authorisation); weight source FV (3.45). -/
noncomputable def Current.sourcesOn (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (S : Finset (inducedGraph G Λ).edgeSet) (n : Current G Λ) : Finset ↑Λ :=
  (Finset.univ : Finset ↑Λ).filter (fun v => n.parityOn G Λ S v ≠ 0)

omit [DecidableEq V] in
/-- **Membership in `Current.sourcesOn`**: `v ∈ n.sourcesOn S` iff
`n.parityOn S v ≠ 0`. Part of ingredient **SL-D₁** brick D1a. -/
theorem Current.mem_sourcesOn_iff (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (S : Finset (inducedGraph G Λ).edgeSet) (n : Current G Λ) (v : ↑Λ) :
    v ∈ n.sourcesOn G Λ S ↔ n.parityOn G Λ S v ≠ 0 := by
  classical
  simp [Current.sourcesOn]

omit [DecidableEq V] in
/-- **A restricted source set is a symmetric difference** (degeneracy-uniform D1a
source-decoupling step). Suppose,
on a vertex block `D`, the parity of `M` differs from its `S`-restricted parity by a
single bridge bump at `p`
(`hpar : ∀ v ∈ D, parity M v = parityOn S M v + [v = p]`), the restricted source set
sits inside `D` (`hsub`), the bridge point `p` and the source point `q` both lie in
`D` (`hpD`, `hqD`), and within `D` the unique global source is `q` (`hDsrc`). Then
`sourcesOn S M = {q} △ {p}` (the `ZMod 2` symmetric-difference inversion): off `D`
the restricted parity vanishes; on `D` it equals `[v = q] + [v = p]`, non-zero
exactly at the symmetric difference `{q} △ {p}`. This form
**needs no `p ≠ q` nor `p ∉ sources` side condition**: the symmetric difference
absorbs the degeneracy `p = q` (where it collapses to `∅`, `M`'s near-endpoint
source coinciding with the bridge endpoint), so the pinned-pivotal-fiber corollary
`Current.pivotalFiber_sourcesOn_symmDiff` holds unconditionally (the `x = a` / `y = b`
degenerate configurations of a backbone pinned fiber are handled correctly, resolving
the D1b nondegeneracy design blocker). Part of ingredient **SL-D₁** brick D1a. -/
theorem Current.sourcesOn_eq_symmDiff (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (S : Finset (inducedGraph G Λ).edgeSet) (M : Current G Λ) (D : Finset ↑Λ)
    (p q : ↑Λ)
    (hpar : ∀ v ∈ D, M.parity G Λ v
      = M.parityOn G Λ S v + (if v = p then (1 : ZMod 2) else 0))
    (hsub : ∀ v, M.parityOn G Λ S v ≠ 0 → v ∈ D)
    (hpD : p ∈ D) (hqD : q ∈ D)
    (hDsrc : ∀ v ∈ D, M.parity G Λ v ≠ 0 ↔ v = q) :
    M.sourcesOn G Λ S = ({q} : Finset ↑Λ) ∆ {p} := by
  ext v
  rw [Current.mem_sourcesOn_iff, Finset.mem_symmDiff, Finset.mem_singleton,
    Finset.mem_singleton]
  by_cases hvD : v ∈ D
  · -- On `D`: `parity M v = [v = q]` (unique source), so `parityOn = [v=q] + [v=p]`.
    have hq : M.parity G Λ v = (if v = q then (1 : ZMod 2) else 0) := by
      by_cases hvq : v = q
      · rw [if_pos hvq]
        have hne : M.parity G Λ v ≠ 0 := (hDsrc v hvD).mpr hvq
        revert hne; generalize M.parity G Λ v = a; revert a; decide
      · rw [if_neg hvq]
        by_contra h; exact hvq ((hDsrc v hvD).mp h)
    have key : M.parityOn G Λ S v
        = (if v = q then (1 : ZMod 2) else 0) - (if v = p then 1 else 0) := by
      rw [eq_sub_iff_add_eq, ← hpar v hvD]; exact hq
    rw [key]
    rcases eq_or_ne v q with hvq | hvq <;> rcases eq_or_ne v p with hvp | hvp <;>
      subst_vars <;> simp_all
  · -- Off `D`: restricted parity vanishes and `v ∉ {q} △ {p}` (both `p, q ∈ D`).
    have hpo : M.parityOn G Λ S v = 0 := by
      by_contra h; exact hvD (hsub v h)
    have hnq : v ≠ q := fun h => hvD (h ▸ hqD)
    have hnp : v ≠ p := fun h => hvD (h ▸ hpD)
    rw [hpo]
    simp [hnq, hnp]

set_option linter.unusedDecidableInType false in
/-- **D1a symmetric-difference source-set split of a pinned pivotal fiber**
(degeneracy-uniform Corollary D1a.5(b), F1 labelling `a ∈ C, b ∉ C`). This is the
**unconditional** source-set split: with `sources M = {x, y}`
but **no** nondegeneracy side conditions `x ≠ a`, `y ≠ b`, the interior/exterior
restricted source sets are the symmetric differences
`sourcesOn (interiorEdges C) M = {x} △ {a}` and
`sourcesOn (interiorEdges Cᶜ) M = {b} △ {y}`.
Here `x ∈ C` (reflexive reachability) and `y ∉ C` (the second `EdgePivotal` clause).
When `x ≠ a` this is the labelled pair `{x, a}`; the
degenerate branch `x = a` (a source coinciding with the near endpoint of the pivotal
bridge) gives `{x} △ {a} = ∅`, which is exactly what happens on the fiber when the
`e₀`-bump cancels `a`'s source parity — resolving the D1b nondegeneracy design
blocker (the even-cardinality handshake cannot rule out `x = a`, and does not need
to). Proof: `Current.sourcesOn_eq_symmDiff` applied to the interior block (`D = C`,
bridge `p = a`, source `q = x`) and the exterior block (`D = Cᶜ`, bridge `p = b`,
source `q = y`), using the D1a parity clauses
(`Current.parity_eq_parityOn_add_ite`) and the restricted-parity vanishing lemmas;
the exterior symmetric difference is normalised by `symmDiff_comm`. **D1b (the
product Fubini) and the SL-D₂ conditioned-switching core (Aizenman Lemma 4.1) are
follow-ups, the latter awaiting explicit user authorisation.** Tracked ingredient
(Group 1a), downstream: future Lemma 5.1 → `hLogLip` → lsc half of GJ Theorem
17.5.1 (§17.5, issue #4386 / thread #4418); weight source FV (3.45). -/
theorem Current.pivotalFiber_sourcesOn_symmDiff (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (e₀ : (inducedGraph G Λ).edgeSet) (M : Current G Λ) (x y a b : ↑Λ)
    (C : Finset ↑Λ) (hab : (e₀ : Sym2 ↑Λ) = s(a, b))
    (hpiv : Current.EdgePivotal G Λ e₀ M x y)
    (hC : Current.reachableCluster G Λ (M - Current.fromEdgeFinset G Λ {e₀}) x = C)
    (haC : a ∈ C) (hbC : b ∉ C)
    (hsrc : M.sources G Λ = {x, y}) :
    M.sourcesOn G Λ (Current.interiorEdges G Λ C) = ({x} : Finset ↑Λ) ∆ {a}
    ∧ M.sourcesOn G Λ (Current.interiorEdges G Λ Cᶜ) = ({b} : Finset ↑Λ) ∆ {y} := by
  -- `x ∈ C` (reflexive reachability) and `y ∉ C` (second `EdgePivotal` clause).
  have hxC : x ∈ C := by
    rw [← hC, Current.mem_reachableCluster_iff]
  have hyC : y ∉ C := by
    intro hy
    rw [← hC, Current.mem_reachableCluster_iff] at hy
    exact hpiv.2 hy
  -- The global source set is `{x, y}` (membership characterisation).
  have hsrc_iff : ∀ v, M.parity G Λ v ≠ 0 ↔ (v = x ∨ v = y) := by
    intro v
    rw [← Current.mem_sources_iff, hsrc, Finset.mem_insert, Finset.mem_singleton]
  -- Interior/exterior restricted parity clauses (D1a, F1 labelling).
  have hpar_int : ∀ v ∈ C, M.parity G Λ v
      = M.parityOn G Λ (Current.interiorEdges G Λ C) v + (if v = a then 1 else 0) := by
    intro v hv
    apply Current.parity_eq_parityOn_add_ite
    have h := Current.degreeAt_eq_degreeOn_interior_add_bridge_of_mem
      G Λ e₀ M x y a b C hab hpiv hC v hv
    have hvb : v ≠ b := fun h' => hbC (h' ▸ hv)
    rw [h, if_neg hvb]; ring
  have hpar_ext : ∀ v ∈ Cᶜ, M.parity G Λ v
      = M.parityOn G Λ (Current.interiorEdges G Λ Cᶜ) v + (if v = b then 1 else 0) := by
    intro v hv
    rw [Finset.mem_compl] at hv
    apply Current.parity_eq_parityOn_add_ite
    have h := Current.degreeAt_eq_degreeOn_exterior_add_bridge_of_not_mem
      G Λ e₀ M x y a b C hab hpiv hC v hv
    have hva : v ≠ a := by rintro rfl; exact hv haC
    rw [h, if_neg hva]; ring
  -- Restricted source sets sit inside their blocks.
  have hsub_int : ∀ v, M.parityOn G Λ (Current.interiorEdges G Λ C) v ≠ 0 → v ∈ C := by
    intro v hpo
    by_contra hvC
    apply hpo
    rw [Current.parityOn_eq_degreeOn,
      Current.degreeOn_interiorEdges_eq_zero_of_not_mem G Λ C M v hvC]
    simp
  have hsub_ext : ∀ v, M.parityOn G Λ (Current.interiorEdges G Λ Cᶜ) v ≠ 0 → v ∈ Cᶜ := by
    intro v hpo
    rw [Finset.mem_compl]
    intro hvC
    apply hpo
    rw [Current.parityOn_eq_degreeOn,
      Current.degreeOn_interiorEdges_compl_eq_zero_of_mem G Λ C M v hvC]
    simp
  -- Within each block, the unique global source.
  have hDsrc_int : ∀ v ∈ C, M.parity G Λ v ≠ 0 ↔ v = x := by
    intro v hvC
    rw [hsrc_iff v]
    constructor
    · rintro (h | rfl)
      · exact h
      · exact absurd hvC hyC
    · exact Or.inl
  have hDsrc_ext : ∀ v ∈ Cᶜ, M.parity G Λ v ≠ 0 ↔ v = y := by
    intro v hv
    rw [Finset.mem_compl] at hv
    rw [hsrc_iff v]
    constructor
    · rintro (rfl | h)
      · exact absurd hxC hv
      · exact h
    · exact Or.inr
  refine ⟨?_, ?_⟩
  · exact Current.sourcesOn_eq_symmDiff G Λ (Current.interiorEdges G Λ C) M C a x
      hpar_int hsub_int haC hxC hDsrc_int
  · rw [symmDiff_comm]
    exact Current.sourcesOn_eq_symmDiff G Λ (Current.interiorEdges G Λ Cᶜ) M Cᶜ b y
      hpar_ext hsub_ext (Finset.mem_compl.mpr hbC) (Finset.mem_compl.mpr hyC) hDsrc_ext

end Ambient

end IsingModel
