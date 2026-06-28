import IsingModel.Conditioning.CorrelationClosed.PairBound

/-!
# Sharp `tanh`-coefficient Simon-Lieb inequality (GJ §18 / FFS Ch 12)

The **sharp** edge form of the Simon-Lieb inequality for the two-point function at `h = 0`: for a
finite graph `G`, `0 ≤ β·J` and distinct `i ≠ j`,

`⟨σ_i σ_j⟩ ≤ tanh(βJ) · ∑_{e ∋ i} ⟨σ^{ {i,j} △ e} ⟩`.

This is **sharper** than the random-current edge form `correlation_inducedGraph_simon_lieb`
(coefficient `β·J ≥ tanh(βJ)`).  The key is to work at the **numerator** of the high-temperature
expansion closed form, `⟨σ_A⟩ = N(A)/Z`, where `N(A) = ∑_{X ⊆ E, ∂X = A} tanh^{|X|}` and `Z = N(∅)`
is a *shared* denominator.  In this subset (`0/1`-occupancy) representation each edge carries
exactly one factor of `tanh`, so peeling one edge `e = {i,u}` incident to `i` off each `X` with
`∂X = {i,j}` (every such `X` has `deg_X(i)` odd ≥ 1) lands in `N({i,j} △ e)` — an *elementary*
`Finset` injection, no random-current switching lemma.

This is **brick 1** of the sharp-decay programme (#4393): composing with the walk-sum geometric
decay (`tsum_walkSum_le_geometric`, #4394) and a cubic-exhaustion wrap yields the sharp lattice-mass
lower bound `latticeMass ≥ ofReal(−log(2d·tanh βJ))`, tightening the GJ §17.5 Lemma 17.5.2 sandwich
toward Theorem 17.5.1 continuity (#4386).

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §18.
* Fernández–Fröhlich–Sokal, *Random Walks…* (1992), Ch 12.
* Friedli–Velenik, *Statistical Mechanics of Lattice Systems* (2017), §3.7.3 eq. (3.46), p. 117.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The FV (3.46) **boundary filter**: subgraphs `X ⊆ E` whose odd-degree vertex set is exactly
`A` (`∀ v, deg_X(v) ≡ [v ∈ A] (mod 2)`). -/
private def htBoundaryFilter (G : SimpleGraph ι) [Fintype G.edgeSet] (A : Finset ι) :
    Finset (Finset (Sym2 ι)) :=
  G.edgeFinset.powerset.filter (fun X => ∀ v : ι,
    Even ((if v ∈ A then (1 : ℕ) else 0) + (X.filter (v ∈ ·)).card))

/-- The FV (3.46) **numerator** `N(A) = ∑_{X ⊆ E, ∂X = A} tanh(βJ)^{|X|}`. -/
private noncomputable def htNum (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℝ)
    (A : Finset ι) : ℝ :=
  ∑ X ∈ htBoundaryFilter G A, Real.tanh (β * J) ^ X.card

/-- The FV (3.46) **even-subgraph denominator** `Z = ∑_{X ⊆ E, ∂X = ∅} tanh(βJ)^{|X|}`. -/
private noncomputable def htDen (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℝ) : ℝ :=
  ∑ X ∈ G.edgeFinset.powerset.filter (fun X => ∀ v : ι, Even ((X.filter (v ∈ ·)).card)),
    Real.tanh (β * J) ^ X.card

/-- **Closed form in `N/Z` shape**: `⟨σ_A⟩ = N(A)/Z`. -/
private theorem correlation_eq_htNum_div (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℝ)
    (A : Finset ι) :
    correlation G ⟨J, 0, β⟩ A = htNum G J β A / htDen G J β := by
  rw [correlation_high_temp_expansion_h_zero_closed]
  rfl

/-- **Positivity of the even-subgraph denominator** `Z ≥ 1 > 0`. -/
private theorem htDen_pos (G : SimpleGraph ι) [Fintype G.edgeSet] {J β : ℝ}
    (hβJ : 0 ≤ β * J) : 0 < htDen G J β :=
  lt_of_lt_of_le zero_lt_one (one_le_sum_pow_tanh_even_subgraph G J β hβJ)

/-- **Erase-one-edge boundary law**: removing an edge `e ∈ X` flips parity at exactly its two
endpoints, so `∂(X ∖ e) = ∂X △ e`. -/
private theorem htBoundaryFilter_erase_mem (G : SimpleGraph ι) [Fintype G.edgeSet] {A : Finset ι}
    {X : Finset (Sym2 ι)} (hX : X ∈ htBoundaryFilter G A) {e : Sym2 ι} (heX : e ∈ X) :
    X.erase e ∈ htBoundaryFilter G (symmDiff A e.toFinset) := by
  classical
  rcases Finset.mem_filter.mp hX with ⟨hpow, hpar⟩
  refine Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr ((Finset.erase_subset _ _).trans (Finset.mem_powerset.mp hpow)),
      fun v => ?_⟩
  have hcard := filter_mem_card_erase X e heX v
  have hpv := hpar v
  rw [hcard] at hpv
  by_cases hA : v ∈ A <;> by_cases hE : v ∈ e
  · have hs : v ∉ symmDiff A e.toFinset := by
      rw [Finset.mem_symmDiff, Sym2.mem_toFinset]; tauto
    rw [if_pos hA, if_pos hE] at hpv
    rw [if_neg hs, Nat.even_iff] at *; omega
  · have hs : v ∈ symmDiff A e.toFinset := by
      rw [Finset.mem_symmDiff, Sym2.mem_toFinset]; tauto
    rw [if_pos hA, if_neg hE] at hpv
    rw [if_pos hs, Nat.even_iff] at *; omega
  · have hs : v ∈ symmDiff A e.toFinset := by
      rw [Finset.mem_symmDiff, Sym2.mem_toFinset]; tauto
    rw [if_neg hA, if_pos hE] at hpv
    rw [if_pos hs, Nat.even_iff] at *; omega
  · have hs : v ∉ symmDiff A e.toFinset := by
      rw [Finset.mem_symmDiff, Sym2.mem_toFinset]; tauto
    rw [if_neg hA, if_neg hE] at hpv
    rw [if_neg hs, Nat.even_iff] at *; omega

/-- **Sharp numerator peeling**: `N({i,j}) ≤ tanh(βJ) · ∑_{e ∋ i} N({i,j} △ e)`. -/
private theorem htNum_peel (G : SimpleGraph ι) [Fintype G.edgeSet] {J β : ℝ}
    (hβJ : 0 ≤ β * J) {i j : ι} :
    htNum G J β {i, j}
      ≤ Real.tanh (β * J) * ∑ e ∈ G.edgeFinset.filter (fun e => i ∈ e),
          htNum G J β (symmDiff {i, j} e.toFinset) := by
  classical
  have ht0 : 0 ≤ Real.tanh (β * J) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr hβJ) (Real.cosh_pos _).le
  -- chosen incident edge at `i` (junk `s(i,i)` off our filter, never used).
  set chosen : Finset (Sym2 ι) → Sym2 ι := fun X =>
    if h : (X.filter (fun e => i ∈ e)).Nonempty then h.choose else s(i, i) with hchosen
  have hchosen_mem : ∀ X ∈ htBoundaryFilter G ({i, j} : Finset ι), chosen X ∈ X ∧ i ∈ chosen X := by
    intro X hX
    have hne : (X.filter (fun e => i ∈ e)).Nonempty := by
      obtain ⟨e, heX, hie⟩ := evenSubgraph_pair_boundary_exists_edge_incident_to G i j X hX
      exact ⟨e, Finset.mem_filter.mpr ⟨heX, hie⟩⟩
    have hspec := hne.choose_spec
    rw [hchosen]; dsimp only; rw [dif_pos hne]
    rcases Finset.mem_filter.mp hspec with ⟨h1, h2⟩
    exact ⟨h1, h2⟩
  set Ei : Finset (Sym2 ι) := G.edgeFinset.filter (fun e => i ∈ e) with hEi
  set m : Finset (Sym2 ι) → (Σ _ : Sym2 ι, Finset (Sym2 ι)) :=
    fun X => ⟨chosen X, X.erase (chosen X)⟩ with hm
  set S : Finset (Σ _ : Sym2 ι, Finset (Sym2 ι)) :=
    Ei.sigma (fun e => htBoundaryFilter G (symmDiff {i, j} e.toFinset)) with hS
  set v : (Σ _ : Sym2 ι, Finset (Sym2 ι)) → ℝ :=
    fun p => Real.tanh (β * J) ^ (p.2.card + 1) with hv
  have hmaps : ∀ X ∈ htBoundaryFilter G ({i, j} : Finset ι), m X ∈ S := by
    intro X hX
    obtain ⟨hcX, hciX⟩ := hchosen_mem X hX
    have hce : chosen X ∈ G.edgeFinset := (Finset.mem_powerset.mp (Finset.mem_filter.mp hX).1) hcX
    refine Finset.mem_sigma.mpr ⟨Finset.mem_filter.mpr ⟨hce, hciX⟩, ?_⟩
    exact htBoundaryFilter_erase_mem G hX hcX
  have hweight : ∀ X ∈ htBoundaryFilter G ({i, j} : Finset ι),
      Real.tanh (β * J) ^ X.card = v (m X) := by
    intro X hX
    obtain ⟨hcX, _⟩ := hchosen_mem X hX
    rw [hv, hm]; dsimp only
    rw [Finset.card_erase_of_mem hcX]
    have hpos : 0 < X.card := Finset.card_pos.mpr ⟨chosen X, hcX⟩
    congr 1; omega
  have hinj : ∀ X ∈ htBoundaryFilter G ({i, j} : Finset ι),
      ∀ Y ∈ htBoundaryFilter G ({i, j} : Finset ι), m X = m Y → X = Y := by
    intro X hX Y hY hxy
    obtain ⟨hcX, _⟩ := hchosen_mem X hX
    obtain ⟨hcY, _⟩ := hchosen_mem Y hY
    rw [hm] at hxy; dsimp only at hxy
    rw [Sigma.mk.injEq] at hxy
    obtain ⟨h1, h2⟩ := hxy
    have h2' : X.erase (chosen X) = Y.erase (chosen Y) := eq_of_heq h2
    calc X = insert (chosen X) (X.erase (chosen X)) := (Finset.insert_erase hcX).symm
      _ = insert (chosen Y) (Y.erase (chosen Y)) := by rw [h2', h1]
      _ = Y := Finset.insert_erase hcY
  have hstep1 : htNum G J β ({i, j} : Finset ι)
      = ∑ p ∈ (htBoundaryFilter G ({i, j} : Finset ι)).image m, v p := by
    rw [htNum, Finset.sum_congr rfl hweight, ← Finset.sum_image hinj]
  have hsub : (htBoundaryFilter G ({i, j} : Finset ι)).image m ⊆ S := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨X, hX, rfl⟩
    exact hmaps X hX
  have hstep2 : ∑ p ∈ (htBoundaryFilter G ({i, j} : Finset ι)).image m, v p ≤ ∑ p ∈ S, v p :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun p _ _ => by rw [hv]; exact pow_nonneg ht0 _)
  have hstep3 : ∑ p ∈ S, v p
      = Real.tanh (β * J) * ∑ e ∈ Ei, htNum G J β (symmDiff {i, j} e.toFinset) := by
    have h1 : ∑ p ∈ S, v p
        = ∑ e ∈ Ei, Real.tanh (β * J) * htNum G J β (symmDiff {i, j} e.toFinset) := by
      rw [hS, Finset.sum_sigma]
      refine Finset.sum_congr rfl (fun e _ => ?_)
      rw [htNum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun Y _ => ?_)
      simp only [hv]; ring
    rw [h1]
    exact (Finset.mul_sum _ _ _).symm
  rw [hstep1]
  exact hstep2.trans (le_of_eq hstep3)

/-- **Sharp `tanh`-coefficient Simon-Lieb edge inequality** (GJ §18 / FFS Ch 12): for a finite graph
`G`, `0 ≤ β·J`, and distinct `i ≠ j`,
`⟨σ_iσ_j⟩ ≤ tanh(βJ) · ∑_{e ∋ i} ⟨σ^{ {i,j} △ e }⟩`.

Sharper than the random-current `correlation_inducedGraph_simon_lieb` (coefficient `β·J ≥ tanh βJ`).
Proof: both sides are `(·)/Z` over the shared even-subgraph denominator `Z > 0`
(`correlation_eq_htNum_div`); cancel `Z` and apply the sharp numerator peeling `htNum_peel`. -/
theorem correlation_simon_lieb_sharp (G : SimpleGraph ι) [Fintype G.edgeSet] {J β : ℝ}
    (hβJ : 0 ≤ β * J) {i j : ι} :
    correlation G ⟨J, 0, β⟩ ({i, j} : Finset ι)
      ≤ Real.tanh (β * J) * ∑ e ∈ G.edgeFinset.filter (fun e => i ∈ e),
          correlation G ⟨J, 0, β⟩ (symmDiff {i, j} e.toFinset) := by
  classical
  have hZ : 0 < htDen G J β := htDen_pos G hβJ
  have hpeel := htNum_peel G hβJ (i := i) (j := j)
  rw [correlation_eq_htNum_div]
  have hrhs : (∑ e ∈ G.edgeFinset.filter (fun e => i ∈ e),
        correlation G ⟨J, 0, β⟩ (symmDiff {i, j} e.toFinset))
      = (∑ e ∈ G.edgeFinset.filter (fun e => i ∈ e),
          htNum G J β (symmDiff {i, j} e.toFinset)) / htDen G J β := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun e _ => correlation_eq_htNum_div G J β _)
  rw [hrhs, ← mul_div_assoc]
  exact (div_le_div_iff_of_pos_right hZ).mpr hpeel

end IsingModel
