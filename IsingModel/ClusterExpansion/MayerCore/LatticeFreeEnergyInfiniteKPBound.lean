import IsingModel.ClusterExpansion.MayerCore.LatticeFreeEnergyKPBound
import IsingModel.Concrete.CubicFreeEnergy
import IsingModel.Concrete.LatticeGraphBED.NeighborDegree

/-!
# Infinite-volume real-axis KP bound on the lattice free energy (GJ §18.6)

This is PR-D2.1 of issue #4149 (§18.6).  It passes the **volume-uniform finite-volume**
Kotecky--Preiss free-energy deviation bound `latticeGraph_freeEnergy_deviation_le_kpBound`
(#4153) to the cubic thermodynamic limit, obtaining the infinite-volume deviation bound for the
free-energy density `Ambient.freeEnergyInfinite (latticeGraph d) (Ambient.cubicExhaustion d)`.

The limit has two ingredients:

* the **cubic edge-density limit** `tendsto_inducedLatticeGraph_cubicBox_edgeDensity`, which shows
  the per-site edge count `|E_n| / |B_n|` of the induced lattice graph on the stage-`n` cube
  tends to `d` (the bulk coordination half-degree).  This is proven by squeezing the edge density
  between the interior-degree lower bound `d · |B_{n-1}| / |B_n|` and the handshake upper bound
  `d`; both bounds tend to `d` since `|B_{n-1}| / |B_n| → 1`;
* the **cubic free-energy convergence**
  `freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_tendsto` (GJ Prop. 4.6.1 on the cubic
  exhaustion), which gives convergence of the finite-volume free energies to `freeEnergyInfinite`.

Combining these by `Filter.Tendsto.sub`, the deviation sequence
`f_n − (log 2 + (|E_n|/|B_n|)·log cosh βJ)` converges to
`freeEnergyInfinite − (log 2 + d·log cosh βJ)`.  Each term of the deviation sequence is bounded
absolute value by `kpBound (2d) (tanh βJ)` (#4153), so `le_of_tendsto` of the continuous absolute
value transfers the bound to the limit.

## References

* Glimm--Jaffe, *Quantum Physics*, 2nd ed., §18.5--§18.6, pp.~335--340.
* Friedli--Velenik, *Statistical Mechanics of Lattice Systems*, §5.4
  (Theorem 5.4, the Kotecky--Preiss criterion).
-/

namespace IsingModel

open Finset Ambient

/-! ## Part 1 — the cubic edge-density limit -/

/-- **Interior vertices of the cubic box have full coordination degree `2d`**.  If a vertex
`v : ↑(cubicBox d n)` of the induced lattice graph satisfies `v.val ∈ cubicBox d m` for some
`m + 1 ≤ n` (so `v` is in the strict interior, away from the boundary face), then all of its
`2d` lattice neighbours `v ± e_j` stay inside `cubicBox d n` and are genuinely adjacent, so the
induced-graph degree is exactly `2 * d`.

We prove the harder `2 * d ≤ degree` direction here (the matching `degree ≤ 2 * d` is
`inducedLatticeGraph_degree_le`).  An injective `Fin d × Bool`-indexed family of the `2d`
candidate neighbours embeds into `neighborFinset v` via `Subtype.val`, so its image cardinality
`2 * d` lower-bounds the degree. -/
theorem inducedLatticeGraph_cubicBox_interior_degree_eq
    (d : ℕ) {n m : ℕ} (hmn : m + 1 ≤ n) (v : ↑(cubicBox d n))
    (hint : v.val ∈ cubicBox d m) :
    (Ambient.inducedGraph (latticeGraph d) (cubicBox d n)).degree v = 2 * d := by
  classical
  set G := Ambient.inducedGraph (latticeGraph d) (cubicBox d n) with hG
  -- Upper bound is the existing degree bound.
  refine le_antisymm (inducedLatticeGraph_degree_le d (cubicBox d n) v) ?_
  -- Lower bound `2 * d ≤ degree v`: embed `Fin d × Bool` into the neighbours.
  -- Candidate neighbour for `(i, b)`: perturb coordinate `i` of `v` by `±1`.
  let g : Fin d × Bool → (Fin d → ℤ) :=
    fun p => Function.update v.val p.1 (v.val p.1 + (if p.2 then 1 else -1))
  -- Pointwise unfolding of `g`.
  have hg_app : ∀ p : Fin d × Bool,
      g p = Function.update v.val p.1 (v.val p.1 + (if p.2 then 1 else -1)) := fun _ => rfl
  -- Each candidate lies in `cubicBox d n` (interior coords stay in `[-n, n]`).
  have hmem : ∀ p : Fin d × Bool, g p ∈ cubicBox d n := by
    intro p
    rw [mem_cubicBox] at hint ⊢
    intro j
    rw [hg_app]
    by_cases hj : j = p.1
    · subst hj
      simp only [Function.update_self]
      have hmj := hint p.1
      have hmn' : (m : ℤ) + 1 ≤ (n : ℤ) := by exact_mod_cast hmn
      cases p.2 with
      | false => simp only [Bool.false_eq_true, if_false]; obtain ⟨h1, h2⟩ := hmj; omega
      | true => simp only [if_true]; obtain ⟨h1, h2⟩ := hmj; omega
    · rw [Function.update_of_ne hj]
      have hint' := hint j
      have hmn' : (m : ℤ) ≤ (n : ℤ) := by exact_mod_cast (Nat.le_of_succ_le hmn)
      obtain ⟨h1, h2⟩ := hint'; omega
  -- Each candidate is genuinely adjacent to `v` in `latticeGraph d`.
  have hadj : ∀ p : Fin d × Bool, (latticeGraph d).Adj v.val (g p) := by
    intro p
    change (∑ i : Fin d, |v.val i - g p i|) = 1
    rw [Finset.sum_eq_single p.1]
    · rw [hg_app]
      simp only [Function.update_self]
      cases p.2 with
      | false =>
          simp only [Bool.false_eq_true, if_false]
          rw [show v.val p.1 - (v.val p.1 + -1) = 1 by ring]; rfl
      | true =>
          simp only [if_true]
          rw [show v.val p.1 - (v.val p.1 + 1) = -1 by ring]; rfl
    · intro j _ hj
      rw [hg_app, Function.update_of_ne hj]
      simp
    · intro hp; exact absurd (Finset.mem_univ p.1) hp
  -- Promote candidates to subtype neighbours of `v`.
  let f : Fin d × Bool → ↑(cubicBox d n) := fun p => ⟨g p, hmem p⟩
  have hf_app : ∀ p : Fin d × Bool, (f p).val = g p := fun _ => rfl
  have hmaps : Set.MapsTo f (↑(Finset.univ : Finset (Fin d × Bool)))
      (↑(G.neighborFinset v) : Set _) := by
    intro p _
    rw [Finset.mem_coe, SimpleGraph.mem_neighborFinset, hG]
    show (Ambient.inducedGraph (latticeGraph d) (cubicBox d n)).Adj v (f p)
    rw [Ambient.inducedGraph, SimpleGraph.induce_adj]
    exact hadj p
  -- The candidate family is injective on `Fin d × Bool`.
  have hinj : Set.InjOn f (↑(Finset.univ : Finset (Fin d × Bool))) := by
    intro p _ q _ hpq
    have hval : g p = g q := by rw [← hf_app p, ← hf_app q, hpq]
    by_contra hne
    -- Either the coordinates differ or the signs differ; both give a contradiction.
    by_cases hcoord : p.1 = q.1
    · -- Same coordinate, so the signs must differ.
      have hbool : p.2 ≠ q.2 := by
        intro hb; exact hne (Prod.ext hcoord hb)
      have hpc := congrFun hval p.1
      have hgpp : g p p.1 = v.val p.1 + (if p.2 then 1 else -1) := by
        rw [hg_app, Function.update_self]
      have hgqp : g q p.1 = v.val q.1 + (if q.2 then 1 else -1) := by
        rw [hg_app, hcoord, Function.update_self]
      have hveq : v.val p.1 = v.val q.1 := by rw [hcoord]
      rw [hgpp, hgqp, hveq] at hpc
      -- `v p.1 + s_p = v p.1 + s_q` with `s_p = ±1` and `s_p ≠ s_q` is impossible.
      have hsgn : (if p.2 then (1 : ℤ) else -1) = (if q.2 then (1 : ℤ) else -1) := by
        have := hpc; linarith
      rcases Bool.eq_false_or_eq_true p.2 with hp2 | hp2 <;>
        rcases Bool.eq_false_or_eq_true q.2 with hq2 | hq2
      · exact hbool (by rw [hp2, hq2])
      · rw [hp2, hq2] at hsgn; norm_num at hsgn
      · rw [hp2, hq2] at hsgn; norm_num at hsgn
      · exact hbool (by rw [hp2, hq2])
    · -- Different coordinates: evaluate at `q.1`, where `g p` agrees with `v` but `g q` does not.
      have hgpq1 : g p q.1 = v.val q.1 := by
        rw [hg_app, Function.update_of_ne (Ne.symm hcoord)]
      have hgqq1 : g q q.1 = v.val q.1 + (if q.2 then 1 else -1) := by
        rw [hg_app, Function.update_self]
      have hqc := congrFun hval q.1
      rw [hgpq1, hgqq1] at hqc
      -- `v q.1 = v q.1 + (±1)` is impossible.
      have hsgn : (if q.2 then (1 : ℤ) else -1) = 0 := by linarith
      rcases Bool.eq_false_or_eq_true q.2 with hq2 | hq2 <;>
        · rw [hq2] at hsgn; norm_num at hsgn
  -- Conclude: `2 * d = |univ| ≤ |neighborFinset v| = degree v`.
  calc 2 * d = Fintype.card (Fin d × Bool) := by
            simp [Fintype.card_prod, Fintype.card_fin, mul_comm]
    _ = (Finset.univ : Finset (Fin d × Bool)).card := (Finset.card_univ).symm
    _ ≤ (G.neighborFinset v).card := Finset.card_le_card_of_injOn f hmaps hinj
    _ = G.degree v := SimpleGraph.card_neighborFinset_eq_degree _ _

/-- **Interior lower bound on the cubic edge count**: at stage `n + 1`, the number of edges of
the induced lattice graph satisfies `2 * |E_{n+1}| ≥ 2 d · |B_n|`, since the `|B_n|` interior
vertices each contribute full degree `2d` to the handshake sum `∑_v deg_v = 2 |E|`. -/
theorem inducedLatticeGraph_cubicBox_card_edgeFinset_ge (d n : ℕ) :
    2 * d * (cubicBox d n).card
      ≤ 2 * (Ambient.inducedGraph (latticeGraph d) (cubicBox d (n + 1))).edgeFinset.card := by
  classical
  set G := Ambient.inducedGraph (latticeGraph d) (cubicBox d (n + 1)) with hG
  -- The interior `cubicBox d n` injects into `↑(cubicBox d (n+1))`.
  have hsub : cubicBox d n ⊆ cubicBox d (n + 1) := cubicBox_mono d (Nat.le_succ n)
  -- Each interior vertex (those in `cubicBox d n`) has degree exactly `2d`.
  have hdeg : ∀ v : ↑(cubicBox d (n + 1)), v.val ∈ cubicBox d n → G.degree v = 2 * d := by
    intro v hv
    exact inducedLatticeGraph_cubicBox_interior_degree_eq d (le_refl (n + 1)) v hv
  -- Handshake: `2|E| = ∑ deg`.
  have hhand : 2 * G.edgeFinset.card = ∑ v : ↑(cubicBox d (n + 1)), G.degree v := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges]
  -- The interior subtype set `S` of `↑(cubicBox d (n+1))`.
  set S : Finset (↑(cubicBox d (n + 1))) :=
    Finset.univ.filter (fun v => v.val ∈ cubicBox d n) with hS
  have hScard : S.card = (cubicBox d n).card := by
    -- `S.image Subtype.val = cubicBox d n`, and `Subtype.val` is injective on `S`.
    have hinjval : Set.InjOn (Subtype.val : ↑(cubicBox d (n + 1)) → (Fin d → ℤ)) (↑S) :=
      fun a _ b _ hab => Subtype.ext hab
    have himg : S.image Subtype.val = cubicBox d n := by
      apply Finset.ext
      intro x
      rw [Finset.mem_image]
      constructor
      · rintro ⟨w, hw, rfl⟩
        rw [hS, Finset.mem_filter] at hw
        exact hw.2
      · intro hx
        refine ⟨⟨x, hsub hx⟩, ?_, rfl⟩
        rw [hS, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hx⟩
    calc S.card = (S.image Subtype.val).card := (Finset.card_image_of_injOn hinjval).symm
      _ = (cubicBox d n).card := by rw [himg]
  -- Lower-bound the handshake sum by the interior contribution.
  calc 2 * d * (cubicBox d n).card
      = ∑ _v ∈ S, (2 * d) := by rw [Finset.sum_const, hScard, smul_eq_mul, mul_comm]
    _ = ∑ v ∈ S, G.degree v := by
        refine Finset.sum_congr rfl ?_
        intro v hv
        rw [hS, Finset.mem_filter] at hv
        rw [hdeg v hv.2]
    _ ≤ ∑ v : ↑(cubicBox d (n + 1)), G.degree v :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ S)
    _ = 2 * G.edgeFinset.card := hhand.symm

/-- **Edge density `|E_n| / |B_n|` tends to `d`** for the cubic exhaustion of `ℤ^d`.  The density
is squeezed between the interior lower bound `d · |B_{n-1}| / |B_n|` and the handshake upper bound
`d`.  The ratio `|B_{n-1}| / |B_n| = (2n-1)^d / (2n+1)^d → 1`, so both bounds tend to `d`. -/
theorem tendsto_inducedLatticeGraph_cubicBox_edgeDensity (d : ℕ) :
    Filter.Tendsto
      (fun n : ℕ => ((Ambient.inducedGraph (latticeGraph d) (cubicBox d n)).edgeFinset.card : ℝ)
        / ((cubicBox d n).card : ℝ))
      Filter.atTop (nhds (d : ℝ)) := by
  -- Upper-bound sequence: constant `d`.
  -- Lower-bound sequence: `d · |B_{n-1}| / |B_n|`, written at the shifted index `n+1`.
  -- We use the squeeze lemma on `atTop`; both bounds tend to `d`.
  have hcardpos : ∀ n : ℕ, (0 : ℝ) < ((cubicBox d n).card : ℝ) := by
    intro n; rw [card_cubicBox]; positivity
  -- The ratio `|B_n| / |B_{n+1}| → 1`.
  have hratio : Filter.Tendsto
      (fun n : ℕ => ((cubicBox d n).card : ℝ) / ((cubicBox d (n + 1)).card : ℝ))
      Filter.atTop (nhds 1) := by
    have hbase : Filter.Tendsto
        (fun n : ℕ => ((2 * n + 1 : ℕ) : ℝ) / ((2 * (n + 1) + 1 : ℕ) : ℝ))
        Filter.atTop (nhds 1) := by
      have hden : Filter.Tendsto (fun n : ℕ => ((2 * (n + 1) + 1 : ℕ) : ℝ)) Filter.atTop
          Filter.atTop := by
        apply Filter.tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
        push_cast; linarith
      have hlow : Filter.Tendsto (fun n : ℕ => 1 - (2 : ℝ) / ((2 * (n + 1) + 1 : ℕ) : ℝ))
          Filter.atTop (nhds 1) := by
        have h0 : Filter.Tendsto (fun n : ℕ => (2 : ℝ) / ((2 * (n + 1) + 1 : ℕ) : ℝ))
            Filter.atTop (nhds 0) :=
          Filter.Tendsto.div_atTop tendsto_const_nhds hden
        simpa using tendsto_const_nhds.sub h0
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
      · filter_upwards with n
        have hpos : (0 : ℝ) < ((2 * (n + 1) + 1 : ℕ) : ℝ) := by positivity
        rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hpos]
        push_cast; nlinarith [hpos]
      · filter_upwards with n
        have hpos : (0 : ℝ) < ((2 * (n + 1) + 1 : ℕ) : ℝ) := by positivity
        rw [div_le_one hpos]; push_cast; linarith
    have hpow := hbase.pow d
    rw [one_pow] at hpow
    refine hpow.congr (fun n => ?_)
    rw [card_cubicBox, card_cubicBox]; push_cast; rw [div_pow]
  -- Lower-bound sequence at shifted index: `d · |B_n| / |B_{n+1}|`.
  have hlowtend : Filter.Tendsto
      (fun n : ℕ => (d : ℝ) * (((cubicBox d n).card : ℝ) / ((cubicBox d (n + 1)).card : ℝ)))
      Filter.atTop (nhds (d : ℝ)) := by
    have := hratio.const_mul (d : ℝ)
    simpa using this
  -- The lower bound holds: density at `n+1` is `≥ d · |B_n| / |B_{n+1}|`.
  have hge : ∀ n : ℕ,
      (d : ℝ) * (((cubicBox d n).card : ℝ) / ((cubicBox d (n + 1)).card : ℝ))
        ≤ ((Ambient.inducedGraph (latticeGraph d) (cubicBox d (n + 1))).edgeFinset.card : ℝ)
            / ((cubicBox d (n + 1)).card : ℝ) := by
    intro n
    have hposN1 : (0 : ℝ) < ((cubicBox d (n + 1)).card : ℝ) := hcardpos (n + 1)
    rw [mul_div_assoc' (d : ℝ), div_le_div_iff_of_pos_right hposN1]
    have hint := inducedLatticeGraph_cubicBox_card_edgeFinset_ge d n
    have hcast : (2 : ℝ) * d * ((cubicBox d n).card : ℝ)
        ≤ 2 * ((Ambient.inducedGraph (latticeGraph d)
            (cubicBox d (n + 1))).edgeFinset.card : ℝ) := by
      have := (Nat.cast_le (α := ℝ)).mpr hint
      push_cast at this ⊢; linarith
    linarith
  -- The upper bound holds: density `≤ d` for every `n`.
  have hle : ∀ n : ℕ,
      ((Ambient.inducedGraph (latticeGraph d) (cubicBox d n)).edgeFinset.card : ℝ)
          / ((cubicBox d n).card : ℝ)
        ≤ (d : ℝ) := by
    intro n
    have hposN : (0 : ℝ) < ((cubicBox d n).card : ℝ) := hcardpos n
    rw [div_le_iff₀ hposN]
    have hub := inducedLatticeGraph_card_edgeFinset_le d (cubicBox d n)
    rw [Fintype.card_coe] at hub
    linarith
  -- Apply the squeeze at the shifted index `n + 1`, then shift back.
  have hshift : Filter.Tendsto
      (fun n : ℕ => ((Ambient.inducedGraph (latticeGraph d)
            (cubicBox d (n + 1))).edgeFinset.card : ℝ)
        / ((cubicBox d (n + 1)).card : ℝ))
      Filter.atTop (nhds (d : ℝ)) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlowtend tendsto_const_nhds ?_ ?_
    · filter_upwards with n; exact hge n
    · filter_upwards with n; exact hle (n + 1)
  -- Shift the index back: `f (n+1) → L` and `f` defined for all `n` ⇒ `f n → L`.
  exact (Filter.tendsto_add_atTop_iff_nat 1).mp hshift

/-! ## Part 2 — pass the finite-volume KP bound to the limit -/

/-- **Infinite-volume real-axis KP free-energy deviation bound on the lattice** (GJ §18.6).  For
the cubic exhaustion of `ℤ^d`, at zero external field with ferromagnetic coupling `0 ≤ J` and
inverse temperature `0 < β`, the deviation of the **infinite-volume** free-energy density
`Ambient.freeEnergyInfinite (latticeGraph d) (Ambient.cubicExhaustion d)` from its explicit
`log 2 + d · log cosh(βJ)` bulk part is bounded by `kpBound (2 d) (tanh βJ)`, the same constant
that bounds every finite volume (#4153).

The Kotecky--Preiss hypotheses are stated at a volume-uniform radius `T` with `tanh(βJ) < T`:
`(2d)²·e·T < 1` and `4·(2d)²eT/(1−(2d)²eT)² < 1`.

Proof: the finite-volume bound (#4153) applies to every cubic box `cubicBox d n` (nonempty since
`0 ∈ cubicBox d n`), so the deviation sequence
`f_n − (log 2 + (|E_n|/|B_n|)·log cosh βJ)` is bounded by `kpBound (2 d) (tanh βJ)` for all
`n`.
The free energies `f_n` converge to `freeEnergyInfinite` (GJ Prop. 4.6.1 on the cube), and the
edge densities `|E_n|/|B_n|` converge to `d` (`tendsto_inducedLatticeGraph_cubicBox_edgeDensity`),
so the deviation sequence converges to `freeEnergyInfinite − (log 2 + d·log cosh βJ)`.  The
continuous absolute value and `le_of_tendsto` transfer the uniform bound to the limit. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_deviation_le_kpBound
    (d : ℕ) {J β T : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (hT : 0 < T)
    (hkp2dT : ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T) < 1)
    (hρ2dT : 4 * (((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T))
        / (1 - ((2 * d : ℕ) : ℝ) ^ 2 * (Real.exp 1 * T)) ^ 2 < 1)
    (htanh : Real.tanh (β * J) < T) :
    |Ambient.freeEnergyInfinite (latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ)
      - (Real.log 2 + (d : ℝ) * Real.log (Real.cosh (β * J)))|
      ≤ kpBound (2 * d) (Real.tanh (β * J)) := by
  classical
  set p : IsingParams ℝ := ⟨J, 0, β⟩ with hp
  have hf : Ferromagnetic p := ⟨hJ, le_refl 0, hβ⟩
  -- The deviation sequence.
  set logcosh : ℝ := Real.log (Real.cosh (β * J)) with hlogcosh
  set dev : ℕ → ℝ := fun n =>
    Ambient.freeEnergyAlongExhaustion (latticeGraph d) (Ambient.cubicExhaustion d) p n
      - (Real.log 2
          + ((Ambient.inducedGraph (latticeGraph d) (cubicBox d n)).edgeFinset.card : ℝ)
              / ((cubicBox d n).card : ℝ) * logcosh) with hdev
  -- STEP 1: each deviation term is bounded by `kpBound (2d) (tanh βJ)`.
  have hbound : ∀ n : ℕ, |dev n| ≤ kpBound (2 * d) (Real.tanh (β * J)) := by
    intro n
    have hne : Nonempty (↑(cubicBox d n) : Type _) :=
      (cubicBox_nonempty d n).to_subtype
    have hstage := latticeGraph_freeEnergy_deviation_le_kpBound d (cubicBox d n) hJ hβ hT
      hkp2dT hρ2dT htanh
    -- Rewrite `freeEnergyΛ`/`Fintype.card` into the `dev` form.
    rw [hdev]
    simp only
    rw [Ambient.freeEnergyAlongExhaustion_apply]
    rw [show (Ambient.cubicExhaustion d).volume n = cubicBox d n from rfl]
    rw [Ambient.freeEnergyΛ_apply]
    rw [Fintype.card_coe] at hstage
    exact hstage
  -- STEP 2: the deviation sequence converges.
  -- `f_n → freeEnergyInfinite`.
  have hfe := freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_tendsto d p hf
  -- `|E_n|/|B_n| → d`.
  have hed := tendsto_inducedLatticeGraph_cubicBox_edgeDensity d
  -- `log 2 + (|E_n|/|B_n|)·logcosh → log 2 + d·logcosh`.
  have hbulk : Filter.Tendsto
      (fun n : ℕ => Real.log 2
        + ((Ambient.inducedGraph (latticeGraph d) (cubicBox d n)).edgeFinset.card : ℝ)
            / ((cubicBox d n).card : ℝ) * logcosh)
      Filter.atTop (nhds (Real.log 2 + (d : ℝ) * logcosh)) :=
    Filter.Tendsto.const_add _ (hed.mul_const logcosh)
  -- Combine: `dev n → freeEnergyInfinite − (log 2 + d·logcosh)`.
  have hdevtend : Filter.Tendsto dev Filter.atTop
      (nhds (Ambient.freeEnergyInfinite (latticeGraph d) (Ambient.cubicExhaustion d) p
        - (Real.log 2 + (d : ℝ) * logcosh))) := by
    rw [hdev]
    exact hfe.sub hbulk
  -- STEP 3: transfer the bound to the limit via the continuous absolute value.
  have habstend : Filter.Tendsto (fun n => |dev n|) Filter.atTop
      (nhds |Ambient.freeEnergyInfinite (latticeGraph d) (Ambient.cubicExhaustion d) p
        - (Real.log 2 + (d : ℝ) * logcosh)|) :=
    (continuous_abs.tendsto _).comp hdevtend
  have hlimle : |Ambient.freeEnergyInfinite (latticeGraph d) (Ambient.cubicExhaustion d) p
        - (Real.log 2 + (d : ℝ) * logcosh)|
      ≤ kpBound (2 * d) (Real.tanh (β * J)) :=
    le_of_tendsto habstend (Filter.Eventually.of_forall hbound)
  -- Conclude, unfolding `p` and `logcosh`.
  rw [hp, hlogcosh] at hlimle
  exact hlimle

end IsingModel
