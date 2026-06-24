import IsingModel.ComplexAnalyticity.VitaliPorter.PerCompact
import IsingModel.ComplexAnalyticity.VitaliPorter.Exhaustion

/-!
# Vitali–Porter: Montel diagonal extraction

Building block toward eliminating the declared scope-excluded axiom
`vitaliPorter_tendstoLocallyUniformlyOn` (Issue #4280). Assembling the per-compact Arzelà–Ascoli
extraction (`PerCompact.lean`) over a compact exhaustion (`Exhaustion.lean`) by a diagonal argument
gives the full **Montel** theorem: a locally uniformly bounded family of holomorphic functions on an
open `U ⊆ ℂ` has a subsequence converging **locally uniformly on `U`** to a holomorphic limit.

The headline `exists_subseq_tendstoLocallyUniformlyOn_of_locallyBounded` is the **complex Montel
theorem**: a locally uniformly bounded family of holomorphic functions on an open `U ⊆ ℂ` has a
subsequence converging locally uniformly on `U` to a holomorphic limit. It is built from the
uniform-bound-on-compacts helper `exists_bound_on_compact_of_locallyBounded`, the per-compact
Arzelà–Ascoli extraction, and a `VitaliDiagState` diagonal recursion over the exhaustion. The
remaining step toward `vitaliPorter_tendstoLocallyUniformlyOn` is the Vitali uniqueness upgrade
(whole sequence converges, via the identity-theorem core in `Uniqueness.lean`).

**Reference:** Conway, *Functions of One Complex Variable I*, VII §2 (Montel / normal families). -/

namespace IsingModel
namespace FunctionTheory

open Filter Topology Metric Set

/-- **Per-level cumulative-extractor data for the Montel diagonal** (auxiliary).

At level `m`, `φ` is the cumulative subsequence (`φ = (previous φ) ∘ ρ`, with `ρ` the relative
extractor produced by the per-compact Arzelà–Ascoli step on `K m`), and `F ∘ φ` converges uniformly
on `K m` to `g`. Keeping `ρ` as a field lets the chain relation `φ (m+1) = φ m ∘ ρ (m+1)` be
definitional. -/
structure VitaliDiagState (F : ℕ → ℂ → ℂ) (K : ℕ → Set ℂ) (m : ℕ) : Type where
  /-- Cumulative extractor through level `m`. -/
  φ : ℕ → ℕ
  /-- The cumulative extractor is strictly monotone. -/
  hφ : StrictMono φ
  /-- Relative extractor producing this level from the previous one. -/
  ρ : ℕ → ℕ
  /-- The relative extractor is strictly monotone. -/
  hρ : StrictMono ρ
  /-- The level-`m` uniform limit. -/
  g : ℂ → ℂ
  /-- `F ∘ φ` converges uniformly on `K m`. -/
  hconv : TendstoUniformlyOn (fun k => F (φ k)) g atTop (K m)

/-- **A locally uniformly bounded family is uniformly bounded on each compact subset**.

From the local-boundedness data (each point of `U` has a ball on which the whole family is bounded)
and compactness of `K ⊆ U`, a finite subcover yields a single bound `M` valid for all `n` and all
`z ∈ K`. -/
theorem exists_bound_on_compact_of_locallyBounded
    {U : Set ℂ} {F : ℕ → ℂ → ℂ}
    (hbdd : ∀ z ∈ U, ∃ r M : ℝ, 0 < r ∧ ball z r ⊆ U ∧
      ∀ n, ∀ w ∈ ball z r, ‖F n w‖ ≤ M)
    {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ M : ℝ, ∀ n, ∀ z ∈ K, ‖F n z‖ ≤ M := by
  classical
  -- Per-point ball radius and bound.
  choose! r M hr hball hbound using hbdd
  -- Open cover of `K` by the balls `ball ↑z (r ↑z)`, indexed by `z : ↥K`.
  have hcover : K ⊆ ⋃ z : K, ball (↑z) (r ↑z) := by
    intro z hz
    exact mem_iUnion.mpr ⟨⟨z, hz⟩, mem_ball_self (hr z (hKU hz))⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun z : K => ball (↑z) (r ↑z))
    (fun _ => isOpen_ball) hcover
  rcases t.eq_empty_or_nonempty with rfl | htne
  · -- empty subcover forces `K = ∅`; any bound works
    exact ⟨0, fun n z hz => absurd (ht hz) (by simp)⟩
  · refine ⟨t.sup' htne (fun z : K => M ↑z), fun n z hz => ?_⟩
    obtain ⟨i, hit, hzi⟩ := mem_iUnion₂.mp (ht hz)
    calc ‖F n z‖ ≤ M ↑i := hbound (↑i) (hKU i.2) n z hzi
      _ ≤ t.sup' htne (fun z : K => M ↑z) := Finset.le_sup' (fun z : K => M ↑z) hit

/-- **Reindexing a uniform limit along a divergent index map preserves uniform convergence.** -/
theorem tendstoUniformlyOn_comp_index {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {s : Set ℂ}
    (h : TendstoUniformlyOn F f atTop s) {r : ℕ → ℕ} (hr : Tendsto r atTop atTop) :
    TendstoUniformlyOn (fun n => F (r n)) f atTop s :=
  fun u hu => hr.eventually (h u hu)

/-- **Montel theorem (the diagonal subsequence)**.

A locally uniformly bounded family `F` of holomorphic functions on an open `U ⊆ ℂ` has a
subsequence converging **locally uniformly on `U`** to a function `g` holomorphic on `U`.

Construction: per-compact Arzelà–Ascoli (`exists_subseq_tendstoUniformlyOn_compact`) on a compact
exhaustion `K m` (`exists_compactExhaustion_of_isOpen`, with uniform bounds from
`exists_bound_on_compact_of_locallyBounded`) builds cumulative extractors `φ m` (a
`VitaliDiagState` recursion) whose diagonal `ψ n = φ n n` is a subsequence of every `φ m` on its
tail; hence `F ∘ ψ` converges uniformly on each `K m`, so locally uniformly on `U`. Holomorphy of
the limit is `TendstoLocallyUniformlyOn.differentiableOn`. -/
theorem exists_subseq_tendstoLocallyUniformlyOn_of_locallyBounded
    {U : Set ℂ} (hU : IsOpen U) {F : ℕ → ℂ → ℂ}
    (hF : ∀ n, DifferentiableOn ℂ (F n) U)
    (hbdd : ∀ z ∈ U, ∃ r M : ℝ, 0 < r ∧ ball z r ⊆ U ∧
      ∀ n, ∀ w ∈ ball z r, ‖F n w‖ ≤ M) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ g : ℂ → ℂ,
      DifferentiableOn ℂ g U ∧ TendstoLocallyUniformlyOn (fun k => F (ψ k)) g atTop U := by
  classical
  have hcont : ∀ n, ContinuousOn (F n) U := fun n => (hF n).continuousOn
  have hequi : ∀ x ∈ U, EquicontinuousAt (fun n => F n) x :=
    fun x hx => equicontinuousAt_of_locallyBounded hU hF (hbdd x hx)
  obtain ⟨K, hKcpt, hKU, _hKcover, hKsuper⟩ := exists_compactExhaustion_of_isOpen hU
  choose Mbd hMbd using fun m =>
    exists_bound_on_compact_of_locallyBounded hbdd (hKcpt m) (hKU m)
  -- One per-compact extraction step at level `m`, refining a cumulative extractor `φ₀`.
  have hstep : ∀ (m : ℕ) (φ₀ : ℕ → ℕ), StrictMono φ₀ →
      ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ g : ℂ → ℂ,
        TendstoUniformlyOn (fun k => F (φ₀ (ρ k))) g atTop (K m) := by
    intro m φ₀ _hφ₀
    obtain ⟨ρ, hρ, g, hg⟩ := exists_subseq_tendstoUniformlyOn_compact
      (F := fun n => F (φ₀ n)) (fun n => hcont (φ₀ n)) (hKcpt m) (hKU m)
      (fun x hx => (hequi x hx).comp φ₀) (fun n => hMbd m (φ₀ n))
    exact ⟨ρ, hρ, g, hg⟩
  -- Cumulative-extractor recursion.
  let mkBase : VitaliDiagState F K 0 :=
    let e := (hstep 0 id strictMono_id)
    { φ := e.choose, hφ := e.choose_spec.1, ρ := e.choose, hρ := e.choose_spec.1,
      g := e.choose_spec.2.choose, hconv := e.choose_spec.2.choose_spec }
  let mkStep : ∀ m, VitaliDiagState F K m → VitaliDiagState F K (m + 1) := fun m prev =>
    let e := (hstep (m + 1) prev.φ prev.hφ)
    { φ := prev.φ ∘ e.choose, hφ := prev.hφ.comp e.choose_spec.1, ρ := e.choose,
      hρ := e.choose_spec.1, g := e.choose_spec.2.choose,
      hconv := e.choose_spec.2.choose_spec }
  let D : (m : ℕ) → VitaliDiagState F K m := fun m =>
    Nat.rec (motive := fun m => VitaliDiagState F K m) mkBase mkStep m
  set φ : ℕ → (ℕ → ℕ) := fun m => (D m).φ with hφ_def
  have hφmono : ∀ m, StrictMono (φ m) := fun m => (D m).hφ
  have hconv : ∀ m, TendstoUniformlyOn (fun k => F (φ m k)) (D m).g atTop (K m) :=
    fun m => (D m).hconv
  have hchain : ∀ m k, φ (m + 1) k = φ m ((D (m + 1)).ρ k) := fun _ _ => rfl
  -- The diagonal.
  let ψ : ℕ → ℕ := fun n => φ n n
  have hψ : StrictMono ψ := by
    apply strictMono_nat_of_lt_succ
    intro n
    change φ n n < φ (n + 1) (n + 1)
    rw [hchain n (n + 1)]
    exact hφmono n (lt_of_lt_of_le (Nat.lt_succ_self n) (D (n + 1)).hρ.le_apply)
  -- Factorisation (pointwise): `φ n k = φ m (τ k)` for some strict-mono `τ`, when `m ≤ n`.
  have hfactor : ∀ m n, m ≤ n → ∃ τ : ℕ → ℕ, StrictMono τ ∧ ∀ k, φ n k = φ m (τ k) := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => exact ⟨id, strictMono_id, fun _ => rfl⟩
    | succ n _ ih =>
        obtain ⟨τ, hτ, hτeq⟩ := ih
        refine ⟨τ ∘ (D (n + 1)).ρ, hτ.comp (D (n + 1)).hρ, fun k => ?_⟩
        rw [hchain n k]
        exact hτeq ((D (n + 1)).ρ k)
  -- The diagonal converges uniformly on each `K m`.
  have hψconv : ∀ m, ∃ g : ℂ → ℂ,
      TendstoUniformlyOn (fun n => F (ψ n)) g atTop (K m) := by
    intro m
    refine ⟨(D m).g, ?_⟩
    -- A totalised reindex `σ` with `ψ n = φ m (σ n)` and `n ≤ σ n` for `n ≥ m`.
    let σ : ℕ → ℕ := fun n => if h : m ≤ n then (hfactor m n h).choose n else 0
    have hσval : ∀ n, m ≤ n → ψ n = φ m (σ n) ∧ n ≤ σ n := by
      intro n hn
      have hσn : σ n = (hfactor m n hn).choose n := dif_pos hn
      obtain ⟨hτmono, hτeq⟩ := (hfactor m n hn).choose_spec
      refine ⟨?_, ?_⟩
      · change φ n n = φ m (σ n)
        rw [hσn]; exact hτeq n
      · rw [hσn]; exact hτmono.le_apply
    have hσtop : Tendsto σ atTop atTop := by
      rw [tendsto_atTop_atTop]
      intro b
      refine ⟨max b m, fun a ha => ?_⟩
      exact le_trans (le_trans (le_max_left b m) ha)
        (hσval a (le_trans (le_max_right b m) ha)).2
    have hreindex : TendstoUniformlyOn (fun n => F (φ m (σ n))) (D m).g atTop (K m) :=
      tendstoUniformlyOn_comp_index (hconv m) hσtop
    refine hreindex.congr ?_
    filter_upwards [eventually_ge_atTop m] with n hn
    intro x _
    exact congrFun (congrArg F (hσval n hn).1.symm) x
  -- Package the limit as a single `g : ℂ → ℂ` and upgrade to locally uniform + holomorphic.
  let g : ℂ → ℂ := fun z => limUnder atTop (fun n => F (ψ n) z)
  have hg_local : TendstoLocallyUniformlyOn (fun k => F (ψ k)) g atTop U := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU]
    intro C hCU hC
    obtain ⟨m, hCm⟩ := hKsuper C hC hCU
    obtain ⟨gm, hgm⟩ := hψconv m
    have hgm' : TendstoUniformlyOn (fun k => F (ψ k)) g atTop (K m) := by
      refine hgm.congr_right ?_
      intro z hz
      exact ((hgm.tendsto_at hz).limUnder_eq).symm
    exact hgm'.mono hCm
  refine ⟨ψ, hψ, g, ?_, hg_local⟩
  exact hg_local.differentiableOn (Eventually.of_forall fun n => hF (ψ n)) hU

end FunctionTheory
end IsingModel
