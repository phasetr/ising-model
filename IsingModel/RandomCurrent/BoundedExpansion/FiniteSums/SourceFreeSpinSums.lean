import IsingModel.RandomCurrent.BoundedExpansion.FiniteSums.DegreeProducts

/-!
# The spin sum at a fixed current, and its source-free form

At a fixed current `n` on `inducedGraph G Λ`, the subgraph of `G` that `Λ` induces, for an
arbitrary `G : SimpleGraph V` and an arbitrary finite volume `Λ : Finset V`, the quantity
summed is the product over the edges of the product of the spin signs over the endpoint
`Finset` of the edge, raised to the multiplicity `n e`; the sum ranges over all spin
configurations `σ : ↥Λ → Spin`.

That sum is `2 ^ Fintype.card ↥Λ` when the total incident degree `Current.degreeAt G Λ n v`
is even at every vertex of `Λ`, and `0` otherwise, as a single `if`-`then`-`else` equality.
Evenness at every vertex is equivalent to `n` being source-free, which is to say that its
source set is empty, and the same sum is recorded again with source-freeness in place of the
evenness condition; that second form additionally takes a `[Decidable (n.IsSourceFree G Λ)]`
instance.

Every statement here takes `[Fintype (inducedGraph G Λ).edgeSet]` together with
`[DecidableEq ↥Λ]`, and none carries a hypothesis.
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
/-- **Spin sum of the spin-edge product at fixed current**: at
fixed current `n`,
`∑_σ ∏_e (e.toFinset.prod σ.toSign) ^ n e = 2^|Λ|` if
`degreeAt n` is even at every vertex (i.e. `n` is source-free),
else `0`. Direct consequence of `prod_pow_spin_degreeAt` and
`Config.sum_prod_toSign_pow_real`; the per-current spin-sum step
of the random-current expansion (FV §3.10.6). -/
theorem Config.sum_prod_spin_pow_degreeAt
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) :
    (∑ σ : ↑Λ → Spin, ∏ e : (inducedGraph G Λ).edgeSet,
        ((e : Sym2 ↑Λ).toFinset.prod
          (fun v => ((σ v).toSign : ℝ))) ^ n e)
      = if (∀ v : ↑Λ, Even (n.degreeAt G Λ v))
        then (2 : ℝ)^(Fintype.card ↑Λ) else 0 := by
  simp_rw [← Config.prod_pow_spin_degreeAt G Λ _ n]
  exact Config.sum_prod_toSign_pow_real (k := n.degreeAt G Λ)

omit [DecidableEq V] in
/-- **Even `degreeAt` everywhere ↔ source-free**: a current `n`
is source-free iff its total incident degree is even at every
vertex. Bridges the degree-side condition (output of
`Config.sum_prod_spin_pow_degreeAt`) with the parity-side
characterisation (`isSourceFree_iff`). -/
theorem Current.even_degreeAt_iff_isSourceFree
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) :
    (∀ v : ↑Λ, Even (n.degreeAt G Λ v)) ↔ n.IsSourceFree G Λ := by
  rw [Current.isSourceFree_iff]
  refine forall_congr' (fun v => ?_)
  rw [Current.parity_eq_degreeAt, ZMod.natCast_eq_zero_iff,
    ← even_iff_two_dvd]

omit [DecidableEq V] in
/-- **Spin sum at fixed current — source-free form**: at fixed
current `n`, the spin sum of the spin-edge product equals
`2^|Λ|` if `n` is source-free, else `0`. Combines
`Config.sum_prod_spin_pow_degreeAt` with
`Current.even_degreeAt_iff_isSourceFree` to produce the per-current
spin-sum identity in its final form (FV §3.10.6, p. 144). -/
theorem Config.sum_prod_spin_pow_degreeAt_isSourceFree
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) [Decidable (n.IsSourceFree G Λ)] :
    (∑ σ : ↑Λ → Spin, ∏ e : (inducedGraph G Λ).edgeSet,
        ((e : Sym2 ↑Λ).toFinset.prod
          (fun v => ((σ v).toSign : ℝ))) ^ n e)
      = if n.IsSourceFree G Λ
        then (2 : ℝ)^(Fintype.card ↑Λ) else 0 := by
  rw [Config.sum_prod_spin_pow_degreeAt]
  exact if_congr (Current.even_degreeAt_iff_isSourceFree G Λ n) rfl rfl


end Ambient
end IsingModel
