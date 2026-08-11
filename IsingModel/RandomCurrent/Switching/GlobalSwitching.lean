import IsingModel.RandomCurrent.Switching.Core

/-!
# Global switching identity (bounded form)

The *outer* reindexing of the Aizenman switching method in bounded-`Finset`
form: a genuine finite, weight-preserving bijection turning a product of two
source-constrained current sums into a single sum over a *doubled* current
carrying a distinguished subcurrent.

The bijection is `Φ : (n₁, n₂) ↦ (n₁ + n₂, n₁)` with inverse
`(M, m) ↦ (m, M − m)` on `{m ≤ M}`. It preserves the summand term by term
(`w(n₁) w(n₂) = w(m) w(M − m)`), so the resulting identity is true by
construction — no positivity, inequality, or convergence enters.

This is Stage A brick 1 of the random-current build toward the
lower-semicontinuous half of Glimm–Jaffe Theorem 17.5.1 (issue #4386). The
`N → ∞` / `tsum` lift and the connectivity (percolation) representation are
deferred to later bricks.

## References

* Aizenman, M. (1982). Geometric analysis of φ⁴ fields, Lemma 4.1.
* Fernández–Fröhlich–Sokal, *Random Walks, Critical Phenomena, and
  Triviality* (1992), Chapter 12.
* Glimm–Jaffe, *Quantum Physics*, §5.1; Friedli–Velenik, Lemma 3.55, p. 144.
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

set_option linter.unusedDecidableInType false in
/-- **Global switching identity, bounded form (Stage A brick 1)**: as an
identity of finite real sums, the product of two per-edge-bounded,
source-constrained current sums equals a single sum over the doubled current
`M` carrying its distinguished subcurrent `m`. The forward change of variables
is `Φ : (n₁, n₂) ↦ (n₁ + n₂, n₁)`, with inverse `(M, m) ↦ (m, M − m)` on
`{m ≤ M}`; it preserves the summand `n₁.weight * n₂.weight = m.weight *
(M − m).weight` term by term. The doubled current lands in `boundedFinset (2 N)`,
the distinguished subcurrent ranges over `M.subFinset` with the two source
filters and the two per-edge caps `m e ≤ N`, `(M − m) e ≤ N` retained. Proved by
`Finset.sum_nbij'` (Aizenman 1982 Lemma 4.1 / FV Lemma 3.55, p. 144). -/
theorem Current.sum_prod_eq_sum_doubled_subFinset
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (N : ℕ) (A B : Finset ↑Λ) (β J : ℝ) :
    (∑ n₁ ∈ (Current.boundedFinset G Λ N).filter (fun n => n.sources G Λ = A),
       ∑ n₂ ∈ (Current.boundedFinset G Λ N).filter (fun n => n.sources G Λ = B),
         n₁.weight G Λ β J * n₂.weight G Λ β J)
      = ∑ M ∈ Current.boundedFinset G Λ (2 * N),
          ∑ m ∈ (Current.subFinset G Λ M).filter
              (fun m => m.sources G Λ = A ∧ (M - m).sources G Λ = B
                ∧ ∀ e, m e ≤ N ∧ (M - m) e ≤ N),
            m.weight G Λ β J * (M - m).weight G Λ β J := by
  classical
  -- `(a + b) - a = b` pointwise, the algebraic core of the bijection.
  have key : ∀ a b : Current G Λ, a + b - a = b := by
    intro a b
    ext e
    simp
  rw [← Finset.sum_product', Finset.sum_sigma']
  refine Finset.sum_nbij'
    (fun p => (⟨p.1 + p.2, p.1⟩ : Σ _ : Current G Λ, Current G Λ))
    (fun x => (x.2, x.1 - x.2)) ?_ ?_ ?_ ?_ ?_
  · -- forward membership: `(n₁, n₂) ↦ ⟨n₁ + n₂, n₁⟩` lands in the sigma set.
    intro p hp
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter] at hp
    obtain ⟨⟨hp1mem, hp1src⟩, hp2mem, hp2src⟩ := hp
    rw [Current.mem_boundedFinset_iff] at hp1mem hp2mem
    rw [Finset.mem_sigma, Finset.mem_filter, Current.mem_subFinset_iff]
    refine ⟨?_, ?_, hp1src, ?_, ?_⟩
    · change p.1 + p.2 ∈ Current.boundedFinset G Λ (2 * N)
      rw [Current.mem_boundedFinset_iff]
      intro e
      have h1 := hp1mem e
      have h2 := hp2mem e
      rw [Current.add_apply]
      omega
    · exact Current.le_self_add_right G Λ p.1 p.2
    · change (p.1 + p.2 - p.1).sources G Λ = B
      rw [key p.1 p.2]; exact hp2src
    · change ∀ e, p.1 e ≤ N ∧ (p.1 + p.2 - p.1) e ≤ N
      intro e
      rw [key p.1 p.2]
      exact ⟨hp1mem e, hp2mem e⟩
  · -- backward membership: `⟨M, m⟩ ↦ (m, M − m)` lands in the product set.
    intro x hx
    rw [Finset.mem_sigma, Finset.mem_filter, Current.mem_subFinset_iff] at hx
    obtain ⟨_, _, hmsrc, hdsrc, hcap⟩ := hx
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter]
    refine ⟨⟨?_, hmsrc⟩, ?_, hdsrc⟩
    · change x.2 ∈ Current.boundedFinset G Λ N
      rw [Current.mem_boundedFinset_iff]
      intro e
      exact (hcap e).1
    · change x.1 - x.2 ∈ Current.boundedFinset G Λ N
      rw [Current.mem_boundedFinset_iff]
      intro e
      exact (hcap e).2
  · -- left inverse: `(m, M − m) ∘ Φ = id` on the product set.
    intro p _
    change (p.1, p.1 + p.2 - p.1) = p
    rw [key p.1 p.2]
  · -- right inverse: `Φ ∘ (m, M − m) = id` on the sigma set.
    intro x hx
    rw [Finset.mem_sigma, Finset.mem_filter, Current.mem_subFinset_iff] at hx
    change (⟨x.2 + (x.1 - x.2), x.2⟩ : Σ _ : Current G Λ, Current G Λ) = x
    rw [Current.add_sub_cancel_of_le G Λ hx.2.1]
  · -- value: the summand is preserved term by term under `Φ`.
    intro p _
    change p.1.weight G Λ β J * p.2.weight G Λ β J
      = p.1.weight G Λ β J * (p.1 + p.2 - p.1).weight G Λ β J
    rw [key p.1 p.2]

end Ambient
end IsingModel
