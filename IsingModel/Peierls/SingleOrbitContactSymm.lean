import IsingModel.Peierls.SingleOrbitContactEquiv

/-!
# Contact-move connectivity is symmetric (FV §3.7.2)

Although a single `ContactMove` is directed (a fan prefix or a forward slide), the *connectivity*
`ReflTransGen ContactMove` is symmetric: via `reflTransGen_contactMove_iff_sameOrbit` it agrees with
the same-orbit relation, which is symmetric. Hence contact-move connectivity is an equivalence
relation on contact pairs (`reflTransGen_contactMove_symm`, with reflexivity and transitivity from
`ReflTransGen`). This lets the global planar-connectivity argument route in either direction.

* `reflTransGen_contactMove_symm` — connectivity is symmetric.
* `reflTransGen_contactMove_equivalence` — it is an equivalence relation.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

variable {F : Finset (Fin 2 → ℤ)}

/-- **Contact-move connectivity is symmetric**: if `c` reaches `c'` by contact moves, then `c'`
reaches `c` (via the same-orbit characterisation, which is symmetric). -/
theorem reflTransGen_contactMove_symm (c c' : ContactPair F)
    (h : Relation.ReflTransGen ContactMove c c') :
    Relation.ReflTransGen ContactMove c' c := by
  rw [← toDart_toContactPair c, ← toDart_toContactPair c'] at h ⊢
  rw [reflTransGen_contactMove_iff_sameOrbit] at h
  rw [reflTransGen_contactMove_iff_sameOrbit]
  exact h.symm

/-- **Contact-move connectivity is an equivalence relation** on contact pairs. -/
theorem reflTransGen_contactMove_equivalence :
    Equivalence (Relation.ReflTransGen (ContactMove (F := F))) where
  refl _ := Relation.ReflTransGen.refl
  symm h := reflTransGen_contactMove_symm _ _ h
  trans h₁ h₂ := h₁.trans h₂

end IsingModel
