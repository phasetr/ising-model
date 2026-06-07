import IsingModel.Peierls.SingleOrbitContactSymm

/-!
# Reduction of connectivity to a basepoint (FV §3.7.2)

A standard connectivity reduction using the symmetry of contact-move connectivity: if every contact
pair is connected to one fixed basepoint, then any two contact pairs are connected
(`reflTransGen_contactMove_of_basepoint`). This turns the global `hconn` goal
(`∀ c c', ReflTransGen ContactMove c c'`) into the simpler `∀ c, ReflTransGen ContactMove c c₀` —
"every boundary contact pair reaches a fixed one", the form the `F`-path argument establishes by
walking the boundary back to the basepoint.

* `reflTransGen_contactMove_of_basepoint` — basepoint connectivity gives full connectivity.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

variable {F : Finset (Fin 2 → ℤ)}

/-- **Connectivity from a basepoint**: if every contact pair reaches the fixed basepoint `c₀` by
contact moves, then any two contact pairs are connected (via `c → c₀ → c'`, using symmetry). -/
theorem reflTransGen_contactMove_of_basepoint (c₀ : ContactPair F)
    (h : ∀ c : ContactPair F, Relation.ReflTransGen ContactMove c c₀)
    (c c' : ContactPair F) : Relation.ReflTransGen ContactMove c c' :=
  (h c).trans (reflTransGen_contactMove_symm c' c₀ (h c'))

end IsingModel
