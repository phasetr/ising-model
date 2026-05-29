import IsingModel.Quantum.SingleSpin
import IsingModel.Quantum.TwoSiteSpin1Half

/-!
# Quantum spin systems (Tasaki Ch 2)

Umbrella module re-exporting the Tasaki Ch 2 quantum spin formalisation:

* `IsingModel.Quantum.SingleSpin` — Tasaki §2.1: single quantum spin (S=1/2),
  Pauli matrices, commutation relations, S² = (3/4)·I.
* `IsingModel.Quantum.TwoSiteSpin1Half` — Tasaki §2.2 (start): two-site
  spin-1/2 system via Kronecker product, site-local and total spin operators,
  cross-site commutativity.

References:

* H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, GTP,
  Springer 2020, Ch 2 (Basics of Quantum Spin Systems), pp. 13-44.
-/
