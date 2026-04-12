-- Numerical verification of the Lee-Yang circle theorem.
-- Float-based: compute the Ising partition polynomial on the open unit polydisk
-- and check that it is nonzero.

/-- Ising partition polynomial for a list of edges at given z values.
`P_E(z) = Σ_{X⊆V} (∏_e w_e(X)) ∏_{i∈X} z_i`
where w_e(X) = t_e if exactly one endpoint of e is in X, else 1. -/
def edgeWeightFloat (i j : Nat) (t : Float) (X : List Nat) : Float :=
  let iIn := X.contains i
  let jIn := X.contains j
  if iIn == jIn then 1.0 else t

def isingPolyFloat (n : Nat) (edges : List (Nat × Nat × Float))
    (z : Nat → Float) : Float :=
  let subsets := allSubsets n
  subsets.foldl (fun acc X =>
    let weight := edges.foldl (fun w (i, j, t) => w * edgeWeightFloat i j t X) 1.0
    let monomial := X.foldl (fun m i => m * z i) 1.0
    acc + weight * monomial) 0.0
where
  allSubsets : Nat → List (List Nat)
    | 0 => [[]]
    | k + 1 => (allSubsets k).flatMap (fun s => [s, k :: s])

/-- Check that the Ising partition polynomial is nonzero at a given point. -/
def checkLeeYang (label : String) (n : Nat)
    (edges : List (Nat × Nat × Float)) (z : Nat → Float) : IO Bool := do
  let val := isingPolyFloat n edges z
  let pass := val.abs > 1e-10
  let status := if pass then "✓ PASS" else "✗ FAIL"
  IO.println s!"  {status}: {label} | P(z) = {val}"
  return pass

def main : IO UInt32 := do
  IO.println "=== Lee-Yang circle theorem: numerical verification ==="
  IO.println ""
  let mut allPassed := true

  -- Edge list: (i, j, t) where t = e^{-2βJ}, 0 ≤ t < 1
  let edge01 : List (Nat × Nat × Float) := [(0, 1, 0.5)]
  let triangle : List (Nat × Nat × Float) := [(0, 1, 0.3), (1, 2, 0.3), (0, 2, 0.3)]
  let square : List (Nat × Nat × Float) :=
    [(0, 1, 0.4), (1, 2, 0.4), (2, 3, 0.4), (0, 3, 0.4)]

  IO.println "--- z_k = 0 (trivial: P = 1) ---"
  allPassed := allPassed && (← checkLeeYang "2-site single edge" 2 edge01 (fun _ => 0.0))
  allPassed := allPassed && (← checkLeeYang "triangle" 3 triangle (fun _ => 0.0))

  IO.println ""
  IO.println "--- z_k = 0.5 (inside polydisk) ---"
  allPassed := allPassed && (← checkLeeYang "2-site single edge" 2 edge01 (fun _ => 0.5))
  allPassed := allPassed && (← checkLeeYang "triangle" 3 triangle (fun _ => 0.5))
  allPassed := allPassed && (← checkLeeYang "square" 4 square (fun _ => 0.5))

  IO.println ""
  IO.println "--- z_k = -0.9 (near boundary, inside polydisk) ---"
  allPassed := allPassed && (← checkLeeYang "2-site single edge" 2 edge01 (fun _ => -0.9))
  allPassed := allPassed && (← checkLeeYang "triangle" 3 triangle (fun _ => -0.9))
  allPassed := allPassed && (← checkLeeYang "square" 4 square (fun _ => -0.9))

  IO.println ""
  IO.println "--- mixed z_k (different values per site) ---"
  allPassed := allPassed && (← checkLeeYang "triangle mixed" 3 triangle
    (fun k => if k == 0 then 0.3 else if k == 1 then -0.7 else 0.1))
  allPassed := allPassed && (← checkLeeYang "square mixed" 4 square
    (fun k => [0.8, -0.5, 0.2, -0.9].getD k 0.0))

  IO.println ""
  IO.println "--- strong coupling t close to 1 ---"
  let strongEdge : List (Nat × Nat × Float) := [(0, 1, 0.99)]
  allPassed := allPassed && (← checkLeeYang "2-site t=0.99" 2 strongEdge (fun _ => 0.8))
  allPassed := allPassed && (← checkLeeYang "2-site t=0.99 neg" 2 strongEdge (fun _ => -0.95))

  IO.println ""
  if allPassed then
    IO.println "All Lee-Yang tests passed."
    return 0
  else
    IO.println "SOME TESTS FAILED!"
    return 1
