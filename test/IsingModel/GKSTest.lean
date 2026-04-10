-- Numerical verification of GKS and basic Ising model properties
-- Float-based reference implementation for property testing.

def allSpins : List Float := [1.0, -1.0]

def allConfigs : Nat → List (List Float)
  | 0 => [[]]
  | n + 1 => Id.run do
    let mut result : List (List Float) := []
    for rest in allConfigs n do
      for s in allSpins do
        result := (s :: rest) :: result
    return result

def testHamiltonian (edges : List (Nat × Nat)) (J hf : Float) (σ : List Float) : Float :=
  let interaction := edges.foldl (fun acc (i, j) => acc + σ.getD i 0 * σ.getD j 0) 0
  let field := σ.foldl (· + ·) 0
  (0.0 - J) * interaction - hf * field

def boltzmann (edges : List (Nat × Nat)) (J h β : Float) (σ : List Float) : Float :=
  Float.exp (-β * testHamiltonian edges J h σ)

def partitionFn (n : Nat) (edges : List (Nat × Nat)) (J h β : Float) : Float :=
  (allConfigs n).foldl (fun acc σ => acc + boltzmann edges J h β σ) 0

def gibbsExpect (n : Nat) (edges : List (Nat × Nat)) (J h β : Float)
    (F : List Float → Float) : Float :=
  let Z := partitionFn n edges J h β
  (allConfigs n).foldl (fun acc σ => acc + F σ * boltzmann edges J h β σ) 0 / Z

def spinProd (A : List Nat) (σ : List Float) : Float :=
  A.foldl (fun acc i => acc * σ.getD i 0) 1

def testCorrelation (n : Nat) (edges : List (Nat × Nat)) (J h β : Float)
    (A : List Nat) : Float :=
  gibbsExpect n edges J h β (spinProd A)

-- Test graphs

-- 2-site chain: 0 — 1
def graph2 : List (Nat × Nat) := [(0, 1)]

-- 3-site chain: 0 — 1 — 2
def graph3 : List (Nat × Nat) := [(0, 1), (1, 2)]

-- 3-site triangle: 0 — 1 — 2 — 0
def triangle3 : List (Nat × Nat) := [(0, 1), (1, 2), (0, 2)]

-- 4-site square: 0 — 1 — 2 — 3 — 0
def square4 : List (Nat × Nat) := [(0, 1), (1, 2), (2, 3), (0, 3)]

-- GKS-I tests

-- Helper: check all subsets up to given size
def allSubsets (n : Nat) : List (List Nat) :=
  let sites := List.range n
  sites.foldl (fun acc i =>
    acc ++ acc.map (fun s => i :: s)) [[]]

def checkGKS1 (label : String) (n : Nat) (edges : List (Nat × Nat))
    (J h β : Float) : IO Bool := do
  let mut ok := true
  let subsets := allSubsets n
  for A in subsets do
    let c := testCorrelation n edges J h β A
    if c < -1e-10 then
      IO.println s!"  FAIL: ⟨σ_{A}⟩ = {c} < 0"
      ok := false
  if ok then
    IO.println s!"  {label}: GKS-I passed for all {subsets.length} subsets"
  return ok

-- GKS-II tests

def checkGKS2 (label : String) (n : Nat) (edges : List (Nat × Nat))
    (J h β : Float) : IO Bool := do
  let mut ok := true
  let subsets := allSubsets n
  for A in subsets do
    for B in subsets do
      let cAB := testCorrelation n edges J h β (A ++ B)
      let cA := testCorrelation n edges J h β A
      let cB := testCorrelation n edges J h β B
      if cAB - cA * cB < -1e-10 then
        IO.println s!"  FAIL: ⟨σ_{A}σ_{B}⟩ - ⟨σ_{A}⟩⟨σ_{B}⟩ = {cAB - cA * cB} < 0"
        ok := false
  if ok then
    IO.println s!"  {label}: GKS-II passed for all subset pairs"
  return ok

-- Z > 0 test

def checkZPos (label : String) (n : Nat) (edges : List (Nat × Nat))
    (J h β : Float) : IO Bool := do
  let Z := partitionFn n edges J h β
  if Z > 0 then
    IO.println s!"  {label}: Z = {Z} > 0 ✓"
    return true
  else
    IO.println s!"  {label}: Z = {Z} NOT > 0 ✗"
    return false

-- Spin flip symmetry test

def checkFlipSymmetry (label : String) (n : Nat) (edges : List (Nat × Nat))
    (J : Float) : IO Bool := do
  let mut ok := true
  for σ in allConfigs n do
    let σ_flip := σ.map (· * (-1))
    let h1 := testHamiltonian edges J 0 σ
    let h2 := testHamiltonian edges J 0 σ_flip
    if (h1 - h2).abs > 1e-10 then
      IO.println s!"  FAIL: H({σ}) = {h1} ≠ H({σ_flip}) = {h2}"
      ok := false
  if ok then
    IO.println s!"  {label}: Spin flip symmetry (h=0) ✓"
  return ok

-- Check that GKS-I is violated (expected for anti-ferromagnetic parameters)
def checkGKS1Violation (label : String) (n : Nat) (edges : List (Nat × Nat))
    (J h β : Float) : IO Bool := do
  let subsets := allSubsets n
  for A in subsets do
    let c := testCorrelation n edges J h β A
    if c < -1e-10 then
      IO.println s!"  {label}: GKS-I violation confirmed (⟨σ_{A}⟩ = {c} < 0) ✓"
      return true
  IO.println s!"  FAIL: {label}: expected GKS-I violation but all correlations ≥ 0"
  return false

-- Main test runner

def main : IO UInt32 := do
  IO.println "=== Ising Model Numerical Tests ==="
  let mut allPassed := true
  IO.println ""

  IO.println "--- Z > 0 ---"
  allPassed := allPassed && (← checkZPos "2-chain J=1 h=0.5 β=1" 2 graph2 1.0 0.5 1.0)
  allPassed := allPassed && (← checkZPos "3-chain J=2 h=0 β=0.5" 3 graph3 2.0 0.0 0.5)
  allPassed := allPassed && (← checkZPos "triangle J=1 h=1 β=2" 3 triangle3 1.0 1.0 2.0)
  allPassed := allPassed && (← checkZPos "square J=0.5 h=0.3 β=1" 4 square4 0.5 0.3 1.0)

  IO.println ""
  IO.println "--- Spin flip symmetry (h=0) ---"
  allPassed := allPassed && (← checkFlipSymmetry "2-chain J=1" 2 graph2 1.0)
  allPassed := allPassed && (← checkFlipSymmetry "triangle J=2" 3 triangle3 2.0)

  IO.println ""
  IO.println "--- GKS-I: ⟨σ_A⟩ ≥ 0 (ferromagnetic) ---"
  allPassed := allPassed && (← checkGKS1 "2-chain J=1 h=0.5 β=1" 2 graph2 1.0 0.5 1.0)
  allPassed := allPassed && (← checkGKS1 "2-chain J=1 h=0 β=1" 2 graph2 1.0 0.0 1.0)
  allPassed := allPassed && (← checkGKS1 "3-chain J=2 h=0.3 β=0.5" 3 graph3 2.0 0.3 0.5)
  allPassed := allPassed && (← checkGKS1 "triangle J=1 h=1 β=2" 3 triangle3 1.0 1.0 2.0)
  allPassed := allPassed && (← checkGKS1 "square J=0.5 h=0.3 β=1" 4 square4 0.5 0.3 1.0)
  allPassed := allPassed && (← checkGKS1 "square J=3 h=0 β=0.1" 4 square4 3.0 0.0 0.1)

  IO.println ""
  IO.println "--- GKS-II: ⟨σ_Aσ_B⟩ ≥ ⟨σ_A⟩⟨σ_B⟩ (ferromagnetic) ---"
  allPassed := allPassed && (← checkGKS2 "2-chain J=1 h=0.5 β=1" 2 graph2 1.0 0.5 1.0)
  allPassed := allPassed && (← checkGKS2 "3-chain J=2 h=0.3 β=0.5" 3 graph3 2.0 0.3 0.5)
  allPassed := allPassed && (← checkGKS2 "triangle J=1 h=1 β=2" 3 triangle3 1.0 1.0 2.0)

  IO.println ""
  IO.println "--- GKS-I violation (anti-ferromagnetic, J < 0) ---"
  allPassed := allPassed && (← checkGKS1Violation "2-chain J=-1 h=0 β=1" 2 graph2 (-1.0) 0.0 1.0)

  IO.println ""
  if allPassed then
    IO.println "=== All tests passed ==="
    return 0
  else
    IO.println "=== SOME TESTS FAILED ==="
    return 1
