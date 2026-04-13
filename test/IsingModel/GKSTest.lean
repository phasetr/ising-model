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
      IO.println s!"  FAIL: ⟨σ^A⟩ = {c} < 0"
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
        IO.println s!"  FAIL: ⟨σ^Aσ^B⟩ - ⟨σ^A⟩⟨σ^B⟩ = {cAB - cA * cB} < 0"
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
      IO.println s!"  {label}: GKS-I violation confirmed (⟨σ^A⟩ = {c} < 0) ✓"
      return true
  IO.println s!"  FAIL: {label}: expected GKS-I violation but all correlations ≥ 0"
  return false

-- Check that GKS-II is violated (expected for anti-ferromagnetic parameters)
def checkGKS2Violation (label : String) (n : Nat) (edges : List (Nat × Nat))
    (J h β : Float) : IO Bool := do
  let subsets := allSubsets n
  for A in subsets do
    for B in subsets do
      let cAB := testCorrelation n edges J h β (A ++ B)
      let cA := testCorrelation n edges J h β A
      let cB := testCorrelation n edges J h β B
      if cAB - cA * cB < -1e-10 then
        IO.println s!"  {label}: GKS-II violation confirmed (A={A}, B={B}, diff={cAB - cA * cB}) ✓"
        return true
  IO.println s!"  FAIL: {label}: expected GKS-II violation but all pairs satisfied"
  return false

-- FKG test: ⟨fg⟩ ≥ ⟨f⟩⟨g⟩ for monotone f, g
-- f = magnetization (Σ σ_i), g = σ_0, both monotone nondecreasing
def checkFKG (label : String) (n : Nat) (edges : List (Nat × Nat))
    (J h β : Float) : IO Bool := do
  let magnetization (σ : List Float) : Float := σ.foldl (· + ·) 0
  let sigma0 (σ : List Float) : Float := σ.getD 0 0
  let expect_fg := gibbsExpect n edges J h β (fun σ => magnetization σ * sigma0 σ)
  let expect_f := gibbsExpect n edges J h β magnetization
  let expect_g := gibbsExpect n edges J h β sigma0
  if expect_fg - expect_f * expect_g >= -1e-10 then
    IO.println s!"  {label}: FKG passed (⟨fg⟩-⟨f⟩⟨g⟩ = {expect_fg - expect_f * expect_g})"
    return true
  else
    IO.println s!"  FAIL: {label}: FKG violated (⟨fg⟩-⟨f⟩⟨g⟩ = {expect_fg - expect_f * expect_g})"
    return false

-- GHS inequality test: truncated3 ≤ 0

def truncated3 (n : Nat) (edges : List (Nat × Nat)) (J h β : Float)
    (i j k : Nat) : Float :=
  let cijk := testCorrelation n edges J h β [i, j, k]
  let ci := testCorrelation n edges J h β [i]
  let cj := testCorrelation n edges J h β [j]
  let ck := testCorrelation n edges J h β [k]
  let cij := testCorrelation n edges J h β [i, j]
  let cik := testCorrelation n edges J h β [i, k]
  let cjk := testCorrelation n edges J h β [j, k]
  cijk - ci * cjk - cj * cik - ck * cij + 2 * ci * cj * ck

def checkGHS (label : String) (n : Nat) (edges : List (Nat × Nat))
    (J h β : Float) : IO Bool := do
  let sites := List.range n
  let mut ok := true
  for i in sites do
    for j in sites do
      for k in sites do
        if i < j && j < k then
          let t3 := truncated3 n edges J h β i j k
          if t3 > 1e-10 then
            IO.println s!"  FAIL: truncated3({i},{j},{k}) = {t3} > 0"
            ok := false
  if ok then
    IO.println s!"  {label}: GHS (truncated3 ≤ 0) passed"
  return ok

-- Cor 4.3.3: truncated4 ≤ 0 for h = 0

def truncated4 (n : Nat) (edges : List (Nat × Nat)) (J β : Float)
    (i j k l : Nat) : Float :=
  let cijkl := testCorrelation n edges J 0 β [i, j, k, l]
  let cij := testCorrelation n edges J 0 β [i, j]
  let ckl := testCorrelation n edges J 0 β [k, l]
  let cik := testCorrelation n edges J 0 β [i, k]
  let cjl := testCorrelation n edges J 0 β [j, l]
  let cil := testCorrelation n edges J 0 β [i, l]
  let cjk := testCorrelation n edges J 0 β [j, k]
  cijkl - cij * ckl - cik * cjl - cil * cjk

def checkCor433 (label : String) (n : Nat) (edges : List (Nat × Nat))
    (J β : Float) : IO Bool := do
  let sites := List.range n
  let mut ok := true
  for i in sites do
    for j in sites do
      for k in sites do
        for l in sites do
          if i < j && j < k && k < l then
            let t4 := truncated4 n edges J β i j k l
            if t4 > 1e-10 then
              IO.println s!"  FAIL: truncated4({i},{j},{k},{l}) = {t4} > 0"
              ok := false
  if ok then
    IO.println s!"  {label}: Cor 4.3.3 (truncated4 ≤ 0, h=0) passed"
  return ok

-- Odd correlation vanishing for h = 0

def checkOddVanish (label : String) (n : Nat) (edges : List (Nat × Nat))
    (J β : Float) : IO Bool := do
  let mut ok := true
  for A in allSubsets n do
    if A.length % 2 == 1 then
      let c := testCorrelation n edges J 0 β A
      if c.abs > 1e-10 then
        IO.println s!"  FAIL: ⟨σ^{A}⟩ = {c} ≠ 0 for odd |A| at h=0"
        ok := false
  if ok then
    IO.println s!"  {label}: Odd correlation vanishing (h=0) passed"
  return ok

-- Susceptibility non-negative: χ(i) = Σ_j truncated2(i,j) ≥ 0

def checkSusceptibility (label : String) (n : Nat) (edges : List (Nat × Nat))
    (J h β : Float) : IO Bool := do
  let mut ok := true
  for i in List.range n do
    let mut chi : Float := 0
    for j in List.range n do
      let cij := testCorrelation n edges J h β [i, j]
      let ci := testCorrelation n edges J h β [i]
      let cj := testCorrelation n edges J h β [j]
      chi := chi + (cij - ci * cj)
    if chi < -1e-10 then
      IO.println s!"  FAIL: χ({i}) = {chi} < 0"
      ok := false
  if ok then
    IO.println s!"  {label}: Susceptibility ≥ 0 passed"
  return ok

-- Magnetization monotone in h

def checkMagnetizationMonotone (label : String) (n : Nat) (edges : List (Nat × Nat))
    (J β : Float) (h1 h2 : Float) : IO Bool := do
  let m1 := testCorrelation n edges J h1 β [0]
  let m2 := testCorrelation n edges J h2 β [0]
  if m1 - 1e-10 <= m2 then
    IO.println s!"  {label}: M({h1})={m1} ≤ M({h2})={m2} ✓"
    return true
  else
    IO.println s!"  FAIL: {label}: M({h1})={m1} > M({h2})={m2}"
    return false

-- Correlation monotonicity in J

def checkCorrelationMonotoneJ (label : String) (n : Nat) (edges : List (Nat × Nat))
    (h β J1 J2 : Float) : IO Bool := do
  let c1 := testCorrelation n edges J1 h β [0, 1]
  let c2 := testCorrelation n edges J2 h β [0, 1]
  if c1 - 1e-10 <= c2 then
    IO.println s!"  {label}: ⟨σ₀σ₁⟩(J={J1})={c1} ≤ ⟨σ₀σ₁⟩(J={J2})={c2} ✓"
    return true
  else
    IO.println s!"  FAIL: {label}: monotonicity violated"
    return false

-- Z bounds: exp(-|β|(|J||E|+|h||ι|)) ≤ Z ≤ 2^|ι| exp(|β|(|J||E|+|h||ι|))

def checkZBounds (label : String) (n : Nat) (edges : List (Nat × Nat))
    (J h β : Float) : IO Bool := do
  let Z := partitionFn n edges J h β
  let numEdges := edges.length.toFloat
  let bound := β.abs * (J.abs * numEdges + h.abs * n.toFloat)
  let lower := Float.exp (-bound)
  let upper := (2.0 ^ n.toFloat) * Float.exp bound
  if lower - 1e-10 <= Z && Z <= upper + 1e-10 then
    IO.println s!"  {label}: {lower} ≤ Z={Z} ≤ {upper} ✓"
    return true
  else
    IO.println s!"  FAIL: {label}: Z={Z} out of bounds [{lower}, {upper}]"
    return false

-- Free energy monotonicity in h

def checkFreeEnergyMonotoneH (label : String) (n : Nat) (edges : List (Nat × Nat))
    (J β h1 h2 : Float) : IO Bool := do
  let Z1 := partitionFn n edges J h1 β
  let Z2 := partitionFn n edges J h2 β
  let f1 := Float.log Z1 / n.toFloat
  let f2 := Float.log Z2 / n.toFloat
  if f1 - 1e-10 <= f2 then
    IO.println s!"  {label}: f({h1})={f1} ≤ f({h2})={f2} ✓"
    return true
  else
    IO.println s!"  FAIL: {label}: f({h1})={f1} > f({h2})={f2}"
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
  IO.println "--- GKS-I: ⟨σ^A⟩ ≥ 0 (ferromagnetic) ---"
  allPassed := allPassed && (← checkGKS1 "2-chain J=1 h=0.5 β=1" 2 graph2 1.0 0.5 1.0)
  allPassed := allPassed && (← checkGKS1 "2-chain J=1 h=0 β=1" 2 graph2 1.0 0.0 1.0)
  allPassed := allPassed && (← checkGKS1 "3-chain J=2 h=0.3 β=0.5" 3 graph3 2.0 0.3 0.5)
  allPassed := allPassed && (← checkGKS1 "triangle J=1 h=1 β=2" 3 triangle3 1.0 1.0 2.0)
  allPassed := allPassed && (← checkGKS1 "square J=0.5 h=0.3 β=1" 4 square4 0.5 0.3 1.0)
  allPassed := allPassed && (← checkGKS1 "square J=3 h=0 β=0.1" 4 square4 3.0 0.0 0.1)

  IO.println ""
  IO.println "--- GKS-II: ⟨σ^Aσ^B⟩ ≥ ⟨σ^A⟩⟨σ^B⟩ (ferromagnetic) ---"
  allPassed := allPassed && (← checkGKS2 "2-chain J=1 h=0.5 β=1" 2 graph2 1.0 0.5 1.0)
  allPassed := allPassed && (← checkGKS2 "2-chain J=1 h=0 β=1" 2 graph2 1.0 0.0 1.0)
  allPassed := allPassed && (← checkGKS2 "3-chain J=2 h=0.3 β=0.5" 3 graph3 2.0 0.3 0.5)
  allPassed := allPassed && (← checkGKS2 "triangle J=1 h=1 β=2" 3 triangle3 1.0 1.0 2.0)
  allPassed := allPassed && (← checkGKS2 "square J=0.5 h=0.3 β=1" 4 square4 0.5 0.3 1.0)
  allPassed := allPassed && (← checkGKS2 "square J=3 h=0 β=0.1" 4 square4 3.0 0.0 0.1)

  IO.println ""
  IO.println "--- FKG: ⟨fg⟩ ≥ ⟨f⟩⟨g⟩ for monotone f, g ---"
  -- Test with f = magnetization = Σ σ_i, g = σ_0 (both monotone)
  allPassed := allPassed && (← checkFKG "2-chain J=1 h=0.5 β=1" 2 graph2 1.0 0.5 1.0)
  allPassed := allPassed && (← checkFKG "triangle J=1 h=1 β=2" 3 triangle3 1.0 1.0 2.0)
  allPassed := allPassed && (← checkFKG "square J=0.5 h=0.3 β=1" 4 square4 0.5 0.3 1.0)

  IO.println ""
  IO.println "--- GKS-I violation (anti-ferromagnetic, J < 0) ---"
  allPassed := allPassed && (← checkGKS1Violation "2-chain J=-1 h=0 β=1" 2 graph2 (-1.0) 0.0 1.0)

  IO.println ""
  IO.println "--- GKS-II violation (anti-ferromagnetic, J < 0) ---"
  allPassed := allPassed && (← checkGKS2Violation "2-chain J=-1 h=0 β=1" 2 graph2 (-1.0) 0.0 1.0)

  IO.println ""
  IO.println "--- GHS: truncated3 ≤ 0 (ferromagnetic, h ≥ 0) ---"
  allPassed := allPassed && (← checkGHS "3-chain J=1 h=0.5 β=1" 3 graph3 1.0 0.5 1.0)
  allPassed := allPassed && (← checkGHS "triangle J=1 h=1 β=2" 3 triangle3 1.0 1.0 2.0)
  allPassed := allPassed && (← checkGHS "square J=0.5 h=0.3 β=1" 4 square4 0.5 0.3 1.0)

  IO.println ""
  IO.println "--- Cor 4.3.3: truncated4 ≤ 0 (h = 0) ---"
  allPassed := allPassed && (← checkCor433 "square J=1 β=1" 4 square4 1.0 1.0)
  allPassed := allPassed && (← checkCor433 "square J=0.5 β=2" 4 square4 0.5 2.0)

  IO.println ""
  IO.println "--- Odd correlation vanishing (h = 0) ---"
  allPassed := allPassed && (← checkOddVanish "2-chain J=1 β=1" 2 graph2 1.0 1.0)
  allPassed := allPassed && (← checkOddVanish "triangle J=2 β=0.5" 3 triangle3 2.0 0.5)
  allPassed := allPassed && (← checkOddVanish "square J=1 β=1" 4 square4 1.0 1.0)

  IO.println ""
  IO.println "--- Susceptibility ≥ 0 ---"
  allPassed := allPassed && (← checkSusceptibility "2-chain J=1 h=0.5 β=1" 2 graph2 1.0 0.5 1.0)
  allPassed := allPassed && (← checkSusceptibility "triangle J=1 h=0 β=2" 3 triangle3 1.0 0.0 2.0)
  allPassed := allPassed && (← checkSusceptibility "square J=0.5 h=0.3 β=1" 4 square4 0.5 0.3 1.0)

  IO.println ""
  IO.println "--- Magnetization monotone in h ---"
  allPassed := allPassed && (← checkMagnetizationMonotone "2-chain J=1 β=1" 2 graph2 1.0 1.0 0.0 0.5)
  allPassed := allPassed && (← checkMagnetizationMonotone "2-chain J=1 β=1" 2 graph2 1.0 1.0 0.5 1.0)
  allPassed := allPassed && (← checkMagnetizationMonotone "triangle J=1 β=2" 3 triangle3 1.0 2.0 0.0 1.0)

  IO.println ""
  IO.println "--- Correlation monotone in J ---"
  allPassed := allPassed && (← checkCorrelationMonotoneJ "2-chain h=0.5 β=1" 2 graph2 0.5 1.0 0.5 1.0)
  allPassed := allPassed && (← checkCorrelationMonotoneJ "2-chain h=0.5 β=1" 2 graph2 0.5 1.0 1.0 2.0)

  IO.println ""
  IO.println "--- Z bounds ---"
  allPassed := allPassed && (← checkZBounds "2-chain J=1 h=0.5 β=1" 2 graph2 1.0 0.5 1.0)
  allPassed := allPassed && (← checkZBounds "triangle J=1 h=1 β=2" 3 triangle3 1.0 1.0 2.0)
  allPassed := allPassed && (← checkZBounds "square J=0.5 h=0.3 β=1" 4 square4 0.5 0.3 1.0)

  IO.println ""
  IO.println "--- Free energy monotone in h ---"
  allPassed := allPassed && (← checkFreeEnergyMonotoneH "2-chain J=1 β=1" 2 graph2 1.0 1.0 0.0 0.5)
  allPassed := allPassed && (← checkFreeEnergyMonotoneH "2-chain J=1 β=1" 2 graph2 1.0 1.0 0.5 1.0)

  IO.println ""
  if allPassed then
    IO.println "=== All tests passed ==="
    return 0
  else
    IO.println "=== SOME TESTS FAILED ==="
    return 1
