/-
Dump the *elaborated* dependency graph of the `IsingModel` library, one line per
constant:

```
<constant name><TAB><space-separated IsingModel constants it uses>
```

Run with `lake env lean scripts/audit/DumpDeps.lean` on a green build; it is the
`--lean` phase of `scripts/dead_candidate_scan.py`.

This is the one instrument that sees what a textual scan structurally cannot: a
lemma used only through a `simp` set, found by `exact?`, referred to under an
`open`-shortened name, or introduced by a tactic still appears here, because the
constants are read off the elaborated proof term. It is deliberately *not* the
primary instrument: it cannot see the documentation channel at all, it needs a
full build (unavailable on the half-deleted tree where the question is asked),
and it reports `u → v` without a use site. Its job is to keep the cheap text
scan honest -- a consumer that Lean sees and the text scan misses is a scanner
bug, not a judgement call.
-/
import IsingModel

open Lean

run_cmd do
  let env ← Lean.getEnv
  let root : Name := `IsingModel
  let mut out : Array String := #[]
  for (name, info) in env.constants.toList do
    if root.isPrefixOf name && !name.isInternal then
      let used := info.type.getUsedConstants ++
        (info.value?.map Expr.getUsedConstants).getD #[]
      let deps := used.filter fun dep => root.isPrefixOf dep && dep != name && !dep.isInternal
      let deps := deps.toList.eraseDups
      if !deps.isEmpty then
        out := out.push s!"{name}\t{String.intercalate " " (deps.map toString)}"
  for line in out do
    IO.println line
