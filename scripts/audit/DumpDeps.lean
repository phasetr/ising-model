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

/-- The user-facing name of a constant.

A `private` declaration is stored as `_private.<module>.<hash>.IsingModel.foo`, so
filtering on the `IsingModel` prefix alone drops every private consumer -- and a
consumer the cross-check cannot see is exactly the blind spot this file exists to
close. -/
def userName (n : Name) : Name := Lean.privateToUserName n

run_cmd do
  let env ← Lean.getEnv
  let root : Name := `IsingModel
  let mut out : Array String := #[]
  for (name, info) in env.constants.toList do
    let src := userName name
    if root.isPrefixOf src && !src.isInternal then
      let used := info.type.getUsedConstants ++
        (info.value?.map Expr.getUsedConstants).getD #[]
      let deps := used.filterMap fun dep =>
        let tgt := userName dep
        if root.isPrefixOf tgt && tgt != src && !tgt.isInternal then some tgt else none
      let deps := deps.toList.eraseDups
      if !deps.isEmpty then
        out := out.push s!"{src}\t{String.intercalate " " (deps.map toString)}"
  for line in out do
    IO.println line
