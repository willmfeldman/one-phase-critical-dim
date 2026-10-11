/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

-- Standalone script, run with `lake env lean --run`; not part of any library.
-- Driver: `check.sh`. Adapted from `scripts/challenge_fingerprint.lean` of
-- EllipticBernoulli v0.3.0 (same author and license), with the project prefix changed.
public import Lean

open Lean

/-- Print a structural fingerprint of the given theorems and of every `OnePhaseDimension` or
`EllipticBernoulli` constant their statements depend on (types, definition values, inductive
shapes). Running this against the `Challenge` and the `Solution` environments and diffing the
outputs emulates Comparator's statement and definition-equality check. -/
partial def visit (env : Environment) (n : Name) (seen : IO.Ref NameSet) (out : IO.Ref (Array String)) :
    IO Unit := do
  if (← seen.get).contains n then return
  seen.modify (·.insert n)
  let some ci := env.find? n | out.modify (·.push s!"{n} MISSING"); return
  let ours := (`OnePhaseDimension).isPrefixOf n || (`EllipticBernoulli).isPrefixOf n
  let descend (e : Expr) : IO Unit := do
    for c in e.getUsedConstants do visit env c seen out
  if !ours then
    out.modify (·.push s!"{n} ext {hash ci.type}")
    return
  match ci with
  | .defnInfo v =>
    out.modify (·.push s!"{n} def {hash v.type} {hash v.value} {v.levelParams}")
    descend v.type; descend v.value
  | .thmInfo v =>
    out.modify (·.push s!"{n} thm {hash v.type} {v.levelParams}")
    descend v.type
  | .inductInfo v =>
    out.modify (·.push s!"{n} ind {hash v.type} {v.numParams} {v.numIndices} {v.ctors} {v.isRec}")
    descend v.type
    for c in v.ctors do visit env c seen out
  | .ctorInfo v =>
    out.modify (·.push s!"{n} ctor {hash v.type} {v.cidx} {v.numFields}")
    descend v.type
  | .opaqueInfo v =>
    out.modify (·.push s!"{n} opaque {hash v.type} {hash v.value}")
    descend v.type; descend v.value
  | _ =>
    out.modify (·.push s!"{n} other {hash ci.type}")
    descend ci.type

public unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | modName :: thms =>
    initSearchPath (← findSysroot)
    let mod := modName.toName
    let env ← importModules #[{ module := mod }] {} (loadExts := false)
    let seen ← IO.mkRef ({} : NameSet)
    let out ← IO.mkRef (#[] : Array String)
    for t in thms do visit env t.toName seen out
    for l in (← out.get).qsort (· < ·) do IO.println l
    return 0
  | _ => IO.eprintln "usage: Fingerprint <module> <theorem>..."; return 2
