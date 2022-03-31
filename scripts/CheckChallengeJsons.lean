/-
Copyright 2026 Google LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Lean

/-!
# Challenge configuration checker

Checks the Comparator challenge configurations in `QuantumComputationSpecs/ChallengeJsons`
against the specifications they refer to, following the rules in the `README.md` there. Run it
with:

    lake test

A *hole* is a definition whose body uses `sorry`, and a *target* is a theorem whose proof does.
-/

@[expose] public section

open Lean System

namespace CheckChallengeJsons

/-- The directory containing the challenge configurations. -/
def configDir : FilePath := "QuantumComputationSpecs" / "ChallengeJsons"

/-- The module prefix of the specifications. -/
def specsRoot : Name := `QuantumComputationSpecs

/-- The directory containing verified solutions. -/
def discoveriesDir : FilePath := "QuantumComputationDiscoveries"

/-- The module prefix of verified solutions. -/
def discoveriesRoot : Name := `QuantumComputationDiscoveries

/-- The keys of a configuration. -/
def configKeys : List String := ["challenge_module", "solution_module", "theorem_names",
  "definition_names", "permitted_axioms", "allow_disproofs"]

/-- The axioms a solution may use. -/
def standardAxioms : Array String := #["propext", "Quot.sound", "Classical.choice"]

/-- Whether the body or proof of `c` uses `sorry`. -/
def usesSorry (c : ConstantInfo) : Bool :=
  (c.value? (allowOpaque := true)).any (·.hasSorry)

/-- The module declaring `n`. -/
def moduleOf? (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).map (env.header.moduleNames[·]!)

/-- The holes that the statement `type` depends on, and the library declarations using `sorry`
that it depends on but which are not holes. Follows the types of library declarations, and the
bodies and constructors of those that are not holes. -/
def statementDeps (env : Environment) (holes : Array Name) (type : Expr) :
    Array Name × Array Name := Id.run do
  let mut todo := type.getUsedConstants
  let mut seen : NameSet := {}
  let mut used := #[]
  let mut stray := #[]
  repeat
    let some n := todo.back? | break
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some c := env.find? n | continue
    unless (moduleOf? env n).any (`QuantumComputationSpecs).isPrefixOf do continue
    todo := todo ++ c.type.getUsedConstants
    if holes.contains n then
      used := used.push n
      continue
    if usesSorry c then stray := stray.push n
    if let some v := c.value? then todo := todo ++ v.getUsedConstants
    if let .inductInfo v := c then todo := todo ++ v.ctors
  return (used, stray)

/-- Whether the hole sets `groups` are connected by the relation of sharing a hole. -/
def connected (groups : Array (Array Name)) : Bool := Id.run do
  let some first := groups[0]? | return true
  let mut reached := first
  let mut rest := groups.extract 1
  let mut progress := true
  while progress do
    let (linked, unlinked) := rest.partition (·.any reached.contains)
    reached := reached ++ linked.flatten
    rest := unlinked
    progress := !linked.isEmpty
  return rest.isEmpty

/-- Reads the field `key` of the configuration `j`. -/
def field (j : Json) (α : Type) [FromJson α] (key : String) : IO α :=
  IO.ofExcept (j.getObjValAs? α key)

/-- Checks the configuration at `path`, returning the errors found, the declarations it lists, and
any discovery file referenced by `solution_module`. Throws if the configuration cannot be read. -/
def checkConfig (env : Environment) (path : FilePath) :
    IO (Array String × Array Name × Option FilePath) := do
  let j ← IO.ofExcept <| Json.parse (← IO.FS.readFile path)
  let keys := (← IO.ofExcept j.getObj?).keys
  unless keys.length == configKeys.length && configKeys.all keys.contains do
    throw <| .userError s!"expected exactly the keys {configKeys}"
  let challenge ← field j String "challenge_module"
  let solution ← field j String "solution_module"
  let theorems := (← field j (Array String) "theorem_names").map String.toName
  let holes := (← field j (Array String) "definition_names").map String.toName
  let mod := challenge.toName
  unless specsRoot.isPrefixOf mod && mod != specsRoot && (env.getModuleIdx? mod).isSome do
    throw <| .userError s!"`{challenge}` is not a specification module"
  let mut errs := #[]
  let parts := (mod.replacePrefix specsRoot .anonymous).components.map toString
  let dir := parts.dropLast.foldl (· / ·) configDir
  unless path.parent == some dir && path.fileStem.any (·.startsWith parts.getLast!) do
    errs := errs.push s!"the configuration should be named `{dir / parts.getLast!}*.json`"
  let mut solFile? : Option FilePath := none
  if solution != challenge then
    let solMod := solution.toName
    let solParts := (solMod.replacePrefix discoveriesRoot .anonymous).components.map toString
    let solFile := (solParts.foldl (· / ·) discoveriesDir).addExtension "lean"
    let validName :=
      discoveriesRoot.isPrefixOf solMod && solMod != discoveriesRoot &&
      solMod.toString == solution &&
      solParts.dropLast == parts.dropLast &&
      solParts.getLast?.any fun stem =>
        stem.startsWith parts.getLast! && path.fileStem.any (·.startsWith stem)
    if !validName then
      let expectedPrefix := parts.foldl Name.str discoveriesRoot
      errs := errs.push <|
        s!"`solution_module` must equal `challenge_module` or be `{expectedPrefix}*` " ++
          "(a prefix of the configuration name)"
    else
      if ← solFile.pathExists then
        solFile? := some solFile
      else
        errs := errs.push s!"`solution_module` file `{solFile}` does not exist"
  let axioms ← field j (Array String) "permitted_axioms"
  unless axioms.size == standardAxioms.size && standardAxioms.all axioms.contains do
    errs := errs.push s!"`permitted_axioms` must be {standardAxioms.toList}"
  if (← field j Bool "allow_disproofs") && !holes.isEmpty then
    errs := errs.push "`allow_disproofs` must be false when there are definition holes"
  let names := theorems ++ holes
  if names.toList.eraseDups.length != names.size then
    errs := errs.push "a name is listed twice"
  unless theorems.any (·.toString.endsWith "_correctness") do
    errs := errs.push "no `*_correctness` theorem is listed"
  let isOpenIn (n : Name) (p : ConstantInfo → Bool) : Bool :=
    (env.find? n).any fun c => p c && usesSorry c && moduleOf? env n == some mod
  for n in holes do
    unless isOpenIn n (·.isDefinition) do
      errs := errs.push s!"`{n}` is not a definition of `{mod}` whose body uses `sorry`"
  let mut groups := #[]
  for n in theorems do
    unless isOpenIn n (·.isTheorem) do
      errs := errs.push s!"`{n}` is not a theorem of `{mod}` whose proof uses `sorry`"
      continue
    let some c := env.find? n | continue
    let (used, stray) := statementDeps env holes c.type
    for s in stray do
      errs := errs.push s!"`{n}` depends on `{s}`, which uses `sorry` but is not a listed hole"
    groups := groups.push used
  for n in holes do
    unless groups.any (·.contains n) do
      errs := errs.push s!"no listed theorem depends on the hole `{n}`"
  unless connected groups do
    errs := errs.push "some listed theorems share no hole with the others; split the configuration"
  return (errs, names, solFile?)

end CheckChallengeJsons

open CheckChallengeJsons in
/-- Checks all challenge configurations, returning `1` if any check fails. -/
def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `QuantumComputationSpecs }] {}
  let paths := ((← configDir.walkDir).filter (·.extension == some "json")).qsort
    (·.toString < ·.toString)
  let mut errors := #[]
  let mut listed : NameSet := {}
  let mut solFiles : Array FilePath := #[]
  for path in paths do
    try
      let (errs, names, solFile?) ← checkConfig env path
      errors := errors ++ errs.map (s!"{path}: " ++ ·)
      listed := names.foldl NameSet.insert listed
      if let some solFile := solFile? then
        solFiles := solFiles.push solFile
    catch e =>
      errors := errors.push s!"{path}: {e}"
  if ← discoveriesDir.pathExists then
    let discFiles :=
      ((← discoveriesDir.walkDir (enter := fun p => pure (p.fileName != some "Solution"))).filter
        (·.extension == some "lean")).qsort (·.toString < ·.toString)
    for f in discFiles do
      unless solFiles.contains f do
        errors := errors.push
          s!"{f}: no challenge configuration has `solution_module` pointing to this file"
  for mod in env.header.moduleNames, data in env.header.moduleData do
    unless specsRoot.isPrefixOf mod do continue
    for c in data.constants do
      unless c.name.isInternalDetail || !usesSorry c || listed.contains c.name do
        errors := errors.push
          s!"{mod}: `{c.name}` uses `sorry` but no challenge configuration lists it"
  for e in errors do
    IO.eprintln s!"error: {e}"
  if errors.isEmpty then
    IO.println s!"All {paths.size} challenge configurations are consistent with the specifications."
  return if errors.isEmpty then 0 else 1
