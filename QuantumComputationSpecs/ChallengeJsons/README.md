# Challenge configurations

Each JSON file in this directory is a [Comparator](https://github.com/leanprover/comparator)
challenge configuration for a specification in `QuantumComputationSpecs`.

**Every specification MUST have challenge configurations**: each `sorry`-ed theorem and
definition of a specification module must be listed in at least one configuration. CI enforces
this (see [Checking](#checking)).

## Writing configurations

Configurations are written by hand, in the same PR that adds or changes the specification. They
are not generated.

`<Folder>/<Spec><Suffix>.json` configures the module `QuantumComputationSpecs.<Folder>.<Spec>`:

| Field | Value |
| --- | --- |
| `challenge_module` | The specification module (`QuantumComputationSpecs.<Folder>.<Spec>`). |
| `solution_module` | A solution module `QuantumComputationDiscoveries.<Folder>.<Spec>*` (whose stem is a prefix of `<Spec><Suffix>`) if solved in `QuantumComputationDiscoveries/`, otherwise equal to `challenge_module`. |
| `theorem_names` | The `sorry`-ed theorems to prove, fully qualified. |
| `definition_names` | The holes the solution fills in: exactly the `sorry`-ed definitions that the statements of `theorem_names` depend on. |
| `permitted_axioms` | `["propext", "Quot.sound", "Classical.choice"]` |
| `allow_disproofs` | `false`. Required when there are holes, since otherwise a solution could fill a hole with a bad definition and disprove the target. |

## One configuration per claim

A cost bound on its own is met by a trivial program, so every configuration lists the
`*_correctness` theorem. A specification with several cost theorems gets one configuration per
cost theorem, for example:

| Configuration | `theorem_names` |
| --- | --- |
| `GroverFindAllRelCost.json` | `groverFindAll_correctness`, `groverFindAllCells_nonempty`, `groverFindAllCells_mem_grid`, `groverFindAll_rel_cost` |
| `GroverFindAnyRelCost.json` | `groverFindAny_correctness`, `groverFindAnyCells_nonempty`, `groverFindAnyCells_mem_grid`, `groverFindAny_rel_cost` |

If a cost theorem bounds another hole rather than the program, the theorem constraining that hole
is listed too.

## Checking

Run

```bash
lake test
```

This checks every configuration against its specification: the fields and file name above, that
each listed theorem or definition belongs to the module and uses `sorry`, that a `*_correctness`
theorem is listed, that the holes are exactly those the theorems depend on, and that theorems
sharing no hole are not bundled together. It also checks that every `sorry`-ed declaration of a
specification and every solution module in `QuantumComputationDiscoveries/` is listed somewhere. CI
runs it on every push.
