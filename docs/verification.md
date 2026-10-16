# Reproducing the verification

The public repository contains 712 Lean modules, including the entry point.
The source hashes and declaration inventory are in
[`verification/modules.json`](../verification/modules.json). All mathematical
Lean files retain their checked declarations and proofs.

## Pinned environment

The toolchain is Lean 4.32.2. Lake fetches `harmonicMaps` at
`f3a3097025ab9ddd956859600211d1d4edf0654e` and Mathlib at
`905b95818eb32af7874a58b427f50c1711a5e96c`, together with the transitive Git
revisions in `lake-manifest.json`. An adjacent research checkout, source
symlinks and package overrides are unnecessary.

From a fresh checkout, with `elan` and Python 3.9 or later installed:

```sh
lake exe cache get
lake build
python3 scripts/check_sources.py
python3 scripts/check_statements.py
python3 scripts/check_axioms.py
LEAN_NUM_THREADS=2 lake --no-build env leanchecker StratificationTheory -v
```

The Mathlib command obtains dependency artifacts. The build compiles the
project and any required upstream modules. The inspection commands use
`--no-build`, so they inspect those compiled artifacts without silently
rebuilding dependencies. Keep the committed toolchain and lockfile.

## What each check establishes

| Check | Exact scope |
|---|---|
| `lake build` | The complete `StratificationTheory.*` library, including its public entry module |
| `check_sources.py` | Exact 712-source inventory and hashes; module headers; 1500-line limit; public exports; absence of unfinished proofs, project axioms, native trust bypasses and resource overrides; meaning-carrying definition files; manuscript and build/tool fingerprints; clean pinned Git dependency sources |
| `check_statements.py` | The exact public-import closure and Main-only visibility of all 493 registered public names; complete elaborated kernel-type fingerprints for 42 source-facing interfaces; corresponding provider types |
| `check_axioms.py` | Transitive axiom dependencies of all 1349 ordinary and source-facing registered exports, permitting only `propext`, `Classical.choice` and `Quot.sound` |
| `leanchecker StratificationTheory -v` | Compiled-declaration replay for every project module through the pinned Lean kernel, including private implementation declarations |

The 42 source-facing declarations consist of 29 theorems and 13 definitions.
The 29 provider results are compared with the complete theorem interfaces.
Three pairs contain corresponding declaration-local generated proof constants:
the checker allows only those corresponding names and also checks their closed
propositions and complete types for kernel definitional equality. No other
statement normalization is used. The axiom check follows provider results
transitively through the source-facing proofs.

Definition meanings are protected by complete file hashes and the declared
definition closures, as well as the full project source inventory. Kernel-type
fingerprints preserve universe parameters, binder names, visibility and the
complete expression structure, excluding source-position metadata. The encoder
is the one used for the checked mathematical interfaces.

Kernel replay uses Lean's compiled-declaration checker. It is an additional
replay of the compiled terms, rather than a separately implemented external
proof assistant. Hash checks establish equality to the supplied baselines;
mathematical meaning is given by the actual declarations, definitions and
source explanation.

## Continuous integration

The [build workflow](../.github/workflows/build.yml) runs the build and all three
Python checks. The [kernel workflow](../.github/workflows/kernel.yml) additionally
runs compiled-declaration replay. They run on pushes to `main`, pull requests
and manual dispatch, use separate build-cache keys, and check that the pinned
configuration is unchanged. Hosted jobs reclaim disk space before building.
The badges on the README show GitHub's actual workflow results.

The public verification baselines are intended for maintenance in this
repository. Changes to a mathematical source, statement, definition, dependency
or checker require review and an explicit corresponding baseline update.
The detailed mathematical scope and source corrections are described in
[the mathematical guide](stratification.md).

The local release checks are recorded in
[`verification/release-validation.json`](../verification/release-validation.json),
with an independent review in
[`verification/release-audit.json`](../verification/release-audit.json).
These records certify the identified local sources and checks. The workflow
pages report the separate CI results for each published commit.
