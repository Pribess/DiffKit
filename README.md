# DiffKit

DiffKit shows semantic call-tree changes instead of changed source lines. It is
Git-based by default, understands a single-file forest when asked, and has one
semantic analysis pipeline—there is no `--syntax`/`--semantic` mode split.

Rust and OCaml are implemented first. Language compilers keep their native
representations internally and emit only a compact semantic call graph to the
shared tree/diff/renderer. DiffKit is one library and one binary, not one crate
per language.

## Installation

DiffKit currently supports macOS and Linux. Rust analysis uses compiler APIs
from the pinned `nightly-2026-05-06` toolchain, including the `rustc-dev`
component:

```sh
rustup toolchain install nightly-2026-05-06 \
  --profile minimal \
  --component rustc-dev \
  --component llvm-tools-preview
cargo +nightly-2026-05-06 install --locked diffkit
```

To install the current source checkout instead:

```sh
git clone https://github.com/Pribess/DiffKit.git
cd DiffKit
cargo install --locked --path .
```

Rust-only projects need no additional tools. For compiler-backed OCaml
analysis, install OCaml and Dune in the active environment; DiffKit compiles its
small `compiler-libs.common` adapter against that OCaml compiler at runtime.

## Quick start

Run DiffKit inside a Git repository to compare `HEAD` with the complete current
worktree:

```sh
cd your-project
diffkit
```

Common forms are:

```sh
# Only changes selected by a Git pathspec
diffkit -- src/service.rs

# One commit against its first parent
diffkit git 71b148d

# Two explicit revisions
diffkit git v1.2.0 v1.3.0

# Display the semantic forest rooted in one source file
diffkit file src/service.rs

# Compare two files and select a concrete generic entry
diffkit file old.rs new.rs -e 'run<Postgres>'

# Add argument types, remove ANSI colors, and inspect cache/resolution details
diffkit --types --color plain --verbose
```

The first Rust project analysis runs Cargo and `rustc_public`; subsequent runs
reuse semantic endpoint caches under `target/diffkit-semantic`. DiffKit never
modifies the analyzed working tree.

## CLI

```text
diffkit [OPTIONS] [-- PATHSPEC...]
diffkit git [REV | BEFORE AFTER] [OPTIONS] [-- PATHSPEC...]
diffkit file FILE [OPTIONS]
diffkit file BEFORE AFTER [OPTIONS]
```

Git forms mean:

- `diffkit`: `HEAD` versus the current worktree, including staged, unstaged,
  and untracked files.
- `diffkit git REV`: `REV^` versus `REV`.
- `diffkit git BEFORE AFTER`: two explicit Git revisions.
- `-- PATHSPEC...`: analyze the full project context but restrict the after
  snapshot to changes in those paths.

The old positional snapshot form is intentionally absent. Use `diffkit file`
for files and `diffkit git` for revisions.

Useful options:

```text
-e, --entry SYMBOL    Select an entry; repeat for multiple entries
    --types           Put inferred/concrete argument types on the same line
    --color ansi      ANSI colors (default)
    --color plain     No terminal control sequences
    --max-depth N     Maximum displayed call depth (default: 8)
-l, --language LANG   Override extension-based Rust/OCaml selection
-v, --verbose         Show analysis progress, cache hit/miss, and timings
```

Concrete generic arguments that select an analyzed local specialization are
always shown. External leaves keep source turbofish arguments and closure
identity such as `filter_map<λ#1>`, but omit other rustc-only implementation
details such as `iter<impl [T]>`. Argument values/names are shown by default,
argument types are opt-in, and return types are not printed. Normal output
contains no analysis-progress line.

## Rust examples

```sh
diffkit file src/service.rs --color plain
```

```text
src/service.rs

  entry(order)
  └─ run<Postgres>(&Postgres, order)
     └─ Postgres::save(order)
```

`file FILE` uses the surrounding Cargo project to resolve that leaf, but does
not expand a function body located outside `FILE`. Comparing two files compares
two forests. A root with the same semantic identity is diffed internally; an
unmatched old root is a removed tree and an unmatched new root is an added
tree. DiffKit does not guess that differently named roots are renames.

An unobserved generic can be requested explicitly:

```sh
diffkit file src/service.rs -e 'detached<Postgres>'
```

DiffKit makes a temporary workspace copy, injects a hidden instantiation seed
in the declaring module, runs Cargo/rustc, removes the seed nodes, and maps
source locations back to the original project. The working tree is untouched.

An uninstantiated generic is still represented from its source body. Its open
type parameter is kept on the tree until a connected caller provides a concrete
context:

```text
run<T: Store>(storage)
└─ T::save()
```

Concrete contexts are propagated through workspace-crate calls, so a root in
one crate can specialize a generic body or trait-object receiver declared in
another analyzed crate.

Trait-object calls use double lines only for the dispatch relation:

```text
run(storage, order)
└─ dyn Store::save(order)
   ╠═ Postgres::save(order)
   ║  └─ sql::insert(order)
   ╚═ S3::save(order)
      └─ aws::put_object(order)
```

Resolution has three explicit states:

```text
dyn Store::save(order)
╚═ Postgres::save(order)

dyn Store::save(order) [partial]
╠═ Postgres::save(order)
╚═ … unresolved targets

dyn Store::save(order) [unresolved]
```

`… unresolved targets` appears only for a partial result. Rust trait-object
provenance is propagated through MIR places, control-flow joins, direct
arguments, direct return values, aliases, and typed heap/container boundaries.
Calls to the same function are specialized by their incoming dyn context, so
`run_dyn(&Postgres)` does not acquire an `S3` candidate merely because another
caller passes one. A value entering through an actual graph root is opaque;
visibility (`pub`) by itself never means “external value.” A join of proven
local values and opaque input is partial, while unsupported or externally
opaque flow with no proven target is unresolved. DiffKit never substitutes a
component-wide RTA set for a known receiver flow.

A typed function-pointer call is distinct from an unknown name:

```text
callback(value) [indirect]
```

With `--verbose`, dynamic and indirect sites also report their evidence
(`exact-flow` or `closed-set`) and structured unresolved causes such as opaque
input, external memory, or a function pointer. Ordinary calls to external
libraries remain normal leaves and do not flood these diagnostics.

Closures retain the source variable and expose their body:

```text
run(order)
└─ λpersist(order)
   └─ write(value)
```

A closure expression passed to a generic call becomes part of that concrete
call identity instead of being serialized into one source line:

```text
├─ values.iter()
├─ filter_map<λ#1>()
└─ collect()
```

Distinct anonymous closures remain distinct concrete instances and connect to
their own bodies:

```text
run()
├─ apply<λ#1>()
│  └─ λ#1()
│     └─ db::save()
└─ apply<λ#2>()
   └─ λ#2()
      └─ cache::save()
```

A named closure inside a generic parent inherits the parent's concrete
arguments, for example `λsave<Postgres>()`. Async closures use the same lambda
shape; polling machinery remains hidden. Internal closure identities are
structural, while `λ#N` is only a source-facing display label, so inserting an
unrelated closure does not turn an existing closure subtree into a removal and
addition.

Recursion is a real back-edge, not a repeated fake subtree:

```text
a() ◀────┐
└─ b()   │
   └─────┘
```

Async functions use source-logical calls. Poll/runtime machinery is not shown.
Implicit calls such as drops and deref coercions are intentionally outside the
call graph.

## OCaml examples

OCaml labels stay in OCaml application syntax:

```text
run order
├─ validate order
├─ Postgres.save order
│  └─ Sql.insert order
└─ finalize order
```

Local functions are explicit closure nodes:

```text
run order
└─ persist order [closure#0]
   └─ write order
```

Function parameters are propagated per connected call context. Two callers
that pass different functions no longer contaminate one another's candidate
sets. A proven function value is a double-line candidate; a single flow that
joins proven and opaque values is partial and uses the same
`… unresolved targets` tail. A root-only opaque parameter and an object method
with no proven receiver target are `[unresolved]`.

For a Dune project, DiffKit runs `dune build @check`, reads the generated
`.cmt` files with the active switch's official `compiler-libs.common`
(`Cmt_format`/Typedtree), and merges resolved `Path.t` identities with source
labels. The small OCaml adapter is compiled against the active compiler because
Typedtree is deliberately version-coupled. Missing `dune`/`ocamlc` or an
incompatible compiler-libs API is an analysis error; DiffKit does not silently
switch a Dune project to a weaker mode. For standalone compilable `.ml` files,
the same compiler-libs adapter is used through a temporary `.cmt`; inferred
curried argument types are available to `--types`. If no OCaml compiler is
installed, standalone source sets retain conservative local/module and
function-value resolution. Functions nested in functor bodies are included.

## How project analysis works

Rust project flow:

```text
Git/file snapshot
  → Cargo workspace/feature/target selection
  → DiffKit as RUSTC_WORKSPACE_WRAPPER
  → rustc_public typed MIR + monomorphized instances/vtables
  → source-shaped labels and spans
  → semantic call forest
```

OCaml project flow:

```text
Git/file snapshot
  → Dune @check
  → .cmt Typedtree through compiler-libs
  → resolved paths + function-value flow
  → source-shaped labels and spans
  → semantic call forest
```

DiffKit builds every backend-declared or inferred graph-root tree. Functions
not connected to a main/library entry form additional detached trees, so their
changes are not lost. A shared changed subtree is repeated under each real root
that reaches it. Call graphs are may-call structure; runtime branch feasibility
is not part of the model. Both complete semantic graphs are compared; roots
with no change are removed from the report, and unchanged descendants are
collapsed to one line of context around changed paths. `--max-depth` is applied
only after that comparison, so a deeper change is retained as
`… changed below max depth` instead of being reported as no change.

Rust semantic results are cached per before/after endpoint under
`target/diffkit-semantic`. The cache key includes project inputs, relevant
compiler environment, rustc/Cargo identity, and the DiffKit analyzer identity.
An unchanged endpoint skips Cargo and `rustc_public` entirely; when only the
worktree changes, the revision endpoint remains a cache hit. Use `--verbose`
to inspect hit/miss and timing information. Revision snapshots are materialized
with one Git archive operation, and worktree snapshot fingerprints hash only
Git-reported changed/untracked inputs instead of rescanning generated trees.

## Source layout

```text
src/
  language/
    mod.rs       backend registry + file/project contracts
    rust.rs      syn labels + Cargo/rustc_public semantics
    ocaml.rs     OCaml labels + compiler-libs/function-value semantics
  model.rs       language-neutral semantic call graph, edge identity, evidence
  graph.rs       root inference and cycle-safe forest expansion
  diff.rs        semantic-key tree alignment
  render.rs      tree/diff/color rendering; no language syntax branches
  engine.rs      file/project orchestration
  git.rs         Git endpoints and isolated snapshots
  lib.rs
  main.rs        clap CLI and rustc-wrapper entry
support/
  ocaml/extract.ml
```

Adding TypeScript or Zig means adding `language/typescript.rs` or
`language/zig.rs` that uses that compiler's own semantic representation and
emits the same small call-graph result. It does not mean introducing a shared
compiler AST/IR.

## Building

The pinned nightly installs `rustc-dev`, LLVM tools, rustfmt, and clippy.
`.cargo/config.toml` uses dynamic compiler libraries, and `build.rs` embeds the
active sysroot library path so the resulting binary can run outside
`cargo run`.

```sh
cargo test --all-targets
cargo clippy --all-targets -- -D warnings
cargo build --release
```
