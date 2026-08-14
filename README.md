# DiffKit

DiffKit turns source changes into semantic call-tree diffs. It analyzes both
sides of a Git or file comparison, follows calls from every graph root, and
keeps the paths affected by the change.

Rust and OCaml are supported today. Each language backend uses its compiler's
semantic representation and emits a compact call graph for the shared diff and
renderer.

Under the hood, DiffKit resolves Rust calls from Cargo-selected
`rustc_public` MIR and OCaml calls from Dune `.cmt` Typedtrees, propagates
generics, trait-object provenance, and function values per caller context, then
aligns complete call forests by semantic symbol and call-site identity. The
result combines compiler-accurate targets, explicit dynamic-dispatch
completeness, source-shaped output, and fast repeat runs through Git-aware
semantic caches.

![DiffKit colored terminal output](https://raw.githubusercontent.com/Pribess/DiffKit/main/docs/terminal.svg)

## Installation

DiffKit currently supports macOS and Linux. The crates.io package is named
`diffkit-cli`; the installed executable is `diffkit`.

Rust analysis uses compiler APIs from the pinned `nightly-2026-05-06`
toolchain:

```sh
rustup toolchain install nightly-2026-05-06 \
  --profile minimal \
  --component rustc-dev \
  --component llvm-tools-preview
cargo +nightly-2026-05-06 install --locked diffkit-cli
```

To install from source:

```sh
git clone https://github.com/Pribess/DiffKit.git
cd DiffKit
cargo install --locked --path .
```

Rust projects require no additional tools. OCaml projects get compiler-backed
analysis when OCaml and Dune are available in the active environment.

## Quick start

Run `diffkit` inside a Git repository to compare `HEAD` with the current
worktree, including staged, unstaged, and untracked files:

```sh
cd your-project
diffkit
```

Common commands:

```sh
# Limit the Git comparison with a pathspec
diffkit -- src/service.rs

# Compare one commit with its first parent
diffkit git 71b148d

# Compare two revisions
diffkit git v1.2.0 v1.3.0

# Show the semantic call forest for one file
diffkit file src/service.rs

# Compare two file-scoped forests
diffkit file old.rs new.rs

# Select a concrete generic entry
diffkit file src/service.rs -e 'run<Postgres>'

# Add argument types and use plain output
diffkit --types --color plain

# Show cache timings and resolution evidence
diffkit --verbose
```

## Examples

Concrete generic paths stay separate:

```diff
  run<Postgres>(Postgres)
  └─ Postgres::save()
+    └─ sql::commit()

  run<S3>(S3)
  └─ S3::save()
+    └─ aws::put_object()
```

Dynamic-dispatch candidates use double-line edges and preserve incomplete
resolution:

```diff
  dyn Store::save() [partial]
  ╠═ Postgres::save()
+ ╠═ S3::save()
  ╚═ … unresolved targets
```

OCaml keeps its application syntax:

```diff
  run order
  ├─ validate order
  ├─ Store.save order
+ └─ audit order
```

## Command reference

```text
diffkit [OPTIONS] [-- PATHSPEC...]
diffkit git [REV | BEFORE AFTER] [OPTIONS] [-- PATHSPEC...]
diffkit file FILE [OPTIONS]
diffkit file BEFORE AFTER [OPTIONS]
```

Git comparisons:

- `diffkit` compares `HEAD` with the current worktree.
- `diffkit git REV` compares `REV^` with `REV`.
- `diffkit git BEFORE AFTER` compares two explicit revisions.
- `-- PATHSPEC...` keeps full project context while selecting changes from the
  requested paths.

Options:

```text
-e, --entry SYMBOL    Select an entry; repeat for multiple entries
    --types           Add inferred or concrete argument types
    --color ansi      ANSI colors (default)
    --color plain     Plain text without terminal control sequences
    --max-depth N     Maximum displayed call depth (default: 8)
-l, --language LANG   Select Rust or OCaml explicitly
-v, --verbose         Show analysis, cache, timing, and resolution details
```

Argument expressions are visible in the default output. Concrete generic
arguments remain visible because they identify distinct call trees. `--types`
adds argument types to the same lines.

## Rust

DiffKit combines source-shaped labels with Cargo's real build graph and
`rustc_public` typed MIR. Generic instances and trait dispatch therefore follow
the concrete context established by their callers, including calls across
workspace crates.

```text
entry(order)
└─ run<Postgres>(&Postgres, order)
   ├─ validate(order)
   ├─ Postgres::save(order)
   │  ├─ sql::begin()
   │  └─ sql::commit()
   └─ finalize()
```

An open generic definition keeps its type parameter until a caller supplies a
concrete instance:

```text
run<T: Store>(storage)
└─ T::save()
```

An explicit entry can request a concrete instance that Cargo has not otherwise
instantiated:

```sh
diffkit file src/service.rs -e 'detached<Postgres>'
```

DiffKit performs that analysis in an isolated temporary workspace and maps the
result back to the original source locations.

### Dynamic dispatch

Double lines connect a dynamic call site to its resolved candidates:

```text
run(storage, order)
└─ dyn Store::save(order)
   ╠═ Postgres::save(order)
   ║  └─ sql::insert(order)
   ╚═ S3::save(order)
      └─ aws::put_object(order)
```

Candidate completeness is visible on the call site:

```text
dyn Store::save(order)
╚═ Postgres::save(order)

dyn Store::save(order) [partial]
╠═ Postgres::save(order)
╚═ … unresolved targets

dyn Store::save(order) [unresolved]
```

Trait-object provenance flows through MIR places, branches, arguments, return
values, aliases, and typed heap or container boundaries. Each incoming context
gets its own specialization, which keeps candidate sets local to the callers
that establish them.

Typed function-pointer calls have a separate marker:

```text
callback(value) [indirect]
```

`--verbose` reports evidence such as `exact-flow` or `closed-set`, together
with unresolved causes such as opaque input, external memory, and function
pointers.

### Closures, async, and recursion

Named and anonymous closures have compact lambda nodes whose children contain
their calls:

```text
run()
├─ λpersist()
│  └─ db::save()
└─ apply<λ#1>()
   └─ λ#1()
      └─ cache::save()
```

Closure identities remain stable across unrelated insertions. Closures inside
generic functions inherit the parent's concrete arguments, and async functions
retain the same source-level tree shape.

Recursive calls connect directly back to the active ancestor:

```text
a() ◀────┐
└─ b()   │
   └─────┘
```

The graph covers explicit source-level calls. Compiler-generated drop glue and
deref coercions are outside its current scope.

## OCaml

OCaml output keeps native application syntax:

```text
run order
├─ validate order
├─ Postgres.save order
│  └─ Sql.insert order
└─ finalize order
```

Local functions are represented as callable closure nodes:

```text
run order
└─ persist order [closure#0]
   └─ write order
```

Function values flow through parameters per connected caller context. Proven
targets use the same double-line relation as Rust dispatch, and joins with an
opaque value are marked `[partial]`.

For Dune projects, DiffKit runs `dune build @check`, reads generated `.cmt`
files through `compiler-libs.common`, and combines resolved `Path.t` identities
with source labels. The adapter is compiled against the active OCaml compiler
to match its Typedtree version. Standalone compilable `.ml` files use a
temporary `.cmt`; source-level module and function-value analysis remains
available when an OCaml compiler is not installed.

`--types` displays inferred curried argument types. Functions declared inside
functor bodies participate in the same call graph.

## Comparison model

Project analysis produces a forest rather than assuming a single entry point.
Compiler-provided roots are used when available, and inferred roots cover the
remaining connected components. Changed detached components therefore appear
as their own trees, while a changed shared subtree can appear below every root
that reaches it.

Both complete semantic graphs are compared before presentation depth is
applied. Unchanged roots disappear from the report, stable branches collapse to
one line of context, and a deeper change beyond `--max-depth` appears as:

```text
… changed below max depth
```

`diffkit file FILE` uses the surrounding project for semantic resolution and
sets the selected file as the expansion boundary. Comparing two files matches
roots by semantic identity and renders unmatched roots as added or removed
trees.

## Performance

Rust semantic endpoints are cached under `target/diffkit-semantic`. Cache keys
cover project inputs, compiler settings, Cargo and rustc identities, and the
DiffKit analyzer version. An unchanged endpoint can reuse its call graph
without another compiler run.

Git revisions are materialized with one archive operation. Worktree cache keys
hash Git-reported changed and untracked inputs, keeping cache checks proportional
to the active change set. Use `--verbose` to inspect hit/miss and timing data.

## Architecture

```text
src/
  language/
    mod.rs       backend registry and file/project contracts
    rust.rs      syn labels and Cargo/rustc_public semantics
    ocaml.rs     OCaml labels and compiler-libs/function-value semantics
  model.rs       semantic call graph, call-site identity, dispatch evidence
  graph.rs       root inference and cycle-safe forest expansion
  diff.rs        semantic tree alignment
  render.rs      tree, diff, and color rendering
  engine.rs      file and project orchestration
  git.rs         Git endpoints and isolated snapshots
  lib.rs
  main.rs        clap CLI and rustc wrapper entry
support/
  ocaml/extract.ml
```

A new language backend owns its parser or compiler representation and emits the
shared `SemanticCallGraph`. TypeScript and Zig support can therefore live in
`language/typescript.rs` and `language/zig.rs` while reusing graph comparison,
root handling, and rendering.

## Development

The repository pins the required nightly toolchain and components through
`rust-toolchain.toml`.

```sh
cargo test --all-targets
cargo clippy --all-targets --all-features -- -D warnings
cargo build --release
```
