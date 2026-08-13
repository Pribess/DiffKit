# DiffKit

DiffKit shows semantic call-tree changes instead of changed source lines. It is
Git-based by default, understands a single-file forest when asked, and has one
semantic analysis pipeline—there is no `--syntax`/`--semantic` mode split.

Rust and OCaml are implemented first. Language compilers keep their native
representations internally and emit only a compact semantic call graph to the
shared tree/diff/renderer. DiffKit is one library and one binary, not one crate
per language.

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
    --max-depth N     Maximum expanded call depth (default: 8)
-l, --language LANG   Override extension-based Rust/OCaml selection
```

Concrete generic arguments are always shown. Argument values/names are shown
by default; argument types are opt-in. Return types are not printed.

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
arguments, and direct return values. Calls to the same function are specialized
by their incoming dyn context, so `run_dyn(&Postgres)` does not acquire an `S3`
candidate merely because another caller passes one. A value entering through
an actual graph root is opaque; visibility (`pub`) by itself never means
“external value.” A join of proven local values and opaque input is partial,
while unsupported or externally opaque flow with no proven target is
unresolved. DiffKit never substitutes a component-wide RTA set for a known
receiver flow.

Closures retain the source variable and expose their body:

```text
run(order)
└─ persist(order) [closure#0]
   └─ write(value)
```

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
switch a Dune project to a weaker mode. Standalone `.ml` source sets still use
the same graph contract and conservative local/module resolution.

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

DiffKit builds every inferred graph-root tree. Functions not connected to a
main/library entry form additional detached trees, so their changes are not
lost. A shared changed subtree is repeated under each real root that reaches
it. Call graphs are may-call structure; runtime branch feasibility is not part
of the model.

## Source layout

```text
src/
  language/
    mod.rs       backend contract only
    rust.rs      syn labels + Cargo/rustc_public semantics
    ocaml.rs     OCaml labels + compiler-libs/function-value semantics
  model.rs       language-neutral symbols, calls, dispatch completeness
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
