# DiffKit

DiffKit is an experimental AST-aware structural diff engine. Its current
vertical slices parse Rust and OCaml source snapshots, build function call
trees, and render additions and removals in a `git diff`-shaped tree.

Rust has two analysis modes:

- the default syntax mode accepts incomplete source and resolves only
  unambiguous names;
- `--semantic` compiles standalone `.rs` snapshots with `rustc_public`, walks
  typed MIR, and resolves concrete generic and trait-call instances.

```sh
cargo run -- examples/rust/before.rs examples/rust/after.rs -e checkout
```

```diff
rustdiff examples/rust/before.rs → examples/rust/after.rs

  checkout(total)
- ├─ validate(total)
+ ├─ prepare(total)
+ │  ├─ validate(total)
+ │  └─ reserve()
  ├─ charge(total)
- └─ receipt()
```

Concrete Rust dispatch is visible in the tree instead of being left as the
receiver variable from source:

```sh
cargo run -- \
  examples/rust-semantic/before.rs \
  examples/rust-semantic/after.rs \
  --semantic -e 'run<Postgres>' -e 'run<S3>'
```

```diff
rustdiff examples/rust-semantic/before.rs → examples/rust-semantic/after.rs

  run<Postgres>(storage, order)
  ├─ validate(order)
  ├─ Postgres::save(order)
+ │  ├─ sql::begin()
  │  ├─ sql::insert(order)
+ │  └─ sql::commit()
  └─ finalize(order)

  run<S3>(storage, order)
  ├─ validate(order)
  ├─ S3::save(order)
  │  ├─ aws::sign(order)
+ │  └─ aws::put_object(order)
  └─ finalize(order)
```

OCaml applications keep OCaml syntax rather than being forced into Rust-like
parentheses:

```sh
cargo run -- examples/ocaml/before.ml examples/ocaml/after.ml -e run
```

```diff
ocamldiff examples/ocaml/before.ml → examples/ocaml/after.ml

  run order
  ├─ validate order
  ├─ Postgres.save order
+ │  ├─ Sql.begin_tx order
  │  ├─ Sql.insert order
+ │  └─ Sql.commit order
  └─ finalize order
```

In syntax mode, both input paths may be individual source files or
directories. Rust semantic mode currently accepts standalone compilable
`.rs` files. When `--entry` is omitted, exported entry candidates whose
expanded call trees changed are selected. A concrete generic entry such as
`-e 'run<Postgres>'` is instantiated for analysis even when no source caller
already creates that instance.

The CLI infers Rust from `.rs` and OCaml from `.ml`/`.mli`. Mixed-language
directories require an explicit `--language rust` or `--language ocaml`.

The CLI and renderer API use ANSI colors by default: additions are green and
removals are red. Use `--color plain` for files, snapshots, or consumers that
must not receive terminal escape sequences. `--color ansi` selects the default
mode explicitly.

The pinned nightly toolchain installs `rustc-dev` and LLVM tools, and
`.cargo/config.toml` enables dynamic compiler-library linking required by
`rustc_public`. The build script embeds the active sysroot library path so the
built `diffkit` binary can also run directly outside `cargo run`.

## Initial architecture

- `language::LanguageFrontend`: parser-specific ASTs stay inside `rust.rs` and
  `ocaml.rs` and are lowered into common IR.
- `model`: semantic symbol keys are separate from language-owned `CallLabel`s.
  Rust emits `save(order)` while OCaml emits `save order`.
- `graph`: conservative name resolution and cycle-safe call tree expansion.
- `diff`: LCS alignment uses semantic keys; changed call-site arguments are
  represented as modified labels without turning labels into symbol identity.
- `render`: language-independent tree branches, diff markers, and colors. It
  consumes labels and contains no Rust/OCaml syntax branches.
- `engine`: source-set loading and changed-entry inference.

The current OCaml slice uses `tree-sitter-ocaml` for function/application spans
and exact source labels. `CallSite::target` is the semantic-resolution seam for
the `ocaml-index` adapter; until that adapter is connected, OCaml resolution is
conservative and limited to unambiguous source paths. Rust semantic mode fills
that same field from the concrete `rustc_public::mir::mono::Instance` selected
for each explicit source call.
