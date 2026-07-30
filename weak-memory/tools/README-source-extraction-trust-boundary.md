# Treiber source-extraction trust boundary

`extract_treiber_source_trust_boundary.py` is a deliberately narrow,
explicitly trusted bridge from the current C source to normalized JSON and
Lean descriptors. It is **not** a proved C semantics frontend. In particular,
it does not prove Clang correct, formalize the C11 abstract machine, or prove
that executions of the C program refine the Lean control-flow model.

The extractor invokes the bundled Clang 18 frontend, checks the exact AST
shape of:

- `treiber_push`;
- `treiber_pop`;
- `treiber_is_empty`;
- the separate `treiber_init` initializer.

For the three public stack operations it records atomic operation kinds,
success and failure memory orders, weak compare-exchange loop behavior,
failure updates through the expected operand, non-atomic `node->next`
accesses, and return paths. It also checks the reclamation-free contract text
in `treiber.h`.

The extractor generates two synchronized artifacts:

```text
c/treiber.source-extraction-trust-boundary.json
WeakMemory/TreiberExtractedProgram.lean
```

Both carry the same compact program facts. The generated Lean module imports
the stable data schema from `WeakMemory/TreiberProgramDescriptor.lean` and
contains the SHA-256 digests, Clang version, and descriptor value consumed by
the formal development. Neither artifact contains timestamps or absolute
paths.

`WeakMemory/TreiberProgramRefinement.lean` proves that this generated
descriptor equals the compact descriptor computed from
`TreiberRA.Action.order`. It also proves precise component lemmas for
`ControlFlow.LocalStep`: per-attempt `next` accesses, expected-value updates,
spurious weak failures, retries, and response transitions. These are checks
against the existing Lean model, not a C semantics refinement theorem.

From the `weak-memory` directory, regenerate it with:

```sh
python3 tools/extract_treiber_source_trust_boundary.py
```

Check the committed descriptor without changing it with:

```sh
python3 tools/extract_treiber_source_trust_boundary.py --check
```

`--check` byte-compares both the JSON and generated Lean files. It exits
nonzero if Clang rejects the source, the AST has an unexpected shape, the
source hashes differ, the Clang version differs, or either normalized artifact
is not byte-for-byte current. A different Clang 18 executable can be selected
explicitly with `--clang`.

Passing this check establishes only that the checked-in artifacts match this
trusted extractor and the pinned source. Lean's kernel separately checks the
generated descriptor's equality and component lemmas against the formal model.
The trusted AST extraction/rendering remains one boundary; the absence of a
theorem connecting actual C/RC11 executions to accepted raw validator inputs
is the other. Closing the latter requires a proved C semantics frontend or an
explicitly trusted execution translator with a precisely stated contract.
