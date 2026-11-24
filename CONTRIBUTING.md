# Contributing

Contributions are welcome: new results from the sources, corrections, simpler proofs, and
reports of statements that are wrong or hard to use. For anything larger than a small fix, open
an issue first to agree on the statement and on where it goes.

## Setting up

```
git clone https://github.com/dvillacis/lean-variational
cd lean-variational
lake exe cache get
lake build
```

`lake exe cache get` downloads the compiled Mathlib; without it, Mathlib is compiled locally,
which takes hours. The Lean version is fixed by `lean-toolchain`.

## What a change must satisfy

Changes go through pull requests against `master`. CI runs the checks below, and each can be
run locally.

| Check | Command |
|---|---|
| The library builds with no warnings | `lake build` |
| The root file imports every module | `lake exe mk_all --check` (`lake exe mk_all` to fix) |
| The tests build | `lake test` |
| The README example is the tested one | `python3 scripts/check_readme.py` |
| Environment linters of Batteries | `lake lint` |
| Every declaration has a docstring | `lake env lean scripts/LintDocs.lean` |
| No `sorry` and no new axiom | `lake env lean scripts/AuditAxioms.lean` |

No `sorry` is merged, and no declaration may depend on an axiom beyond `propext`,
`Classical.choice` and `Quot.sound`.

## Conventions

The mathematical conventions (dual elements for normals and subgradients, the setting of each
construction, extended-real functions) are in the "Conventions" section of the
[README](README.md#conventions). New material should follow them.

**Style.** The library follows the
[Mathlib style guide](https://leanprover-community.github.io/contribute/style.html) and
[naming conventions](https://leanprover-community.github.io/contribute/naming.html); Mathlib's
style linters are enabled and their warnings fail CI. Lines have at most 100 characters.

**Files.** Each file starts with the copyright header and a module docstring that says what the
file contains, cites the source, and lists the main results. Declarations live in the namespace
`VariationalAnalysis`.

**Docstrings and citations.** Every definition, structure, instance and theorem has a
docstring. A result taken from one of the sources cites it with its number, in the form
`[Mordukhovich 2018, Thm. 2.16]`; the keys are those of the "References" section of the README.
A docstring states what the declaration says, in the notation of the source where possible, and
names every hypothesis that the source does not have.

**Differences from the sources.** If a statement of a source is false as printed, or its proof
has a gap that changes the hypotheses, say so in the docstring and add an entry to
[`ERRATA.md`](ERRATA.md). Describe a counterexample when there is one.

## Bookkeeping

A pull request that adds or changes results also updates:

- [`ROADMAP.md`](ROADMAP.md): the row of each statement, with its status and Lean names;
- the tables of [`README.md`](README.md), if a file is added or its contents change;
- [`CHANGELOG.md`](CHANGELOG.md), under "Unreleased". Renaming a declaration or changing the
  statement of a theorem is a breaking change and is marked as such.

## Tests

`VariationalAnalysisTest/Statements.lean` restates the main results with all their hypotheses
written out and proves each by the library theorem. If one of these `example`s stops compiling,
the statement of a main result has changed: either restore it, or change the `example` and
record a breaking change. Add an `example` there for a new result that users are likely to rely
on.

`VariationalAnalysisTest/Readme.lean` contains the example of the README; keep the two
identical.

## License

By contributing you agree that your contribution is licensed under the Apache 2.0 license of
the project (see [LICENSE](LICENSE)). Add yourself to the `Authors:` line of the files you
change substantially.
