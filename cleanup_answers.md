# Specl Cleanup Checklist Answers

Audit performed 2026-02-17. All tests passing (185/185).

## 1. Format tool working

**YES.** `specl format` builds and runs correctly. The `all_examples_format_roundtrip` integration test passes — formatting is idempotent across the entire example corpus.

## 2. All examples formatted

**YES.** The roundtrip test confirms: parse -> format -> re-parse -> re-format produces identical output for every `.specl` file in `examples/`.

## 3. All examples parse, typecheck, and check

**YES.** Four integration tests pass:

- `all_examples_parse` — ok
- `all_examples_typecheck` — ok
- `all_examples_format_roundtrip` — ok
- `examples_with_constants_check` — ok (150 examples model-checked)

Note: TLA translate corpus tests need `RUST_MIN_STACK=8388608` in debug builds (already set in CI).

## 4. VIEW feature

**Implemented, undocumented, no examples.**

Syntax: `view { var1, var2, ... }` — top-level declaration.

How it works: creates a boolean mask over state variables. During BFS, state fingerprints only incorporate the view variables. Two states identical on view variables are deduplicated even if they differ on other variables. This is a state abstraction / over-approximation.

Implementation touches: parser (`Decl::View`), IR compiler (resolves to variable indices), model checker (`view_mask` in explorer, `view_mode` in store), state hashing (only view vars contribute to fingerprint), symmetry canonicalization (respects view mask).

`view` is a contextual keyword — also usable as an identifier in expressions.

**Action needed:** add at least one example using `view`, add to CLAUDE.md documentation.

## 5. `fix` keyword

**Exists in the language, but no example uses it.**

- Lexer: `"fix" => TokenKind::Choose`
- AST: `ExprKind::Fix { var, predicate }` — domain-free variant (vs `Choose` which has domain)
- Pretty-printer: `fix x: P`
- Semantics: picks an arbitrary value satisfying predicate P (TLA+ CHOOSE without domain)

Since `fix` maps to `TokenKind::Choose` and `parse_choose()` expects `choose/fix x in S: P`, the domain-free `fix x: P` form currently only arises from TLA+ translation. There is no parser path to produce an `ExprKind::Fix` node from hand-written specl.

**Action needed:** either (a) add parser support for `fix x: P` syntax and add an example, or (b) keep it as TLA+ translation internal and document that decision.

## 6. `choose` keyword

**EXISTS — contradicts expectation that it doesn't.**

- Token: `TokenKind::Choose` with keywords `"choose"` and `"fix"`
- Syntax: `choose x in S: P(x)`
- AST: `ExprKind::Choose { var, domain, predicate }`
- Documented in CLAUDE.md operators table
- Evaluator has `ChooseFailed` error
- No `.specl` example file uses it (only appears in comments)

**Action needed:** decide whether to keep `choose` or rename/remove it. If keeping, add an example.

## 7. No concept of `record`

**Partially true.** There is no `record` keyword in user-facing syntax. Users cannot declare record types. `Dict[K, V]` serves the record-like role in practice.

However, the type system internally has `Type::Record(RecordType)` with named fields in a `BTreeMap`, and the AST has `RecordUpdate` / `RecordFieldUpdate` nodes. These appear to be used for dict literal type inference and TLA+ translation, not directly by users.

**Verdict:** correct from the user perspective — Dict is the unified map/record type. The internal Record type is an implementation detail.

## 8. Empty set and empty dictionary

**Both possible.**

| Collection | Syntax | Notes |
|---|---|---|
| Empty set | `{}` | `SetLit` with 0 elements |
| Empty dict | `{:}` | Colon disambiguates from empty set |
| Empty sequence | `[]` | Used in examples (e.g. `SeqTest.specl`) |

Parser explicitly handles all three cases in `parse_set_or_record_lit()`.

## 9. Soundness guarantees

**Default checking is SOUND.** Only one flag makes it unsound:

| Flag | Soundness | Notes |
|---|---|---|
| `--bloom` | UNSOUND | Explicitly marked: "UNSOUND: may miss bugs" with detailed warning in CLI help |
| `--fast` | Sound | Two-phase: fingerprint-only then auto re-runs with full tracking |
| `--por` | Sound | Proven reduction technique, auto-enabled |
| `--symmetry` | Sound | Proven reduction technique, auto-enabled |
| `--directed` | Sound | Traces may not be shortest (documented) |
| `--swarm N` | Sound | Parallel shuffled exploration |
| `--max-states/depth/time` | Sound within bounds | Reports "OK (bounded)" |

`--bloom` is clearly marked with both short help ("UNSOUND: may miss bugs") and detailed `long_help` warning. No other flags compromise soundness.

Hash collision detection in `store.rs` also warns if fingerprint collisions occur (extremely rare with 64-bit fingerprints).

---

## Summary of action items

1. `view`: add example, add to CLAUDE.md docs
2. `fix`: decide on parser support for domain-free form, or document as internal-only
3. `choose`: decide whether to keep or remove; if keeping, add example
4. Consider whether internal `Type::Record` is intentional or should be unified with Dict
