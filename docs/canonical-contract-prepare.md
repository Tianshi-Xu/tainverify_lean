# Canonical reference preparation (source-only)

`python3 -m trainverify.canonical_contract_prepare --config /absolute/config.json --recipe /absolute/recipe.json --recipe-sha256 <externally-pinned-sha256> --out /absolute/new-directory`

This command never invokes Lean, captures graphs, imports historical controllers, or discovers a candidate publication. It prepares independently accepted fragments over an accepted baseline, not a new proof acceptance. The caller must authenticate the recipe digest independently; a self-generated recipe hash is integrity evidence, not independent authority.

## Recipe v1

Exact top-level keys: `version`, `namespace`, `base_module`, `base`, `seed`, `previous`, `stages`.

Every file pin is exactly `{path: original_absolute_path, sha256: original_expected_digest}`. The existing `artifact_tools.Configuration` resolves explicit file/directory relocations; expected digests are never recomputed from relocated bytes. The same captured bytes are hashed and consumed. `bound_files` records original and resolved paths. No fallback search occurs.

`base` contains pins for `receipt`, `preparation`, `complete`, `full_records`, `joint_records`, `joint_source`, and the independent accepted `world`. The completed receipt binds the old record files; preparation binds old Joint source. Published module source hashes and the public declaration census are checked. Old record names are used exactly, including private internal names. Old full and joint record files are copied byte-for-byte, not renamed or re-rendered.

Each `stages` item contains file pins `source`, `detail`, `world`, `kernel`, `joint_source`, `joint_kernel`, plus identifiers `first_import`, `module`, `pair`, `cumulative`. `module` is a fresh reference module. The first fragment import must exactly equal `first_import`; only that import line changes, to the baseline module for stage one and the preceding independent reference module thereafter. All other fragment bytes are retained. Sources must use the supported generated declaration grammar; this is not a general Lean parser.

`seed` contains `anchor`, `instance`, `prelude`, `arguments`, `read_worlds`. `arguments` maps exactly `s,p,t,q,hs,hp,hvalues` to explicit old seeded expressions/hypotheses. `read_worlds` maps `sm` and `pm` to `initial,final,hypothesis,run`. Both the instance conclusion and its entire proof prelude/application are checked against the pinned old declarations. Unknown mappings, run names not bound by old conditional binders, and extra value/output assumptions fail closed. `previous` names the old cumulative conditional theorem.

## Checks and outputs

- Exact fullrefs, complete execution order and initial-parameter binding match the accepted base world at every stage.
- Historical fragment and joint kernel receipts bind their exact original source, object and dependency bytes. Fragment axiom inventories independently close new declaration counts.
- Reads + units must exactly census new declarations; public and audit names cannot overwrite old targets.
- `artifact_tools.render_joint` supplies the full global shape, every-local shape and value proposition. Replica axes must remain null. Retained and deferred source boundaries must cover the complete frontier; old carry signatures are checked against existing seeded audits.
- The complete old Joint body, including reopened namespaces, remains byte-identical through the final namespace ending boundary. Only the old trailing observer is replaced. Each stage appends seeded read/unit audits, a conditional/inhabited stage pair, and a cumulative conditional/inhabited pair.
- `artifact_contracts.dump_contracts` supplies explicit full-Expr target manifests and observers. No private names are normalized. Each stage has its own full and joint manifests and reference source files.
- All preflight checks happen before exclusive output directory creation. Existing destinations are always rejected. The success manifest is written last. An I/O failure may leave an incomplete directory; there is deliberately no destructive cleanup or automatic retry. This is a single trusted local-writer protocol, not hostile same-UID namespace race protection.

`kernel_verified=false` and `proof_admissible=false` are unconditional. `old_full_preserved`/`old_joint_preserved` describe the retained accepted baseline records and source, **not** a freshly compiled Expr equality check. `actual_read=false` means no new candidate actual was ingested; the completed baseline publication is necessarily read. No new types are invented. Kernel evaluation, emitted Expr comparison and candidate validation remain separate gates.

## Tests

`PYTHONDONTWRITEBYTECODE=1 python3 -m unittest scripts.tests.test_canonical_contract_prepare -v`

Tests use explicitly synthetic receipt/object fixtures, never simulated results labelled as real Lean output. Coverage includes relocated original digests, complete replica values, premise/mapping errors, missing/duplicate census, coherent source/detail deletion against an independent kernel binding, no-clobber preparation, legacy term proofs, indented source declarations, reopened namespaces and local-shape alpha-renaming. They do not establish arbitrary Lean parsing or adversarial filesystem race safety.
