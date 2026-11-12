# Verification and export record

## Original proof checks

| Result | Completed in Europe/Copenhagen | Proof inventory |
| --- | --- | --- |
| Theorem 12 | 9 November 2026, 23:37 | 558 registered modules, including the audit, plus `Markov.lean`. 4,433 audited names |
| Theorem 1 | 11 November 2026, 01:41 | 124 additional Markov proof modules and 199 port modules. 2,426 additional distinct audited names, including the final endpoints |

Both original roots and axiom audits passed with Lean 4.28.0 and mathlib
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`. The combined export contains
894 local Lean files and 6,859 distinct registered axiom checks. Those
totals include the two roots and 12 audit files.

The export retains the verified Lean code and the original toolchain and
dependency pins. The combined `lakefile.toml` registers the additional
library. Publication edits updated outdated comments and added notices to
the affected upstream files. The verifier reverses the recorded comment
edits when comparing with the original source hashes. For Theorem 1, it
also removes the port notices first added by the combined export. The
export supplies its own combined root and deduplicated audit batches.

## Recorded evidence

- [Theorem 12 checkpoint](../verification/original-checkpoint.json) and
  [original source hashes](../verification/source-sha256.json) record the
  earlier Theorem 12 snapshot, including its original Lake configuration.
- [Theorem 1 checkpoint](../verification/theorem1-checkpoint.json) records
  the exact endpoints and proof source provenance, including the hashes
  of the upstream and locally checked zeta files.
- [Combined source hashes](../verification/combined-source-sha256.json)
  cover the sources, pinned build configuration, licenses, and comment
  revision record.
- [Theorem 12 reports](../verification/original-axiom-reports.txt) and
  [Theorem 1 reports](../verification/theorem1-original-axiom-reports.txt)
  record the historical Lean results in the order used by the export.
  The corresponding inventories list one entry per qualified name.
- [Combined export checks](../verification/combined-export-check.json)
  record the checks on the first combined package. The
  [publication check](../verification/publication-check.json) records the
  comment and license update, including the code comparison and fresh
  Lean checks. The original Theorem 12 export check is also retained.
- [Comment revisions](../verification/comment-revisions.json) record the
  earlier comments for historical hash checks.

The original root objects, full development logs, and original manuscript
are identified by hashes and are outside this source distribution.

For the first combined export, Lean recompiled the two final theorem modules, the zeta
zero-free-region module, the eleven new audit batches, and the combined root
using the pinned libraries and previously verified local dependency objects.
The original full verifications supply the complete source-check record.

## Rechecking the proofs

`python3 scripts/verify.py --check-only` checks the source hashes, module
registration and import order, proof provenance, historical axiom reports,
and pinned configuration. It runs without Lean.

`python3 scripts/verify.py` also checks the installed toolchain and Git
revisions, then compiles every local file in dependency order with
`lean -j1 -DwarningAsError=true -DautoImplicit=false` and default resource
limits. Each fresh audit must report its registered names exactly once and
use only `propext`, `Classical.choice`, and `Quot.sound`. The script checks
the snapshot again after compilation and records success in
`verification/run/SUCCESS.json`. Local logs are under `verification/run/logs/`.

A full run recompiles the local proofs and reuses the pinned compiled
mathlib and support-package dependencies. The GitHub Actions workflow runs
the same verifier on a checkout. It can also be triggered manually.
