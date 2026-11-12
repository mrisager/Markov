# Packed Frobenius verification

The verification is run with `frobenius_packed_verify.py`. It checks all
positive ordered Markov triples `a <= b <= c <= 10^K`. The output report
records the actual result; the earlier counting plots alone do not check
uniqueness.

## Enumeration and exact pruning

The strict tree starts at `(1,2,5)` and has children
`(a,c,3ac-b)` and `(b,c,3bc-a)`. Vieta descent gives each non-exceptional
ordered triple a unique smaller parent. This tree property concerns whole
triples and does not assume Frobenius uniqueness of their largest entries.

All bound comparisons use exact GMP integers. If the bound has bit length
`L` and `bit_length(a)+bit_length(c)>L`, then `2ac >= 2^L > bound`.
Since `3ac-b > 2ac`, that child and all its descendants can be pruned.
The same test applies to the other child. As `a<b`, failure of the first
test also rejects the second child. All remaining children are compared
with the exact bound.

An adaptive prefix-free frontier divides the tree into 64 disjoint jobs
at the large cutoff. The 63 expanded ancestors are enumerated separately.
Floating-point weights affect job scheduling only. No triples are removed
because their largest entries coincide. The exceptional triples `(1,1,1)`
and `(1,1,2)` are included as separate records in the same global test.

## Global uniqueness test

Each accepted triple contributes exactly 16 bytes: its largest coordinate
modulo `2^128`, as an unsigned little-endian integer (low64, then high64).
These records are retained in per-job files. SHA-256 checks file integrity;
it is not the mathematical uniqueness signature.

Every job file, all ancestors, and both exceptions are globally sharded by
the most significant residue byte. Equal signatures always enter the same
bucket, regardless of worker or tree branch. Each bucket is sorted by both
unsigned 64-bit words, and adjacent equal signatures are collected with
their full multiplicities. Oversized buckets are recursively divided by
successive residue bytes, preserving this property. The sorter uses bounded
arrays rather than a global Python hash set.

If no residue repeats, every largest coordinate is distinct: equal integers
would necessarily have equal residues. This conclusion is deterministic
and does not depend on a probability estimate for collisions. If residues
repeat, an independent exact traversal groups matching occurrences by
their full largest coordinate and compares their complete triples. A
residue collision alone is never reported as a Frobenius counterexample.

## Checkpoints and checks

A job checkpoint is saved only after its output has been flushed and
fsynced. It records the committed byte count and checksum, exact DFS
frontier, and traversal statistics. Resume truncates any uncommitted tail,
validates the committed prefix, and continues from that frontier. Global
sharding commits one input at a time; sorting commits each completed node.
An exclusive work-directory lock prevents concurrent writers.

The manifest fixes the bound, subtree roots, record format, source-code
checksums, and input hashes. For each completed job, `bytes=16*records`
and `pruned_children=records+1`. The merged tree satisfies
`pruned_children=strict_triples+1`. The verification count must agree with
the independently saved counting experiment where available. The global
sort must process exactly that strict count plus the two exceptions.

For `K=30000`, the independent prior count is 862,356,771 strict triples,
or 862,356,773 including the exceptions. The packed input occupies
13,797,708,368 bytes (about 12.85 GiB). Temporary buckets require a further
similar amount before sorting; processed buckets are removed. The original run retained the packed inputs, manifests, hashes and final
candidate file. The default sorting memory allowance is 512 MiB.

Validation before the large run included independent unguarded DFS
comparisons at small cutoffs, exact byte and hash comparisons, partial
checkpoint resume with junk tails, corrupted-prefix rejection, injected
interruptions during sharding and recursive sorting, duplicates across
different worker files, unsigned/endian boundary cases, and homogeneous
oversized buckets. A forced 8-bit-signature replay test correctly resolved
71 repeated residue groups against distinct full coordinates. End-to-end
verification through `10^2000` checked all 3,834,392 records, matched the
earlier count, and found no repeated 128-bit residues. Completed resume
with a different worker count reused the same files and hashes.

## Run and resume

See [README.md](README.md) for installation and complete commands. After
activating the virtual environment, run from this folder with fresh output
and work paths:

```sh
python -B frobenius_packed_verify.py \
  --max-exponent 30000 --workers 6 --backend gmpy2 \
  --output-prefix results/frobenius-my-10e30000 \
  --workdir results/frobenius-my-10e30000-work
```

To resume the same saved work, add `--resume`. The source files and input
paths must match the saved manifest. The new final reports are
`results/frobenius-my-10e30000.json` and `.txt`; live stage summaries are
saved in `results/frobenius-my-10e30000-work/progress.json` and its
`sort/progress.json`. The README shows how to save the console log with
`tee`.

The public historical reports and [sorting evidence](evidence/frobenius-10e30000/)
record the completed run. They contain the per-bucket results and hashes.
Rerun the calculation in a fresh work directory to regenerate the packed
inputs and checkpoints.
