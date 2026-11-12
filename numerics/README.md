# Running the Markov numerical experiments

This folder contains the programs and saved results for the experiments in the paper:

1. **Counting and plotting:** compute the exact number of ordered Markov triples at `x = 10^k`, then plot the error and its normalization by `sqrt(log x)`.
2. **Frobenius uniqueness:** enumerate the triples with largest coordinate at most `10^K`, then compare their largest coordinates globally using packed residues and exact replay if needed.
3. **Unit-ball area:** compute numerical intervals for the McShane–Rivin unit-ball area and the counting constant from Appendix A.

Both experiments include the exceptional triples `(1,1,1)` and `(1,1,2)`. The counting experiment does not test uniqueness. The uniqueness experiment does not need to compute the error plot.

The commands below run from this folder and put new output in `results/`, leaving the saved historical results unchanged. Choose another output prefix and work directory for each fresh run.

## 1. Install the environment

Use **Python 3.10 or newer** on **macOS or Linux**. The uniqueness coordinator uses the Unix `fcntl` locking module; on Windows, use a Linux environment such as WSL. The original large runs used Python 3.14.3, gmpy2 2.3.1 and NumPy 2.5.3.

From the companion repository root, change to `numerics/` and create a virtual environment:

```sh
cd numerics
python3 --version
python3 -m venv .venv
source .venv/bin/activate
python -m pip install --upgrade pip
python -m pip install -r requirements.txt
mkdir -p results .cache/matplotlib .cache/plots
export MPLCONFIGDIR="$PWD/.cache/matplotlib"
export XDG_CACHE_HOME="$PWD/.cache/plots"
```

`gmpy2` provides fast exact integers, NumPy supports the global packed-record sorting, and Matplotlib produces the figures. The commands explicitly request `--backend gmpy2` so a missing GMP installation produces an error rather than silently selecting slower Python integers. `--backend python` is available for small comparisons.

`requirements.txt` lets pip select versions compatible with your Python. `requirements-tested.txt` records the exact library versions used here: gmpy2 2.3.1, NumPy 2.5.3 and Matplotlib 3.11.2. With Python 3.14.3, use `python -m pip install -r requirements-tested.txt` to reproduce that tested environment.

If pip cannot find a suitable gmpy2 wheel, install the GMP, MPFR and MPC development libraries using your operating system's package manager and retry. Keep the virtual environment on the computer where it was created; recreate it after copying the folder to another computer.

Record your installed versions if you want to reproduce the environment later:

```sh
python -m pip freeze > results/environment.txt
```

To reactivate the environment from the repository root in a new terminal:

```sh
cd numerics
source .venv/bin/activate
export MPLCONFIGDIR="$PWD/.cache/matplotlib"
export XDG_CACHE_HOME="$PWD/.cache/plots"
```

## 2. Try both programs at a small cutoff

These commands use `K = 100`, two workers and eight subtree jobs. They should finish quickly and verify that the environment, multiprocessing, figures and packed sorting work.

```sh
set -o pipefail
python -u -B markov_error_parallel.py \
  --max-exponent 100 --workers 2 --tasks 8 --backend gmpy2 \
  --output-prefix results/markov-error-test-10e100 \
  --checkpoint-dir results/count-test-10e100-work \
  2>&1 | tee results/markov-error-test-10e100-run.log
```

```sh
python -u -B frobenius_packed_verify.py \
  --max-exponent 100 --workers 2 --tasks 8 --backend gmpy2 \
  --output-prefix results/frobenius-test-10e100 \
  --workdir results/frobenius-test-10e100-work \
  2>&1 | tee results/frobenius-test-10e100-run.log
```

At `10^100`, both programs should report **9,668 strict triples**, or **9,670 including the two exceptions**. The uniqueness report should say `VERIFIED`, with zero repeated 128-bit signatures. Inspect the PNG plots and the final `.txt` report before launching a large run.

The small verification reports `Independent prior count matched: False` because no historical counting JSON for `K = 100` is supplied beside the scripts. This means no saved reference was available. Compare its total with the counting test above. At `K = 30000`, the supplied historical counting JSON provides that additional check.

`tee` saves the console output while displaying it. In Bash and zsh, `set -o pipefail` makes a failed Python command remain a failed pipeline. Logs are written by these shell commands; the Python programs themselves write the checkpoint and result files.

## 3. Compute the error plots through $10^{30000}$

```sh
python -u -B markov_error_parallel.py \
  --max-exponent 30000 --sample-step 1 \
  --workers 6 --tasks 64 --backend gmpy2 \
  --checkpoint-seconds 300 --progress-every 5000000 \
  --output-prefix results/markov-error-my-10e30000 \
  --checkpoint-dir results/count-my-10e30000-work \
  2>&1 | tee results/markov-error-my-10e30000-run.log
```

The program traverses the Markov tree once and counts at **30,000 sampled cutoffs**, `10^1, 10^2, ..., 10^30000`. Every cutoff comparison uses exact integer arithmetic. Decimal arithmetic at 70-digit precision computes the main term and error from the exact counts.

For the definitions in the paper,

\[
M(x)=\#\{(a,b,c):1\leq a\leq b\leq c\leq x,\ a^2+b^2+c^2=3abc\},
\]

\[
E(x)=M(x)-C(\log(3x))^2,\qquad
\frac{E(x)}{\sqrt{\log x}}.
\]

All logarithms in these formulas are **natural logarithms**. The programs use the corrected constant

```text
C = 0.18071710471180647805779264904916762147630562767088273
```

The constant's source is [OEIS A261613](https://oeis.org/A261613). At `x = 10^k`, the main term is `C * (k * ln(10) + ln(3))^2`, and the normalizing denominator is `sqrt(k * ln(10))`.

The command produces:

| File | Contents |
| --- | --- |
| `results/markov-error-my-10e30000.csv` | Exact counts and high-precision main term/error at every sampled `k` |
| `results/markov-error-my-10e30000.json` | Definitions, constant, extrema, count, configuration and timing |
| `results/markov-error-my-10e30000.png` and `.svg` | Plot of the error `E(x)` |
| `results/markov-error-normalized-my-10e30000.png` and `.svg` | Plot of `E(x)/sqrt(log x)` |
| `results/count-my-10e30000-work/` | Manifest, checkpoints, completed subtree results and `progress.json` |

The CSV columns are `k`, `x`, `strict_triples`, `M_x`, `main_term` and `error`. The normalized values are derived from `error` and `k` by the formula above. The plots connect the sampled values by lines; they do not compute the error at every real value between consecutive cutoffs.

The original six-worker computation took **4,343.847 seconds**, about **72 minutes 24 seconds**. It gave

```text
M(10^30000)          = 862,356,773
main term           = 862,356,737.6632782951423753...
error               = 35.3367217048576247...
error / sqrt(log x) = 0.13444906442950635...
```

Runtime depends on the computer, available cores, integer library and other work running at the same time. The observed timing is a reference, not a guarantee.

### Render an existing CSV without recounting

For example, regenerate both plots from the historical CSV into a new output prefix:

```sh
python -B markov_error_plot.py \
  --render-csv markov-error-10e30000.csv --plot-mode both \
  --output-prefix results/markov-error-redrawn-10e30000
```

Use `--plot-mode normalized` for only the normalized figure, or `--plot-mode raw` for only the error figure. These plotting scripts generate PNG and SVG files.

The separate helper produces the compact vector PDF used in the paper directly from a CSV, without recounting. It requires Matplotlib and a working LaTeX installation so the tick numbers and formulas use the paper's Computer Modern fonts:

```sh
python -B plot_normalized_for_paper.py \
  --input markov-error-10e30000.csv \
  --output results/normalized-error-paper.pdf
```

To compute CSV/JSON now and plot later, add `--no-plot` to the parallel counting command. The single-process `markov_error_plot.py` also supports counting, but the parallel program is the recommended entry point for large runs.

## 4. Verify Frobenius uniqueness through $10^{30000}$

Check free disk space before starting. The original run retained **13,797,708,368 bytes** of packed signatures: about **13.8 GB**, or **12.85 GiB**. Global sorting temporarily needs approximately another copy. Allow **at least 30 GiB of free space for a fresh 30,000 run**, in addition to any historical records you keep. The program checks approximately 29.7 GiB at this bound, including a 4 GiB reserve.

```sh
python -u -B frobenius_packed_verify.py \
  --max-exponent 30000 --workers 6 --tasks 64 --backend gmpy2 \
  --checkpoint-seconds 300 --progress-every 5000000 \
  --buffer-records 1000000 --sort-memory-mib 512 \
  --output-prefix results/frobenius-my-10e30000 \
  --workdir results/frobenius-my-10e30000-work \
  2>&1 | tee results/frobenius-my-10e30000-run.log
```

The default 512 MiB setting is the sorting memory allowance, not a limit on the entire process tree. Enumeration workers also need memory for exact integers and output buffers. The counting experiment stores many exact powers in each worker, so reduce `--workers` if memory is tight. Run the two large experiments sequentially to avoid competing for memory, cores and disk bandwidth.

The verification proceeds in three stages:

1. Enumerate disjoint subtrees using exact integers and write a 16-byte record for every accepted triple. The record is its largest coordinate modulo `2^128`.
2. Globally shard and sort all records, including the prefix ancestors and both exceptional triples, so records from different workers are compared together.
3. If any residue repeats, replay an exact traversal to compare the full integers and triples involved.

**Zero repeated residues proves uniqueness at the cutoff deterministically:** equal full integers would have equal residues. A repeated residue is not by itself a Frobenius counterexample. The exact replay distinguishes different integers with the same residue from a genuine repeated largest coordinate.

The original run took **5,416.845 seconds**, about **90 minutes 17 seconds**, including enumeration and the global comparison. It found all **862,356,773** triples, and **no repeated residues modulo `2^128`**.

The command produces:

| File | Contents |
| --- | --- |
| `results/frobenius-my-10e30000.txt` | Human-readable final verification result |
| `results/frobenius-my-10e30000.json` | Counts, stage timings, source hashes, sorting details and any exact replay result |
| `results/frobenius-my-10e30000-work/records/` | Packed record files and enumeration checkpoints |
| `results/frobenius-my-10e30000-work/manifest.json` | Configuration and source-code identity |
| `results/frobenius-my-10e30000-work/progress.json` | Coordinator stage and completion status |
| `results/frobenius-my-10e30000-work/sort/` | Sorting manifest, progress, certificates and candidate records |

After successful completion, temporary sorting buckets are removed automatically. Packed enumeration files and the final certificates are retained. See [frobenius-packed-method.md](frobenius-packed-method.md) for the mathematical argument and checkpoint/integrity checks.

## 5. Monitor and resume a run

The programs print progress as workers pass the specified number of triples and as jobs/stages finish. `--progress-every 5000000` means five million triples per worker; it is not a fixed time interval. `--checkpoint-seconds 300` requests checkpointing roughly every five minutes, checked at traversal intervals.

In another terminal, follow the log:

```sh
tail -f results/markov-error-my-10e30000-run.log
```

Or inspect a snapshot:

```sh
python -m json.tool results/count-my-10e30000-work/progress.json
python -m json.tool results/frobenius-my-10e30000-work/progress.json
python -m json.tool results/frobenius-my-10e30000-work/sort/progress.json
```

During counting, the coordinator snapshot mainly records completed subtrees. Worker log lines and checkpoints also show progress within unfinished jobs. The sorting snapshot appears when that stage starts. Keep the computer awake during a long run.

If the process is interrupted, rerun the same command with `--resume` and append to the log using `tee -a`. For the counting example:

```sh
python -u -B markov_error_parallel.py \
  --max-exponent 30000 --sample-step 1 \
  --workers 6 --tasks 64 --backend gmpy2 --resume \
  --output-prefix results/markov-error-my-10e30000 \
  --checkpoint-dir results/count-my-10e30000-work \
  2>&1 | tee -a results/markov-error-my-10e30000-run.log
```

For the uniqueness example:

```sh
python -u -B frobenius_packed_verify.py \
  --max-exponent 30000 --workers 6 --tasks 64 --backend gmpy2 --resume \
  --buffer-records 1000000 --sort-memory-mib 512 \
  --output-prefix results/frobenius-my-10e30000 \
  --workdir results/frobenius-my-10e30000-work \
  2>&1 | tee -a results/frobenius-my-10e30000-run.log
```

Keep the cutoff, backend, task partition and, for counting, sampling unchanged. The number of worker processes may be changed on resume. The uniqueness manifest also pins the five Python source files by SHA-256; editing them invalidates that manifest. Never run two coordinators against the same work directory. The uniqueness program locks it automatically.

Counting checkpoints are Python pickle files. Resume only checkpoints produced by these programs that you trust. An interruption can lose the work since the most recent committed checkpoint; completed jobs are reused.

### Historical results in this repository

The saved CSVs, figures, run reports and validation summaries are beside the
programs. The [historical Frobenius evidence](evidence/frobenius-10e30000/)
includes the configuration, global sorting report and the 256 bucket
summaries. The 13.8 GB of packed records and the restart checkpoints were
kept in the original run workspace. For a new computation, use a fresh
output prefix and work directory as shown above.

The [provenance record](provenance.json) gives the original and public file
hashes for copies whose paths or plotting cache defaults were adjusted.
Hashes inside historical reports refer to the original run. The saved
`markov-error-10e30000.json` remains beside the scripts, where the Frobenius
program reads the independent count. The [normalized-error PDF](markov-error-normalized-10e30000.pdf)
is byte-identical to the figure submitted with arXiv v1.

## 6. Increase the bound or change sampling

For a different bound, change `--max-exponent K`, the output prefix and the checkpoint/work directory together. Start a **new run without `--resume`**. A checkpoint for `K = 30000` cannot be extended in place to a larger bound.

For the error experiment, `--sample-step 10` stores cutoffs `10^1, 10^11, ...`, plus the final requested cutoff. It reduces the number of histogram cutoffs and plot samples; it does not skip enumeration of triples below the final bound. Use `--sample-step 1` to reproduce the plots in the paper.

The number of triples, and therefore packed storage, grows approximately as `K^2`. Enumeration time also depends on the growing sizes of the exact integers, and disk sorting has its own cost. Measure a smaller run on your computer and check storage before increasing the bound; the observed 30,000 timings do not promise a particular runtime at a larger cutoff.

For the complete option lists:

```sh
python markov_error_parallel.py --help
python markov_error_plot.py --help
python frobenius_packed_verify.py --help
```

## 7. Reproduce the unit-ball area intervals

This program uses Python's standard library. Run it from `numerics/`:

```sh
mkdir -p results
python -B unit_ball_volume.py --cutoff 1000000000000 --precision 100 \
  > results/unit-ball-volume.txt
cmp unit-ball-volume.txt results/unit-ball-volume.txt
```

The saved [output](unit-ball-volume.txt) gives lower and upper bounds for
the area and for $C=2\operatorname{area}(B_X)/\pi^2$, using the Farey area
series and truncation bound in Appendix A. The count plots use the decimal
constant recorded in their own historical run reports.
