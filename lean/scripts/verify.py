#!/usr/bin/env python3
"""Check the source snapshot and strictly verify Theorems 1 and 12."""

import argparse
from collections import Counter
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time


ROOT = Path(__file__).resolve().parents[1]
THEOREM_12 = "Markov.modularMcShaneRivin_lattice_asymptotic"
THEOREM_1 = "Markov.t1_mainTheorem"
COMBINED_ROOT = "MarkovTheorem1"
UPSTREAM_LICENSE = "LICENSES/RiemannGaussian-Apache-2.0.txt"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
TOOLCHAIN = "leanprover/lean4:v4.28.0"
MATHLIB_REV = "8f9d9cff6bd728b17a24e163c9402775d9e6a365"
REPORT = re.compile(
    r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)"
)


class VerificationError(Exception):
    pass


def require(condition, message):
    if not condition:
        raise VerificationError(message)


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_json(path):
    return json.loads(path.read_text(encoding="utf-8"))


def imports(path):
    """The frozen sources use ordinary, one-line import commands."""
    result = []
    for line in path.read_text(encoding="utf-8").splitlines():
        if line.startswith("import "):
            result.extend(line.split("--", 1)[0].split()[1:])
    return result


def module_path(module):
    relative = module.replace(".", "/") + ".lean"
    if module == "Markov" or module.startswith("Markov."):
        return ROOT / relative
    return ROOT / "Theorem1" / relative


def check_reports(text, names):
    matches = list(REPORT.finditer(text))
    reported = [match.group(1) for match in matches]
    require(
        Counter(reported) == Counter(names),
        "Axiom reports do not match the registered names exactly once.",
    )
    require(reported == names, "Axiom report order differs from the registered audit.")
    used = set()
    for match in matches:
        axioms = {part.strip() for part in (match.group(2) or "").split(",") if part.strip()}
        require(
            axioms <= ALLOWED_AXIOMS,
            f"Unexpected axioms for {match.group(1)}: {sorted(axioms - ALLOWED_AXIOMS)}",
        )
        used.update(axioms)
    return used


def restore_previous_comments(data, hunks):
    """Undo the recorded publication edits before checking historical hashes."""
    if not hunks:
        return data
    lines = data.decode("utf-8").splitlines(keepends=True)
    previous_end = 0
    for hunk in hunks:
        start = hunk["line"]
        end = start + hunk["publishedLineCount"]
        require(previous_end <= start <= end <= len(lines), "Invalid comment revision range.")
        previous_end = end
    for hunk in reversed(hunks):
        start = hunk["line"]
        end = start + hunk["publishedLineCount"]
        lines[start:end] = hunk["previousLines"].splitlines(keepends=True)
    return "".join(lines).encode("utf-8")


def check_snapshot():
    verification = ROOT / "verification"
    manifest = load_json(verification / "combined-source-sha256.json")
    original_manifest = load_json(verification / "source-sha256.json")
    theorem12 = load_json(verification / "original-checkpoint.json")
    theorem1 = load_json(verification / "theorem1-checkpoint.json")
    revisions = load_json(verification / "comment-revisions.json")["changedFiles"]
    historical_sources = {name for name in original_manifest if name.endswith(".lean")}
    historical_sources.update(theorem1["proofSourceProvenance"])
    require(set(revisions) <= historical_sources, "Unexpected file in the comment revision record.")
    require(
        sha256(verification / "source-sha256.json") == theorem12["canonicalSourceManifestSHA256"],
        "The historical Theorem 12 source manifest differs from its checkpoint.",
    )
    for name, expected in original_manifest.items():
        if name == "lakefile.toml":
            continue
        if name in revisions:
            previous = restore_previous_comments((ROOT / name).read_bytes(), revisions[name])
            digest = hashlib.sha256(previous).hexdigest()
        else:
            digest = manifest.get(name)
        require(digest == expected, f"Historical Theorem 12 source mismatch: {name}")

    base_modules = imports(module_path("Markov"))
    extension_imports = imports(module_path(COMBINED_ROOT))
    require(extension_imports and extension_imports[0] == "Markov",
            "The combined root must import the original Markov root first.")
    extension_modules = extension_imports[1:]
    modules = [*base_modules, "Markov", *extension_modules, COMBINED_ROOT]
    require(len(base_modules) == 558 and len(modules) == len(set(modules)) == 894,
            "Unexpected module registration.")
    expected_sources = {module_path(module).relative_to(ROOT).as_posix() for module in modules}
    expected_files = expected_sources | {
        "lakefile.toml", "lake-manifest.json", "lean-toolchain", "LICENSE", UPSTREAM_LICENSE,
        "verification/comment-revisions.json",
    }
    require(set(manifest) == expected_files, "The source manifest has missing or extra entries.")
    for name, expected in manifest.items():
        path = ROOT / name
        require(path.is_file() and sha256(path) == expected, f"Source hash mismatch: {name}")
    actual_sources = {p.relative_to(ROOT).as_posix() for p in ROOT.rglob("*.lean")
                      if p.relative_to(ROOT).parts[0] not in {".lake", ".git", "verification"}}
    require(actual_sources == expected_sources, "There are missing or unregistered Lean files.")

    positions = {module: i for i, module in enumerate(modules)}
    for module in modules:
        for dependency in imports(module_path(module)):
            if dependency in positions:
                require(positions[dependency] < positions[module],
                        f"Out-of-order dependency: {module} imports {dependency}")
            else:
                require(dependency.split(".")[0] in {"Mathlib", "Lean", "Init", "Std"},
                        f"Unexpected or unregistered import: {module} imports {dependency}")

    def read_audit(module):
        return re.findall(r"^#print axioms ([^\s]+)$",
                          module_path(module).read_text(encoding="utf-8"), re.MULTILINE)

    audits = {"Markov.Audit": read_audit("Markov.Audit")}
    for module in extension_modules:
        names = read_audit(module)
        if names:
            audits[module] = names
    theorem12_names = audits["Markov.Audit"]
    theorem1_names = [name for module in extension_modules for name in audits.get(module, ())]
    for names, prefix, expected_count in [
        (theorem12_names, "", 4433),
        (theorem1_names, "theorem1-", 2426),
    ]:
        recorded = (verification / f"{prefix}audited-declarations.txt").read_text(
            encoding="utf-8"
        ).splitlines()
        require(names == recorded and len(names) == len(set(names)) == expected_count,
                f"Unexpected audit inventory: {prefix or 'Theorem 12'}")
        check_reports((verification / f"{prefix}original-axiom-reports.txt").read_text(
            encoding="utf-8"
        ), names)
    require(THEOREM_12 in theorem12_names and THEOREM_1 in theorem1_names
            and set(theorem1["endpoints"]) <= set(theorem1_names)
            and not set(theorem12_names).intersection(theorem1_names),
            "The audit is missing a final declaration or repeats a declaration.")

    proof_files = theorem1["proofSourceProvenance"]
    expected_proofs = {module_path(m).relative_to(ROOT).as_posix()
                       for m in extension_modules if m not in audits}
    require(set(proof_files) == expected_proofs and len(proof_files) == 323,
            "Theorem 1 proof provenance does not cover the exported sources.")
    for name, record in proof_files.items():
        data = restore_previous_comments((ROOT / name).read_bytes(), revisions.get(name))
        notice = record.get("appendedNotice", "").encode("utf-8")
        if notice:
            require(data.endswith(notice), f"Missing adaptation notice: {name}")
            data = data[:-len(notice)]
        require(hashlib.sha256(data).hexdigest() == record["verifiedSHA256"],
                f"Theorem 1 proof differs from the verified source: {name}")

    require((ROOT / "lean-toolchain").read_text(encoding="utf-8").strip() == TOOLCHAIN,
            "Unexpected Lean toolchain pin.")
    lake_manifest = load_json(ROOT / "lake-manifest.json")
    mathlib = [package for package in lake_manifest["packages"] if package["name"] == "mathlib"]
    require(len(mathlib) == 1 and mathlib[0]["rev"] == MATHLIB_REV,
            "Unexpected mathlib revision pin.")
    lines = sum(len(module_path(m).read_text(encoding="utf-8").splitlines()) for m in modules)
    require(lines == 115066, "Source line count differs from the export record.")
    return modules, audits, lake_manifest, lines


def dependency_environment(packages, lake_manifest):
    """Use only this export's objects and the pinned external package objects."""
    libraries = []
    for package in lake_manifest["packages"]:
        path = packages / package["name"]
        result = subprocess.run(
            ["git", "-C", str(path), "rev-parse", "HEAD"],
            capture_output=True, text=True, check=True,
        )
        require(result.stdout.strip() == package["rev"],
                f"Installed revision mismatch: {package['name']}")
        library = path / ".lake/build/lib/lean"
        # Build-tool-only packages need not have any compiled Lean library.
        # Missing objects for an actual import will be rejected by Lean.
        if library.is_dir():
            libraries.append(library)
    require((packages / "mathlib/.lake/build/lib/lean/Mathlib.olean").is_file(),
            "Compiled mathlib is missing. Run `lake exe cache get` first.")
    build = ROOT / ".lake/build/lib/lean"
    build.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    env["LEAN_PATH"] = os.pathsep.join(str(p) for p in [build, *libraries])
    return env


def compile_source(source, module, env, logs):
    output = Path(".lake/build/lib/lean") / (module.replace(".", "/") + ".olean")
    (ROOT / output).parent.mkdir(parents=True, exist_ok=True)
    command = ["lean", "-j1", "-DwarningAsError=true", "-DautoImplicit=false"]
    if source.startswith("Theorem1/"):
        command += ["-R", "Theorem1"]
    command += ["-o", output.as_posix(), source]
    logfile = logs / (module + ".log")
    with logfile.open("w", encoding="utf-8") as handle:
        handle.write("COMMAND: " + " ".join(command) + "\n")
        handle.flush()
        result = subprocess.run(command, cwd=ROOT, env=env, stdout=handle,
                                stderr=subprocess.STDOUT, text=True)
        handle.write(f"\nEXIT: {result.returncode}\n")
    if result.returncode:
        print(logfile.read_text(encoding="utf-8")[-10000:], file=sys.stderr)
        raise VerificationError(f"Compilation failed for {module}; see {logfile.relative_to(ROOT)}")
    return logfile


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-only", action="store_true",
                        help="Check export integrity without running Lean.")
    parser.add_argument("--packages", type=Path, default=ROOT / ".lake/packages",
                        help="Existing pinned compiled dependencies (default: .lake/packages).")
    args = parser.parse_args()
    run = ROOT / "verification/run"
    success = run / "SUCCESS.json"
    if not args.check_only:
        success.unlink(missing_ok=True)
    modules, audits, lake_manifest, lines = check_snapshot()
    name_count = sum(len(names) for names in audits.values())
    print(f"Snapshot OK: {len(modules)} Lean files, {name_count:,} audited names, "
          f"{lines:,} source lines.", flush=True)
    if args.check_only:
        print("Integrity checks passed. Lean was not run.")
        return

    run.mkdir(parents=True, exist_ok=True)
    version = subprocess.run(["lean", "--version"], cwd=ROOT,
                             capture_output=True, text=True, check=True).stdout.strip()
    require(re.search(r"version 4\.28\.0(?:[, )]|$)", version), f"Unexpected Lean version: {version}")
    env = dependency_environment(args.packages.resolve(), lake_manifest)
    logs = run / "logs"
    logs.mkdir(exist_ok=True)
    started = time.time()
    used_axioms = set()
    for i, module in enumerate(modules, 1):
        print(f"[{i}/{len(modules)}] {module}", flush=True)
        source = module_path(module).relative_to(ROOT).as_posix()
        logfile = compile_source(source, module, env, logs)
        if module in audits:
            used_axioms.update(check_reports(logfile.read_text(encoding="utf-8"), audits[module]))
    check_snapshot()
    receipt = {
        "status": "SUCCESS", "theorems": [THEOREM_1, THEOREM_12],
        "completedUTC": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "elapsedSeconds": round(time.time() - started, 2),
        "leanVersion": version, "mathlibRevision": MATHLIB_REV,
        "modules": len(modules), "auditedDeclarations": name_count,
        "axiomsUsed": sorted(used_axioms),
        "sourceManifestSHA256": sha256(ROOT / "verification/combined-source-sha256.json"),
    }
    success.write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
    print("SUCCESS: all local sources, both axiom inventories, and the combined root passed.")
    print("Receipt: verification/run/SUCCESS.json")


if __name__ == "__main__":
    try:
        main()
    except (VerificationError, OSError, ValueError, KeyError, subprocess.CalledProcessError) as exc:
        print(f"Verification failed: {exc}", file=sys.stderr)
        sys.exit(1)
