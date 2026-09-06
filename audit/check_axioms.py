#!/usr/bin/env python3
"""Audit all project source modules; run inside `lake env` after a strict build.

Only the Python standard library is used. Negative controls compile in a
temporary module root and never alter the real project or its build products.
"""
import argparse
import os
from pathlib import Path
import re
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parent.parent
CHECKER = ROOT / "audit" / "AllProjectAxioms.lean"


def project_modules(root=ROOT):
    sources = sorted((root / "RequestProject").rglob("*.lean"))
    root_module = root / "RequestProject.lean"
    if root_module.is_file():
        sources.insert(0, root_module)
    if not sources:
        raise RuntimeError("No RequestProject source modules found")
    modules = []
    for path in sources:
        parts = path.relative_to(root).with_suffix("").parts
        # Fail visibly on unsupported file names instead of silently skipping them.
        if not all(re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", part) for part in parts):
            raise RuntimeError(f"Unsupported Lean module path: {path}")
        modules.append(".".join(parts))
    return modules


def lean_run(path, module_root, *, output=None, extra_path=None):
    env = os.environ.copy()
    if extra_path is not None:
        env["LEAN_PATH"] = str(extra_path) + os.pathsep + env.get("LEAN_PATH", "")
    command = ["lean", "-DwarningAsError=true", f"--root={module_root}"]
    if output is not None:
        command += ["-o", str(output)]
    command.append(str(path))
    return subprocess.run(command, cwd=ROOT, env=env, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT)


def driver(directory, modules):
    path = directory / "AllProjectAudit.lean"
    path.write_text("".join(f"import {module}\n" for module in modules)
                    + CHECKER.read_text(encoding="utf-8"), encoding="utf-8")
    return path


def require(result, *markers, success):
    if (result.returncode == 0) != success or any(m not in result.stdout for m in markers):
        print(result.stdout, end="")
        raise RuntimeError(f"Audit control failed: exit={result.returncode}, required={markers}")


def self_test(directory):
    fixtures = ROOT / "audit" / "fixtures"
    # The external axiom tests transitive dependencies; the project module also
    # has a direct custom axiom and private/public proofs outside its namespace.
    for relative in ("AuditForeign.lean", "RequestProject/AxiomControl.lean"):
        source = directory / relative
        source.parent.mkdir(parents=True, exist_ok=True)
        source.write_text((fixtures / relative).read_text(encoding="utf-8"), encoding="utf-8")
        result = lean_run(source, directory, output=source.with_suffix(".olean"), extra_path=directory)
        require(result, success=True)
    # Discover the fixture just as CI discovers a new, unlisted project module.
    # Audit it separately: Lean resolves the RequestProject package root as a
    # whole, so prepending this temporary root would shadow the real package.
    # main() has already required the complete real project audit to pass.
    negative = lean_run(driver(directory, project_modules(directory)),
                        directory, extra_path=directory)
    require(negative, "ALLOWLIST_FAIL", "UNEXPECTED_AXIOMS", "auditUnexpected",
            "directUnexpected", "hiddenViolation", "publicViolation", success=False)
    if "ALLOWLIST_PASS" in negative.stdout:
        raise RuntimeError("Negative control unexpectedly emitted a pass marker")
    print("NEGATIVE_CONTROL_PASS: rejected direct and transitive custom axioms, including private declarations")
    for line in negative.stdout.splitlines():
        if "UNEXPECTED_AXIOMS" in line or "ALLOWLIST_FAIL" in line:
            print(line)
    empty = lean_run(driver(directory, []), directory)
    require(empty, "ALLOWLIST_EMPTY", success=False)
    print("EMPTY_CONTROL_PASS: empty declaration inventory rejected")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true", help="also run isolated rejection controls")
    args = parser.parse_args()
    modules = project_modules()
    print(f"SOURCE_INVENTORY modules={len(modules)}", flush=True)
    with tempfile.TemporaryDirectory(prefix="shadow-axiom-audit-") as temporary:
        directory = Path(temporary)
        result = lean_run(driver(directory, modules), directory)
        print(result.stdout, end="", flush=True)
        require(result, "ALLOWLIST_PASS", success=True)
        if args.self_test:
            self_test(directory)


if __name__ == "__main__":
    main()
