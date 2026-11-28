"""Verify the regular-success handlers and their counter invariant from any working directory."""

import argparse
import re
import shutil
import subprocess
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
CACHE = HERE.parent / "components/spider-storage/src/cache"


def method_body(filename: str, declaration: str) -> str:
    """Take the unique method with this declaration. Rust checks its complete token tree."""
    source = (CACHE / filename).read_text(encoding="utf-8")
    matches = list(re.finditer("^    " + re.escape(declaration), source, re.MULTILINE))
    if len(matches) != 1:
        raise ValueError(f"expected exactly one {declaration} in {filename}")
    start = source.index("{", matches[0].end())
    end = re.search(r"^    }$", source[start:], re.MULTILINE)
    if end is None:
        raise ValueError(f"missing method end in {filename}")
    return source[start : start + end.end()]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verus", default="verus", help="Verus executable")
    args = parser.parse_args()
    verifier = shutil.which(args.verus)
    if verifier is None:
        parser.error(f"Verus executable not found: {args.verus}")
    with tempfile.TemporaryDirectory() as temp:
        build = Path(temp)
        shutil.copy(HERE / "job_counters.rs", build)
        shutil.copy(HERE / "handler_projection.rs", build)
        methods = [
            ("accept", "task.rs", "fn succeed_task_instance(&mut self,"),
            ("notify", "task.rs", "pub async fn succeed_task_instance<'guard>("),
            ("charge", "job.rs", "pub async fn succeed_task_instance("),
        ]
        (build / "handler.rs").write_text(
            'use vstd::prelude::*;\ninclude!("handler_projection.rs");\n'
            + "".join(f"{name}! {method_body(file, decl)}\n" for name, file, decl in methods),
            encoding="utf-8",
        )
        result = subprocess.run(
            [
                str(Path(verifier).resolve()),
                "--no-cheating",
                "--crate-type=lib",
                "--out-dir",
                temp,
                str(build / "job_counters.rs"),
            ],
            check=False,
        )
        return result.returncode


if __name__ == "__main__":
    raise SystemExit(main())
