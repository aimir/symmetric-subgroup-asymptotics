#!/usr/bin/env python3
"""Build the manuscript locally, keeping TeX intermediates outside the tree."""

from __future__ import annotations

import argparse
import os
from pathlib import Path
import shutil
import subprocess
import tempfile


def main() -> None:
    root = Path(__file__).resolve().parents[1]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=root / "paper" / "main.pdf")
    parser.add_argument(
        "--build-dir", type=Path,
        help="Keep intermediates in this directory (default: a temporary directory).",
    )
    args = parser.parse_args()
    latexmk = shutil.which("latexmk")
    if latexmk is None:
        parser.error("latexmk is required; install a local TeX distribution")
    paper = root / "paper"
    env = os.environ.copy()
    for variable in ("TEXINPUTS", "BIBINPUTS"):
        env[variable] = str(paper) + os.pathsep + env.get(variable, "")

    def build(directory: Path) -> None:
        directory.mkdir(parents=True, exist_ok=True)
        subprocess.run(
            [latexmk, "-pdf", "-interaction=nonstopmode", "-halt-on-error",
             "-file-line-error", f"-outdir={directory}", "main.tex"],
            cwd=paper, env=env, check=True,
        )
        result = directory / "main.pdf"
        if not result.is_file():
            raise RuntimeError("TeX completed without producing main.pdf")
        args.output.parent.mkdir(parents=True, exist_ok=True)
        if result.resolve() != args.output.resolve():
            shutil.copy2(result, args.output)
        print(f"Manuscript: {args.output.resolve()}")

    if args.build_dir is not None:
        build(args.build_dir.resolve())
    else:
        with tempfile.TemporaryDirectory(prefix="symmetric-subgroups-tex-") as tmp:
            build(Path(tmp))


if __name__ == "__main__":
    main()
