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
        sources = directory / "sources"
        shutil.copytree(
            paper, sources, dirs_exist_ok=True,
            ignore=shutil.ignore_patterns(
                "main.pdf", "*.aux", "*.bbl", "*.blg", "*.log", "*.out",
                "*.toc", "*.fls", "*.fdb_latexmk", "*.synctex.gz",
            ),
        )
        main_source = directory / "main.tex"
        if main_source.resolve() != (paper / "main.tex").resolve():
            shutil.copy2(paper / "main.tex", main_source)
        build_env = env.copy()
        # Stale auxiliaries beside the original sources must not shadow
        # the bibliography and references generated in this build directory.
        build_env["TEXINPUTS"] = os.pathsep.join(
            (str(directory), str(sources), os.environ.get("TEXINPUTS", ""))
        )
        build_env["BIBINPUTS"] = str(sources) + os.pathsep + os.environ.get("BIBINPUTS", "")
        subprocess.run(
            [latexmk, "-pdf", "-interaction=nonstopmode", "-halt-on-error",
             "-file-line-error", f"-outdir={directory}", "main.tex"],
            cwd=directory, env=build_env, check=True,
        )
        result = directory / "main.pdf"
        if not result.is_file():
            raise RuntimeError("TeX completed without producing main.pdf")
        args.output.parent.mkdir(parents=True, exist_ok=True)
        if result.resolve() != args.output.resolve():
            shutil.copy2(result, args.output)
        print(f"Manuscript: {args.output.resolve()}")

    if args.build_dir is not None:
        directory = args.build_dir.resolve()
        if directory.is_relative_to(root):
            parser.error("--build-dir must be outside the publication repository")
        build(directory)
    else:
        with tempfile.TemporaryDirectory(prefix="symmetric-subgroups-tex-") as tmp:
            build(Path(tmp))


if __name__ == "__main__":
    main()
