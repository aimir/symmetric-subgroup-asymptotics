#!/usr/bin/env python3
"""Export one pinned ``bindings8.g`` row without requiring a GAP runtime.

The historical GAP file is data, not a proof premise.  This selected-row
recovery exporter parses its literal permutations, enumerates the chosen
degree-eight top, and independently recomputes its conjugacy classes and
normal subgroups.  It has no bulk mode.  The downstream preparer rechecks
the resulting group, local quotient, Schreier action, and binary basis.

This recovery path is useful on machines where GAP is unavailable.  It is
deliberately restricted to rows whose top is computationally verified to
be simple: then the complete normal-subgroup list is exactly ``1,T``.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / "computations/frames/bindings8.g"
SOURCE_SHA256 = "d5a3ef513faa40a10f666478628f5f23f0a156db58e75d8a7be4068c3c2fa3fa"
SOURCE_LIMIT = 64 * 1024
OUTPUT_LIMIT = 4 * 1024 * 1024
TOKEN = re.compile(r":=|;;|[A-Za-z][A-Za-z0-9_]*|[0-9]+|[\[\]\(\),;]")


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


@dataclass(frozen=True)
class GapPerm:
    cycles: tuple[tuple[int, ...], ...]


@dataclass(frozen=True)
class GapGroup:
    generators: tuple[GapPerm, ...]


class Parser:
    def __init__(self, text: str):
        self.tokens = TOKEN.findall(text)
        compact = re.sub(r"\s+", "", text)
        require("".join(self.tokens) == compact,
                "unsupported token in pinned GAP source")
        self.at = 0

    def peek(self) -> str | None:
        return self.tokens[self.at] if self.at < len(self.tokens) else None

    def take(self, expected: str | None = None) -> str:
        require(self.at < len(self.tokens), "unexpected end of GAP source")
        token = self.tokens[self.at]
        if expected is not None:
            require(token == expected,
                    f"expected {expected!r}, found {token!r}")
        self.at += 1
        return token

    def parse_permutation(self) -> GapPerm:
        cycles: list[tuple[int, ...]] = []
        while self.peek() == "(":
            self.take("(")
            cycle: list[int] = []
            if self.peek() != ")":
                cycle.append(int(self.take()))
                while self.peek() == ",":
                    self.take(",")
                    cycle.append(int(self.take()))
            self.take(")")
            if cycle:
                require(len(cycle) >= 2, "singleton GAP cycle")
                cycles.append(tuple(cycle))
        return GapPerm(tuple(cycles))

    def parse_list(self) -> list[object]:
        self.take("[")
        result: list[object] = []
        if self.peek() != "]":
            result.append(self.parse_value())
            while self.peek() == ",":
                self.take(",")
                result.append(self.parse_value())
        self.take("]")
        return result

    def parse_call(self, name: str) -> object:
        self.take("(")
        arguments: list[object] = []
        if self.peek() != ")":
            arguments.append(self.parse_value())
            while self.peek() == ",":
                self.take(",")
                arguments.append(self.parse_value())
        self.take(")")
        if name == "Group":
            require(len(arguments) == 1, "invalid Group call")
            source = arguments[0]
            if isinstance(source, GapPerm):
                return GapGroup((source,))
            require(isinstance(source, list) and
                    all(isinstance(x, GapPerm) for x in source),
                    "invalid Group generator list")
            return GapGroup(tuple(source))
        if name == "List":
            require(len(arguments) == 2 and isinstance(arguments[0], list)
                    and arguments[1] == "Group",
                    "unsupported List call")
            return arguments[0]
        raise ValueError(f"unsupported GAP call {name}")

    def parse_value(self) -> object:
        token = self.peek()
        require(token is not None, "missing GAP value")
        if token == "[":
            return self.parse_list()
        if token == "(":
            return self.parse_permutation()
        if token.isdigit():
            self.take()
            return int(token)
        require(token[0].isalpha(), f"invalid GAP value token {token}")
        name = self.take()
        if self.peek() == "(":
            return self.parse_call(name)
        return name

    def assignments(self) -> dict[str, object]:
        result: dict[str, object] = {}
        while self.peek() is not None:
            name = self.take()
            require(name[0].isalpha(), "invalid assignment name")
            self.take(":=")
            result[name] = self.parse_value()
            self.take(";;")
        return result


def permutation(value: GapPerm, width: int) -> tuple[int, ...]:
    row = list(range(width))
    used: set[int] = set()
    for cycle1 in value.cycles:
        cycle = tuple(x - 1 for x in cycle1)
        require(all(0 <= x < width for x in cycle),
                "cycle point outside expected degree")
        require(not (used & set(cycle)), "overlapping GAP cycles")
        used.update(cycle)
        for left, right in zip(cycle, cycle[1:] + cycle[:1]):
            row[left] = right
    require(sorted(row) == list(range(width)), "invalid permutation")
    return tuple(row)


def gap_product(left: tuple[int, ...], right: tuple[int, ...]):
    """Rows for GAP right actions: ``i^(left*right)``."""
    return tuple(right[left[i]] for i in range(len(left)))


def inverse(row: tuple[int, ...]) -> tuple[int, ...]:
    result = [0] * len(row)
    for i, value in enumerate(row):
        result[value] = i
    return tuple(result)


def enumerate_group(generators: list[tuple[int, ...]], ceiling: int = 1152):
    require(generators, "empty selected top generator list")
    one = tuple(range(len(generators[0])))
    rows = [one]
    seen = {one}
    for row in rows:
        for generator in generators:
            child = gap_product(row, generator)
            if child not in seen:
                require(len(rows) < ceiling, "selected top order ceiling reached")
                seen.add(child)
                rows.append(child)
    return rows


def conjugate(x, g):
    return gap_product(gap_product(inverse(g), x), g)


def conjugacy_classes(group: list[tuple[int, ...]]):
    remaining = set(group)
    classes = []
    for representative in group:
        if representative not in remaining:
            continue
        orbit = {conjugate(representative, g) for g in group}
        require(orbit <= remaining, "conjugacy classes overlap")
        remaining.difference_update(orbit)
        classes.append((representative, len(orbit)))
    require(not remaining and sum(size for _, size in classes) == len(group),
            "conjugacy classes do not exhaust selected top")
    return classes


def generated_subgroup(generators, width: int, ceiling: int):
    if not generators:
        return {tuple(range(width))}
    return set(enumerate_group(list(generators), ceiling))


def normal_closure(x, group):
    conjugates = {conjugate(x, g) for g in group}
    return generated_subgroup(conjugates, len(x), len(group) + 1)


def rows(values: object, width: int) -> list[list[int]]:
    require(isinstance(values, list) and
            all(isinstance(x, GapPerm) for x in values),
            "expected GAP permutation list")
    return [[x + 1 for x in permutation(value, width)] for value in values]


def selected_binding(row_index: int) -> dict[str, object]:
    raw = SOURCE.read_bytes()
    require(SOURCE.is_file() and not SOURCE.is_symlink(),
            "missing or redirected bindings8 source")
    require(len(raw) <= SOURCE_LIMIT, "bindings8 source ceiling reached")
    require(hashlib.sha256(raw).hexdigest() == SOURCE_SHA256,
            "bindings8 source digest changed")
    parsed = Parser(raw.decode()).assignments()
    tops = parsed.get("FrameEightTops")
    bindings = parsed.get("FrameEightBindings")
    require(isinstance(tops, list) and len(tops) == 24,
            "unexpected literal top list")
    require(isinstance(bindings, list) and len(bindings) == 30,
            "unexpected binding list")
    require(0 <= row_index < 30, "selected row outside [0,30)")
    binding = bindings[row_index]
    require(isinstance(binding, list) and len(binding) == 7,
            "invalid selected binding shape")
    top_number, kernel, stabilizer, local_images, cosets, induced, basis = binding
    require(isinstance(top_number, int) and 1 <= top_number <= len(tops),
            "invalid selected top index")
    require(isinstance(kernel, GapGroup), "invalid selected kernel")
    top_source = tops[top_number - 1]
    require(isinstance(top_source, list), "invalid selected top generators")
    top_generators = [permutation(x, 8) for x in top_source]
    group = enumerate_group(top_generators)

    # The recovery exporter is intentionally limited to simple selected tops.
    one = tuple(range(8))
    for x in group:
        if x != one:
            require(len(normal_closure(x, group)) == len(group),
                    "selected top is not computationally simple")
    normal_generators = [[], top_generators]
    normal_orders = [1, len(group)]
    classes = conjugacy_classes(group)

    kernel_generators = [permutation(x, 8) for x in kernel.generators]
    kernel_group = generated_subgroup(kernel_generators, 8, len(group) + 1)
    stabilizer_rows = [permutation(x, 8) for x in stabilizer]
    stabilizer_group = generated_subgroup(stabilizer_rows, 8, len(group) + 1)
    literal_stabilizer = {g for g in group if g[0] == 0}
    require(stabilizer_group == literal_stabilizer,
            "stored stabilizer generators do not generate the point stabilizer")
    require(kernel_group <= stabilizer_group and len(kernel_group) in (1, 2, 4, 7,
            8, 12, 14, 24), "invalid selected stabilizer kernel")
    require(all({conjugate(x, h) for x in kernel_group} == kernel_group
                for h in stabilizer_group),
            "selected stabilizer kernel is not normal")

    return {
        "schema": "frames8-selected-binding-v1",
        "bindings_sha256": SOURCE_SHA256,
        "row": row_index,
        "top_index": top_number - 1,
        "top_order": len(group),
        "top_generators": [[x + 1 for x in row] for row in top_generators],
        "normal_generators": [
            [[x + 1 for x in row] for row in generators]
            for generators in normal_generators],
        "normal_orders": normal_orders,
        "class_representatives": [
            [x + 1 for x in representative] for representative, _ in classes],
        "class_sizes": [size for _, size in classes],
        "stabilizer_generators": rows(stabilizer, 8),
        "kernel_generators": [
            [x + 1 for x in row] for row in kernel_generators],
        "kernel_order": len(kernel_group),
        "local_images": rows(local_images, 3),
        "coset_representatives": rows(cosets, 8),
        "induced_generators": rows(induced, 32),
        "binary_basis": rows(basis, 32),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--row", type=int, required=True,
                        help="zero-based bindings8 row index")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = selected_binding(args.row)
    payload = (json.dumps(result, separators=(",", ":")) + "\n").encode()
    require(len(payload) <= OUTPUT_LIMIT, "selected binding output ceiling reached")
    args.output.write_bytes(payload)
    print(f"{args.output}: {len(payload)} bytes; row {args.row}; "
          f"top order {result['top_order']}; classes "
          f"{len(result['class_representatives'])}")


if __name__ == "__main__":
    main()
