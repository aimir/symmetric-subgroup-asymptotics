#!/usr/bin/env python3
"""Verify the literal degree-16 quotient chart using only Python's standard library.

The certificate uses one-based permutation images. Internally permutations are
zero-based tuples, and compose(x, y) means x after y. No group catalogue is used.
This is a computational verifier, not a Lean proof or a completeness check.
"""

import argparse
from collections import Counter, deque
import json
from pathlib import Path
import sys


DEFAULT_CERTIFICATE = (
    Path(__file__).resolve().parents[2]
    / "certificates/data/degree16_quotient.json"
)


class VerificationError(ValueError):
    """The supplied data does not satisfy the certificate contract."""


def require(condition, message):
    if not condition:
        raise VerificationError(message)


def compose(x, y):
    return tuple(x[y[i]] for i in range(len(x)))


def inverse(x):
    result = [0] * len(x)
    for i, j in enumerate(x):
        result[j] = i
    return tuple(result)


def generated(generators):
    """Enumerate the finite permutation group by generator multiplication."""
    identity = tuple(range(len(generators[0])))
    seen = {identity}
    queue = deque([identity])
    while queue:
        x = queue.popleft()
        for g in generators:
            y = compose(x, g)
            if y not in seen:
                seen.add(y)
                queue.append(y)
    return seen


def read_generators(data, field, degree):
    rows = data.get(field)
    require(isinstance(rows, list) and bool(rows), f"{field}: nonempty list required")
    expected = list(range(1, degree + 1))
    for row in rows:
        require(
            isinstance(row, list)
            and len(row) == degree
            and all(type(value) is int for value in row)
            and sorted(row) == expected,
            f"{field}: each row must be a permutation of 1,...,{degree}",
        )
    return [tuple(value - 1 for value in row) for row in rows]


def element_order(x):
    identity = tuple(range(len(x)))
    power = x
    order = 1
    while power != identity:
        power = compose(power, x)
        order += 1
    return order


def verify(data):
    require(isinstance(data, dict), "certificate must be a JSON object")
    for field, expected in (
        ("degree", 16),
        ("source_order", 1024),
        ("kernel_order", 4),
        ("image_order", 256),
    ):
        require(
            type(data.get(field)) is int and data[field] == expected,
            f"{field} must be the integer {expected}",
        )
    require(
        data.get("target_orbit_types")
        == ["C4 regular", "D8 natural", "D8 natural", "D8 natural"],
        "target orbit-type metadata does not match the stated chart",
    )
    degree = data["degree"]
    source_generators = read_generators(data, "source_generators", degree)
    image_generators = read_generators(data, "image_generators", degree)
    kernel_generators = read_generators(data, "kernel_generators", degree)
    require(
        len(source_generators) == len(image_generators),
        "every source generator must have exactly one corresponding image",
    )

    identity = tuple(range(degree))
    source = generated(source_generators)
    image = generated(image_generators)
    kernel = generated(kernel_generators)
    require(len(source) == 1024, "source must have order 1024")
    require(len(image) == 256, "image must have order 256")
    require(len(kernel) == 4, "proposed kernel must have order 4")
    require({x[0] for x in source} == set(range(degree)), "source must be transitive")

    # Propagate the proposed map across the complete source Cayley graph.
    # Agreement on every edge proves all words defining one element have the
    # same image. Equal list lengths were checked before pairing generators.
    mapping = {identity: identity}
    queue = deque([identity])
    while queue:
        x = queue.popleft()
        for s, p in zip(source_generators, image_generators):
            y = compose(x, s)
            z = compose(mapping[x], p)
            if y in mapping:
                require(mapping[y] == z, "source relation fails in the proposed image")
            else:
                mapping[y] = z
                queue.append(y)
    require(set(mapping) == source, "map does not cover the full source")
    require(set(mapping.values()) == image, "map is not onto the full image")
    require(
        {x for x, y in mapping.items() if y == identity} == kernel,
        "actual kernel differs from the specified subgroup",
    )
    fibres = Counter(mapping.values())
    require(all(size == 4 for size in fibres.values()), "quotient fibres must have size 4")

    centre = {
        x for x in image
        if all(compose(x, g) == compose(g, x) for g in image_generators)
    }
    require(
        len(centre) == 16 and all(compose(x, x) == identity for x in centre),
        "whole centre must be elementary abelian of order 16",
    )
    commutators = [
        compose(compose(inverse(x), inverse(y)), compose(x, y))
        for x in image_generators for y in image_generators
    ]
    derived = generated(commutators)
    require(
        derived <= centre and len(derived) == 8,
        "generator commutators must generate a central subgroup of order 8",
    )
    # Central generator commutators generate the full derived subgroup.
    # In this class-two group, generator squares and commutators generate
    # P^2[P,P], which is the Frattini subgroup of the finite 2-group P.
    frattini = generated(commutators + [compose(x, x) for x in image_generators])
    require(frattini == centre, "Frattini subgroup must equal the centre")
    require(
        all(compose(compose(x, x), compose(x, x)) == identity for x in image),
        "every image element must have order dividing four",
    )

    orbits = []
    remaining = set(range(degree))
    while remaining:
        orbit = {g[min(remaining)] for g in image}
        orbits.append(sorted(orbit))
        remaining -= orbit
    require(
        orbits == [list(range(i, i + 4)) for i in range(0, degree, 4)],
        "target must have the four specified degree-four orbits",
    )
    projection_types = []
    projection_orders = []
    for orbit in orbits:
        positions = {point: i for i, point in enumerate(orbit)}
        generators = [
            tuple(positions[g[point]] for point in orbit) for g in image_generators
        ]
        projection = generated(generators)
        require({g[0] for g in projection} == set(range(4)), "projection not transitive")
        maximum_order = max(element_order(x) for x in projection)
        if len(projection) == 4:
            require(maximum_order == 4, "order-four projection must be cyclic")
            projection_types.append("C4")
        else:
            # An order-eight subgroup of S4 is a Sylow 2-subgroup, hence D8.
            require(len(projection) == 8 and maximum_order == 4, "expected a D8 projection")
            require(
                any(compose(x, y) != compose(y, x) for x in generators for y in generators),
                "D8 projection must be nonabelian",
            )
            projection_types.append("D8")
        projection_orders.append(len(projection))
    require(projection_types == ["C4", "D8", "D8", "D8"], "wrong ordered target types")
    require(len(image) < 4 * 8**3, "target must retain its proper subdirect relations")
    return {
        "source_order": len(source),
        "kernel_order": len(kernel),
        "image_order": len(image),
        "projection_orders": projection_orders,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", nargs="?", type=Path, default=DEFAULT_CERTIFICATE)
    args = parser.parse_args()
    try:
        result = verify(json.loads(args.certificate.read_text()))
    except (OSError, ValueError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        return 1
    print(
        "PASS: degree-16 transitive source of order "
        f"{result['source_order']} maps onto order {result['image_order']} "
        f"with exact kernel order {result['kernel_order']}."
    )
    print("Target orbits: C4[4], D8[4], D8[4], D8[4]; proper subdirect image retained.")
    print("Centre = Frattini = C2^4; derived subgroup = C2^3; exponent four.")
    print("Same physical degree; the C4 orbit retains noncritical degree 4/16.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
