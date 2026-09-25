"""Bounded positive-word witnesses for literal permutation generators.

The search results are untrusted witnesses. Consumers must check their
equations in Lean. No group order returned by a search is a proof premise.
Only parent indices are stored during a search, not a word for every row.
"""

from collections import deque


def compose(a, b):
    return tuple(a[x] for x in b)


def inverse(p):
    q = [0] * len(p)
    for i, x in enumerate(p):
        q[x] = i
    return tuple(q)


def evaluate(generators, word, width):
    result = tuple(range(width))
    for j in word:
        result = compose(result, generators[j])
    return result


def _word(parents, letters, i, max_word_length):
    result = []
    while i:
        result.append(letters[i])
        i = parents[i]
        if len(result) > max_word_length:
            raise ValueError("positive word exceeds configured length limit")
    return list(reversed(result))


def positive_words(generators, targets, width, *, max_states=65536,
                   max_word_length=256):
    """Return a shortest positive word for each target, stopping when found.

    Raise KeyError if a target is outside the generated group, and ValueError
    on a configured resource bound. No source table is serialized.
    """
    generators = tuple(map(tuple, generators))
    targets = tuple(map(tuple, targets))
    identity = tuple(range(width))
    rows, indices, parents, letters = [identity], {identity: 0}, [0], [0]
    missing = set(targets) - {identity}
    cursor = 0
    while missing and cursor < len(rows):
        x = rows[cursor]
        for j, g in enumerate(generators):
            y = compose(x, g)
            if y not in indices:
                if len(rows) >= max_states:
                    raise ValueError("positive-word search exceeds configured state limit")
                indices[y] = len(rows)
                rows.append(y)
                parents.append(cursor)
                letters.append(j)
                missing.discard(y)
        cursor += 1
    if missing:
        raise KeyError("target is outside the literal generated subgroup")
    result = [_word(parents, letters, indices[t], max_word_length) for t in targets]
    assert all(evaluate(generators, ws, width) == t for ws, t in zip(result, targets))
    return result


def character_relations(generators, width, *, max_states=65536,
                        max_word_length=256):
    """Return at most d independent positive-word relation witnesses.

    Parent-edge parity labels provide a spanning-tree character test. Every
    retained relation is a literal equality; independence is only a producer
    compression step, never relied on by the emitted proof.
    """
    identity = tuple(range(width))
    rows, indices, parents, letters, parities = [identity], {identity: 0}, [0], [0], [0]
    pivots, witnesses = {}, []
    for i, x in enumerate(rows):
        for j, g in enumerate(generators):
            y = compose(x, g)
            parity = parities[i] ^ (1 << j)
            if y not in indices:
                if len(rows) >= max_states:
                    raise ValueError("relation search exceeds configured state limit")
                indices[y] = len(rows)
                rows.append(y)
                parents.append(i)
                letters.append(j)
                parities.append(parity)
                continue
            target = indices[y]
            mask = parity ^ parities[target]
            reduced = mask
            while reduced and reduced.bit_length() - 1 in pivots:
                reduced ^= pivots[reduced.bit_length() - 1]
            if reduced:
                pivots[reduced.bit_length() - 1] = reduced
                u = _word(parents, letters, i, max_word_length) + [j]
                v = _word(parents, letters, target, max_word_length)
                if len(u) > max_word_length:
                    raise ValueError("relation exceeds configured word length limit")
                assert evaluate(generators, u, width) == evaluate(generators, v, width)
                witnesses.append((mask, u, v))
    return witnesses


def orbit_coloring(generators, width):
    """Return the orbit-of-zero colouring and a point outside it, if any."""
    reached, queue = {0}, deque([0])
    while queue:
        x = queue.popleft()
        for g in generators:
            y = g[x]
            if y not in reached:
                reached.add(y)
                queue.append(y)
    outside = next((x for x in range(width) if x not in reached), None)
    color = [x in reached for x in range(width)]
    assert all(color[g[x]] == color[x] for g in generators for x in range(width))
    return color, outside


def schreier_generators(generators, bits, outside):
    """Tuple order is (false,j) first, then (true,j), matching Lean."""
    identity = tuple(range(len(outside)))
    return [compose(compose(identity if b else outside, g),
                    inverse(identity if b == bit else outside))
            for b in (False, True) for g, bit in zip(generators, bits)]
