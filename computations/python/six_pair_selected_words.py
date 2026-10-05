#!/usr/bin/env python3
"""Bounded compact-word search for one selected six-pair action.

This is a producer helper, never a verifier.  Every returned word is meant to
be emitted as a `FiniteGeneratorWord` or `FiniteNormalJoinWord`; Lean checks
the resulting literal equation.  Searches retain parent edges only and stop
at an explicit state/operation/time ceiling.
"""
from __future__ import annotations

from dataclasses import dataclass
import time


Permutation = tuple[int, ...]
Word = dict


class Refused(ValueError):
    pass


@dataclass
class Budget:
    operation_limit: int = 4_000_000
    seconds_limit: float = 60.0
    operations: int = 0

    def __post_init__(self):
        self.started = time.monotonic()

    def tick(self, amount: int = 1) -> None:
        self.operations += amount
        if self.operations > self.operation_limit:
            raise Refused("selected compact-word operation ceiling reached")
        if time.monotonic() - self.started > self.seconds_limit:
            raise Refused("selected compact-word cooperative time ceiling reached")


def identity(width: int) -> Permutation:
    return tuple(range(width))


def compose(a: Permutation, b: Permutation, budget: Budget) -> Permutation:
    if len(a) != len(b):
        raise Refused("permutation widths differ")
    budget.tick(len(a))
    return tuple(a[b[x]] for x in range(len(a)))


def inverse(a: Permutation, budget: Budget) -> Permutation:
    if sorted(a) != list(range(len(a))):
        raise Refused("row is not a permutation")
    result = [0] * len(a)
    budget.tick(len(a))
    for x, y in enumerate(a):
        result[y] = x
    return tuple(result)


def validate_permutation(a: Permutation, width: int, budget: Budget) -> None:
    budget.tick(width)
    if len(a) != width or sorted(a) != list(range(width)):
        raise Refused("invalid literal permutation")


def word_one() -> Word:
    return {"tag": "one"}


def word_generator(index: int) -> Word:
    return {"tag": "generator", "index": index}


def word_parent(index: int) -> Word:
    return {"tag": "parent", "index": index}


def word_conjugate(conjugator: Word) -> Word:
    return {"tag": "conjugate", "conjugator": conjugator}


def word_inv(word: Word) -> Word:
    return {"tag": "inv", "word": word}


def word_mul(left: Word, right: Word) -> Word:
    return {"tag": "mul", "left": left, "right": right}


def product_word(atoms: list[Word]) -> Word:
    result = word_one()
    for atom in atoms:
        result = word_mul(result, atom)
    return result


@dataclass(frozen=True)
class Enumeration:
    rows: tuple[Permutation, ...]
    position: dict[Permutation, int]
    parents: tuple[int, ...]
    letters: tuple[int, ...]
    alphabet_words: tuple[Word, ...]

    def word(self, index: int, *, max_word_length: int = 512) -> Word:
        atoms: list[Word] = []
        while index:
            atoms.append(self.alphabet_words[self.letters[index]])
            index = self.parents[index]
            if len(atoms) > max_word_length:
                raise Refused("compact word exceeds selected length ceiling")
        atoms.reverse()
        return product_word(atoms)


def enumerate_generated(
    alphabet: list[tuple[Permutation, Word]],
    width: int,
    budget: Budget,
    *,
    max_states: int = 65_536,
) -> Enumeration:
    if not 1 <= width <= 32:
        raise Refused("unsupported selected permutation width")
    if len(alphabet) > 2_048:
        raise Refused("selected word alphabet ceiling reached")
    for row, _ in alphabet:
        validate_permutation(row, width, budget)
    one = identity(width)
    rows = [one]
    position = {one: 0}
    parents = [0]
    letters = [0]
    cursor = 0
    while cursor < len(rows):
        x = rows[cursor]
        for letter, (g, _) in enumerate(alphabet):
            y = compose(x, g, budget)
            if y not in position:
                if len(rows) >= max_states:
                    raise Refused("selected generated-group state ceiling reached")
                position[y] = len(rows)
                rows.append(y)
                parents.append(cursor)
                letters.append(letter)
        cursor += 1
    return Enumeration(tuple(rows), position, tuple(parents), tuple(letters),
                       tuple(word for _, word in alphabet))


def signed_generator_alphabet(
    generators: list[Permutation], width: int, budget: Budget
) -> list[tuple[Permutation, Word]]:
    result: list[tuple[Permutation, Word]] = []
    for i, generator in enumerate(generators):
        validate_permutation(generator, width, budget)
        result.append((generator, word_generator(i)))
        result.append((inverse(generator, budget), word_inv(word_generator(i))))
    return result


def generator_enumeration(
    generators: list[Permutation], width: int, budget: Budget, *,
    max_states: int = 65_536,
) -> Enumeration:
    return enumerate_generated(
        signed_generator_alphabet(generators, width, budget), width, budget,
        max_states=max_states)


def target_words(
    generators: list[Permutation], targets: list[Permutation], width: int,
    budget: Budget, *, max_states: int = 65_536,
) -> list[Word]:
    enumeration = generator_enumeration(
        generators, width, budget, max_states=max_states)
    result = []
    for target in targets:
        validate_permutation(target, width, budget)
        if target not in enumeration.position:
            raise Refused("target is outside the selected literal subgroup")
        result.append(enumeration.word(enumeration.position[target]))
    return result


def conjugate(g: Permutation, x: Permutation, budget: Budget) -> Permutation:
    return compose(compose(g, x, budget), inverse(g, budget), budget)


def normality_words(
    ambient_generators: list[Permutation], state_generators: list[Permutation],
    width: int, budget: Budget, *, max_states: int = 65_536,
) -> dict:
    state = generator_enumeration(
        state_generators, width, budget, max_states=max_states)
    positive, negative = [], []
    for ambient in ambient_generators:
        ambient_inverse = inverse(ambient, budget)
        positive_row, negative_row = [], []
        for generator in state_generators:
            for target, output in (
                (conjugate(ambient, generator, budget), positive_row),
                (conjugate(ambient_inverse, generator, budget), negative_row),
            ):
                if target not in state.position:
                    raise Refused("selected normality conjugate escaped the state")
                output.append(state.word(state.position[target]))
        positive.append(positive_row)
        negative.append(negative_row)
    return {"positive": positive, "negative": negative}


def join_transition_words(
    ambient_generators: list[Permutation],
    parent_generators: list[Permutation],
    representative: Permutation,
    child_generators: list[Permutation],
    width: int,
    budget: Budget,
    *,
    max_states: int = 65_536,
) -> dict:
    """Words proving one exact parent/normal-closure/child transition."""
    ambient = generator_enumeration(
        ambient_generators, width, budget, max_states=max_states)
    child = generator_enumeration(
        child_generators, width, budget, max_states=max_states)

    parent_to_child = []
    for target in parent_generators:
        if target not in child.position:
            raise Refused("parent generator escaped selected child state")
        parent_to_child.append(child.word(child.position[target]))
    if representative not in child.position:
        raise Refused("class representative escaped selected child state")
    representative_word = child.word(child.position[representative])

    alphabet: list[tuple[Permutation, Word]] = []
    for i, generator in enumerate(parent_generators):
        alphabet.append((generator, word_parent(i)))
        alphabet.append((inverse(generator, budget), word_inv(word_parent(i))))
    seen_conjugates: set[Permutation] = set()
    for index, g in enumerate(ambient.rows):
        atom = conjugate(g, representative, budget)
        if atom in seen_conjugates:
            continue
        seen_conjugates.add(atom)
        conjugator_word = ambient.word(index)
        alphabet.append((atom, word_conjugate(conjugator_word)))
        alphabet.append((inverse(atom, budget),
                         word_inv(word_conjugate(conjugator_word))))
    joined = enumerate_generated(
        alphabet, width, budget, max_states=max_states)
    child_words = []
    for target in child_generators:
        if target not in joined.position:
            raise Refused("child generator escaped checked normal join")
        child_words.append(joined.word(joined.position[target]))
    return {
        "parent_to_child": parent_to_child,
        "representative_word": representative_word,
        "child_to_join": child_words,
    }
