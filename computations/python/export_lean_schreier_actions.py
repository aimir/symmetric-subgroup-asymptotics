#!/usr/bin/env python3
"""Export one bounded original-action Schreier child certificate.

The emitted proof uses only original permutations, sparse relation witnesses,
point colourings, and two-way generator words. It has no source/target order
or source-element-table premise. Source selection is mandatory; there is no
bulk-build mode. Run Lean separately through scripts/check_lean.py.
"""

import argparse
import gzip
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
from export_lean_menu_cayley import ROOT, array, lookup
from permutation_words import (_word, character_relations, compose, evaluate, inverse,
                               orbit_coloring, positive_words,
                               schreier_generators)


def raw(generators):
    return [tuple(x - 1 for x in g) for g in generators]


def label(name):
    return name.removeprefix('b').replace('_', 'T')


def word_literal(word, degree=None):
    if degree is None:
        return '[' + ','.join(map(str, word)) + ']'
    return '[' + ','.join(f'({str(i >= degree).lower()},{i % degree})' for i in word) + ']'


def permutation(name, p):
    width = len(p)
    return f'''private def {name} : Equiv.Perm (Fin {width}) where
  toFun x := ({array(p)} : Array (Fin {width}))[x.val]!
  invFun x := ({array(inverse(p))} : Array (Fin {width}))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

'''


def generator_tuple(name, generators):
    text = ''.join(permutation(f'{name}{i}', g) for i, g in enumerate(generators))
    text += f'''def {name} (j : Fin {len(generators)}) : Equiv.Perm (Fin {len(generators[0])}) :=
  {lookup([f'{name}{i}' for i in range(len(generators))], 'j.val')}

'''
    return text


class _ForwardWordPrefix:
    """One deterministic BFS prefix for an exact ordered generator tuple."""

    __slots__ = ('generators', 'rows', 'indices', 'parents', 'letters', 'cursor',
                 'value_bytes')

    def __init__(self, generators, width):
        self.generators = generators
        identity = tuple(range(width))
        self.rows, self.indices = [identity], {identity: 0}
        self.parents, self.letters, self.cursor = [0], [0], 0
        # Charge referenced integers even when Python shares them. This is a
        # conservative retained-object budget, not a process RSS measurement.
        self.value_bytes = (sys.getsizeof(generators)
                            + sum(self._permutation_bytes(g) for g in generators)
                            + self._permutation_bytes(identity)
                            + 3 * sys.getsizeof(0))

    @staticmethod
    def _permutation_bytes(p):
        return sys.getsizeof(p) + sum(sys.getsizeof(x) for x in p)

    def storage_bytes(self):
        return (sys.getsizeof(self) + self.value_bytes + sys.getsizeof(self.value_bytes)
                + sys.getsizeof(self.cursor)
                + sum(sys.getsizeof(x) for x in
                      (self.rows, self.indices, self.parents, self.letters)))

    def append(self, row, parent, letter):
        index = len(self.rows)
        self.indices[row] = index
        self.rows.append(row)
        self.parents.append(parent)
        self.letters.append(letter)
        self.value_bytes += (self._permutation_bytes(row) + sys.getsizeof(index)
                             + sys.getsizeof(parent) + sys.getsizeof(letter))


class _ForwardWordCache:
    """Bounded search reuse within one selected compile_witnesses call.

    Only forward searches are cached, keyed by width and the literal ordered
    target generators. Prefixes stop at complete BFS parent rows, exactly as
    positive_words does, so every returned shortest word is unchanged.
    Both per-prefix and aggregate state limits apply. The byte limit charges
    retained Python objects conservatively; it excludes interpreter overhead,
    temporary call arguments and the caller's resulting witnesses. It is not
    an OS RSS cap. A container resize can cross it by one insertion; that
    insertion immediately raises ValueError and aborts witness production.
    Nothing is evicted, serialized, or treated as nonmembership on a limit.
    """

    __slots__ = ('max_states', 'max_word_length', 'max_cache_states', 'max_cache_bytes',
                 'prefixes', 'states', 'cache_bytes')

    def __init__(self, *, max_states, max_word_length, max_cache_states, max_cache_bytes):
        if min(max_states, max_word_length, max_cache_states, max_cache_bytes) < 1:
            raise ValueError('all forward-search limits must be positive')
        self.max_states, self.max_word_length = max_states, max_word_length
        self.max_cache_states, self.max_cache_bytes = max_cache_states, max_cache_bytes
        self.prefixes, self.states = {}, 0
        self.cache_bytes = (sys.getsizeof(self) + sys.getsizeof(self.prefixes)
                            + sum(sys.getsizeof(n) for n in
                                  (max_states, max_word_length, max_cache_states,
                                   max_cache_bytes, max_cache_states, 4 * max_cache_bytes)))
        self._check_bytes()

    def _check_bytes(self):
        if self.cache_bytes > self.max_cache_bytes:
            raise ValueError('forward-word cache exceeds configured byte limit')

    def _reserve_state(self):
        if self.states >= self.max_cache_states:
            raise ValueError('forward-word cache exceeds configured aggregate state limit')

    def words(self, generators, targets, width):
        generators = tuple(map(tuple, generators))
        targets = tuple(map(tuple, targets))
        key = (width, generators)
        if key not in self.prefixes:
            self._reserve_state()
            prefix = _ForwardWordPrefix(generators, width)
            before = sys.getsizeof(self.prefixes)
            self.prefixes[key] = prefix
            self.states += 1
            self.cache_bytes += (prefix.storage_bytes() + sys.getsizeof(key)
                                 + sys.getsizeof(width) + sys.getsizeof(self.prefixes) - before)
            self._check_bytes()
        prefix = self.prefixes[key]
        missing = set(targets).difference(prefix.indices)
        while missing and prefix.cursor < len(prefix.rows):
            x = prefix.rows[prefix.cursor]
            for j, g in enumerate(prefix.generators):
                y = compose(x, g)
                if y not in prefix.indices:
                    if len(prefix.rows) >= self.max_states:
                        raise ValueError('positive-word search exceeds configured state limit')
                    self._reserve_state()
                    before = prefix.storage_bytes()
                    prefix.append(y, prefix.cursor, j)
                    self.states += 1
                    self.cache_bytes += prefix.storage_bytes() - before
                    self._check_bytes()
                    missing.discard(y)
            # Do not stop halfway through a parent, even if its first child
            # completed this request. Later requests resume the identical BFS.
            before = sys.getsizeof(prefix.cursor)
            prefix.cursor += 1
            self.cache_bytes += sys.getsizeof(prefix.cursor) - before
            self._check_bytes()
        if missing:
            raise KeyError('target is outside the literal generated subgroup')
        result = [_word(prefix.parents, prefix.letters, prefix.indices[t], self.max_word_length)
                  for t in targets]
        assert all(evaluate(generators, word, width) == t for word, t in zip(result, targets))
        return result


def compile_witnesses(node, action, nodes, *, max_states, max_word_length, max_assignments,
                     max_cache_states=65536, max_cache_bytes=64 * 1024 * 1024):
    gs, width = raw(node['generators']), node['degree']
    degree = len(gs)
    if 2 ** degree > max_assignments:
        raise ValueError('assignment count exceeds configured limit')
    bounds = dict(max_states=max_states, max_word_length=max_word_length)
    forward_cache = _ForwardWordCache(**bounds, max_cache_states=max_cache_states,
                                      max_cache_bytes=max_cache_bytes)
    relations = character_relations(gs, width, **bounds)
    edges = action['action_children']
    branches = []
    for assignment in range(2 ** degree):
        if assignment == 2 ** degree - 1:
            branches.append(dict(kind='trivial'))
            continue
        bad = next(((u, v) for mask, u, v in relations
                    if (mask & ~assignment).bit_count() % 2), None)
        if bad:
            branches.append(dict(kind='relation', words=bad))
            continue
        bits = [bool(assignment & (1 << j)) for j in range(degree)]
        outside = bits.index(False)
        schreier = schreier_generators(gs, bits, gs[outside])
        color, missing = orbit_coloring(schreier, width)
        if missing is not None:
            branches.append(dict(kind='color', outside=outside, color=color, missing=missing))
            continue
        for edge in edges:
            target = raw(nodes[edge['target']]['generators'])
            conjugator = tuple(x - 1 for x in edge['conjugator'])
            conjugated = [compose(compose(conjugator, g), inverse(conjugator)) for g in schreier]
            try:
                forward = forward_cache.words(target, conjugated, width)
                backward = positive_words(conjugated, target, width, **bounds)
            except KeyError:
                continue
            branches.append(dict(kind='accepted', outside=outside, target=edge['target'],
                                 conjugator=conjugator, forward=forward, backward=backward))
            break
        else:
            raise ValueError(f'no literal two-way edge for {node["id"]}, assignment {assignment}')
    return branches


def emit(node, nodes, branches):
    width, name = node['degree'], node['id']
    gs = raw(node['generators'])
    degree, assignments = len(gs), 2 ** len(gs)
    targets = sorted({b['target'] for b in branches if b['kind'] == 'accepted'})
    # Fin 0 targets is legitimate when every index-two child is intransitive.
    text = f'''import SymmetricSubgroupAsymptotics.BinarySchreierRegistry

/-! Word-sized complete original index-two child coverage for {name}.
Generated by export_lean_schreier_actions.py. No group-order premise. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.BinarySchreierChildren{label(name)}

'''
    text += generator_tuple('generators', gs)
    for k, target in enumerate(targets):
        text += generator_tuple(f'target{k}Generators', raw(nodes[target]['generators']))
    target_terms = [f'Subgroup.closure (Set.range target{k}Generators)' for k in range(len(targets))]
    target_value = lookup(target_terms, 'k.val') if targets else 'Fin.elim0 k'
    text += f'''def targets (k : Fin {len(targets)}) : Subgroup (Equiv.Perm (Fin {width})) :=
  {target_value}

'''
    for b, branch in enumerate(branches):
        if branch['kind'] not in ('color', 'accepted'):
            continue
        text += f'''private def child{b} := binarySchreierWords generators
  (schreierAssignment ({b} : Fin {assignments})) (generators {branch['outside']})

'''
        if branch['kind'] == 'color':
            text += f'''private def color{b} (x : Fin {width}) : Bool :=
  {lookup([str(c).lower() for c in branch['color']], 'x.val')}
private theorem intransitive{b} :
    ¬PermutationSubgroupTransitive (Subgroup.closure (Set.range child{b})) :=
  generated_not_transitive_of_coloring child{b} color{b} 0 {branch['missing']}
    (by decide +kernel) (by decide +kernel)

'''
            continue
        k = targets.index(branch['target'])
        text += permutation(f'conjugator{b}', branch['conjugator'])
        forward = [word_literal(w) for w in branch['forward']]
        backward = [word_literal(w, degree) for w in branch['backward']]
        text += f'''private def forward{b} : BinaryNormalGeneratorWords
    (fun j => MulAut.conj conjugator{b} (child{b} j)) target{k}Generators where
  words j := if j.1 then {lookup(forward[degree:], 'j.2.val')}
    else {lookup(forward[:degree], 'j.2.val')}
  equations := by decide +kernel
private def backward{b} : BinaryNormalGeneratorWords target{k}Generators
    (fun j => MulAut.conj conjugator{b} (child{b} j)) where
  words j := {lookup(backward, 'j.val')}
  equations := by decide +kernel
private theorem conjugacy{b} :
    MulAut.conj conjugator{b} • Subgroup.closure (Set.range child{b}) = targets {k} :=
  generatorWords_conjugacy child{b} target{k}Generators conjugator{b} forward{b} backward{b}

'''
    text += f'''private theorem checked {{I : Type*}}
    (actions : I → Subgroup (Equiv.Perm (Fin {width})))
    (hcovered : ∀ k, ActionRegistryCovered actions (targets k)) :
    ∀ bits : Fin {degree} → Bool, (∃ j, bits j=false) →
      (∀ u v : List (Fin {degree}), (u.map generators).prod=(v.map generators).prod →
        binaryWordBit bits u=binaryWordBit bits v) →
      ∃ j, bits j=false ∧
        (¬PermutationSubgroupTransitive (Subgroup.closure
          (Set.range (binarySchreierWords generators bits (generators j)))) ∨
        ActionRegistryCovered actions (Subgroup.closure
          (Set.range (binarySchreierWords generators bits (generators j))))) := by
  intro bits
  obtain ⟨b,rfl⟩ := schreierAssignment_surjective {degree} bits
  fin_cases b
'''
    for b, branch in enumerate(branches):
        kind = branch['kind']
        if kind == 'trivial':
            text += f'''  · intro hn _
    exact False.elim ((show ¬(∃ j : Fin {degree},
      schreierAssignment ({b} : Fin {assignments}) j=false) from by decide +kernel) hn)
'''
        elif kind == 'relation':
            u, v = map(word_literal, branch['words'])
            # The numeric word literals provide no independent Fin d type.
            # Fix d explicitly before kernel reduction of the Boolean goal.
            text += f'''  · intro _ hs
    exact False.elim ((show binaryWordBit (schreierAssignment (d := {degree}) ({b} : Fin {assignments})) {u} ≠
      binaryWordBit (schreierAssignment (d := {degree}) ({b} : Fin {assignments})) {v} from by decide +kernel)
      (hs {u} {v} (by decide +kernel)))
'''
        elif kind == 'color':
            text += f'''  · intro _ _
    exact ⟨{branch['outside']},by decide +kernel,Or.inl intransitive{b}⟩
'''
        else:
            k = targets.index(branch['target'])
            text += f'''  · intro _ _
    refine ⟨{branch['outside']},by decide +kernel,Or.inr ?_⟩
    apply actionRegistryCovered_of_conjugate actions conjugator{b}
    change ActionRegistryCovered actions
      (MulAut.conj conjugator{b} • Subgroup.closure (Set.range child{b}))
    rw [conjugacy{b}]
    exact hcovered {k}
'''
    text += f'''
/-- Every actual transitive index-two child is one of the literal target
actions up to ambient point conjugation. Target coverage is compositional. -/
theorem children_of_covered {{I : Type*}} (actions : I → Subgroup (Equiv.Perm (Fin {width})))
    (hcovered : ∀ k, ActionRegistryCovered actions (targets k))
    (K : Subgroup (Equiv.Perm (Fin {width})))
    (hle : K ≤ Subgroup.closure (Set.range generators))
    (hindex : K.relIndex (Subgroup.closure (Set.range generators))=2)
    (ht : PermutationSubgroupTransitive K) : ActionRegistryCovered actions K :=
  binary_schreier_registry_children generators actions (checked actions hcovered) K hle hindex ht

/-- Unconditional local coverage by the literal targets named in this
certificate. No previously assumed registry coverage is required. -/
theorem children (K : Subgroup (Equiv.Perm (Fin {width})))
    (hle : K ≤ Subgroup.closure (Set.range generators))
    (hindex : K.relIndex (Subgroup.closure (Set.range generators))=2)
    (ht : PermutationSubgroupTransitive K) : ActionRegistryCovered targets K := by
  apply children_of_covered targets ?_ K hle hindex ht
  intro k
  exact ⟨k,1,by simp⟩

end SymmetricSubgroupAsymptotics.BinarySchreierChildren{label(name)}
'''
    return text


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', required=True, help='One original node, e.g. b16_1086')
    parser.add_argument('--output-dir', type=Path,
                        default=ROOT / 'formal/SymmetricSubgroupAsymptotics/GeneratedSchreierActions')
    parser.add_argument('--max-states', type=int, default=65536)
    parser.add_argument('--max-cache-states', type=int, default=65536,
                        help='Aggregate retained forward-BFS states for this one source')
    parser.add_argument('--max-cache-bytes', type=int, default=64 * 1024 * 1024,
                        help='Conservative retained-object cache budget; not a process RSS cap')
    parser.add_argument('--max-word-length', type=int, default=256)
    parser.add_argument('--max-assignments', type=int, default=256)
    parser.add_argument('--max-output-bytes', type=int, default=2 * 1024 * 1024)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    if min(args.max_states, args.max_word_length, args.max_assignments, args.max_output_bytes,
           args.max_cache_states, args.max_cache_bytes) < 1:
        parser.error('all limits must be positive')
    with gzip.open(ROOT / 'certificates/data/binary_menu.jsonl.gz', 'rt') as f:
        header = json.loads(next(f))
        nodes = {n['id']: n for n in header['nodes']}
        if args.source not in nodes:
            parser.error('unknown original source')
        action = next((r for r in map(json.loads, f)
                       if r.get('kind') == 'action' and r['id'] == args.source), None)
    if action is None:
        parser.error('source has no action record')
    branches = compile_witnesses(nodes[args.source], action, nodes,
                                 max_states=args.max_states,
                                 max_word_length=args.max_word_length,
                                 max_assignments=args.max_assignments,
                                 max_cache_states=args.max_cache_states,
                                 max_cache_bytes=args.max_cache_bytes)
    data = emit(nodes[args.source], nodes, branches).encode()
    if len(data) > args.max_output_bytes:
        raise SystemExit('certificate exceeds configured output limit; split it before proceeding')
    path = args.output_dir / f'Source{label(args.source)}.lean'
    if args.check:
        if not path.is_file() or path.read_bytes() != data:
            raise SystemExit(f'Generated witness differs: {path}')
    else:
        args.output_dir.mkdir(parents=True, exist_ok=True)
        if not path.exists() or path.read_bytes() != data:
            path.write_bytes(data)
    counts = {kind: sum(b['kind'] == kind for b in branches)
              for kind in ('trivial', 'relation', 'color', 'accepted')}
    print(json.dumps(dict(source=args.source, file=str(path), bytes=len(data), branches=counts), sort_keys=True))


if __name__ == '__main__':
    main()
