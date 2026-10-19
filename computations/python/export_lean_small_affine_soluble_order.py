#!/usr/bin/env python3
"""Emit ONE small right-generator/word cardinality certificate (order <= 78).

This never builds an action table or normal lattice. The selected original
primitive row's generators fixing point 1 define the representative. Lean
checks every listed word, right-generator transition and distinctness.
"""
import argparse
from collections import deque
import gzip
import hashlib
import json
from pathlib import Path

p = argparse.ArgumentParser()
p.add_argument('--degree', type=int, choices=[8, 16, 27], required=True)
p.add_argument('--index', type=int, required=True)
p.add_argument('--repository', type=Path, default=Path(__file__).resolve().parents[2])
p.add_argument('--receipt-dir', type=Path, required=True,
               help='External directory for generation metadata; never inside the repository')
p.add_argument('--verify-existing', action='store_true')
a = p.parse_args()
REPO = a.repository.resolve()
BASE = a.receipt_dir.resolve()
assert BASE != REPO and REPO not in BASE.parents, 'Keep generation records outside the repository'
BASE.mkdir(parents=True, exist_ok=True)
assert 1 <= a.index <= {8: 2, 16: 10, 27: 9}[a.degree]
data = REPO / 'certificates/data/primitive_rank.jsonl.gz'
with gzip.open(data, 'rt') as f:
    rows = [x for line in f if (x := json.loads(line)).get('degree') == a.degree
            and x.get('index') == a.index and 'socle' in x]
assert len(rows) == 1
row = rows[0]
generators = [tuple(y - 1 for y in g) for g in row['generators'] if g[0] == 1]
assert generators and len(generators) + 1 == len(row['generators'])
expected = row['order'] // a.degree
assert row['order'] == a.degree * expected and expected <= 78
identity = tuple(range(a.degree))
elements, words, indices = [identity], [[]], {identity: 0}
pending = deque([0])
transitions = []
while pending:
    i = pending.popleft()
    nxt = []
    for j, g in enumerate(generators):
        e = tuple(elements[i][g[k]] for k in range(a.degree))
        if e not in indices:
            assert len(elements) < 78, 'Selected certificate exceeds tiny ceiling'
            indices[e] = len(elements)
            elements.append(e)
            words.append(words[i] + [j])
            pending.append(indices[e])
        nxt.append(indices[e])
    transitions.append(nxt)
assert len(elements) == expected

def vec(xs):
    return '![' + ', '.join(map(str, xs)) + ']'

def perm(name, xs):
    inv = [xs.index(i) for i in range(a.degree)]
    return f'''def {name} : Equiv.Perm (Fin {a.degree}) where
  toFun := {vec(xs)}
  invFun := {vec(inv)}
  left_inv := by decide +kernel
  right_inv := by decide +kernel
'''

name = f'SmallAffineSoluble{a.degree}Row{a.index}Order'
out = REPO / f'formal/SymmetricSubgroupAsymptotics/{name}.lean'
assert a.verify_existing or not out.exists(), f'Refusing to overwrite {out}'
s = '''import SymmetricSubgroupAsymptotics.FiniteGroupCertificates
import Mathlib.Data.Fin.VecNotation

/-! Exact order of one small affine complement. The literal generators are
the point-1-fixing generators of the pinned primitive row. Only a small
right-generator transition certificate is used, with no normal census. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
'''
exceptional = (a.degree, a.index) in [(16, 6), (16, 9), (27, 9)]
if exceptional:
    s = 'import SymmetricSubgroupAsymptotics.MetacyclicSolvabilityFactories\n' + s
s += f'namespace {name}\n\n'
for i, g in enumerate(generators):
    s += perm(f'g{i}', g) + '\n'
for i, e in enumerate(elements):
    s += perm(f'e{i}', e) + '\n'
s += f'''def generators : Fin {len(generators)} → Equiv.Perm (Fin {a.degree}) :=
  {vec([f'g{i}' for i in range(len(generators))])}
def elements : Fin {expected} → Equiv.Perm (Fin {a.degree}) :=
  {vec([f'e{i}' for i in range(expected)])}
def next : Fin {expected} → Fin {len(generators)} → Fin {expected} :=
  {vec([vec(x) for x in transitions])}
def words : Fin {expected} → List (Fin {len(generators)}) :=
  {vec(['['+', '.join(map(str,w))+']' for w in words])}

def certificate : FiniteCayleyCertificate generators {expected} where
  elements := elements
  identity := 0
  identity_eq := by decide +kernel
  next := next
  next_eq := by
    intro i j
    apply Equiv.ext
    intro x
    revert i j x
    decide +kernel
  words := words
  words_eq := by
    intro i
    apply Equiv.ext
    intro x
    revert i x
    decide +kernel

theorem elements_injective : Function.Injective elements := by decide +kernel

abbrev R : Subgroup (Equiv.Perm (Fin {a.degree})) :=
  Subgroup.closure (Set.range generators)

theorem card : Nat.card R = {expected} := certificate.card_closure elements_injective
'''
if exceptional:
    assert len(generators) == 2
    def mul(x, y):
        return tuple(x[y[k]] for k in range(a.degree))
    base, actor = (1, 0) if (a.degree, a.index) == (16, 6) else (0, 1)
    gn, hn = f'g{base}', f'g{actor}'
    g, h = generators[base], generators[actor]
    hi = tuple(h.index(k) for k in range(a.degree))
    left, right = mul(mul(h, g), hi), mul(mul(hi, g), h)
    powers, x = {}, identity
    for k in range(expected):
        powers.setdefault(x, k)
        x = mul(x, g)
    k, l = powers[left], powers[right]
    s += f'''
theorem conjugates : {hn}*{gn}*{hn}⁻¹={gn}^{k} ∧ {hn}⁻¹*{gn}*{hn}={gn}^{l} := by
  constructor <;> apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel

theorem soluble : IsSolvable R := by
  have hrange : Set.range generators = ({{{gn},{hn}}} : Set (Equiv.Perm (Fin {a.degree}))) := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨j, rfl⟩
      fin_cases j <;> simp [generators]
    · rintro (h | h)
      · exact ⟨{base}, h.symm⟩
      · exact ⟨{actor}, h.symm⟩
  change IsSolvable (Subgroup.closure (Set.range generators))
  rw [hrange]
  exact isSolvable_closure_of_conjugate_powers {gn} {hn} {k} {l} conjugates.1 conjugates.2
'''
s += f'\nend {name}\nend SymmetricSubgroupAsymptotics\n'
if a.verify_existing:
    assert out.read_text() == s, f'Existing source differs: {out}'
else:
    out.write_text(s)
receipt = {'degree': a.degree, 'index': a.index, 'order': expected,
           'generator_count': len(generators), 'source': str(out),
           'dataset_sha256': hashlib.sha256(data.read_bytes()).hexdigest(),
           'source_sha256': hashlib.sha256(out.read_bytes()).hexdigest(),
           'proof_status': 'generated, not checked'}
(BASE / f'{name}.generation.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt))
