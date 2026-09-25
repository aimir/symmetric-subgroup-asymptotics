#!/usr/bin/env python3
"""Bind literal menu roots to structurally proved Sylow wreath actions.

Python produces only generator-word witnesses. Lean checks both directions;
the Sylow order is proved structurally, not supplied by this computation.
"""
import argparse
import gzip
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'formal/SymmetricSubgroupAsymptotics/BinaryMenuRoots.lean'


def mul(a, b):
    return tuple(a[i] for i in b)


def inverse(a):
    return tuple(a.index(i) for i in range(len(a)))


def words(generators, degree):
    identity = tuple(range(degree))
    rows = [identity]
    result = {identity: []}
    for a in rows:
        for j, b in enumerate(generators):
            c = mul(a, b)
            if c not in result:
                result[c] = result[a] + [j]
                rows.append(c)
    return result


def wreath_generators(degree):
    if degree == 1:
        return []
    half = degree // 2
    return [a + tuple(range(half, degree)) for a in wreath_generators(half)] + [
        tuple(range(half, degree)) + tuple(range(half))]


def row(values):
    return '#[' + ','.join(map(str, values)) + ']'


def permutation(name, a):
    width = len(a)
    return f'''def {name} : Equiv.Perm (Fin {width}) where
  toFun x := ({row(a)} : Array (Fin {width}))[x.val]!
  invFun x := ({row(inverse(a))} : Array (Fin {width}))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

'''


def generate():
    with gzip.open(ROOT / 'certificates/data/binary_menu.jsonl.gz', 'rt') as f:
        header = json.loads(next(f))
    nodes = {node['id']: node for node in header['nodes']}
    text = '''import SymmetricSubgroupAsymptotics.BinaryWreathRoots
import SymmetricSubgroupAsymptotics.BinaryPermutationBlocks

/-! Literal original menu roots, checked against structural Sylow actions.
The generator rows and conjugators are taken from the committed menu.
Only the small two-way generator words are checked by finite evaluation.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics

'''
    for root in header['roots']:
        width = root['degree']
        exponent = width.bit_length() - 1
        assert width == 2**exponent
        node = nodes[root['node']]
        gens = [tuple(i-1 for i in a) for a in node['generators']]
        conjugator = tuple(i-1 for i in root['conjugator'])
        canon = [mul(mul(conjugator, g), inverse(conjugator))
                 for g in wreath_generators(width)]
        fw = words(canon, width)
        bw = words(gens, width)
        forward = [fw[g] for g in gens]
        backward = [bw[g] for g in canon]
        text += f'namespace BinaryMenuRoot{width}\n\n'
        for i, g in enumerate(gens):
            text += permutation(f'generator{i}', g)
        text += permutation('conjugator', conjugator)
        text += f'''def generators (i : Fin {len(gens)}) : Equiv.Perm (Fin {width}) :=
  {row(['generator'+str(i) for i in range(len(gens))])}[i.val]!

private def conjugateGenerators (i : Fin {exponent}) : Equiv.Perm (Fin {width}) :=
  MulAut.conj conjugator (binaryWreathPermGenerator {exponent} i)

theorem root_eq : Subgroup.closure (Set.range generators) =
    MulAut.conj conjugator • (binaryWreathSylow {exponent} :
      Subgroup (Equiv.Perm (Fin {width}))) := by
  have hw := subgroup_closure_eq_of_generator_words generators conjugateGenerators
    (fun i => ({row(['['+','.join(map(str,w))+']' for w in forward])} :
      Array (List (Fin {exponent})))[i.val]!)
    (fun i => ({row(['['+','.join(map(str,w))+']' for w in backward])} :
      Array (List (Fin {len(gens)})))[i.val]!)
    (by decide +kernel) (by decide +kernel)
  rw [binaryWreathSylow_eq_closure, Subgroup.pointwise_smul_def,
    MonoidHom.map_closure]
  simpa only [← Set.range_comp, Function.comp_def, conjugateGenerators] using hw

def sylow : Sylow 2 (Equiv.Perm (Fin {width})) :=
  conjugator • binaryWreathSylow {exponent}

theorem sylow_eq : (sylow : Subgroup (Equiv.Perm (Fin {width}))) =
    Subgroup.closure (Set.range generators) := root_eq.symm

end BinaryMenuRoot{width}

'''
    return text + 'end SymmetricSubgroupAsymptotics\n'


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true', help='compare bytes without writing')
    args = parser.parse_args()
    data = generate().encode()
    if args.check:
        if not OUT.exists() or OUT.read_bytes() != data:
            raise SystemExit('FAIL: generated root witnesses differ from committed Lean source')
        print('PASS: literal root witnesses reproduce exactly')
    else:
        OUT.write_bytes(data)
        print(f'Wrote {OUT.name}: {len(data)} bytes')
