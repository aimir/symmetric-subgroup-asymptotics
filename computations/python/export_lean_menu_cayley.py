#!/usr/bin/env python3
"""Export compact, kernel-checked original-action Cayley certificates.

Defaults to the width-2/4 actions and the largest exceptional chart source.
Use --node ID repeatedly to select other actual menu actions. Every output
checks generator transitions and parent edges, proves the generated group's
exact cardinality, and installs an executable group of rows. The exporter
and the declared orders in the input are not proof premises.
"""
from pathlib import Path
import argparse
import gzip
import json

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'formal/SymmetricSubgroupAsymptotics'


def compose(a, b):
    return tuple(a[x] for x in b)


def packed(p):
    n = len(p)
    return sum(x * n ** i for i, x in enumerate(p))


def lookup(values, var='i.val', start=0):
    if len(values) == 1:
        return str(values[0])
    k = len(values) // 2
    return (f'(if {var} < {start+k} then {lookup(values[:k], var, start)} '
            f'else {lookup(values[k:], var, start+k)})')



def packed_lookup(values, index='i.val', block=32):
    """Fixed-width digits in small Nat blocks; all decoding remains in Lean."""
    bits = max(1, max(values).bit_length())
    chunks = [sum(x << (bits*j) for j,x in enumerate(values[i:i+block]))
              for i in range(0,len(values),block)]
    chunks_expr = lookup(chunks, f'({index}) / {block}')
    return f'(({chunks_expr} : ℕ) / 2 ^ ({bits} * (({index}) % {block})) % 2 ^ {bits})'


def finite_lookup(values, modulus, index='i.val', packed=False):
    if packed:
        return f'Fin.ofNat {modulus} {packed_lookup(values,index)}'
    return lookup(values,index)


def checks(n):
    if n <= 16:
        return '(by decide +kernel)'
    k = n // 2
    return f'(Fin.addCases (m := {k}) (n := {n-k}) {checks(k)} {checks(n-k)})'


def array(xs):
    return '#[' + ','.join(map(str, xs)) + ']'


def node_id(name):
    """The numeric suffix of an original menu node identifier."""
    return int(name.split('_')[1])


def permutation16(name, g):
    """The original public degree-16 data declaration, byte for byte.

    This pure tuple emitter is shared by the bounded data chunks and the
    legacy producer. It performs no group enumeration or filesystem access.
    """
    inv = tuple(g.index(i) for i in range(len(g)))
    return f'''def {name} : Equiv.Perm (Fin 16) where
  toFun x := ({array(g)} : Array (Fin 16))[x.val]!
  invFun x := ({array(inv)} : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

'''


def table(gens, degree):
    identity = tuple(range(degree))
    rows = [identity]
    indices = {identity: 0}
    parents, letters, transitions = [0], [0], []
    for i, p in enumerate(rows):
        edges = []
        for j, g in enumerate(gens):
            q = compose(p, g)
            if q not in indices:
                indices[q] = len(rows)
                rows.append(q)
                parents.append(i)
                letters.append(j)
            edges.append(indices[q])
        transitions.append(edges)
    sorted_indices = sorted(range(len(rows)), key=lambda i: packed(rows[i]))
    remap = {old: new for new, old in enumerate(sorted_indices)}
    nxt = [[remap[x] for x in transitions[i]] for i in sorted_indices]
    prev = [[0] * len(gens) for _ in rows]
    for i, edges in enumerate(nxt):
        for j, k in enumerate(edges):
            prev[k][j] = i
    return dict(codes=[packed(rows[i]) for i in sorted_indices],
                rank=sorted_indices, parent=[remap[parents[i]] for i in sorted_indices],
                letter=[letters[i] for i in sorted_indices],
                identity=remap[0], next=nxt, prev=prev)


def emit(node, *, module_name=None, title=None, generated_from=None,
         scope_text=None, extra_body=''):
    w = node['degree']
    gens = [tuple(x - 1 for x in g) for g in node['generators']]
    d = len(gens)
    t = table(gens, w)
    n = len(t['codes'])
    label = node['id'].removeprefix('b').replace('_', 'T')
    module_name = module_name or f'BinaryMenuCayley{label}'
    title = title or f'Compact literal action certificate {label}'
    generated_from = generated_from or (
        'Generated from the original menu permutations by export_lean_menu_cayley.py.')
    scope_text = scope_text or (
        'This certifies\nthis original action, not finite-menu or normal-registry completeness.')
    use_packed = w == 16
    code_expr = finite_lookup(t['codes'], w**w, packed=use_packed)
    rank_expr = packed_lookup(t['rank']) if use_packed else lookup(t['rank'])
    parent_expr = finite_lookup(t['parent'], n, packed=use_packed)
    letter_expr = finite_lookup(t['letter'], d, packed=use_packed)
    next_expr = finite_lookup([x for row in t['next'] for x in row], n, f'i.val * {d} + j.val', True) if use_packed else f"({lookup([array(x) for x in t['next']])} : Array (Fin {n}))[j.val]!"
    prev_expr = finite_lookup([x for row in t['prev'] for x in row], n, f'i.val * {d} + j.val', True) if use_packed else f"({lookup([array(x) for x in t['prev']])} : Array (Fin {n}))[j.val]!"
    s = f'''import SymmetricSubgroupAsymptotics.FiniteCayleyGroup
import SymmetricSubgroupAsymptotics.FinitePermutationEncoding
import Mathlib.Order.Fin.Basic

/-!
# {title}

{generated_from}
All finite equations use Lean's kernel. BFS parents establish actual group
membership; numeric permutation codes establish faithfulness. {scope_text}
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

namespace SymmetricSubgroupAsymptotics.{module_name}

'''
    for j, g in enumerate(gens):
        inv = tuple(g.index(x) for x in range(w))
        s += f'''private def generator{j} : Equiv.Perm (Fin {w}) where
  toFun x := ({array(g)} : Array (Fin {w}))[x.val]!
  invFun x := ({array(inv)} : Array (Fin {w}))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

'''
    s += f'''def generators (j : Fin {d}) : Equiv.Perm (Fin {w}) :=
  {lookup([f'generator{j}' for j in range(d)], 'j.val')}

private def codes (i : Fin {n}) : Fin ({w}^{w}) :=
  {code_expr}
private def ranks (i : Fin {n}) : ℕ :=
  {rank_expr}
private def parents (i : Fin {n}) : Fin {n} :=
  {parent_expr}
private def letters (i : Fin {n}) : Fin {d} :=
  {letter_expr}
private def nextRow (i : Fin {n}) (j : Fin {d}) : Fin {n} :=
  {next_expr}
private def prevRow (i : Fin {n}) (j : Fin {d}) : Fin {n} :=
  {prev_expr}

private theorem parent_lt_checked : ∀ i : Fin {n},
    i ≠ {t['identity']} → ranks (parents i) < ranks i := {checks(n)}
private theorem parent_next_checked : ∀ i : Fin {n},
    i ≠ {t['identity']} → nextRow (parents i) (letters i) = i := {checks(n)}

def certificate : EncodedCayleyCertificate
    (permutationGeneratorEncoding generators) {n} where
  rows := codes
  identity := {t['identity']}
  identity_eq := by decide +kernel
  next := nextRow
  next_eq := {checks(n)}
  rank := ranks
  parent i _ := parents i
  letter i _ := letters i
  parent_lt := parent_lt_checked
  parent_next := parent_next_checked

private theorem codes_strict : StrictMono codes :=
  Fin.strictMono_iff_lt_succ.mpr {checks(n-1)}

theorem rows_injective : Function.Injective certificate.rows := codes_strict.injective

theorem exact_card : Nat.card (Subgroup.closure (Set.range generators)) = {n} :=
  certificate.card_closure rows_injective

private theorem prev_checked : ∀ i j, certificate.next (prevRow i j) j = i :=
  {checks(n)}

/-- Executable multiplication and inverse, with laws proved by faithfulness. -/
@[reducible] def group : Group (FiniteGroupRow {n}) :=
  certificate.rowGroup rows_injective prevRow prev_checked

/-- Exact identification with the original literal permutation subgroup. -/
def originalEquiv : letI := group
    FiniteGroupRow {n} ≃* Subgroup.closure (Set.range generators) :=
  certificate.rowEquiv rows_injective prevRow prev_checked

{extra_body}end SymmetricSubgroupAsymptotics.{module_name}
'''
    return OUT / f'{module_name}.lean', s


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true', help='Compare bytes without modifying files.')
    parser.add_argument('--node', action='append', help='Original action ID; repeat as needed.')
    args = parser.parse_args()
    selected = args.node or ['b2_1', 'b4_1', 'b4_2', 'b4_3', 'b16_1086']
    with gzip.open(ROOT / 'certificates/data/binary_menu.jsonl.gz', 'rt') as f:
        nodes = {x['id']: x for x in json.loads(next(f))['nodes']}
    for name in selected:
        path, content = emit(nodes[name])
        data = content.encode('utf-8')
        if args.check:
            if not path.is_file() or path.read_bytes() != data:
                raise SystemExit(f'Generated witness differs: {path.relative_to(ROOT)}')
        elif not path.is_file() or path.read_bytes() != data:
            path.write_bytes(data)
        print(f'{path.name}: {len(data)} bytes')


if __name__ == '__main__':
    main()
