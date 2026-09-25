#!/usr/bin/env python3
"""Export full original-point action coverage at a selected binary width.

Each action is checked once by its compact Cayley table. All index-two
children are covered by original-generator bit assignments and literal
conjugacy row maps. The output proves action coverage only; normal-state
acceptance is a separate theorem. No catalogue order is a proof premise.
"""
from pathlib import Path
import argparse
import gzip
import json
import sys
sys.dont_write_bytecode = True
from export_lean_menu_cayley import ROOT, OUT, table, packed, compose, lookup, checks, array, emit


def inverse(p):
    return tuple(p.index(i) for i in range(len(p)))


def raw(gs):
    return [tuple(x-1 for x in g) for g in gs]


def label(name):
    return name.removeprefix('b').replace('_', 'T')


def permdef(name, g):
    w = len(g)
    return f'''private def {name} : Equiv.Perm (Fin {w}) where
  toFun x := ({array(g)} : Array (Fin {w}))[x.val]!
  invFun x := ({array(inverse(g))} : Array (Fin {w}))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

'''


def emit_registry(width, names, nodes, tables):
    count = len(names)
    s = 'import SymmetricSubgroupAsymptotics.BinaryCharacterRegistry\n'
    s += ''.join(f'import SymmetricSubgroupAsymptotics.BinaryMenuCayley{label(n)}\n' for n in names)
    s += f'''\n/-! Exact original-point code rows for every supplied width-{width} action. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryActionRegistry{width}

def actions (k : Fin {count}) : Subgroup (Equiv.Perm (Fin {width})) :=
  ![{','.join('Subgroup.closure (Set.range BinaryMenuCayley'+label(n)+'.generators)' for n in names)}] k

def registry : LiteralPermutationRegistry actions where
  size k := ![{','.join(str(len(tables[n]['codes'])) for n in names)}] k
  rows :=
'''
    row_term = '(fun i => Fin.elim0 i)'
    for n in reversed(names):
        row_term = f'Fin.cases BinaryMenuCayley{label(n)}.certificate.rows ({row_term})'
    s += '    ' + row_term + '\n'
    s += '  mem_iff := by\n    intro k\n    fin_cases k\n'
    s += ''.join(f'    · exact BinaryMenuCayley{label(n)}.certificate.mem_closure_iff\n' for n in names)
    return f'BinaryActionRegistry{width}.lean', s+f'\nend SymmetricSubgroupAsymptotics.BinaryActionRegistry{width}\n'


def emit_children(width, name, names, nodes, actions, tables):
    node = nodes[name]
    t = tables[name]
    n, d = len(t['codes']), len(node['generators'])
    parity = [0] * n
    for i in sorted(range(n), key=lambda i: t['rank'][i]):
        if i != t['identity']:
            parity[i] = parity[t['parent'][i]] ^ (1 << t['letter'][i])
    def expression(p):
        ans = 'true'
        for j in range(d):
            if p & (1 << j):
                ans = f'({ans} == bits {j})'
        return ans
    gs = raw(node['generators'])
    ix = {c:i for i,c in enumerate(t['codes'])}
    # Bind each original child row set to its original ambient conjugator.
    edges = {}
    for edge in actions[name]['action_children']:
        rows = set(table(raw(edge['generators']),width)['codes'])
        edges[frozenset(rows)] = (edge['target'], tuple(x-1 for x in edge['conjugator']))
    identity = tuple(range(width))
    edges[frozenset(t['codes'])] = (name,identity)
    s = f'''import SymmetricSubgroupAsymptotics.BinaryActionRegistry{width}

/-! All original index-two transitive children of {name}, checked by generator bits. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryActionChildren{label(name)}
open BinaryActionRegistry{width}
private def C := BinaryMenuCayley{label(name)}.certificate
private def values (bits : Fin {d} → Bool) (i : Fin {n}) : Bool :=
  {lookup([expression(p) for p in parity])}
private def characters : BinaryRowCharacters C where
  values := values
  identity_eq := by decide +kernel
  parent_eq := by decide +kernel

'''
    targets = []
    for b in range(2**d):
        vals = [((p & (~b)).bit_count() % 2 == 0) for p in parity]
        consistent = all(vals[t['next'][i][j]] == (vals[i] == bool(b & (1<<j)))
                         for i in range(n) for j in range(d))
        reached = {t['codes'][i] % width for i in range(n) if vals[i]}
        selected = frozenset(c for c,v in zip(t['codes'],vals) if v)
        if not consistent:
            targets.append(('inconsistent',None))
            continue
        if len(reached) != width:
            targets.append(('intransitive',None))
            continue
        target,g = edges[selected]
        k = names.index(target)
        rt = tables[target]
        rix = {c:i for i,c in enumerate(rt['codes'])}
        def conj(c):
            h = tuple(c // width**j % width for j in range(width))
            return packed(compose(compose(g,h),inverse(g)))
        forward = [rix[conj(c)] if vals[i] else 0 for i,c in enumerate(t['codes'])]
        backward = {conj(c):i for i,c in enumerate(t['codes']) if vals[i]}
        assert set(backward) == set(rt['codes'])
        back = [backward[c] for c in rt['codes']]
        s += permdef(f'conjugator{b}',g)
        s += f'''private def forward{b} (i : Fin {n}) : Fin {len(rt['codes'])} :=
  {lookup(forward)}
private def backward{b} (j : Fin {len(rt['codes'])}) : Fin {n} :=
  {lookup(back,'j.val')}
private theorem forward_checked{b} : ∀ i,
    characters.values (binaryAssignment ({b} : Fin {2**d})) i = true →
    registry.rows {k} (forward{b} i) = permutationConjugateCode conjugator{b} (C.rows i) :=
  {checks(n)}
private theorem backward_checked{b} : ∀ j,
    characters.values (binaryAssignment ({b} : Fin {2**d})) (backward{b} j) = true ∧
    registry.rows {k} j = permutationConjugateCode conjugator{b} (C.rows (backward{b} j)) :=
  {checks(len(rt['codes']))}

'''
        targets.append(('accepted',(k,b)))
    s += f'''private theorem checked : ∀ bits : Fin {d} → Bool,
    (∀ i j, characters.values bits (C.next i j) = (characters.values bits i == bits j)) →
    (∀ y : Fin {width}, ∃ i, characters.values bits i = true ∧ encodedRowAction C i 0 = y) →
    ∃ k, ∃ g : Equiv.Perm (Fin {width}),
      (∀ i, characters.values bits i = true →
        ∃ j, registry.rows k j = permutationConjugateCode g (C.rows i)) ∧
      (∀ j, ∃ i, characters.values bits i = true ∧
        registry.rows k j = permutationConjugateCode g (C.rows i)) := by
  intro bits
  obtain ⟨b,rfl⟩ := binaryAssignment_surjective {d} bits
  fin_cases b
'''
    for b,(kind,info) in enumerate(targets):
        if kind == 'inconsistent':
            s += f'''  · intro hs _
    exact False.elim ((show ¬(∀ i j, characters.values (binaryAssignment ({b} : Fin {2**d}))
      (C.next i j) = (characters.values (binaryAssignment ({b} : Fin {2**d})) i ==
        binaryAssignment ({b} : Fin {2**d}) j)) from by decide +kernel) hs)
'''
        elif kind == 'intransitive':
            s += f'''  · intro _ ht
    exact False.elim ((show ¬(∀ y : Fin {width}, ∃ i,
      characters.values (binaryAssignment ({b} : Fin {2**d})) i = true ∧
        encodedRowAction C i 0 = y) from by decide +kernel) ht)
'''
        else:
            k,_ = info
            s += f'''  · intro _ _
    exact ⟨{k},conjugator{b},
      fun i hi => ⟨forward{b} i,forward_checked{b} i hi⟩,
      fun j => ⟨backward{b} j,backward_checked{b} j⟩⟩
'''
    s += f'''
/-- Complete literal transitive index-two child coverage for this original action. -/
theorem children (K : Subgroup (Equiv.Perm (Fin {width})))
    (hle : K ≤ Subgroup.closure (Set.range BinaryMenuCayley{label(name)}.generators))
    (hindex : K.relIndex (Subgroup.closure (Set.range BinaryMenuCayley{label(name)}.generators)) = 2)
    (ht : PermutationSubgroupTransitive K) : ActionRegistryCovered actions K :=
  binary_character_registry_children C characters actions registry 0 checked K hle hindex ht

end SymmetricSubgroupAsymptotics.BinaryActionChildren{label(name)}
'''
    return f'BinaryActionChildren{label(name)}.lean',s


def emit_global(width,names,root):
    s = 'import SymmetricSubgroupAsymptotics.BinaryMenuRoots\n'
    s += ''.join(f'import SymmetricSubgroupAsymptotics.BinaryActionChildren{label(n)}\n' for n in names)
    s += f'''\n/-! Complete original-point binary action coverage in width {width}.
Normal-state acceptance is a separate theorem. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryActionRegistry{width}

theorem complete (H : Subgroup (Equiv.Perm (Fin {width})))
    (hH : IsPGroup 2 H) (ht : PermutationSubgroupTransitive H) :
    ActionRegistryCovered actions H := by
  apply permutation_pGroup_action_registry_complete actions BinaryMenuRoot{width}.sylow
    {names.index(root)} ?_ ?_ H hH ht
  · rw [BinaryMenuRoot{width}.sylow_eq]
    change Subgroup.closure (Set.range BinaryMenuCayley{label(root)}.generators) = _
    have he : BinaryMenuCayley{label(root)}.generators = BinaryMenuRoot{width}.generators := by decide +kernel
    rw [he]
  · intro i K hlt hindex htrans
    fin_cases i
'''
    s += ''.join(f'    · exact BinaryActionChildren{label(n)}.children K hlt.le hindex htrans\n' for n in names)
    return f'BinaryActionCoverage{width}.lean',s+f'\nend SymmetricSubgroupAsymptotics.BinaryActionRegistry{width}\n'


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--width',type=int,choices=[8,16],default=8)
    p.add_argument('--check',action='store_true')
    args=p.parse_args()
    with gzip.open(ROOT/'certificates/data/binary_menu.jsonl.gz','rt') as f:
        header=json.loads(next(f));nodes={x['id']:x for x in header['nodes']}
        actions={x['id']:x for x in map(json.loads,f) if x.get('kind')=='action'}
    names=[n for n,x in nodes.items() if x['degree']==args.width]
    tables={n:table(raw(nodes[n]['generators']),args.width) for n in names}
    def save(path,s):
        data=s.encode('utf-8')
        if args.check:
            if not path.is_file() or path.read_bytes()!=data:
                raise SystemExit(f'Generated witness differs: {path.relative_to(ROOT)}')
        elif not path.is_file() or path.read_bytes() != data:path.write_bytes(data)
        print(f'{path.name}: {len(data)} bytes')
    for n in names:save(*emit(nodes[n]))
    name,s=emit_registry(args.width,names,nodes,tables);save(OUT/name,s)
    for n in names:
        name,s=emit_children(args.width,n,names,nodes,actions,tables);save(OUT/name,s)
    root=next(x['node'] for x in header['roots'] if x['degree']==args.width)
    name,s=emit_global(args.width,names,root);save(OUT/name,s)


if __name__=='__main__':main()
