#!/usr/bin/env python3
"""Export generator/cardinality certificates for original action children.

A source and its actual child targets are checked by compact Cayley tables.
For each nontrivial generator-bit assignment, sparse counterexamples reject
invalid or intransitive kernels. Accepted edges check only inverse-conjugated
target generators; exact cardinalities force equality in Lean. The default
source exercises all14 index-two transitive children of b16_1086. This does
not assert full width16 action or normal-registry completeness.
"""
import argparse
import gzip
import json
import sys
sys.dont_write_bytecode = True
from export_lean_menu_cayley import ROOT, OUT, table, packed, compose, lookup, checks, emit, finite_lookup
from export_lean_action_registry import raw, label, permdef, inverse


def registry_module(source,names,nodes,tables):
    w=nodes[source]['degree'];tag=label(source);size=len(names)
    s='import SymmetricSubgroupAsymptotics.BinaryGeneratorRegistry\n'
    s+=''.join(f'import SymmetricSubgroupAsymptotics.BinaryMenuCayley{label(n)}\n'for n in names)
    s+=f'''\n/-! Exact generated target actions for all index-two children of {source}. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryGeneratorMenu{tag}

def actions (k : Fin {size}) : Subgroup (Equiv.Perm (Fin {w})) :=
  ![{','.join('Subgroup.closure (Set.range BinaryMenuCayley'+label(n)+'.generators)'for n in names)}] k

def registry : GeneratedPermutationRegistry actions where
  generatorCount k := ![{','.join(str(len(nodes[n]['generators']))for n in names)}] k
  generators :=
'''
    term='(fun i => Fin.elim0 i)'
    for n in reversed(names):term=f'Fin.cases BinaryMenuCayley{label(n)}.generators ({term})'
    s+='    '+term+'\n  generated_eq := by\n    intro k\n    fin_cases k <;> rfl\n'
    s+=f"  order k := ![{','.join(str(len(tables[n]['codes']))for n in names)}] k\n"
    s+='  card_eq := by\n    intro k\n    fin_cases k\n'
    s+=''.join(f'    · exact BinaryMenuCayley{label(n)}.exact_card\n'for n in names)
    return f'BinaryGeneratorMenu{tag}.lean',s+f'\nend SymmetricSubgroupAsymptotics.BinaryGeneratorMenu{tag}\n'


def children_module(source,names,nodes,actions,tables):
    w=nodes[source]['degree'];tag=label(source);t=tables[source];n=len(t['codes']);d=len(nodes[source]['generators'])
    par=[0]*n
    for i in sorted(range(n),key=lambda i:t['rank'][i]):
        if i!=t['identity']:par[i]=par[t['parent'][i]]^(1<<t['letter'][i])
    def valexpr(p):
        a='true'
        for j in range(d):
            if p&(1<<j):a=f'({a} == bits {j})'
        return a
    ix={c:i for i,c in enumerate(t['codes'])}
    # Identify a child using its literal conjugated target generators.
    # The Lean cardinality bridge proves equality; no child group needs
    # to be enumerated again during untrusted witness production.
    edge_rows=[]
    for edge in actions[source]['action_children']:
        g=tuple(x-1 for x in edge['conjugator'])
        rows=[ix[packed(compose(compose(inverse(g),h),g))]
              for h in raw(nodes[edge['target']]['generators'])]
        edge_rows.append((edge,g,rows))
    s=f'''import SymmetricSubgroupAsymptotics.BinaryGeneratorMenu{tag}

/-! All actual index-two transitive children of {source}, using generator-sized edges. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryGeneratorChildren{tag}
open BinaryGeneratorMenu{tag}
private def C := BinaryMenuCayley{tag}.certificate
private def parity (i : Fin {n}) : Fin {2**d} :=
  {finite_lookup(par,2**d,packed=True)}
private def values (bits : Fin {d} → Bool) (i : Fin {n}) : Bool :=
  {lookup([valexpr(p)for p in range(2**d)],'(parity i).val')}
private def characters : BinaryRowCharacters C where
  values := values
  identity_eq := by decide +kernel
  parent_eq := by decide +kernel

'''
    branches=[]
    for b in range(2**d):
        vals=[(p&(~b)).bit_count()%2==0 for p in par]
        failure=next(((i,j)for i in range(n)for j in range(d)
                      if vals[t['next'][i][j]]!=(vals[i]==bool(b&(1<<j)))),None)
        reached={t['codes'][i]%w for i in range(n)if vals[i]}
        if b==2**d-1:branches.append(('trivial',None));continue
        if failure is not None:branches.append(('inconsistent',failure));continue
        if len(reached)!=w:branches.append(('intransitive',next(y for y in range(w)if y not in reached)));continue
        edge,g,rows=next((e,g,rs)for e,g,rs in edge_rows if all(vals[i]for i in rs))
        target=edge['target'];k=names.index(target)
        assert all(vals[i]for i in rows)
        s+=permdef(f'conjugator{b}',g)
        s+=f'''private def generatorRow{b} (j : Fin {len(rows)}) : Fin {n} :=
  {lookup(rows,'j.val')}
private theorem generator_checked{b} : ∀ j,
    characters.values (binaryAssignment ({b} : Fin {2**d})) (generatorRow{b} j) = true ∧
    C.rows (generatorRow{b} j) = permutationCode (MulAut.conj conjugator{b}⁻¹ (registry.generators {k} j)) :=
  by decide +kernel

'''
        branches.append(('accepted',k))
    s+=f'''private theorem checked : ∀ bits : Fin {d} → Bool,
    (∃ j, bits j = false) →
    (∀ i j, characters.values bits (C.next i j) = (characters.values bits i == bits j)) →
    (∀ y : Fin {w}, ∃ i, characters.values bits i = true ∧ encodedRowAction C i 0 = y) →
    ∃ k, ∃ g : Equiv.Perm (Fin {w}), registry.order k * 2 = {n} ∧
      ∀ j, ∃ i, characters.values bits i = true ∧
        C.rows i = permutationCode (MulAut.conj g⁻¹ (registry.generators k j)) := by
  intro bits
  obtain ⟨b,rfl⟩ := binaryAssignment_surjective {d} bits
  fin_cases b
'''
    for b,(kind,info) in enumerate(branches):
        if kind=='trivial':
            s+=f'''  · intro hn _ _
    exact False.elim ((show ¬(∃ j : Fin {d}, binaryAssignment ({b} : Fin {2**d}) j = false)
      from by decide +kernel) hn)
'''
        elif kind=='inconsistent':
            i,j=info
            s+=f'''  · intro _ hs _
    exact False.elim ((show characters.values (binaryAssignment ({b} : Fin {2**d})) (C.next {i} {j}) ≠
      (characters.values (binaryAssignment ({b} : Fin {2**d})) {i} == binaryAssignment (d := {d}) ({b} : Fin {2**d}) {j})
      from by decide +kernel) (hs {i} {j}))
'''
        elif kind=='intransitive':
            s+=f'''  · intro _ _ ht
    obtain ⟨i,hi,he⟩ := ht {info}
    exact False.elim ((show ∀ i : Fin {n}, characters.values (binaryAssignment ({b} : Fin {2**d})) i = true →
      encodedRowAction C i 0 ≠ {info} from {checks(n)}) i hi he)
'''
        else:
            s+=f'''  · intro _ _ _
    exact ⟨{info},conjugator{b},by decide +kernel,
      fun j => ⟨generatorRow{b} j,generator_checked{b} j⟩⟩
'''
    s+=f'''
/-- Every actual transitive index-two child is covered in its original permutation action. -/
theorem children (K : Subgroup (Equiv.Perm (Fin {w})))
    (hle : K ≤ Subgroup.closure (Set.range BinaryMenuCayley{tag}.generators))
    (hindex : K.relIndex (Subgroup.closure (Set.range BinaryMenuCayley{tag}.generators)) = 2)
    (ht : PermutationSubgroupTransitive K) : ActionRegistryCovered actions K :=
  binary_generator_registry_children C characters actions registry
    BinaryMenuCayley{tag}.rows_injective 0 checked K hle hindex ht

end SymmetricSubgroupAsymptotics.BinaryGeneratorChildren{tag}
'''
    return f'BinaryGeneratorChildren{tag}.lean',s


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--source',default='b16_1086');p.add_argument('--check',action='store_true');a=p.parse_args()
    with gzip.open(ROOT/'certificates/data/binary_menu.jsonl.gz','rt')as f:
        header=json.loads(next(f));nodes={x['id']:x for x in header['nodes']};actions={x['id']:x for x in map(json.loads,f)if x.get('kind')=='action'}
    needed={a.source}|{e['target']for e in actions[a.source]['action_children']};names=[n for n in nodes if n in needed]
    tables={n:table(raw(nodes[n]['generators']),nodes[n]['degree'])for n in names}
    def save(path,s):
        data=s.encode()
        if a.check:
            if not path.is_file()or path.read_bytes()!=data:raise SystemExit(f'Generated witness differs: {path.relative_to(ROOT)}')
        elif not path.is_file()or path.read_bytes()!=data:path.write_bytes(data)
        print(f'{path.name}: {len(data)} bytes')
    for n in names:save(*emit(nodes[n]))
    name,s=registry_module(a.source,names,nodes,tables);save(OUT/name,s)
    name,s=children_module(a.source,names,nodes,actions,tables);save(OUT/name,s)


if __name__=='__main__':main()
