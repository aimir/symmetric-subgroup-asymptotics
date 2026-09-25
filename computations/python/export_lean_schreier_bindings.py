#!/usr/bin/env python3
"""Bind one checked local Schreier source to the original common Data family.

This emits only typed generator equalities, source/target subgroup bindings,
and the installed local-child theorem. It never generates legacy source
tables or an aggregate coverage claim. The selected local source must already
match the bounded Schreier exporter. Compile separately with check_lean.py.
"""
import argparse
import gzip
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
from export_lean_menu_cayley import ROOT, lookup
from export_lean_schreier_actions import compile_witnesses, emit, label
from export_lean_action16_data_chunks import checked_data_layout, chunk_count, chunk_name

OUT = ROOT / 'formal/SymmetricSubgroupAsymptotics/GeneratedSchreierActions'


def common_family_names(nodes):
    """Check the producer's indices against the existing original Data tuple order.

    Lean still checks every resulting source/target equality; this read-only
    check is only an early diagnostic for changed generated Data interfaces.
    """
    names = [n for n, node in nodes.items() if node['degree'] == 16]
    directory = ROOT / 'formal/SymmetricSubgroupAsymptotics/GeneratedAction16'
    size = checked_data_layout(names, directory)
    files = ([directory / 'Data.lean'] if size is None else
             [directory / f'{chunk_name(i)}.lean' for i in range(chunk_count(names, size))])
    defined = ['b16_' + n for path in files for n in
               re.findall(r'^def node(\d+)Generators\b', path.read_text(), re.M)]
    if defined != names:
        raise ValueError('the existing original Data family differs from the committed node order')
    return names


def emit_binding(node, names, branches):
    if node['degree'] != 16:
        raise ValueError('the existing common Data family is degree sixteen')
    name, tag = node['id'], label(node['id'])
    local = f'BinarySchreierChildren{tag}'
    targets = sorted({b['target'] for b in branches if b['kind'] == 'accepted'})
    indices = [names.index(n) for n in targets]
    index_expr = lookup(indices, 'j.val') if indices else 'Fin.elim0 j'
    count, degree = len(names), len(node['generators'])
    text = f'''import SymmetricSubgroupAsymptotics.BinarySchreierActionAdapter
import SymmetricSubgroupAsymptotics.GeneratedAction16.Data
import SymmetricSubgroupAsymptotics.GeneratedSchreierActions.Source{tag}

/-! Typed original-family installation for {name}. Only pointwise
generator equalities bind the independently checked local certificate. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinarySchreierBinding{tag}

def sourceIndex : Fin {count} := {names.index(name)}

def targetIndex (j : Fin {len(targets)}) : Fin {count} :=
  {index_expr}

theorem source_generators_eq :
    {local}.generators=BinaryActionData16.node{name.split('_')[1]}Generators := by
  decide +kernel

'''
    for j, target in enumerate(targets):
        text += f'''private theorem target{j}_generators_eq :
    {local}.target{j}Generators=BinaryActionData16.node{target.split('_')[1]}Generators := by
  decide +kernel

'''
    text += f'''theorem source_eq : BinaryActionData16.actions sourceIndex=
    Subgroup.closure (Set.range {local}.generators) := by
  change Subgroup.closure (Set.range BinaryActionData16.node{name.split('_')[1]}Generators)=_
  rw [source_generators_eq]

theorem target_eq : ∀ j,
    {local}.targets j=BinaryActionData16.actions (targetIndex j) := by
  intro j
'''
    if targets:
        text += '  fin_cases j\n'
        for j, target in enumerate(targets):
            text += f'''  · change Subgroup.closure (Set.range {local}.target{j}Generators)=
      Subgroup.closure (Set.range BinaryActionData16.node{target.split('_')[1]}Generators)
    rw [target{j}_generators_eq]
'''
    else:
        text += '  exact Fin.elim0 j\n'
    text += f'''
/-- Typed binding into the shared original family, with no order premise. -/
def binding : BinarySchreierActionBinding BinaryActionData16.actions sourceIndex where
  generatorCount := {degree}
  generators := {local}.generators
  source_eq := source_eq
  targetCount := {len(targets)}
  targets := {local}.targets
  targetIndex := targetIndex
  target_eq := target_eq
  local_children := {local}.children

/-- Every actual transitive index-two subgroup of this common-family
source is covered in the same common family and on the same points. -/
theorem children : BinaryActionChildrenCovered BinaryActionData16.actions
    (BinaryActionData16.actions sourceIndex) := binding.children

end SymmetricSubgroupAsymptotics.BinarySchreierBinding{tag}
'''
    return text


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', required=True, help='One previously emitted degree-sixteen source')
    parser.add_argument('--output-dir', type=Path, default=OUT)
    parser.add_argument('--max-states', type=int, default=65536)
    parser.add_argument('--max-word-length', type=int, default=256)
    parser.add_argument('--max-assignments', type=int, default=256)
    parser.add_argument('--max-output-bytes', type=int, default=128 * 1024)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    if min(args.max_states, args.max_word_length, args.max_assignments, args.max_output_bytes) < 1:
        parser.error('all limits must be positive')
    with gzip.open(ROOT / 'certificates/data/binary_menu.jsonl.gz', 'rt') as f:
        header = json.loads(next(f))
        nodes = {n['id']: n for n in header['nodes']}
        if args.source not in nodes or nodes[args.source]['degree'] != 16:
            parser.error('source must be an original degree-sixteen node')
        action = next((r for r in map(json.loads, f)
                       if r.get('kind') == 'action' and r['id'] == args.source), None)
    if action is None:
        parser.error('source has no action record')
    names = common_family_names(nodes)
    branches = compile_witnesses(nodes[args.source], action, nodes,
                                 max_states=args.max_states,
                                 max_word_length=args.max_word_length,
                                 max_assignments=args.max_assignments)
    local_file = OUT / f'Source{label(args.source)}.lean'
    if not local_file.is_file() or local_file.read_bytes() != emit(nodes[args.source], nodes, branches).encode():
        raise SystemExit('selected local source must first match export_lean_schreier_actions.py')
    data = emit_binding(nodes[args.source], names, branches).encode()
    if len(data) > args.max_output_bytes:
        raise SystemExit('binding exceeds the output limit; split it before proceeding')
    path = args.output_dir / f'Binding{label(args.source)}.lean'
    if args.check:
        if not path.is_file() or path.read_bytes() != data:
            raise SystemExit(f'Generated binding differs: {path}')
    else:
        args.output_dir.mkdir(parents=True, exist_ok=True)
        if not path.exists() or path.read_bytes() != data:
            path.write_bytes(data)
    print(json.dumps(dict(source=args.source, file=str(path), bytes=len(data),
                          source_index=names.index(args.source),
                          target_count=len({b['target'] for b in branches if b['kind'] == 'accepted'})), sort_keys=True))


if __name__ == '__main__':
    main()
