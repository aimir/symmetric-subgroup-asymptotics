#!/usr/bin/env python3
"""Bind one checked local Schreier source to the original common Data family.

This emits typed generator equalities, source/target subgroup bindings,
and the installed local-child theorem. By default the selected local source
must already match the bounded Schreier exporter. --with-source emits that
same local source too, reusing one bounded witness search for both files.
Both files still require separate kernel checks through check_lean.py.
No legacy source table or aggregate coverage claim is generated.
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
from export_lean_action16_data_chunks import (
    checked_data_layout, chunk_count, chunk_name, write_or_check,
)

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
    parser.add_argument('--source', required=True, help='One original degree-sixteen source')
    parser.add_argument('--output-dir', type=Path, default=OUT)
    parser.add_argument('--with-source', action='store_true',
                        help='Emit/check the selected Source and Binding using one witness search')
    parser.add_argument('--max-states', type=int, default=65536)
    parser.add_argument('--max-cache-states', type=int, default=65536,
                        help='Aggregate retained forward-BFS states for this one source')
    parser.add_argument('--max-cache-bytes', type=int, default=64 * 1024 * 1024,
                        help='Conservative retained-object cache budget; not a process RSS cap')
    parser.add_argument('--max-word-length', type=int, default=256)
    parser.add_argument('--max-assignments', type=int, default=256)
    parser.add_argument('--max-output-bytes', type=int, default=128 * 1024)
    parser.add_argument('--max-source-output-bytes', type=int, default=2 * 1024 * 1024)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    if min(args.max_states, args.max_word_length, args.max_assignments,
           args.max_output_bytes, args.max_source_output_bytes,
           args.max_cache_states, args.max_cache_bytes) < 1:
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
                                 max_assignments=args.max_assignments,
                                 max_cache_states=args.max_cache_states,
                                 max_cache_bytes=args.max_cache_bytes)
    local_file = (args.output_dir if args.with_source else OUT) / f'Source{label(args.source)}.lean'
    local_data = emit(nodes[args.source], nodes, branches).encode()
    if len(local_data) > args.max_source_output_bytes:
        raise SystemExit('local source exceeds the output limit; split it before proceeding')
    if not args.with_source and (not local_file.is_file() or local_file.read_bytes() != local_data):
        raise SystemExit('selected local source must first match export_lean_schreier_actions.py')
    data = emit_binding(nodes[args.source], names, branches).encode()
    if len(data) > args.max_output_bytes:
        raise SystemExit('binding exceeds the output limit; split it before proceeding')
    path = args.output_dir / f'Binding{label(args.source)}.lean'
    # Render and bound both outputs before publishing either. Each file is
    # replaced atomically; an interrupted pair is not a proof receipt and
    # both modules must still be checked in Source, Binding order.
    if args.with_source:
        write_or_check(local_file, local_data, args.check, args.max_source_output_bytes)
    write_or_check(path, data, args.check, args.max_output_bytes)
    word_lengths = [len(word) for branch in branches
                    for words in ((branch['forward'], branch['backward'])
                                  if branch['kind'] == 'accepted' else
                                  (branch['words'],) if branch['kind'] == 'relation' else ())
                    for word in words]
    print(json.dumps(dict(source=args.source, file=str(path), bytes=len(data),
                          local_source_file=str(local_file), local_source_bytes=len(local_data),
                          with_source=args.with_source,
                          branches={kind: sum(b['kind'] == kind for b in branches)
                                    for kind in ('trivial', 'relation', 'color', 'accepted')},
                          witness_words=len(word_lengths), witness_letters=sum(word_lengths),
                          max_witness_word_length=max(word_lengths, default=0),
                          source_index=names.index(args.source),
                          target_count=len({b['target'] for b in branches if b['kind'] == 'accepted'})), sort_keys=True))


if __name__ == '__main__':
    main()
