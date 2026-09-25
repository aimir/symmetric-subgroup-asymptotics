#!/usr/bin/env python3
"""Emit one checked slice of original degree-16 Schreier bindings.

--slice START COUNT emits only that selected assembly module. Slices of at
most 16 entries import their individual typed bindings; larger slices join
two previously checked half-slices. --complete is a separate final step
requiring the checked full slice [0,1427). It has no coverage hypothesis.

Every required local dependency must have a current successful schema-2
check_lean.py receipt. The closure check uses bounded streaming hashes and
never launches Lean or enumerates a group. Installed external objects retain
the runner's existing trust boundary. Missing coverage always fails closed.
"""
import argparse
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
from export_lean_action16_data_chunks import (
    FORMAL, check_chunk_receipt, checked_data_layout, load_nodes, write_or_check,
)
from export_lean_schreier_actions import label

OUT = FORMAL / 'SymmetricSubgroupAsymptotics/GeneratedSchreierActions'
PREFIX = 'SymmetricSubgroupAsymptotics.GeneratedSchreierActions'
HELPER = 'SymmetricSubgroupAsymptotics.BinarySchreierBindingAssembly'
ROOT_ADAPTER = 'SymmetricSubgroupAsymptotics.BinarySchreierAction16'
LEAF_LIMIT = 16


def slice_name(start, count):
    return f'Bindings{start:04d}Count{count:04d}'


def slice_namespace(start, count):
    return 'SymmetricSubgroupAsymptotics.BinarySchreier' + slice_name(start, count)


def source_path(module):
    return FORMAL.joinpath(*module.split('.')).with_suffix('.lean')


def require_checked_closure(path, receipt_dir, checked, pending):
    """Also reject a failed or stale descendant behind a formerly good parent.

    This follows only recorded local source dependencies, never external
    Mathlib imports. Each local module is visited once per invocation.
    """
    path = path.resolve()
    if path in checked:
        return
    if not path.is_relative_to(FORMAL.resolve()) or path.suffix != '.lean':
        raise ValueError(f'dependency is not a local Lean source: {path}')
    if path in pending:
        raise ValueError(f'cyclic checked dependency: {path}')
    pending.add(path)
    check_chunk_receipt(path, receipt_dir)
    relative = path.relative_to(FORMAL)
    module = '.'.join(relative.with_suffix('').parts)
    receipt = json.loads((receipt_dir / f'{module}.json').read_text())
    if receipt.get('legacy_unverified_dependencies'):
        raise ValueError(f'assembly requires checked local dependencies: {module}')
    for dependency in receipt.get('dependency_source_sha256', {}):
        require_checked_closure(Path(dependency), receipt_dir, checked, pending)
    pending.remove(path)
    checked.add(path)


def preamble(imports, namespace):
    return ''.join(f'import {m}\n' for m in imports) + f'''
/-! Exact original-family binding assembly. Every index in the displayed
slice is supplied by a checked typed binding; there is no default entry. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace {namespace}

'''


def slice_dependencies(names, start, count):
    if count <= LEAF_LIMIT:
        return [f'{PREFIX}.Binding{label(name)}' for name in names[start:start+count]]
    left = count // 2
    return [f'{PREFIX}.{slice_name(start, left)}',
            f'{PREFIX}.{slice_name(start+left, count-left)}']


def emit_slice(names, start, count):
    if count < 1 or start < 0 or start+count > len(names):
        raise ValueError('slice must be a nonempty interval of the original Data family')
    namespace = slice_namespace(start, count)
    imports = [HELPER] + slice_dependencies(names, start, count)
    text = preamble(imports, namespace)
    text += f'''def bindings : BinarySchreierBindingSlice BinaryActionData16.actions
    {start} {count} (by decide +kernel) := '''
    if count <= LEAF_LIMIT:
        # Bindings live in Type, so fin_cases' List.Mem elimination is not
        # available here. Fin.cases eliminates into any Sort and computes
        # the original index start+i at every zero/successor branch.
        text += '''by
  unfold BinarySchreierBindingSlice
  exact
'''
        indent = '    '
        for name in names[start:start+count]:
            text += f'{indent}Fin.cases BinarySchreierBinding{label(name)}.binding <|\n'
            indent += '  '
        text += f'{indent}fun i => Fin.elim0 i\n'
    else:
        left = count // 2
        text += f'''
  binarySchreierBindingSlice_add BinaryActionData16.actions
    {start} {left} {count-left} (by decide +kernel)
    {slice_namespace(start, left)}.bindings
    {slice_namespace(start+left, count-left)}.bindings
'''
    return (text + f'\nend {namespace}\n').encode()


def emit_complete(names):
    total = len(names)
    namespace = 'SymmetricSubgroupAsymptotics.BinarySchreierComplete16'
    text = preamble([HELPER, ROOT_ADAPTER, f'{PREFIX}.{slice_name(0, total)}'], namespace)
    text += f'''/-- An actual binding for every original Data index. -/
def bindings : ∀ i, BinarySchreierActionBinding BinaryActionData16.actions i :=
  binarySchreierBindings_of_fullSlice BinaryActionData16.actions
    {slice_namespace(0, total)}.bindings

/-- All transitive binary subgroups on the original sixteen points are
covered, using the actual Sylow root and every checked local source. -/
theorem complete (H : Subgroup (Equiv.Perm (Fin 16))) (hH : IsPGroup 2 H)
    (ht : PermutationSubgroupTransitive H) :
    ActionRegistryCovered BinaryActionData16.actions H :=
  BinarySchreierAction16.complete_of_bindings bindings H hH ht

end {namespace}
'''
    return text.encode()


def require_bytes(path, expected):
    if not path.is_file() or path.read_bytes() != expected:
        raise ValueError(f'missing or changed assembly dependency: {path}')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--slice', type=int, nargs=2, metavar=('START', 'COUNT'))
    mode.add_argument('--complete', action='store_true')
    parser.add_argument('--receipt-dir', type=Path, required=True)
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--max-output-bytes', type=int, default=64 * 1024)
    args = parser.parse_args()
    if args.max_output_bytes < 1:
        parser.error('output byte limit must be positive')
    try:
        names, _ = load_nodes()
        checked_data_layout(names)
        checked, pending = set(), set()
        require_checked_closure(source_path(HELPER), args.receipt_dir, checked, pending)
        if args.slice is not None:
            start, count = args.slice
            data = emit_slice(names, start, count)
            dependencies = slice_dependencies(names, start, count)
            if count > LEAF_LIMIT:
                left = count // 2
                for a, n in [(start, left), (start+left, count-left)]:
                    require_bytes(OUT / f'{slice_name(a, n)}.lean', emit_slice(names, a, n))
            path = OUT / f'{slice_name(start, count)}.lean'
        else:
            require_bytes(OUT / f'{slice_name(0, len(names))}.lean', emit_slice(names, 0, len(names)))
            dependencies = [ROOT_ADAPTER, f'{PREFIX}.{slice_name(0, len(names))}']
            data, path = emit_complete(names), OUT / 'Complete16.lean'
        for module in dependencies:
            require_checked_closure(source_path(module), args.receipt_dir, checked, pending)
        write_or_check(path, data, args.check, args.max_output_bytes)
        print(json.dumps(dict(file=str(path), bytes=len(data), selected_slice=args.slice,
                              complete=args.complete, checked_local_modules=len(checked),
                              dependencies=dependencies, checked=args.check), sort_keys=True))
    except (OSError, ValueError, KeyError) as exc:
        parser.error(str(exc))


if __name__ == '__main__':
    main()
