#!/usr/bin/env python3
"""Split the original degree-16 generator tuples into bounded Lean modules.

Select exactly one --chunk (at most 32 nodes). No group elements, subgroup
tables, source proofs, or action children are enumerated. The tuple emitter
is the original data producer's exact routine. The existing Data.lean stays
untouched until explicit --assemble, which requires every chunk's exact bytes
and a successful current check_lean.py receipt. No compiler is launched here.

Root-owned sequence: emit a selected chunk, check that module with the capped
runner, repeat only as authorized, then assemble and separately check Data.
"""
import argparse
import gzip
import hashlib
import json
import os
from pathlib import Path
import re
import sys
import tempfile

sys.dont_write_bytecode = True
from export_lean_menu_cayley import ROOT, lookup, node_id, permutation16 as permdef

FORMAL = ROOT / 'formal'
OUT = FORMAL / 'SymmetricSubgroupAsymptotics/GeneratedAction16'
PREFIX = 'SymmetricSubgroupAsymptotics.GeneratedAction16'
NAMESPACE = 'SymmetricSubgroupAsymptotics.BinaryActionData16'
DEFAULT_CHUNK_SIZE = 32
HEADER_LIMIT = 4 * 1024 * 1024
SPLIT_MARKER = '-- action16-data-chunks: '


def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda: f.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def load_nodes():
    """Read only the committed menu header, never the action-record stream."""
    with gzip.open(ROOT / 'certificates/data/binary_menu.jsonl.gz', 'rt') as f:
        line = f.readline(HEADER_LIMIT + 1)
    if len(line) > HEADER_LIMIT:
        raise ValueError('menu header exceeds its fixed size limit')
    header = json.loads(line)
    selected = [node for node in header['nodes'] if node['degree'] == 16]
    names = [node['id'] for node in selected]
    if len(names) != 1427 or len(set(names)) != len(names) or names[-1] != 'b16_1823':
        raise ValueError('the original degree-16 family or root has changed')
    for node in selected:
        if not re.fullmatch(r'b16_[1-9][0-9]*', node['id']) or not node['generators']:
            raise ValueError('invalid original node identifier or empty generator tuple')
        if any(sorted(g) != list(range(1, 17)) for g in node['generators']):
            raise ValueError(f"invalid original permutation in {node['id']}")
    return names, {node['id']: node for node in selected}


def node_body(node):
    """Exactly the original public generator definitions, on the same points."""
    num = node_id(node['id'])
    generators = [tuple(x - 1 for x in g) for g in node['generators']]
    text = ''.join(permdef(f'node{num}Generator{j}', g)
                   for j, g in enumerate(generators))
    choices = [f'node{num}Generator{j}' for j in range(len(generators))]
    return text + f'''def node{num}Generators (j : Fin {len(generators)}) : Equiv.Perm (Fin 16) :=
  {lookup(choices, 'j.val')}

'''


def actions_body(names):
    choices = [f'Subgroup.closure (Set.range node{node_id(name)}Generators)' for name in names]
    return f'''def actions (i : Fin {len(names)}) : Subgroup (Equiv.Perm (Fin 16)) :=
  {lookup(choices)}

end {NAMESPACE}
'''


def chunk_name(index):
    return f'DataChunk{index:03d}'


def chunk_count(names, size):
    if not 1 <= size <= DEFAULT_CHUNK_SIZE:
        raise ValueError('chunk size must be between 1 and 32 nodes')
    return (len(names) + size - 1) // size


def chunk_bytes(names, nodes, index, size):
    if not 0 <= index < chunk_count(names, size):
        raise ValueError('selected chunk index is out of range')
    start = index * size
    selected = names[start:start + size]
    header = f'''import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Basic

/-! Original degree-16 generator tuples at common-family indices
{start} through {start + len(selected) - 1}. Only literal permutations and
their finite inverse checks are defined here; no registry claim is made. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace {NAMESPACE}

'''
    return (header + ''.join(node_body(nodes[name]) for name in selected)
            + f'end {NAMESPACE}\n').encode()


def assembled_bytes(names, size):
    imports = ''.join(f'import {PREFIX}.{chunk_name(i)}\n'
                      for i in range(chunk_count(names, size)))
    return (imports + f'''import SymmetricSubgroupAsymptotics.BinaryWordParity
import SymmetricSubgroupAsymptotics.BinaryGeneratorRegistry

{SPLIT_MARKER}{size}
/-! The original common action family, with unchanged generator names,
indices, and balanced action expression. Its tuple chunks are independent
data modules. This file supplies no global action-coverage theorem. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace {NAMESPACE}

''' + actions_body(names)).encode()


def checked_data_layout(names, directory=OUT):
    """Check original order and exact action expression in either data layout.

    Returns None for the original monolith, or the installed chunk size.
    Consumers must not infer catalogue order merely from node-number sorting.
    """
    source = (directory / 'Data.lean').read_text()
    if source.count('\ndef actions ') != 1:
        raise ValueError('Data must define exactly one common actions function')
    actions = 'def actions ' + source.split('\ndef actions ', 1)[1]
    if actions != actions_body(names):
        raise ValueError('the original balanced Data.actions expression has changed')
    sizes = re.findall(r'^' + re.escape(SPLIT_MARKER) + r'(\d+)$', source, re.M)
    if sizes:
        if len(sizes) != 1:
            raise ValueError('ambiguous split-data layout')
        size = int(sizes[0])
        if source.encode() != assembled_bytes(names, size):
            raise ValueError('assembled Data differs from the exact compatible interface')
        return size
    defined = ['b16_' + n for n in re.findall(r'^def node(\d+)Generators\b', source, re.M)]
    if defined != names:
        raise ValueError('the original Data tuple order differs from the committed menu')
    return None


def check_original_chunk(names, nodes, index, size, directory=OUT):
    """Before migration, compare selected declarations byte for byte to Data."""
    installed_size = checked_data_layout(names, directory)
    if installed_size is not None:
        if installed_size != size:
            raise ValueError('installed chunk size differs; explicit remigration is required')
        return
    source = (directory / 'Data.lean').read_text()
    selected = names[index * size:(index + 1) * size]
    start = source.index(f'def node{node_id(selected[0])}Generator0 :')
    next_index = (index + 1) * size
    end = (source.index(f'def node{node_id(names[next_index])}Generator0 :')
           if next_index < len(names) else source.index('def actions '))
    expected = ''.join(node_body(nodes[name]) for name in selected)
    if source[start:end] != expected:
        raise ValueError('selected original Data declarations differ from the committed tuples')


def check_chunk_receipt(path, receipt_dir):
    """Fail closed on stale/failed local chunk checks; not an external DAG audit."""
    relative = path.relative_to(FORMAL)
    module = '.'.join(relative.with_suffix('').parts)
    receipt = json.loads((receipt_dir / f'{module}.json').read_text())
    output = FORMAL / '.lake/build/lib/lean' / relative.with_suffix('.olean')
    if (receipt.get('schema') != 2 or not receipt.get('success')
            or receipt.get('status') != 'complete' or not receipt.get('inputs_unchanged')
            or receipt.get('source') != str(relative)
            or receipt.get('source_sha256') != digest(path)
            or str(output) not in receipt.get('output_hashes', {})):
        raise ValueError(f'chunk has no successful current kernel receipt: {module}')
    for key in ('output_hashes', 'import_olean_hashes', 'dependency_source_sha256',
                'toolchain_fingerprints'):
        for name, expected in receipt.get(key, {}).items():
            if digest(Path(name)) != expected:
                raise ValueError(f'stale chunk receipt {key}: {module}')
    for file in ('lean-toolchain', 'lake-manifest.json'):
        path = FORMAL / file
        if receipt.get('toolchain_fingerprints', {}).get(str(path)) != digest(path):
            raise ValueError(f'chunk receipt lacks current {file}: {module}')


def write_or_check(path, data, check, limit):
    if len(data) > limit:
        raise ValueError('selected output exceeds byte limit; use smaller chunks')
    if check:
        if not path.is_file() or path.read_bytes() != data:
            raise ValueError(f'generated data differs: {path}')
        return
    if path.is_file() and path.read_bytes() == data:
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary = tempfile.mkstemp(prefix=path.name + '.', dir=path.parent)
    try:
        with os.fdopen(fd, 'wb') as f:
            f.write(data)
            f.flush()
            os.fsync(f.fileno())
        os.replace(temporary, path)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--chunk', type=int, help='Emit/check exactly one zero-based chunk')
    mode.add_argument('--assemble', action='store_true', help='Install Data only after every checked chunk')
    parser.add_argument('--chunk-size', type=int, default=DEFAULT_CHUNK_SIZE)
    parser.add_argument('--receipt-dir', type=Path, help='Required for --assemble; root runner receipts')
    parser.add_argument('--max-output-bytes', type=int, default=256 * 1024)
    parser.add_argument('--check', action='store_true', help='Compare bytes without writing')
    args = parser.parse_args()
    if args.max_output_bytes < 1:
        parser.error('output byte limit must be positive')
    if args.assemble and args.receipt_dir is None:
        parser.error('--assemble requires --receipt-dir from the capped kernel runner')
    try:
        names, nodes = load_nodes()
        total = chunk_count(names, args.chunk_size)
        if args.chunk is not None:
            data = chunk_bytes(names, nodes, args.chunk, args.chunk_size)
            check_original_chunk(names, nodes, args.chunk, args.chunk_size)
            path = OUT / f'{chunk_name(args.chunk)}.lean'
        else:
            # Checks may inspect all small tuple chunks, but never emit them.
            # Data is not replaced unless every comparison and receipt passes.
            checked_data_layout(names)
            for i in range(total):
                path = OUT / f'{chunk_name(i)}.lean'
                expected = chunk_bytes(names, nodes, i, args.chunk_size)
                if not path.is_file() or path.read_bytes() != expected:
                    raise ValueError(f'missing or changed chunk: {path}')
                check_original_chunk(names, nodes, i, args.chunk_size)
                check_chunk_receipt(path, args.receipt_dir)
            path, data = OUT / 'Data.lean', assembled_bytes(names, args.chunk_size)
        write_or_check(path, data, args.check, args.max_output_bytes)
        print(json.dumps(dict(file=str(path), bytes=len(data), nodes=len(names),
                              chunk=args.chunk, chunks=total,
                              chunk_size=args.chunk_size, checked=args.check), sort_keys=True))
    except (OSError, ValueError, KeyError) as exc:
        parser.error(str(exc))


if __name__ == '__main__':
    main()
