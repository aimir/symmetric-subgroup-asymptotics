"""Pure emitter for the selected original finite carrier graph.

Called only by export_lean_carriers.py --chart 16T1086 --modular.  The canonical
BinaryExceptional16T1086 module becomes an import wrapper, so legacy import
paths and public theorem names remain unique. No full row multiplication
table is constructed: the original generator transitions, words, and marked
range/kernel maps are retained verbatim as finite data.
"""
from pathlib import Path


def emit_modular_chart(label, w, q, data, out, save, lookup, row, *, check_only=False):
    if (label, w, q) != ('16T1086', 16, 16):
        raise ValueError('Only the selected degree-sixteen recovery chart is enabled')
    expected = {'alpha': 1024, 'beta': 256, 'quotient': 256,
                'axis': 4, 'coverKernel': 1}
    if {k: len(v['rows']) for k, v in data.items()} != expected:
        raise ValueError('Selected original graph sizes changed')
    directory = Path(out) / 'GeneratedCarrier16T1086'
    # --check must not create directories either.
    if not directory.exists():
        if check_only:
            raise SystemExit(f'Missing generated carrier directory: {directory}')
        directory.mkdir(parents=True, exist_ok=True)
    prefix = 'SymmetricSubgroupAsymptotics.GeneratedCarrier16T1086.'
    ns = 'SymmetricSubgroupAsymptotics.BinaryChart16T1086'

    def module(name, imports, body):
        imports = list(dict.fromkeys(imports))
        text = '\n'.join('import ' + (x if '.' in x else prefix+x) for x in imports)
        text += f'''\n\n/-! Selected literal carrier data; all checks use the Lean kernel. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace {ns}

{body}
end {ns}
'''
        path = directory / (name+'.lean')
        save(path, text)
        print(path.name, len(text), flush=True)

    def guarded(name, size, block, predicate):
        lo = block*32
        hi = min(lo+32, size)
        return f'''theorem {name}{block:03d} : ∀ i : Fin {size},
    ({lo} : ℕ) ≤ i.val → i.val < {hi} → {predicate} := by decide +kernel

'''

    def assemble(name, size, indentation=4):
        """Complete guarded coverage; no shifted rows or omitted last interval."""
        result = 'by\n'+' '*indentation+'intro i\n'
        blocks = (size+31)//32
        for b in range(blocks):
            indent = ' '*indentation+'  '*b
            lower = '(Nat.zero_le _)' if b == 0 else f'(Nat.le_of_not_gt h{b-1})'
            if b+1 == blocks:
                result += indent+f'exact {name}{b:03d} i {lower} i.isLt\n'
            else:
                result += indent+f'by_cases h{b} : i.val<{(b+1)*32}\n'
                result += indent+f'· exact {name}{b:03d} i {lower} h{b}\n'
                result += indent+'·\n'
        return result.rstrip()

    def permutations(name, values, width):
        """Keep the old first-occurrence literal names and balanced row lookup."""
        unique = list(dict.fromkeys(values))
        indices = {p: i for i, p in enumerate(unique)}
        modules = []
        for start in range(0, len(unique), 64):
            body = ''
            for j in range(start, min(start+64, len(unique))):
                p = unique[j]
                inverse = tuple(p.index(x) for x in range(width))
                body += f'''def {name}Literal{j} : Equiv.Perm (Fin {width}) where
  toFun x := ({row(p)} : Array (Fin {width}))[x.val]!
  invFun x := ({row(inverse)} : Array (Fin {width}))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

'''
            title = name[0].upper()+name[1:]+f'Literals{start//64:03d}'
            module(title, ['SymmetricSubgroupAsymptotics.FiniteGroupCertificates'], body)
            modules.append(title)
        definition = f'''def {name} (i : Fin {len(values)}) : Equiv.Perm (Fin {width}) :=
  {lookup([name+'Literal'+str(indices[p]) for p in values])}

'''
        return modules, definition

    for name in ['alpha', 'beta', 'quotient', 'axis', 'coverKernel']:
        d = data[name]
        size, degree = len(d['rows']), len(d['generators'])
        title = name[0].upper()+name[1:]
        graph = name in ['alpha', 'beta']
        if graph:
            dependencies, body = permutations(name+'Source', [x[0] for x in d['rows']], w)
            more, target = permutations(name+'Target', [x[1] for x in d['rows']], q)
            dependencies += more
            body += target
            body += f'''def {name}Generators (j : Fin {degree}) := {name}Source ({row(d['generators'])}[j.val]!)
def {name}Images (j : Fin {degree}) := {name}Target ({row(d['generators'])}[j.val]!)
'''
            element = lambda i: f'({name}Source {i}, {name}Target {i})'
            generators = f'(fun j => ({name}Generators j, {name}Images j))'
        else:
            dependencies, body = permutations(name+'Element', d['rows'], q if name == 'quotient' else w)
            body += f'def {name}Generators (j : Fin {degree}) := {name}Element ({row(d["generators"])}[j.val]!)\n'
            element = lambda i: f'{name}Element {i}'
            generators = name+'Generators'
        body += f'''def {name}NextTable (i : Fin {size}) : Array (Fin {size}) :=
  {lookup([row(a) for a in d['next']])}
def {name}WordTable (i : Fin {size}) : List (Fin {degree}) :=
  {lookup(['['+','.join(map(str,x))+']' for x in d['words']])}
'''
        module(title+'Data', dependencies, body)
        checks = []
        for b in range((size+31)//32):
            next_i = f'(({name}NextTable i)[j.val]!)'
            body = guarded(name+'NextChecked', size, b,
                f'∀ j : Fin {degree}, {element(next_i)} = {element("i")} * {generators} j')
            body += guarded(name+'WordsChecked', size, b,
                f'{element("i")} = (({name}WordTable i).map {generators}).prod')
            if graph:
                body += guarded(name+'FirstKernelChecked', size, b,
                    f'{name}Source i = 1 → {name}Target i = 1')
            piece = title+f'Rows{b:03d}'
            module(piece, [title+'Data'], body)
            checks.append(piece)
        body = f'''def {name}Cayley : FiniteCayleyCertificate {generators} {size} where
  elements := fun i => {element('i')}
  identity := 0
  identity_eq := by decide +kernel
  next i j := ({name}NextTable i)[j.val]!
  next_eq := {assemble(name+'NextChecked', size)}
  words i := {name}WordTable i
  words_eq := {assemble(name+'WordsChecked', size)}

'''
        if graph:
            body += f'''def {name}Certificate : FiniteHomCertificate {name}Generators {name}Images {size} where
  cayley := {name}Cayley
  first_kernel := {assemble(name+'FirstKernelChecked', size)}
'''
        else:
            body += f'def {name}Certificate := {name}Cayley\n'
        module(title+'Certificate', checks, body)

    for name in ['alpha', 'beta']:
        d, quotient = data[name], data['quotient']
        title = name[0].upper()+name[1:]
        kname = 'axis' if name == 'alpha' else 'coverKernel'
        kernel = data[kname]
        kt = kname[0].upper()+kname[1:]
        size, nq, nk = len(d['rows']), len(quotient['rows']), len(kernel['rows'])
        qix = {v[1]: i for i, v in reversed(list(enumerate(d['rows'])))}
        kidentity = tuple(range(q))
        kix = {v[0]: i for i, v in enumerate(d['rows']) if v[1] == kidentity}
        if set(kix) != set(kernel['rows']):
            raise ValueError('The exact original marked kernel rows changed')
        maps = [
            ('RangeForward', size, nq, [quotient['ix'][v[1]] for v in d['rows']]),
            ('RangeBackward', nq, size, [qix[v] for v in quotient['rows']]),
            ('KernelForward', size, nk,
             [kernel['ix'].get(v[0], 0) if v[1] == kidentity else 0 for v in d['rows']]),
            ('KernelBackward', nk, size, [kix[v] for v in kernel['rows']]),
        ]
        body = ''
        for suffix, domain, codomain, values in maps:
            body += f'''def {name}{suffix} (i : Fin {domain}) : Fin {codomain} :=
  {lookup(list(map(str, values)))}

'''
        module(title+'MapsData', [title+'Data', 'QuotientData', kt+'Data'], body)
        checks = []
        for suffix, domain, _, _ in maps:
            if suffix == 'RangeForward':
                predicate = f'{name}Target i = quotientElement ({name}{suffix} i)'
            elif suffix == 'RangeBackward':
                predicate = f'quotientElement i = {name}Target ({name}{suffix} i)'
            elif suffix == 'KernelForward':
                predicate = f'{name}Target i = 1 → {name}Source i = {kname}Element ({name}{suffix} i)'
            else:
                predicate = f'{name}Source ({name}{suffix} i) = {kname}Element i ∧ {name}Target ({name}{suffix} i) = 1'
            for b in range((domain+31)//32):
                piece = title+suffix+f'Check{b:03d}'
                module(piece, [title+'MapsData'], guarded(name+suffix+'Checked', domain, b, predicate))
                checks.append(piece)
        body = f'''theorem {name}_range : {name}Certificate.hom.range =
    Subgroup.closure (Set.range quotientGenerators) :=
  {name}Certificate.hom_range_eq_of_rows quotientCertificate
    {name}RangeForward {name}RangeBackward
    ({assemble(name+'RangeForwardChecked', size, 6)})
    ({assemble(name+'RangeBackwardChecked', nq, 6)})

theorem {name}_kernel : {name}Certificate.hom.ker.map
    (Subgroup.closure (Set.range {name}Generators)).subtype =
      Subgroup.closure (Set.range {kname}Generators) :=
  {name}Certificate.kernel_image_eq_of_rows {kname}Certificate
    {name}KernelForward {name}KernelBackward
    ({assemble(name+'KernelForwardChecked', size, 6)})
    ({assemble(name+'KernelBackwardChecked', nk, 6)})
'''
        module(title+'Identification',
               [title+'Certificate', 'QuotientCertificate', kt+'Certificate']+checks, body)

    # There is exactly one declaration path, including for all legacy block
    # and proper-carrier importers. Do not import an alternate pilot namespace
    # alongside the old monolithic module.
    wrapper = ''.join('import '+prefix+x+'Identification\n' for x in ['Alpha', 'Beta'])
    save(Path(out)/'BinaryExceptional16T1086.lean', wrapper)
    print('BinaryExceptional16T1086.lean', len(wrapper), flush=True)
