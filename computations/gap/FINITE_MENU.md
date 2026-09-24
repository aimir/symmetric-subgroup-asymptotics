# Complete finite binary menu

The finite menu covers transitive binary actions of degrees 2, 4, 8 and 16.
It supplies a local certificate for every literal normal subgroup of every
action outside the fixed seventeen-colour base alphabet. The normal is part
of the record; isomorphic quotients do not identify different axes.

The [schema and coverage argument](../../certificates/schema/binary_menu.md)
define the data and the exact conclusions of replay. The certificate is
[compressed JSONL](../../certificates/data/binary_menu.jsonl.gz), with the
[base alphabet](../../certificates/data/base_alphabet.json) pinned separately.

## Replay

From the repository root, using Python 3.9+ and GAP:

```sh
python3 computations/gap/finite_menu.py verify
```

The command discovers `gap` or `sage --gap` on PATH. An explicit executable
command and timeout can be supplied before the mode:

```sh
python3 computations/gap/finite_menu.py --gap-command 'sage --gap' --timeout 7200 verify
```

The checker reconstructs groups and maps from literal permutations. It checks:

* every transitive index-two child, starting from an explicit Sylow wreath
  root at each degree, with actual permutation-conjugacy edges;
* every central-involution extension in the normal-subgroup lists, starting
  from the identity;
* exact original symmetric normalizers and bindings to the fixed base colours;
* every retained central cut, faithful quotient cover, whole-centre character
  inequality or same-degree replacement map;
* all final counts, node reachability and the complete input framing.

Verification does not call a transitive-group catalogue or `NormalSubgroups`.
Those operations are used by the producer to find candidates. GAP's ordinary
permutation-group, quotient, centre and homomorphism algorithms remain part
of the computational trust boundary. This is not Lean verification.

The supplied certificate has the following checked record counts:

| Records | Count |
|---|---:|
| Action nodes | 1,457 |
| Base / other regular / other nonregular actions | 17 / 19 / 1,421 |
| Literal nonbase normals | 132,009 |
| Pair / character / transport witnesses | 131,975 / 30 / 4 |
| Transitive index-two edges | 10,298 |
| Central-involution normal edges | 450,951 |

The direct-cover branch is exercised by a separate control; no record in this
data file needs it. The 132,009 normals include 272 on the nonbase regular
actions and 131,737 on the nonregular actions. Node counts do not assert a
minimal conjugacy-class list. The
[manifest](../../certificates/manifests/finite_witnesses.json) binds the exact
data and checker bytes; a digest alone is not a mathematical verdict.

## Produce a candidate

GAP 4.13.1 with TransGrp 3.6.5 supplies the producer's representatives. The
producer also uses SmallGrp identification to cache small faithful covers;
each cache use has an actual isomorphism and serialized map. Minimality of
the cover degree is not an acceptance premise.

```sh
python3 computations/gap/finite_menu.py export --output candidate_menu.jsonl.gz
python3 computations/gap/finite_menu.py verify --input candidate_menu.jsonl.gz
```

The producer writes a temporary gzip file and publishes the output path only
after its final verdict. Existing outputs require `--force`. Groups, normals,
faithful representations and generating sets can be ordered differently by
different GAP versions, so byte-identical regeneration is not required.
Replay verifies their mathematical properties.

For a smaller exercise of the same interfaces:

```sh
python3 computations/gap/finite_menu.py export --widths 2 4 8 --output small_menu.jsonl.gz
python3 computations/gap/finite_menu.py verify --input small_menu.jsonl.gz --allow-partial
```

Partial replay explicitly reports its degree scope. Without `--allow-partial`,
the verifier requires all four degrees. A successful small run is not the
complete finite certificate.

The separate alphabet producer writes a candidate with all seventeen actions
and their complete symmetric normalizers:

```sh
python3 computations/gap/finite_menu.py export-alphabet --output candidate_alphabet.json
```

The committed alphabet defines the carrier colours in the mathematical
interface. Passing numerical order/weight tests alone does not authorize a
different set of colours. The complete-menu checker binds every header colour
to this fixed alphabet by permutation conjugacy and role.

## Focused controls

```sh
python3 computations/gap/finite_menu.py controls
```

These check local round trips on 729 normals, all four charts under different
point labellings and a separate direct-cover example. This bounded fixture
uses `NormalSubgroups` to generate test cases. It is distinct from the complete
coverage checker, whose all-normal closure does not use that oracle.

Errors, syntax warnings, nonzero process exits, missing mathematical PASS
markers and truncated/framing-invalid data cause failure. The Python wrapper
passes quoted arguments directly to the executable and never runs supplied
certificate contents as a shell command.

## Counting scope

The four accepted local alternatives have separate source-counting theorems.
The finite computation verifies their group/module/map premises and exhaustive
finite coverage. It does not infer the universal epimorphism bound from a
numerical cut alone, or infer the weighted asymptotic theorem from local
reversibility. Original action weights, mixed-family reserves and the single
terminal attachment are retained by the surrounding mathematical argument.
