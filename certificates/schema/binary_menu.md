# Binary small-width witness and coverage schema

Version 1 is a gzip-compressed sequence of JSON objects, one per line. It
contains a header, one record for every declared action node, and a footer.
The format is data, not executable GAP source. The Python wrapper validates
JSON value types and creates quoted GAP literals without shell evaluation.

The [producer and checker](../../computations/gap/finite_menu.py) use the
[literal local predicates](../../computations/gap/finite_entry_witnesses.g)
and [coverage routines](../../computations/gap/finite_menu_coverage.g).

## Conventions

Permutations are one-based image lists of exactly the stated degree. The
image of point i is row[i]. GAP composes permutations on the right, so
`i^(g*h)=(i^g)^h`; conjugation is `H^c=c^-1 H c`. A generator-image list
has one row for each original action generator, in its declared order.
The trivial permutation action has degree zero and an empty image row.

Subgroups are specified by literal generators inside their original action.
Normal subgroups with isomorphic quotients remain distinct records. Quotient
representations and cached covers include actual homomorphism images and
exact kernel checks; an abstract group identifier is never an acceptance
condition.

## Header

* `kind="header"`, `schema_version=1`, and `widths` declare the domain.
  A complete replay requires `[2,4,8,16]`. An explicit partial replay has a
  separate command-line flag and reports its narrower scope.
* `nodes` gives each action's unique string `id`, `degree`, ordered literal
  `generators`, and exact `order`. The `normalizer_generators` and
  `normalizer_order` specify its entire normalizer in the original symmetric
  group. The checker recomputes equality, not just containment.
* `roots` supplies one node per degree and a permutation conjugator from the
  explicitly constructed iterated binary wreath group to that node.
* `base_alphabet` supplies the seventeen literal action colours, their
  `role` (`critical`, `cyclic4` or `carrier`), orders and complete symmetric
  normalizers. Every supplied colour is bound by permutation conjugacy and
  role to the committed [base alphabet](../data/base_alphabet.json).
* `degree16_chart` and `degree8_charts` retain the four exceptional map data.
* `producer` records the GAP and TransGrp versions used to find candidates.
  `catalogue_locator` fields are descriptive. Verification never uses them
  to infer an action, normal subgroup, map or completeness statement.

Action nodes need not be asserted pairwise nonconjugate for coverage. Their
literal index-two edges prove coverage even if redundant nodes are present.
Counts of nodes are therefore not by themselves a proof of a minimal list of
conjugacy classes.

## Action record and coverage edges

Every action record has `kind="action"`, its registry `id`, and a `role`.
`action_children` lists every transitive index-two subgroup H of this literal
U, with H's original-degree generators, a target action-node identifier and
a permutation taking H to that target. Intransitive index-two children are
excluded only after the checker computes all kernels and tests transitivity.

For a regular transitive U, the list is empty: a proper subgroup of a group
of order w cannot act transitively on w points. A nonregular base colour is
not a leaf; it retains every transitive index-two child.

A `base` record also has `base_index` and `base_conjugator`. The latter binds
U to the specified literal base colour. Its `normals` list is empty because
the local entry theorem quantifies outside the base alphabet.

Every other action has role `regular` or `nonregular` and a `normals` list
containing all its literal normals. Each normal record contains
`normal_generators`, `normal_order`, `children` and one local witness.
`children` consists of the sorted, distinct indices of every central
involution extension of N in U, with indices into this same normal list.

## Local witness branches

| `kind` | Retained witness and exact acceptance condition |
|---|---|
| `pair` | The ordered invariant pair `frame`; `top_images`; literal `kernel_generators` for K; `intersection_generators` for M=K intersect N; and `cut_lift_generators` for C0 with M<=C0<=K. The checker verifies [C0,U]<=M, reconstructs all section dimensions and the actual map onto a faithful representation of U/(KN). |
| `direct` | `cover_degree`, one `cover_images` row per U-generator, and `gap`. The map is onto its literal permutation image, has kernel exactly N, moves exactly the declared number of points and satisfies gap=w-cover_degree>0. |
| `character` | `quotient_order`, `z`, and original-degree `centre_lift_generators` and `omega_lift_generators`. Their images must equal the whole centre of U/N and its whole involution subgroup. The checker verifies 38^(8z)<2^w*25^(8z) using integers. |
| `transport` | `quotient_degree` and `quotient_generators`; actual `alpha_images`; original-degree `cover_generators`; `beta_images` and exact `cover_kernel_generators`; and an orbit `word` whose entries give `block` and `base_index`. Both maps are onto the same literal quotient and ker(alpha)=N. Every actual cover orbit projects fully to its assigned base colour, the original physical degree is unchanged and at least one quarter is noncritical. |

For a pair witness write A=K/M and let C=C0/M. Its numerical fields are

    dimA=log_2 |K/M|,
    t=dim A^U,
    ell=dim (A/A^U)^U,
    c=dim C,
    r=dim (A/C)^U,
    gap=w-cover_degree-2c-4r>0.

The lifted cut is central in the same original section, rather than a
submodule selected from an unrelated quotient. The cover map's kernel is
exactly KN. The checker recomputes fixed sections by commutators in the
literal original action. Cache keys include the exact source, ordered frame
and complete element sets of M and C0; different normal maps are still
verified individually.

Transport records retain the actual group P generated by `cover_generators`.
The degree-16 cover is a proper subgroup of C4[4] x D8[4]^3; the ambient
product cannot substitute for P. The regular degree-16 representation used
to encode a degree-8 chart's common quotient is auxiliary, not physical
support.

## Footer and rejection

The footer has `kind="footer"`, `schema_version=1`, and exact `counts` of
nodes, base/regular/nonregular actions, normals, both sorts of edges and the
four local witness branches. The checker recomputes every count, checks that
every declared node was processed once and that every node is reachable from
its degree's explicit wreath root.

A missing record, missing transitive index-two edge, missing normal or central
involution extension, incorrect map/kernel/dimension, altered base binding or
absent final verdict is rejected. A successful GAP process exit by itself is
not acceptance. GAP errors and syntax warnings are also rejected.

## Why the two closure checks prove coverage

For w=2^a the explicitly constructed iterated wreath group W_w has order
2^(w-1), the full two-part of w!, so it is a Sylow 2-subgroup of S_w.
Every binary subgroup of S_w is conjugate into W_w. Any subgroup of a finite
2-group lies at the bottom of a chain of subgroups of index two: repeatedly
choose a maximal proper overgroup along an inclusion chain. If the bottom
action is transitive, every overgroup in that chain is transitive as well.
Thus intransitive branches can be omitted. Checking all transitive index-two
children at every nonregular node, with each literal conjugacy edge, proves
that every transitive binary action of the declared degrees is represented.

The complete child enumeration uses U/Phi(U). The checker verifies that the
chosen quotient generators form a basis of this elementary binary group and
enumerates every nonzero binary functional. Its kernels are exactly all
index-two subgroups of U. Catalogue availability and catalogue counts do not
enter this argument.

For normal coverage, suppose N<L are normal in a finite 2-group U.
The nontrivial normal subgroup L/N of U/N meets Z(U/N) nontrivially, by the
conjugation class equation; that intersection has an element z of order two.
Its inverse image extends N by index two and lies inside L. Repeating this
step reaches L, starting from the identity subgroup. The checker requires the
identity and, at every supplied normal, all such central-involution children.
Consequently its finite normal list is exhaustive. Computing the centre and
all its order-two elements is part of replay; `NormalSubgroups` is not used.

These are mathematical coverage arguments coupled to a GAP computation.
Acceptance relies on GAP's permutation-group and quotient algorithms, Python
parsing and the supplied checker code. It is not a Lean proof. The universal
lift bounds, original-weight aggregation and asymptotic estimates remain
separate mathematical statements, rather than conclusions of this finite run.
