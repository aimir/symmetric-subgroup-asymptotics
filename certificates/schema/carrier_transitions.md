# Carrier transition and quotient certificates

These files supply the finite group and numerical inputs to the heterogeneous
carrier estimate used by the mixed-family argument. They are separate from
the small-width binary entry menu: that menu stops when it reaches one of
these carrier actions.

## Alphabet and literal maps

The original carrier colours are

    8T18, 8T26, 8T27, 8T28, 8T29, 8T31, 8T35,
    16T1082, 16T1083, 16T1084, 16T1332, 16T1547.

Their literal permutation generators and original symmetric-group normalizer
orders are in [base_alphabet.json](../data/base_alphabet.json). Catalogue
locators are names for the supplied actions; verification constructs groups
from the permutation lists and makes no catalogue query. An alternative
alphabet supplied on the command line must have exactly the same action
names, roles and weights, with each action permutation-conjugate to the
committed literal baseline. Every permutation row is checked at its stated
degree before GAP reads it.

[carrier_master_maps.json](../data/carrier_master_maps.json) supplies seven
epimorphisms, with one route for each original degree-eight colour:

    8T26 -> 8T26,
    8T27 -> 8T27, 8T28,
    8T35 -> 8T18, 8T29, 8T31, 8T35.

Each record gives source/target action names, images of the source generators
in precisely their order in the alphabet file, literal kernel generators,
and the kernel order. Source and target have the same physical degree eight.
The degree-sixteen and critical factors stay unchanged. Taking one full
inverse image under the product of these maps preserves all correlations
between coordinates. The group's original action weight is retained; it
is not replaced by its master's normalizer weight.

The GAP checker verifies homomorphism, image and exact kernel. It also tests
proper full subgroups correlated with a retained external C2 coordinate,
checking recovery under the product map and fullness of both projections.
These finite tests illustrate the full-preimage lemma; they do not replace
its proof for arbitrarily many coordinates. The exact source/target route
pairs are checked: an identity on an extra colour cannot replace its
epimorphism from the specified master.

## All literal normal kernels

[carrier_normals.jsonl.gz](../data/carrier_normals.jsonl.gz) has eight JSON
records, one for each master action:

| Master action | Number of literal normal kernels |
|---|---:|
| 8T26 | 27 |
| 8T27 | 13 |
| 8T35 | 28 |
| 16T1082 | 2,911 |
| 16T1083 | 2,911 |
| 16T1084 | 2,911 |
| 16T1332 | 2,292 |
| 16T1547 | 2,915 |
| Total | 14,008 |

Each action record has `schema_version`, `action_id` and `normals`. Each
entry in `normals` contains:

* `normal_generators`: permutations on the original action degree;
* `order`: the exact order of the generated subgroup N;
* `row`: the six integers `(k,n,m,a2,c,g)` defined below;
* `children`: sorted, duplicate-free **one-based** indices into the same
  action's normal list.

Let U be the literal action group. Put

    R_N = N^2[N,U],
    k = log_2 |N/R_N| = d_U(N),       n = log_2 |N|,
    m = max { d_U(M) : M normal in U, M <= N intersect U' },
    a2 = d_U(R_N),                    Q = U/N.

If Q is abelian, `(c,g)=(log_2|Q|,0)`; otherwise
`(c,g)=(log_2|Z(Q)|,log_2|Q'|)`. Non-elementary abelian quotients, including
the C4 and C4 x C2 quotients of 8T27, use the abelian rule.

The checker recalculates every parameter. For the five degree-sixteen
masters it also checks `Phi(U)=U'` and `a2<=m`. The aggregate numerical menu
may inflate `a2` to `m` for those actions. It does not do so for 8T27:
that action has kernels with `a2>m`.

### Normal-list completeness

The supplied `children` of N are exactly the inverse images of all order-two
subgroups of `Z(U/N)`. The checker enumerates the elements of this centre,
constructs every order-two extension, and finds its literal subgroup in the
supplied list. It verifies that each edge doubles the order, that the trivial
kernel occurs once, that no kernel is duplicated, and that all supplied
vertices are reachable from the trivial kernel.

This is a finite coverage argument. If M/N is a nontrivial normal subgroup
of the finite 2-group U/N, then it meets the centre nontrivially and contains
a central involution. Induction therefore reaches every normal subgroup of
U. Verification needs neither `NormalSubgroups` nor a catalogue enumeration.
The producer may use `NormalSubgroups` to discover a candidate list.

## Numerical menu and cones

[carrier_transitions.json](../data/carrier_transitions.json) contains the
profile multiplicities, the 52-to-12 domination classes for the degree-sixteen
rows, the 29 degree-eight rows, the 41-to-6 reduction, and the two rational
positive-semidefinite parts of the final cone certificates. A rational number
is encoded as `[numerator,positive_denominator]`.

For a row r, the transition support is

    h_r(x,y) = max { x delta + y epsilon :
                     0<=delta<=k, 0<=epsilon<=m, delta+epsilon<=n }.

This integral polytope has integral vertices. The pair coefficient is the
maximum of the supports in the two possible orders. Its physical scales
are one for degree eight and two for degree sixteen. The verifier checks
every old and new column in the 52-to-12 reduction and both marked
coefficients. It then checks simultaneous pair-row/k/q domination for all
41 rows, with `q=max(m,a2)`, before merging the identical whole-X and whole-P
rows. The resulting six-row matrix B is scaled by the physical half-degree
`p=4T`; its mark vectors are alpha and beta.

For nonnegative row masses p_i, critical rank R, and critical-ledger
parameters `0<=j<=R`, `0<=ell<=R/2`, the quadratic expression is

    E = ell(R/2-ell) + (j-ell)(R-j) + (1/2)p^T Bp
        + sum_i p_i [ell(alpha_i+beta_i)
                     + alpha_i max(j-2ell,0)].

The verifier reconstructs the entire quadratic deficit in the two exhaustive
cones `j>=2ell` and `j<=2ell` by exact polarization. For each, it checks that
5248 times the deficit is a positive-semidefinite rational matrix plus an
entrywise nonnegative matrix. Exact symmetric Schur elimination proves the
positive-semidefinite assertion without numerical eigenvalues. Consequently,
with `sum p_i=4T`,

    E <= (R+4T)^2/4 - (25/82)RT - (29/164)T^2.

The checker also verifies the original colour sums `3/64` and `65/688128`.
Repeated-type factorials are handled by the mathematical exponential-formula
argument, not by changing the colour weights during transport.

## Scope of the certificate

The joint rank-transition polygon, the five-term radical transport, the
actual-critical attachment formula, the epimorphism estimate, and the
iteration of the recurrence are mathematical lemmas. This certificate
supplies and checks their finite local rows and the numerical domination
and cone inequalities. It does not establish those universal lemmas by
testing finitely many groups, or prove the mixed-family/global asymptotic
without its analytic argument.

See [the execution instructions](../../computations/gap/CARRIER_CHECKS.md).
