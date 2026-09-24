# Carrier Bockstein profiles and critical quadratic constants

The [carrier profile data](../data/carrier_socket.json) supply the remaining
local inputs for the narrow C4 attachment estimate. They bind all twelve
carrier colours to the pinned [base alphabet](../data/base_alphabet.json).
For a finite binary group G define

    Phi=G^2[G,G], Psi=Phi^2[Phi,G],
    d=log_2|G/Phi|, tau=log_2|Phi/Psi|,
    ell=number of abelian invariant factors divisible by four.

The integer ell is the dimension of binary characters lifting to C4, or the
kernel of the coefficient Bockstein H1(G,F2)->H2(G,F2). The data retain d,
ell,tau, the full abelianization, physical weight degree/8 and original
symmetric normalizer order. Every field is reconstructed from the literal
action; no catalogue query is used. The checked inequalities are

    d+ell<=3wt, tau<=2wt, 4d+5ell>=10wt.

The liftable-character space is also counted by actual maps to C4. In
particular 8T27 and 8T28 have ell=1. Replacing it by zero would fail the
replay. Original action normalizers and the two equal-abstract-type but
nonconjugate pairs remain distinct.

For actual binary character rows on A, the checker forms their full central
pullback with C4^e. Writing q for row rank, h for intersection with the
liftable-character space and q'=q-h, it checks the exact Frattini kernel,

    d(H)=d(A)+e-q', tau(H)<=tau(A)+q',

and the actual Phi/Psi kernel sequence. Fifty-two pullbacks include all twelve
carriers, dependent rows and mixed-factor rows. Twenty C4 marker-pair checks
retain the distinction between an early order-four graph and later
order-eight dependent pairs. These controls do not replace the general
cohomological proof or the continuous scalar inequality.

Run:

```sh
python3 computations/gap/run_carrier_socket.py
python3 computations/python/verify_critical_quadratic.py
```

The second program independently enumerates every invertible binary matrix
in dimensions 2 and 4 and tests q(x)=x1*x2, respectively
q(x)=x1*x2+x3*x4. The isometry group orders are 2 and 72; the four-dimensional
form has ten zero vectors. The actual critical group types and their original
normalizers are checked by the base-alphabet verifier. This finite linear
calculation supplies the constant 72 used in the critical lift count; it is
not a classification of arbitrary permutation actions.

Both commands are release-local. The GAP command accepts `--gap-command`
and `--timeout`, and rejects errors and missing mathematical verdicts.
