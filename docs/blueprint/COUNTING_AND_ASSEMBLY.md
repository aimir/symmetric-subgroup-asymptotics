# Counting, critical model and global assembly

Claim identifiers refer to the [blueprint index](README.md). The normalization
is exactly the one fixed in [SPEC.md](../../SPEC.md).

## DEF-COUNT: three different counting sequences

Let s_n count actual subgroups of S_n and put R=floor(n/2), epsilon=n mod 2.
Define

    c_R = [y^R] exp(y/2+y^2/6+y^4/384),
    p_n = c_R + epsilon*c_(R-1)/6,       c_(-1)=0,
    G_R = number of subspaces of F_2^R,
    L_n = n! G_R p_n,                   A_n = s_n/L_n.

For even physical degree 2N, let F_N be the count of all fixed-point-free
2-subgroups of S_(2N), divided by L_(2N). Let E_N be the similarly normalized
subfamily with at least one orbit outside the four specified critical actions.
Then

    F_N = Ccrit_(2N) + E_N.

Here Ccrit_n is a normalized subgroup-family count, not an EGF coefficient.
At odd degree its critical model includes one singleton or natural S3 marker,
along with critical even actions. The complete ordinary sequence A and the
complete binary sequence F are never interchangeable without a proved bound.

## CNT-WEIGHT: recovered orbits and the exact labelled weight

For a transitive action U of degree w, set a(U)=|N_(S_w)(U)|. A profile having
q_U occurrences of each specified permutation action contributes exactly

    n! / product_U (a(U)^q_U q_U!)

labelled orbit data. First partition into unordered blocks and then choose
the action on each block; the block factorials cancel. A subgroup projecting
onto every specified transitive action recovers its orbit partition and those
actions, giving the required uniqueness of the underlying physical data.

All subsequent pointing arguments begin with this weight. If an original
width-w orbit is pointed and its complete complement has degree b=n-w, the
factor n!/(b!a(U)) combines with the source count b! exactly once. An auxiliary
quotient cover changes a graph encoding, not the original action denominator.
Repeated types retain their occurrence factorials. The complete joint quotient
and extension records, all concrete same-prime columns and restricted
transgression conditions belong to this same physical subgroup.

## CRT-MODEL: critical actions and every central lift

The critical family uses the following four specified even actions, with
their quotients and normalizers supplied by explicit action calculations:

| Action | Degree | Elementary binary quotient rank | a(U) |
|---|---:|---:|---:|
| C2 | 2 | 1 | 2 |
| regular V4 | 4 | 2 | 24 |
| natural D8 | 4 | 2 | 8 |
| plus-type extraspecial group of order 32 | 8 | 4 | 384 |

The two odd deficiency-one actions are a singleton and natural S3, giving the
factor 1+y/6. Counting this chosen family does not require asserting that
these actions exhaust equality in a permutation-rank bound. Where needed for
noncritical refinements, that equality classification is a separate input.

For a critical orbit product D, take the product K of the specified canonical
kernels and the quotient pi:D->V=F_2^R. Full-projecting subspaces U<=V give
the canonical subgroups pi^(-1)(U). Each contains K, so its projection to an
actual factor contains the specified kernel and is full on its quotient;
it is therefore the whole factor. This step needs no Frattini theorem.
The subgroup itself recovers its blocks,
actions, kernels and quotient subspace. Failure to project fully onto any
coordinate lies in at most 15R hyperplanes, so its relative mass is
O(R G_(R-1)/G_R)=O(R2^(-R/2)), uniformly in the profile.

Extra subdirect lifts must also be summed. For the nonabelian critical factors,
let q:V->K be the vector-valued squaring form, k=dim U and
c=codim_K span(q(U)). The exact number of lifts over U is

    sum_(j=0)^c GaussianBinomial(c,j;2) * 2^(k*j).

For each possible intersection W with K, the admissibility condition is
span(q(U))<=W. Every element of the resulting quotient has square one, so
the inverse-of-a-product identity forces commutativity. The quotient is
therefore elementary abelian, and its complements form a torsor under
Hom(U,K/W). This argument works for any finite central extension with binary
kernel and quotient. The square condition also contains the commutator
condition; replacing it by the polar form alone is invalid.

The needed quadratic realization lemma says that, for a prescribed quadratic
form on a k-space and a surjection onto a nonsingular plus-type space of
dimension 2 or 4, the fibre has either zero elements or |O^+(d,2)| elements,
hence at most 72. Choose a basis of the retained relation dual from the
actual coordinate restrictions. Its dual relations isolate the pivot
outcomes, so fixing nonpivot maps fixes all pivot quadratic forms jointly.
Counting their actual realization fibres gives total exceptional lift mass O(G_R 2^(-d)), where

    d = R/2 - (number of nonabelian factors).

This may be only a constant-factor estimate on a particular word. The gain
becomes exponential after summing labelled profiles: the exceptional EGF is
bounded using

    P_tilde(y) = y/(2 sqrt(2)) + 7y^2/48 + y^4/768,

with odd marker 1+y/(6 sqrt(2)). Halving the quartic coefficient yields
relative error 2^(-R/4+O(sqrt R)). For an odd S3 marker, the actual subgroup
contains its A3 kernel; after quotienting that forced subgroup the binary
lift argument applies. Thus, for some a>0,

    Ccrit_n = 1 + O(2^(-a*n))

at both parities. This is proved inside the critical family and supplies both
an independent bounded term and the matching lower bound for the final proof.

## BIN-ERROR: close the complete binary family before the main induction

Actual transitive 2-group orbit sizes are powers of two. Partition E into
the disjoint families with an orbit of width at least 64, with width 32 but no
larger orbit, and with every orbit of width at most 16. The large and small
theorems give one scalar epsilon_B and one nonnegative forward kernel K_B:

    E_N <= epsilon_B(N) + sum_(M<N) K_B(N,M) F_M.

The full scalar and full row are O(2^(-a*N)) for fixed positive rates, after
all widths, normals, witnesses and profiles have been summed. Their derivation
does not assume F is bounded.

Use F=Ccrit+E. Since Ccrit is bounded, the forcing is bounded. Once the row
is at most 1/2, induction from finitely many initial values bounds E and F.
Substitute that bound into the SAME recurrence to obtain

    E_N = O(2^(-a_E*N)).

This auxiliary theorem estimates the complete binary family. It is proved
once and used on the appropriate disjoint source families in the main count.

## NB-EXHAUST: the surviving binary handoff

Earlier complete consumers reduce the residual nonbinary alphabet to selected
pair tops of sizes 24,32,48,64,96,128,192,256. CAP-SECTION proves an already
admissible certificate for every selected actual normal entry. This recognizes
an existing menu; it does not pay a new copy of that menu's scalar or kernel.

The unmarked residual is empty. The marked residual consists of natural S3
markers, fixed points and binary orbits, with at least one noncritical binary
orbit. Its whole mass is bounded by one positive transfer H_E into E. For
n=2j+epsilon, define

    p_odd(j)=c_j+c_(j-1)/6,
    alpha_j=c_j/p_odd(j), beta_j=c_j/(3p_odd(j)),
    r_j=(j-1)/4 * (c_(j-1)/c_j) * (G_(j-1)/G_j)    (j>=2),
    u_j=alpha_j+beta_j*(7+(6j)^(1/4)), v_j=beta_j*r_j,

with r_0=r_1=0 and absent negative targets. The transfer is

    H_E(n,m)=K_mark(n,m)
       + 1_(n odd)*(u_j 1_(m=n-1)+v_j 1_(m=n-3)),

where K_mark has exponentially small complete row. The coefficients u_j,v_j
are bounded, u_j->1 and v_j->0. This row is not a strict contraction on complete
counts. Its two shifted terms multiply the already proved error E, so H_E E
is exponentially small. The same-family marked-moment estimate underlying it
must retain the factor 1/4 in duplicate-pair collapse and the joint ternary
character fibres.

## ASM-OLD: the consumer aggregate

Let epsilon_old be the complete separate scalar sum and (epsilon_F,K_F)
the complete forward scalar/kernel aggregate on a disjoint physical
partition. The assembly theorem below assumes

    epsilon_old=O(2^(-a n)), epsilon_F=O(2^(-b n²)),
    sum_(m<n)K_F(n,m)=O(2^(-c n))

for positive constants a,b,c. Each bound includes its entire support,
parameter and action sum after exact normalization. A recognition that
routes a state to an existing consumer contributes no second copy of its
scalar or kernel. The even binary source families are paid together once
by E, without an additional coarse scalar.

[GLOBAL_COMPONENTS](GLOBAL_COMPONENTS.md) gives exact terminal and packet
interfaces and the local graph mechanism. Those interfaces alone do not
assert that the consumer domains exhaust the physical partition; that
coverage is a separate hypothesis of the master inequality.

## ASM-MAIN and THM-MAIN: the exact master

Given the exhaustive physical partition and the stated complete consumer
bounds, the master inequality is

    A_n <= Ccrit_n + epsilon_old(n) + epsilon_F(n)
          + sum_(b<n) K_F(n,b) A_b
          + 1_(n even) E_(n/2)
          + sum_(even m<n) H_E(n,m) E_(m/2).

There is one inherited aggregate, one same-degree even binary error and one
typed H_E. Each physical atom keeps one terminal attachment. The auxiliary
binary kernels are not also added directly to K_F.

The forcing excluding K_F is bounded and tends to one. The complete row of
K_F tends to zero; choosing an onset with row at most 1/2 and using finite
initial values first proves boundedness of A. The assumed complete estimates give
exponential scalar and row bounds. Substitution then gives A_n<=1+O(2^(-cn)).
The critical lower family gives A_n>=1-O(2^(-cn)), proving THM-MAIN with a
common positive c at both parities. No effective starting degree or optimized
c is claimed.

## APP-C1: required validity check

The split one-external-triple application retains the exact surviving character
weight sigma_3^surv(K)=|Theta_surv(K)|, with all prior exclusion indicators
inside that count. It satisfies 0<=sigma_3^surv(K)<=3^d_3(K)-3^h_3(K);
equality need not hold after exclusions. Its
inverse-complement chart weights each order-three representative by 1/q, where
q counts representatives of that oriented character. Quotienting by a binary
kernel preserves this split mark. A shared-C3 insertion followed by the external
mark can produce a genuine double moment; it cannot be replaced by one moment
or by independent sources.

The high-incidence remainder is excluded using the relative theorem
20 delta_U(N)>3 deg(U), whose exceptional actual actions are already accepted
earlier. The orbit filtration then gives d_3(K)<=3m/20, contradicting the
residual condition. This is an earlier-consumer-or-capacity application of the
complete framework, not a direct instance of an arbitrary odd-order action
on a vector space. Its consumed reserve is never reused in ASM-MAIN.
