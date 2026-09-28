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

with odd marker 1+y/(6 sqrt(2)). Evaluate the positive perturbed series at
the original saddle rho_R. The independent original saddle lower bound
gives perturbed/original coefficient ratio at most

    O(sqrt(R) exp(P_tilde(rho_R)-P(rho_R)))
      <= O(sqrt(R) exp(-R/16)) = O(2^(-R/32)).

Here P_tilde(rho)<=P(rho)-rho^4/768 and rho_R^4>=48R eventually.
This uses the already proved original saddle estimate and avoids a second
saddle analysis. The positive weighted sum of the bounds at R and R-1,
divided by c_R+c_(R-1)/6, gives the same rate for the two odd markers;
the exceptional S3 marker's extra 1/sqrt(2) improves the bound.
For an odd S3 marker, the actual subgroup
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

## NB-EXHAUST: the post-E7 alphabet and binary handoff

Earlier complete consumers reduce the residual nonbinary alphabet to selected
pair tops of sizes 24,32,48,64,96,128,192,256. CAP-SECTION proves an already
admissible certificate for every selected actual normal entry. This recognizes
an existing menu; it does not pay a second copy of that menu's scalar or
kernel. The literal E7 hot/cold union is now itself installed as a complete
original-weight forward estimate. Its existential pointing and pair frame
remain proof data, while the counted index is the finite original-action and
literal-normal menu. The estimate has zero scalar and an exponentially small
strictly forward row.

At the formal interface the complete outside frontier is now partitioned
exactly into the subfamily carrying this orbitwise alphabet and its complement.
The first subfamily injects unchanged into the E7 hot/cold union and therefore
has the preceding complete forward estimate. Thus the outside-frontier
producer needs only one remaining estimate, for the pre-E7 complement; adding
it to the installed E7 estimate closes the full outside term without overlap.

Orbitwise, the remaining alphabet is binary, natural S3, or a selected UP
pair orbit. E7 removes the third alternative. Therefore the complete original
subgroup satisfies the intrinsic `Fits` predicate used by the repeated-marker
owner. In particular an outside-`Fits` residual is empty. If the state also
has no fixed or natural-S3 marker orbit and claims nontrivial O^2, simultaneous
restriction to all actual orbits makes the whole group binary and gives a
contradiction. This is the O02 branch, including proper subdirect products.

The marked O03 branch enters the already counted complete `Fits` owner with
the original subgroup unchanged. Its positive marker-defect part uses the
strictly forward complete row K_mark against ordinary counts. Its zero-defect
part uses the typed binary frontier. For n=2j+epsilon, define

    p_odd(j)=c_j+c_(j-1)/6,
    alpha_j=c_j/p_odd(j), beta_j=c_j/(3p_odd(j)),
    r_j=(j-1)/4 * (c_(j-1)/c_j) * (G_(j-1)/G_j)    (j>=2),
    u_j=alpha_j+beta_j*(7+(6j)^(1/4)), v_j=beta_j*r_j,

with r_0=r_1=0 and absent negative targets. The zero-defect target is

    B_(2j)=E_j,
    B_(2j+1)=u_j E_j+v_j E_(j-1).

The row K_mark is exponentially small. The coefficients u_j,v_j have
polynomial bounds, with u_j->1 and v_j->0. First apply the proved native
binary recurrence to E_j and E_(j-1), then pad their even targets to the full
ambient-degree range. This converts B_n into an exponentially small scalar and
strictly forward ordinary row before the main boundedness induction.

There is also a sharper historical positive transfer H_E directly into E,
obtained by retaining a noncritical binary orbit through marker collapse. It
is valid but unnecessary for the compositional main proof. The formal and
manuscript assembly use the earlier `Fits` partition above, avoiding a second
residual predicate and a duplicated marker route.

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
bounds, before transporting the binary target the master inequality is

    A_n <= Ccrit_n + epsilon_old(n) + epsilon_F(n)
          + sum_(b<n) K_F(n,b) A_b
          + sum_(m<n) K_mark(n,m) A_m
          + B_n.

Substitute the native binary recurrence in B_n before induction. Its current
and predecessor coefficients introduce only polynomial factors, which are
absorbed by a smaller exponential rate. The result is one exponentially small
scalar and one nonnegative strictly forward ordinary kernel. Each physical
atom keeps one terminal attachment, and no binary or marker kernel is paid
twice.

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

The formal audit now keeps this marking through the finite continuation.  A
certified high-C3 cell contains the actual normal subgroup on the selected
retained action, the strict high inequality for that subgroup, the intrinsic
earlier-owner witness, and the precise branch property on the same action.
The older width/branch/action-class index remains a valid conditional union
bound, but branch-specific estimates use the aligned index.  In particular,
the degree-twelve prime-base subbranch now consumes the internal A4 top-map
theorem directly on its canonical physical family; no unmarked cell or
external top-map premise is used.  The remaining aligned numerical producers
are the ternary 3-group rows (degree-sensitive at 3, 9 and 27), the two
degree-six intrinsic owners, the binary-nine degree-twelve owner, and the
critical natural-A4 packet.
