# Component interfaces for the global counting proof

This document states terminal, marker, packet and aggregation interfaces for
the [counting blueprint](COUNTING_AND_ASSEMBLY.md). Their hypotheses and
counting domains are part of each statement. These interfaces are not a
standalone proof of exhaustive consumer coverage. Finite coverage is treated in
[FINITE_CERTIFICATES.md](FINITE_CERTIFICATES.md), and published inputs in
[the literature register](../../provenance/LITERATURE.md). The
[dependency specification](../../provenance/claims.json) records the declared
mathematical input edges and their scopes; it is not a proof certificate.

All counts concern actual labelled subgroups. All logarithms are binary.
Use the exact normalization of [SPEC.md](../../SPEC.md):

    R=floor(n/2), epsilon=n mod 2,
    P(y)=y/2+y²/6+y⁴/384, c_j=[y^j]exp(P(y)),
    C_n=c_R+epsilon·c_(R-1)/6, L_n=n! C_n G_R,
    A_n=s_n/L_n,

with c_j=0 for j<0. Here G_j counts all subspaces of F₂^j. In particular,
the symbol L_n always denotes the exact coefficient benchmark in this file.
Write d_p(T)=dim_Fp T/(T'T^p), and let O²(T) be the smallest normal
subgroup with binary quotient. Gaussian coefficients {r choose j}_q
count j-dimensional subspaces of F_q^r. The fixed constants used below are

    phi=∏_{i>=1}(1-2^(-i)),
    rho₃=∏_{i>=1}(1-3^(-i))^(-1),
    kappa_*=max(kappa0,kappa1),

where kappa0,kappa1 are the theta constants in SPEC.md. These products
converge, with phi>0 and finite rho₃. In expressions such as
rho₃(c+1), juxtaposition means the product rho₃·(c+1).

## 1. Assembly interface and normalization

**ASM-COMPONENTS.** Let E_N count all fixed-point-free binary subgroups of
S_(2N) with at least one actual noncritical orbit, divided by (2N)!c_NG_N.
Let Ccrit_n be the normalized complete critical family, including its
noncanonical lifts. The intended
exhaustive master is

    A_n <= Ccrit_n + epsilon_sep(n) + epsilon_fwd(n)
              + Σ_{b<n}K(n,b)A_b
              + 1_{n even}E_(n/2)
              + Σ_{even m<n}H(n,m)E_(m/2).              (1.1)

The positive kernel K targets complete lower-degree subgroup counts.
The separate transfer H targets complete binary errors. They cannot be
combined and treated as one contractive row. The even E term includes
both the complete fixed carrier-cylinder subfamily and the remaining
marker-free binary subfamily, with coefficient one on their disjoint union.
It is valid forcing only after the independent theorem for complete E.

The required aggregate conclusions are

    epsilon_sep(n)=O(2^(-a n)),
    row(K)(n)=O(2^(-b n)), epsilon_fwd(n)=O(2^(-d n²))   (1.2)

for positive constants a,b,d. All unbounded support, action and parameter
sums must already be included in these complete bounds. Small individual
kernel entries are insufficient.

**ASM-CONVERSION.** Put

    Delta(n,b)=C_b G_floor(b/2)/(C_n G_floor(n/2)),
    a(U)=|N_{S_w}(U)| for an actual transitive U<=S_w.

An actual-orbit deletion against a complete complement J<=S_b, b=n-w,
with fibre envelope z_U(b), contributes

    K_U(n,b)=Delta(n,b) z_U(b)/a(U).                     (1.3)

The original placement n!/(b!a(U)) cancels the b! in s_b. There is no
extra b! inside Delta and no replacement of a(U) by |U| or |Aut U|.
Pointing sums are positive upper bounds and must be summed once over the
whole accepted union before splitting it by earlier domain restrictions.

If another expression uses a benchmark L'_k=lambda_k L_k, its exact
conversion is

    h_n/L'_n <= q(n,b)s_b/L'_b + e_n
    ==> h_n/L_n <= q(n,b)(lambda_n/lambda_b)A_b+lambda_n e_n.

For the theta approximation to G_R, 1<=lambda_k<=kappa_* uniformly.
An odd scalar proved against n!G_Rc_(R-1)/6 gains the exact factor
sigma_n=(c_(R-1)/6)/C_n<=1. Apply such conversions once.

**ASM-PARTITION.** All domains are predicates on complete subgroups,
including actual actions, quotient maps, markers, continuation and terminal.
Precedence residualizes them by set difference. Restricting a whole-cylinder
theorem by positivity repays its complete right side. Bounds on the same
owner are alternatives; they do not yield multiplicative independent savings.
The exhaustive partition and each restriction licence must accompany (1.1).

## 2. Exact terminal attachment

The critical action set is C2[2], regular V4[4], D8[4] and 2_+^(1+4)[8].
For a displayed critical product D, let K_D be the product of the centres
of its nonabelian factors and V=D/K_D=F₂^r. Let N_D(T) count subgroups
of D×T full on T and on every displayed critical factor.

**TERM-CONTRACT.** For every complete exterior projection T, image and
full preimage give a canonical bijection

    N_D(T)=N_D(T/O²(T)).                                (2.1)

Every common quotient with D is binary, so every such subgroup contains
1×O²(T). Internal exterior couplings must be assembled before contraction.

**TERM-WEIGHT.** If U is inserted as the m-th occurrence of its action
type, its exact counting-measure transition has multiplier 1/(a(U)m).
Induction by uniquely recovered coordinate projections gives the full
weight product_U 1/(a(U)^{m_U}m_U!). In a Goursat representation by two
onto maps to one abstract quotient Q there is one divisor |Aut Q|.

**TERM-ANN.** For a central extension 1→K→X→Y→1 with K elementary
binary and extension class ξ, put
Ann(ξ)={λ∈K*:λ_*(ξ)=0 in H²(Y,F₂)}. Then

    #{H<=X: H→Y onto}=Σ_{L<=Ann(ξ)}2^{d₂(Y)dim L}.       (2.2)

Indeed L is the annihilator of H∩K. Its splitting condition is exactly
L<=Ann(ξ), and the complement fibre is a torsor under Hom(Y,K/(H∩K)).
This applies to arbitrary nonabelian Y and retains the actual extension.

**TERM-RECORD.** For binary E let d=d₂(E). Let P_u consist of linear maps
p:F₂^u⊕E/Φ(E)→V injective on F₂^u and full on each displayed critical
quotient coordinate. Pull back the critical extension to C2^u×E and
call its class ξ_p. Then

    N_D(E)=Σ_{u=0}^r [|GL(u,2)|2^{ud}]^{-1}
                  Σ_{p∈P_u}Σ_{L<=Ann(ξ_p)}2^{(u+d)dim L}. (2.3)

The divisor counts a basis of the intersection with V and a lift of its
quotient graph. Fullness modulo each critical Frattini kernel implies
actual fullness. An equivalent translated-Hom chart may be used only after
proving its bijection with (2.3); it is not an additional fibre.

**TERM-BOUND.** For arbitrary finite T set

    d=d₂(T), tau=dim ker[H²(T/T'T²,F₂)→H²(T,F₂)],
    c=dim K_D, delta=r/2-c,
    X_r(d)=Σ_{j=0}^r {r choose j}_2 2^{dj}.

The required uniform ledger is

    N_D(T)<=phi^{-2}Σ_{j=0}^rΣ_{ell=0}^c
          {c choose ell}_2 72^ell 2^{tau ell}
          2^{(j-ell)(r-j+d)},                           (2.4)

and hence

    N_D(T)/X_r(d)<=2^{O(log(r+2))}
       [1+Σ_{ell>=1}2^{-ell(delta+d/2-tau-log₂72)-3ell²/4}]. (2.5)

The algebra behind this bound has four separate ingredients:

* Künneth splits a scalar quadratic lifting condition into its restriction
  on the binary intersection, its cross polarization and its pullback in
  the actual inflation kernel. The last condition cannot be replaced by
  vanishing of the quadratic form itself.
* Row reduction of an ell-dimensional annihilator fixes pivot critical
  factors. A fixed quadratic form has at most 72 surjective realizations
  in either nonsingular plus-type target of dimension two or four; each
  pivot has at most 72·2^tau possibilities and removes at least two free
  target dimensions.
* The exact record divisor is retained before Gaussian summation. When
  d>=r, the maximizing index is the constrained endpoint j=r; an interior
  completed square alone does not prove (2.5) there.

In particular tau=0 gives absolute C,k with

    N_D(T)<=C(r+2)^k X_r(d₂(T)).                         (2.6)

This zero-transgression consequence uses no permutation classification.
Separately, the permutation bound tau<=floor(b/2) for T<=S_b follows
from the five-term sequence and the abelian binary quotient bound.
The strengthened d₂(T)<=b/2-1 in even degree with a noncritical orbit
requires the corresponding equality classification.

Standard algebra needed here is extension classification, splitting under
coefficient quotients, five-term exactness, degree-two Künneth, elementary
binary H², Burnside's basis theorem and Gaussian formulas. The fixed
critical group and orthogonal calculations are finite algebraic inputs.
Specialized sparse-carrier bounds are not prerequisites for
the general ledger (2.4).

## 3. Marker transport and the pure-marker scalar

**MARK-TRANSPORT.** For X<=T×S3^g full on T and every marker, put
K_X=X∩C3^g, bar X=XC3^g/C3^g and L=bar X∩C2^g, ell=dim L. Then

    bar X≅T×L,
    X/O²(X)≅(T/O²(T))×C2^ell,
    d₂(X)=d₂(T)+ell, tau₂(X)=tau₂(T).                   (3.1)

Odd-kernel inflation and Künneth prove these statements. A choice of
linear complement proves the first isomorphism and is not counted.
If p_(T,g,ell) counts the actual X with that value of ell, the conditional
marker-and-terminal contribution is exactly

    [6^g g!f!]^{-1}Σ_ell p_(T,g,ell)
                            N_D((T/O²(T))×C2^ell).      (3.2)

For g=1 the coefficients are p_(T,1,1)=1 and
p_(T,1,0)=2^{d₂(T)}-1+|Epi(T,S3)|. The target epimorphisms cancel the
single diagonal Aut(S3); no additional division by six occurs inside
that graph fibre.

**MARK-PARTITION.** If SD(q,g) counts full subdirect subgroups of
C2^q×S3^g, then

    SD(q,g)<=3^gΣ_{Π partition [g]}G₂(q+|Π|)∏_{B∈Π}G₃(|B|),
    log₂SD(q,g)<=F(q,g)+O(g log(g+2)+1),
    F(q,g)=¼max{(q+g)²,q²+(log₂3)g²}.                   (3.3)

The error is independent of q. Equal marker sign characters determine
Π; semisimplicity counts invariant ternary kernels and coprime H¹
vanishing bounds literal coboundaries. This is a direct finite partition
argument, not a classification input.

**MARK-PURE.** For T=1 every marker subgroup has tau₂=0, so (2.6) applies.
The exact identity

    Σ_{H full<=S3^g}X_r(d₂(H))=Σ_{q=0}^r binom(r,q)SD(q,g)

recovers the supported subset of the r binary coordinates. Combining it
with (3.3) and original weights gives

    shape(g,f)/n! <= c_r/(6^g g!f!)
              ·2^{F(r,g)+O(g log(g+2)+log(N+2))}.

For n=2N+epsilon put D=(g+f-epsilon)/2 and r=N-D-g. Every admissible
D>=1 satisfies F(r,g)<=N²/4-(9/200)ND. Coefficient transfer and the
complete shape sum give

    pure noncanonical marker mass <=2^(-N/300)

relative to (2N)!c_NG_N or (2N+1)!c_(N-1)G_N/6, eventually. The latter
is converted by sigma_n. This includes every actual critical lift.
It does not bound arbitrary nonmarker prefixes; (3.2) is an identity,
not permission to extend this pure-marker estimate to general T.

## 4. Minimal macroscopic A4-packet interface

**PACK-SOURCE.** For finite J let F=J'J³, E=J/F=C3^r and
M=H₁(F;F₂). Write

    M≅1^f⊕⨁_h S_h^{a_h},

where nonzero E-characters modulo sign index two-dimensional binary
simples with endomorphism field F₄. For D<=E and its inverse image K,

    H₁(K;F₂)≅M_D≅1^f⊕⨁_{h:D<=ker h}S_bar(h)^{a_h}.     (4.1)

This equivariant isomorphism follows from odd-order homology vanishing.
Retained character types do not merge. For J<=S_b,
A=Σ_h a_h<=d₂(F)/2<=b/4 by the abelian quotient bound.

**PACK-FIBRE.** Fix L<=J×C3^t, onto J and coordinate-full on its ternary
image U. Let K=ker(L→U), A_L=H₁(K;F₂), V=(F₂²)^t and W<=_U V.
Put Q=V/W. Literal subgroups above this image and intersection correspond
to Z¹(L,Q), and

    H¹(L,Q)≅Hom_U(A_L,Q), Q^U=0,
    |Z¹(L,Q)|=|Q|·|Hom_U(A_L,Q)|.                       (4.2)

The image on coordinate i is full A4 precisely when p_i(W)=V_i or
p_i(W)=0 and the induced map A_L→Q→V_i is nonzero. Thus the exact fibre
is the sum of |Q| times the number of module maps satisfying those tests.
Distinct cocycles give distinct literal subgroups; coboundaries are counted.

**PACK-GAUSSIAN.** If m_h is a packet multiplicity and a_h the matching
source multiplicity, dropping only those fullness tests gives

    Fib_full(L)<=∏_hΣ_{x=0}^{m_h}{m_h choose x}_4 4^{(a_h+1)x},
    Σ_{x=0}^m{m choose x}_4 4^{(a+1)x}<=2^{2am+m²/2+4m}. (4.3)

The same Gaussian sum counts kernels, module maps and coboundaries. A
separate largest kernel count times a largest cohomology fibre is invalid.
Semisimplicity and the Gaussian product formula prove this specialization
directly; a general modular source-graph theorem is unnecessary here.

**PACK-DUAL.** Every image L is recovered by C_T<=(F₃^t)^* and a map
Γ:C_T→E*. Fullness requires Γ(e_i)≠0 whenever e_i∈C_T. If s coordinate
axes lie in C_T, put u=t-s and a=dim C_T-s. Source-eligible packet types
are exactly those s axes; eligible and ineligible types cannot coincide.
Their joint assignment is bounded by

    (2Σ_h4^{a_h})^s·3^{ra},
    Σ_h4^{a_h}<=(3^r-1)/2+4^A-1,

and the image subspace count by binom(t,s){u choose a}_3. There is no
extra quotient-automorphism factor in this literal graph chart.

**PACK-RANK.** If J has no actual regular C3 or natural A4 orbit, the
relative ternary rank theorem gives d₃(J)<=2b/9. This inequality, together
with A<=b/4, is sufficient for the packet argument; its equality cases
are needed elsewhere, not here. The primitive and induced-module inputs
and finite coverage for this rank theorem remain explicit dependencies.

**PACK-MACRO.** Let Z_(b,c,t) count all packet subgroups in
S_b×C3^c×A4^t, full on the displayed C3/A4 factors, whose residual J has
no actual regular C3 or natural A4 orbit. Uniformly for b,c>=0,t>=1,

    log₂Z_(b,c,t)<=n²/16-(43/450)t²
                   +O(b^(3/2)+t+log(c+2)), n=b+3c+4t. (4.4)

The dual sum first gives packet reserve delta0·t²,
delta0=(2-log₂3)/4. The same-source regular-triple moment
Σ_j{c choose j}_3 3^{j d₃(L)} spends less than t²/225. Finally sum once
over J using the independent coarse subgroup theorem
s_b<=2^{b²/16+O(b^(3/2))}. Apply exactly n!/(b!6^c c!24^t t!).
For t>=n/1000, the complete scalar is eventually at most

    2^(-43n²/(900·10^6)).                               (4.5)

The cohomology in (4.1)–(4.3) uses odd-order vanishing, not a faithful
irreducible H¹ dimension theorem. The substantive published inputs are
the abelian quotient bound, coarse subgroup bound and inputs to PACK-RANK.

## 5. Uniform support sums and complete forward rows

The aggregate in (1.1) is conditional on the exhaustive physical partition
and complete bounds (1.2). A collection of plausible local domains or
positive certificate gaps alone does not supply either hypothesis.

Two uniform support-summation implications used by scalar estimates are:

* If N=s+B, Z_(2B)=2^o(B²) and a support term is bounded by
  poly(N) Z_(2B)(2N)^B 2^(-sB/8-7B²/64), then its complete sum over
  1<=B<=N is 2^(-Omega(N)). Choose finite C0 with
  Z_(2B)<=C0·2^(7B²/128) for every B>=1 and use
  -sB/8-7B²/128<=-7BN/128; the remaining errors are uniformly o(BN).
* If N=s+5b/2 with nonzero even b and a support term has exponent
  -bs-(65/48)b²+O(b log N+b^(3/2)+log N), then its support sum is
  2^(-Omega(N)). Indeed b<=2N/5 gives a main exponent at most
  -(13/24)bN, with error uniformly o(bN).

For the terminal-trivial forward term, set

    I_s=Σ_{critical profiles gamma of quotient rank s}
                      W(gamma)|FS(gamma)|.

The critical-family estimate gives an absolute B_crit with
I_s<=B_crit c_sG_s for every s. B_crit is a constant, distinct from the
complete critical-family sequence Ccrit_n. A literal direct product of a nonempty
critical projection of rank N-B and an exterior projection of degree2B
has normalized upper-kernel coefficient

    B_crit c_(N-B)c_B G_(N-B)G_B/(c_NG_N), 1<=B<N.

The complete convolution row is O(2^(-N/8)); no boundedness of the exterior
normalized counts is assumed when bounding that row.

## 6. Same-source local entry interface

**FW-ENTRY.** Generic actual-orbit consumers use (1.3). For an actual
normal axis N normal U, put Q=U/N. A graph entry retains one complete
source J and supplies

    |Epi(J,Q)|<=D·2^{lambda b}Phi(J),
    Σ_{J<=S_b}Phi(J)^ell<=s_(b+ell v),
    g=w-v-8lambda>0.                                   (6.1)

The actual hot event is Phi(J)>2^{(v/8+g/16)b}. The entire any-hot
union is consumed first. On its complement, the cold kernel summand is
Delta(n,b)D·2^{(w/8-g/16)b}/a(U). Its exponent is
-gb/16+O(log(n+2)) for a fixed menu. Direct character entries use their
strict coefficient below w/8 and no hot moment. A quotient-replacement
graph may instead target m=b+v<n, with exact coefficient
m!C_mG_floor(m/2)/(b!a(U)C_nG_floor(n/2)).

## 7. The exact typed binary-error transfer

**MARK-BINARY-HANDOFF.** The same-family character moment satisfies

    pE_j<=[7+(6j)^(1/4)]E_j+r_jE_(j-1),
    r_j=(j-1)/4·(c_(j-1)/c_j)(G_(j-1)/G_j), j>=2.

It concerns complete E because pair fusion and duplicate-pair collapse
preserve a noncritical orbit but need not preserve prior domain exclusions.
Set E_0=pE_0=r_0=r_1=0. For n=2j+epsilon put

    Codd_j=c_j+c_(j-1)/6,
    alpha_j=c_j/Codd_j, beta_j=c_j/(3Codd_j),
    u_j=alpha_j+beta_j[7+(6j)^(1/4)], v_j=beta_jr_j,
    H(n,m)=K_mark(n,m)
       +1_{n odd}[u_j1_{m=n-1}+v_j1_{m=n-3}].            (7.1)

Negative targets are omitted. The complete noncanonical marker row
obeys row(K_mark)<=2^(-j/10) eventually. Also u_j→1 and v_j→0.
Thus H has bounded row and finite-target escape, but its odd row tends
to one. Once E_j=O(2^(-a_E j)) is independently established, both shifted
targets and the small marker row contribute exponentially small error.
No convergence rate for u_j is needed.

## 8. Trivial sections in an even nonbinary transitive action

**PAIR-TRIVIAL-SECTION.** Let T<=S_s be faithful and transitive, with
s>=4 even and T not a 2-group. If D<=C<=F₂^s are T-submodules and
T acts trivially on C/D, then

    dim(C/D)<=s/2-1.                                    (8.1)

This statement concerns sections of the actual permutation module;
it does not require a faithful action on the section. Its only
nonelementary input is the soluble-transitive induced-module bound in
[LIT-TRACEY-MODULE](../../provenance/LITERATURE.md#module-and-transitive-generator-bounds).

If an odd prime p divides s, a Sylow p-subgroup P has every orbit of
size at least p: a point stabilizer has strictly smaller p-part than T.
Taking P-invariants is exact in characteristic two. Therefore

    dim(C/D)<=dim(F₂^s)^P=number of P-orbits<=s/p<=s/2-1.

If s=2^a with a>=3, an actual Sylow 2-subgroup P is transitive. Indeed,
for every point x, |P_x|<=|T_x|₂=|P|/s, forcing |x^P|>=s.
The soluble-transitive module bound gives

    dim(C/D)<=binomial(a,floor(a/2))<=3s/8<=s/2-1.

The middle inequality follows from the nonincreasing central-binomial
proportion, whose value for a=3 is 3/8. Finally, suppose s=4.
The nonbinary subgroup T contains an element of order three, acting with
one fixed point x. Its cyclic subgroup P has a two-dimensional fixed
space on F₂^4. If dim(C/D)=2, exactness gives C^P=(F₂^4)^P and D^P=0.
Thus C contains the basis vector at x. Transitivity implies C=F₂^4,
whose largest trivial quotient has dimension one, a contradiction.
This proves (8.1).

For a central pair quotient with this section dimension t, (8.1) gives
an actual effective cover degree v_eff=s+2t<=2s-2. The retained quotient
map, extension class and graph-lift torsor still supply the counting
record; the numerical gap alone is not a replacement for that record.
No classification of simple groups having a subgroup of prime-power
index is needed for this lemma.
