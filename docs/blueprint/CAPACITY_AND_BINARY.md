# Common-source capacity, fusion and complete binary control

These mathematical interfaces state their prerequisite bounds and exact
counting scopes. See the [claim index](README.md).

## CNT-LIFT: a cocycle bound above one actual quotient map

Fix an extension 1->A->Q->B->1, with A elementary abelian of order p^a.
It need not split. For simple B-module types X in the ACTUAL socle of A, put

    r(A)=max_X m_X/d_X,  d_X=dim_(End_B X) X,  r(0)=0.

For every J<=S_b and every specified epimorphism beta:J->B, the number of
epimorphisms J->Q above beta is at most

    |A| |H^1(B,A)| p^((b/p)*r(A)).

If a lift exists, choosing one lift identifies the homomorphic lift set with
the cocycle torsor Z^1(J,A_beta). Write F=ker beta. Inflation-restriction and
|B^1|<=|A| reduce the bound to Hom(F,A)^J. Choose one actual Sylow-p subgroup
P of F. Its actual normalizer D=N_J(P) maps onto B by the Frattini argument.
Restriction injects this Hom space into Hom_D(P/Phi(P),A). Composition factors
and Schur endomorphism dimensions bound its dimension by
r(A) dim(P/Phi(P)). The published abelian p-quotient bound gives
dim(P/Phi(P))<=b/p.

There is no ceiling on r(A), no extra Aut(Q) factor, and no separate source
chosen for different simple types. Nonliftable quotient maps contribute zero.
The actual H2 obstruction and its restricted transgression conditions remain
attached before any positive enlargement.

For p=2 this yields e_Q(J)<=D 2^(lambda*b)e_B(J), where
D=|A||H1(B,A)| and lambda=r(A)/2. At fixed width D is a finite target
constant. At growing binary widths it requires a uniform entropy bound;
it cannot simply be called constant uniformly in width.

## CNT-GRAPH and CNT-FUSION: same-source moments and original weights

If a specified permutation group R of degree v covers B, tuples of epimorphisms
beta_i:J->B are encoded by the subgroup of R^ell x J defined by
pi(r_i)=beta_i(j). Projection recovers J and every literal map. This includes
repeated or dependent maps and proves

    sum_(J<=S_b) e_B(J)^ell <= s_(b+ell*v).

For c binary characters on the same J, include c disjoint two-point actions in
each graph block. Thus Phi(J)=e_B(J) 2^(c*d2(J)) has moment degree v+2c.
A proper joint image is retained; demanding independent target coordinates
would lose valid tuples. The shared-C3 graph fixture audits this exact point.

Consider a fixed finite menu of original width-w entries with envelope

    e_Q(J)<=D 2^(lambda*b) Phi(J),
    sum_J Phi(J)^ell <= s_(b+ell*v),
    g=w-v-8lambda>0.

Set a=v/8+g/16. Consume the union of ACTUAL hot entries Phi(J)>2^(a*b)
before pointing cold entries. For cold entries the original Gaussian ratio
and exact labelled weights give an exponent -g*b/16+O(log(n+2)), with target
the complete source count at degree b. For v>0 choose
ell=max(1,ceil(g*b/(2*v^2))). Writing e=g/16, the exact hot exponent is

    (b+ell*v)^2/16 - (ell-1)*a*b + lambda*b - (b+w)^2/16
      = -4e^2*b^2/v^2 - e*b - w^2/16
        + (v^2/16)*(ell-8e*b/v^2)^2.

The final square is bounded. The independent published coarse count supplies
the main quadratic exponent with a lower-order error, so the hot union is
quadratically negligible. Entries with v=0 use their direct estimate.

Fixed witness choices must be transported from original-normalizer orbits
before J is counted, or the full invariant finite menu must be paid. No
equivariant basis selector is assumed. All original normalizers, occurrence
factorials, later continuation and the single terminal are retained.

## CAP-SECTION: retained annihilator gives one simultaneous cut

Let T be faithful transitive of even degree s>=24 and A an actual section of
F2^s whose action factors through the specified B. Define

    S=A^B, t=dim S,
    L=ker[H1(B,S)->H1(B,A)], ell=dim L.

The connecting homomorphism identifies L with (A/S)^B. This is a module
annihilator on the original section; it does not replace the separate group
extension/transgression conditions in CNT-LIFT.

The coupled actual-section theorem is

    2 dim(M^T)+4 r_nontrivial(M) <=47s/48

for EVERY section M of the same permutation module. It does not require a
split trivial socle. Its proof uses induced-module bounds, normal-orbit
filtration for a simple constituent's kernel, the actual Schur field, and
the small faithful-image alternatives GL2(2), GL2(4).

When T is not a 2-group, two additional bounds hold on this same state:

    t<=floor(5s/16),       t+ell<=3s/8.

The first is derived from the precise published induced-module theorem and
the minimally transitive degree-3-times-a-power-of-two orbit statement.
The second uses the unipotent preimage of (A/S)^B and the actual O^2(T)-orbit
filtration. Odd order acting trivially on an arbitrary vector space does not
supply either physical permutation-module bound.

Write H1(B,S)=H1(B,F2) tensor S and row-reduce L. Its ell pivot coordinates
occupy at most ell S-blocks. The span Z of unoccupied blocks has dimension
at least max(t-ell,0), and L intersects H1(B,Z) trivially. Choose

    C<=Z, c=dim C=min(floor(t/2),max(t-ell,0)).

The exact annihilator sequence gives dim(A/C)^B=t-c. Apply the coupled theorem
to the ACTUAL quotient A/C, including any newly exposed nontrivial types.
Then

    2c+4r_nontrivial(A/C)<=47s/48,
    2c+4(t-c)<=max(3t+1,2(t+ell))<=47s/48.

Therefore one actual C simultaneously gives

    2dim C+4r(A/C)<=47s/48<s.

For an original pair action U of width 2s, take its actual pair kernel K and
ANY literal N normal U. The section is A=KN/N=K/(K intersect N), and
B=U/(KN). No containment N<=K or split quotient is required. Central lifting
through C, followed by CNT-LIFT, has moment degree s+2dim C and tail
r(A/C)/2, hence a strict original-width gap at least s/48.

This structural theorem is degree-uniform. Its selected-orbit
aggregation uses a fixed finite alphabet; a growing alphabet requires
its own entropy analysis. Acceptance of selected entries does not remove the
earlier consumer/exhaustion prerequisites listed in the global blueprint.

## BIN-LARGE: uniform large widths and the two finite boundaries

For binary T of degree s=2^a, every simple binary module is trivial. Put
B_a=binomial(a,floor(a/2)). The deterministic separator gives

    2dim C+4dim(A/C)^B <=2B_a+2B_(a-1).

It uses the SAME L<=H tensor S and the largest character slice
j0=max_(lambda!=0) dim(L intersect(lambda tensor S)). One can choose q
independent evaluations injective on L with

    q<=floor((ell+max(1,j0))/2).

The joint character-kernel bound t+j0<=2B_(a-1), together with t,ell<=B_a,
gives the claimed capacity, including its rounding case. For a>=6 the cost
is at most 15s/16. The top-degree-32 joint incidence argument improves the
boundary to cost at most 30=15*32/16. These are proofs on all actual sections,
not a census of sampled modules.

Consequently every original binary action of width w>=64 has a strict
central-prefix entry with gap at least w/32. Every invariant pair frame,
literal normal and certified cut is covered. The weighted full menu has
logarithmic cost O(w^2/sqrt(log w)): use the published soluble transitive
normal-generation bound, the actual Sylow ambient group, and the bound on
the number of central cuts. This supplies the uniform unbounded-width hot/cold
argument, with no arbitrary upper cutoff.

At original width 32, the actual top has degree 16. The separate adaptive
cover theorem gives a cover of the same B of degree v0 in {8,16} and a cut C
such that

    v0+2dim C+4r(A/C)<=30<32.

The degree-eight alternative concerns a regular E16 quotient represented by
four two-point actions. Its module remains a section of the original
sixteen-point permutation module; it is not replaced by an eight-point module.

The two bounds combine into one large-width kernel/scalar in the complete
binary recurrence. The earlier weaker cutoff estimates are not added again.

## BIN-MIX and BIN-TRANSPORT: the whole mixed family

The fixed base alphabet contains the four critical actions, regular C4 and
twelve specified degree-eight/sixteen carriers. For a profile with critical
rank R, a copies of C4 and carrier weight T, the physical half-degree is

    N=R+2a+4T,

and its exact profile coefficient is

    c_R/(8^a a!) * [z^T] exp((3/64)z+(65/688128)z^2).

The theorem covers every full-subdirect coupling, including nonsplit proper
relations and all critical lifts. A retained-factor comparison
|Sub_P(C4^a x Y)|<=|Sub_P(C2^(2a) x Y)| is valid when P depends only on the
projection to Y. It does not preserve arbitrary added marking weights.
Combine the joint carrier cross bound, the C4-heavy envelope and the original
small-support bridge on disjoint profile regions. Their support-sensitive
reserves, not only the final O(2^(-gamma*N)) statement, are prerequisites for
transport.

A replacement chart consists of actual epimorphisms alpha:U->Q=U/N and
beta:P->Q, where P is full subdirect on a word of base-alphabet actions of
the SAME physical degree. Require a fixed positive fraction delta of that
word to be noncritical. For a subgroup H on several old coordinates whose
literal axes are the specified N_i, set

    Hbar=alpha(H),   H=alpha^(-1)(Hbar),
    Hnew=beta^(-1)(Hbar).

The product of all embedded N_i lies in H. The equations therefore apply
simultaneously and preserve every outside relation. From Hnew recover Hbar
and then H; the actual proper subgroups P_i remain in the construction.
For fixed decorations this is injective. If b is the original noncritical
degree, the decoration fibre is at most (2N+2)^(K*b), and retained support
satisfies delta*C_old<=C_new<=C_old. The mixed-family profile reserves absorb
this factor after the original small-support strip is handled separately.

## FIN-MENU and BIN-SMALL: coverage is an independent theorem

For every relevant width-eight/sixteen action U and EVERY literal N normal U,
the finite boundary supplies one of:

1. A central-prefix certificate with actual cover and strict gap
   w-v0-2dim C-4r(A/C)>0.
2. A smaller faithful quotient cover.
3. A direct character certificate with an exponent strictly below w/8.
4. One of four literal replacement charts into the base alphabet, retaining
   at least 1/4 of the original degree as noncritical support.

Regular binary actions of degree at least eight have a generic central-
involution certificate. C4 is already part of the mixed base alphabet.
At the finite boundary, local map correctness, completeness of the normal
list and completeness of the action list are distinct mathematical claims;
a check of the first does not imply the other two.

On the complete small-width family, partition into any-hot, no-hot with an
accepted cold entry, and no-local-entry. The first is one negligible scalar;
the second is one forward kernel with shifts N-4 or N-8; the third is bounded
by simultaneous transport. This proves BIN-SMALL without summing duplicate
physical copies of the same source. Combine it with BIN-LARGE to obtain the
complete binary recurrence in [the assembly blueprint](COUNTING_AND_ASSEMBLY.md).
