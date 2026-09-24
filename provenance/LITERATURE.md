# Literature inputs and source boundaries

This reference describes external mathematical statements used by the
[proof blueprint](../docs/blueprint/README.md), with their hypotheses,
source locators and applications. Public preprints are distinguished from
journal articles. Logs are base two
unless explicitly indicated; d(G), d_G(N), c(G) and k(G) denote ordinary
generator number, normal-generator number, composition length and conjugacy
class number, respectively.

## Coarse counting, ranks and epimorphisms

**LIT-RDT — public preprint.** Colva M. Roney-Dougal and Gareth
Tracey, *Subgroups of symmetric groups: enumeration and asymptotic properties*,
[arXiv:2503.05416v1](https://arxiv.org/abs/2503.05416v1), 2025. Locators use
this version, not an unspecified later revision.

* Theorem 1, p.1: an absolute B satisfies
  s_n <= 2^(n^2/16+B n^(3/2)) for n>1. This is the independent coarse bound
  used in hot moments and small-support estimates; it does not assume the new
  sharp asymptotic.
* Theorem 2.8, p.6: for nonperfect G<=S_n, there exists a prime p dividing
  |G/G'| such that |G/G'|<=p^(n/p). In particular an actual permutation
  p-group P satisfies dim(P/Phi(P))<=floor(n/p). The general statement is
  existential in p, not a bound for every prime on the entire abelianization.
* Lemma 6.1, p.20: an absolute zeta bounds d_G(N) by
  zeta*n/sqrt(log n) when G<=S_n is soluble and transitive, n>1, and N is
  normal in G. The input controls normal generators. For a finite p-group
  G, the project uses d_G(G)=d(G) as a separate elementary consequence.
* Theorem 4.6, pp.12–13: for fixed p,k, let G,Q be finite p-groups and
  F normal in Q; write G<=R x P with G onto P. Assume Q, the direct factors
  of P, and the subdirect factors of R have order at most p^k. If d_N bounds
  d_G(H) for every G-normal H<=G' intersect ker(G->P), then

      |Epi(G,Q)| <= kappa_3 d(G)^kappa_4
                     |C_Q(F)|^d(G) |[F,Q]|^d_N,

  with constants depending only on p,k. The carrier application uses F=Q.
  This is an epimorphism count under these hypotheses, not an unrestricted
  conditional lifting theorem for any fixed quotient map.

Applications: CNT-LIFT, CNT-GRAPH, CNT-FUSION, BIN-LARGE, BIN-MIX and the
macro-A4/terminal estimates in ASM-OLD. The faithful degree is that of the
actual source permutation group.

The marked C4 moment and carrier estimates also use the following interfaces
from the same version. These are separate from the coarse subgroup count.

* **Tableau count:** Theorem 3.10 and its proof, p.9, with the consistent
  normal-subgroup tableaux and ordering of Lemma 3.6. For p-group factors
  G_i, |G_i|<=p^(n_i), put d_i=d_(G_i)(U_ii) and
  c_i=log_p|U_ii|/n_i. Under (3.1),
  c_i>=log_p|U_ji|/n_j for j<=i, the proof gives

      log_p |Subdir(U)| <= sum_(j<i) (c_i-c_j)n_j d_i.

  The marked argument retains this inequality before the independent
  maxima leading to Theorems 3.10/3.2's coarser conclusion.
* **Excessive factors:** Definition 5.1 and Proposition 5.3, pp.14,16.
  Excess means d_G(N)>n/4 for a normal subgroup N of a transitive 2-group
  G of degree n. It occurs only for n<=32, with excess at most 2; the
  proposition gives the normal-pair exceptions, and also the odd-prime
  n/(2p) and 2n/p^2 alternatives. These classification conclusions, not
  merely sample computations, enter the rank endpoints and marked C4 case.
* **Dependent factors:** Theorem 5.5, pp.17–18. For a full subdirect word
  with a maximal fully independent tail, let x and y be the degrees before
  and in that tail. For normal N the binary bounds are
  d_G(N)<=3x/8+y/2, improved to 5x/16+y/2 if no preceding factor has
  excess 2 and degree 8, and to x/4+y/2 if none has excess 2. If
  N<=G' intersect ker(tail), then d_G(N)<=x/4.
* **Nonabelian excessive quotients:** Theorem 5.7, pp.18–19. For such a
  quotient Q=G/N there is F normal in Q with
  log_2|[F,Q]|+e log_2|C_Q(F)|<=n/2 and log_2|C_Q(F)|<=n/4.
  Here e=3 for degree-8 excess 2 (log_2|C_Q(F)|=n/8), e=1 for
  excess 1, and e=5/4 for excess 2. The excess-1 branch requires
  d(Q)=d(G). This supplies the parameters for Theorem 4.6.

The reductions from bounded nilpotent words to permutation groups use
Lemma 2.7 (gridded Sylow actions and the maximal transitive nilpotent
container), Proposition 7.4 (bounded binary words), and the following
soluble encoding statements:

| Locator in LIT-RDT | Input retained in the reduction |
|---|---|
| Proposition 6.2, p.21 | Soluble G<=S_n whose nontrivial orbits have length at least m>=2 satisfies d(G)<=zeta*n/sqrt(log m). |
| Theorem 6.4, pp.21–22 | Subgroup- and quotient-closed property P; transitive containers of order <=2^(delta*n), in <=2^(gamma*n) conjugacy classes; and d(G)<=epsilon*n/delta when every nontrivial orbit has length at least C. A P-subgroup bound 2^(epsilon*n^2+f(n)) for words of containers of degrees <C, with f nonnegative and nondecreasing, gives 2^(epsilon*n^2+f(n)+n log n+gamma*n+4sqrt(n)) globally. |
| Theorem 7, p.3, proved using Theorem 8.4, p.32 | A finite soluble G is generated by a nilpotent subgroup and at most 4 sl(G)sqrt(ma(G)) elements; an arbitrary finite G needs at most one further element. The nilpotent subgroup is not asserted normal. Here sl is socle length and ma is the maximum prime-factor length of an abelian section. |
| Lemma 8.5 and Theorem 8.6, pp.33–34 | Soluble full subdirect products have socle length at most the maximum factor socle length; maximal transitive soluble containers have at most 2^(3(log n)^3+2log n) conjugacy classes, and soluble G<=S_n has order <=24^(n/3). |

In the marked C4 application the maps and marks must be counted through these
encodings on the same source group. The unmarked reduction alone is not a
marked-moment theorem.

**LIT-ORDER-COUNT — journal article.** Marco Fusari and Pablo Spiga,
*On the maximum number of subgroups of a finite group*, J. Algebra 635 (2023),
486–526. [DOI](https://doi.org/10.1016/j.jalgebra.2023.07.047);
[published open-access text](https://boa.unimib.it/retrieve/554c38e7-7b6d-4be6-8678-af1353d1454e/Fusari-2023-Journal%20of%20Algebra-VoR.pdf),
Theorem 1.1, p.487:

    |Sub(X)| < C_0 * 2^((log_2|X|)^2/4),   C_0 < 7.372,

for every finite group X. The regular-factor joint envelope and the complete
C4/carrier mixture apply this to the actual joint group. No permutation
degree or independent factor-by-factor subgroup bound is substituted.

**LIT-KP — journal article.** L. G. Kovács and C. E. Praeger,
*Finite permutation groups with large abelian quotients*, Pacific J. Math.
136 (1989), 283–292. [DOI](https://doi.org/10.2140/pjm.1989.136.283);
[primary scan](https://archives.maths.anu.edu.au/people/Kovacs/K070.pdf).
Use the unnumbered Theorem on p.283 and Corollary on p.284.

If a Sylow p-subgroup of G moves m_p points, the largest abelian p-quotient
has order at most p^(m_p/p). Equality forces the stated direct product of
the largest p'-constituent and transitive non-p' constituents. The latter
are C_p[p]; for p=2, C4[4], V4[4], D8[4], (D8 central-product D8)[8],
AGL(1,3) and AGL(1,5); and AGL(1,p+1) when p+1 is a power of two.
Bracketed degrees specify actions.

Applications: CRT-MODEL, the rank bounds in CNT-WEIGHT and odd critical seams.
The elementary-binary equality list, its normalizers and the odd singleton/S3
alternatives are project deductions, rather than literal assertions of the
cited theorem. Replacing this moved-support input by LIT-RDT's
existential-prime corollary loses needed information.

## Module and transitive generator bounds

**LIT-TRACEY-MODULE — journal article.** Gareth M. Tracey,
*Minimal generation of transitive permutation groups*, J. Algebra 509 (2018),
40–100. [DOI](https://doi.org/10.1016/j.jalgebra.2018.04.030);
[author manuscript](https://pure-oai.bham.ac.uk/ws/files/147250737/transgens1.pdf).
The following numbering and pages refer to that manuscript.

Theorem 1.6, p.3, with Definitions 1.4–1.5: if H<=G has index s, V is an
a-dimensional F[H]-module in characteristic p>0, and M<=Ind_H^G V, then
d_G(M)<=a E'(s,p). Use E'=E_sol when the actual coset-action image has a
soluble transitive subgroup and E'=E otherwise. Writing s_p for the p-part,
lpp for the largest prime-power divisor, and K(s)=sum_q v_q(s)(q-1),

    E(s,p) = min(floor(sqrt(2/pi)*s/sqrt((p-1)*log_p(s_p))),
                 s/lpp(s/s_p)),
    E_sol(s,p) = min(s*2^(-K(s))*binomial(K(s),floor(K(s)/2)), s_p).

The first branch is infinite when s_p=1; lpp(1)=1.

Corollary 3.12, p.17: if a transitive group of degree 3*2^m has no soluble
transitive subgroup, there are a Mersenne prime p=2^a-1, e>=1 and
t>=t_1>=0 with m=ea+t, and a soluble subgroup with binomial(e,j)*2^t_1
orbits of size 3*p^j*2^(t-t_1), for 0<=j<=e. The preceding nonabelian
PSL_2(p) construction is additionally needed to exclude p=3 and infer a>=3;
that strengthening is not stated in the corollary alone.

Two additional interfaces of the 2018 paper enter affine block-kernel fusion:

* Corollaries 4.26–4.27, pp.30–31, retain the unconditional induced-module
  bound and its soluble-coset-image improvement separately. In particular,
  if [G:H]=s>=2, dim V=a and M<=Ind_H^G V, Corollary 4.27(iii) implies
  d_G(M)<=ceil(4as/sqrt(log s)). No solubility assumption on G is needed
  for this weaker displayed bound.
* Lemma 5.8, pp.35–36, constructs the local-chief filtration for a large
  subgroup G<=R wr S, where S is transitive of degree s. Its series is
  (G intersect N_i^s), for a local normal series 1=N_0<...<N_e=R.
  Each local factor is elementary abelian or a nonabelian R-chief factor.
  An elementary abelian factor supplies a submodule of the corresponding
  induced module; a nonabelian factor supplies either zero or a G-chief
  factor. The series ends at the block kernel K=G intersect R^s.
  The printed final equality with G in the lemma's displayed series is
  inconsistent with its definitions; the construction and proof give K.

Theorem 1.1(1), p.1, also gives the uniform transitive generator bound
floor(c*n/sqrt(log n)), with c approximately 0.920581<1. It is sufficient
for the coarse affine-block estimate, but is distinct from the sharp
constant in the following input.

Applications: CAP-SECTION, APP-C1, BIN-LARGE and the relative ternary endpoints
in ASM-OLD. The numerical inequalities 5s/16, 3s/8 and the coupled
annihilator/socle bound are new project deductions, not imported theorems.

**LIT-TRACEY-SHARP — public preprint.** Gareth Tracey,
*Sharp upper bounds on the minimal number of elements required to generate
a transitive permutation group*,
[arXiv:2102.10070v1](https://arxiv.org/abs/2102.10070v1), 2021,
Theorem 1.1, p.1:

    d(G) <= floor(sqrt(3)*n/(2*sqrt(log_2 n)))

for transitive G<=S_n, n>=2. The finite relative-rank alphabet/tail uses this
constant. The 2018 theorem has exceptions to this sharper constant and cannot
silently substitute for it. The cited theorem itself uses degree-48
classification; importing it is distinct from proving that classification
with the project's finite checkers.

## Character bounds

**LIT-CLASSES — journal article.** Martino Garonzi and Attila Maróti,
*On the number of conjugacy classes of a permutation group*, J. Combin.
Theory A 133 (2015), 251–260.
[DOI](https://doi.org/10.1016/j.jcta.2015.02.007);
[author PDF](https://www.math.unipd.it/~mgaronzi/classes.pdf), Theorem 1.1,
p.1: k(J)<=5^((b-1)/3) for J<=S_b, b>=4. The project may use the weaker
uniform k(J)<=5^(b/3) after checking b=0,1,2,3 directly.

**LIT-NILPOTENT-CLASSES — journal article.** Attila Maróti,
*Bounding the number of conjugacy classes of a permutation group*,
J. Group Theory 8 (2005), 273–289.
[DOI](https://doi.org/10.1515/jgth.2005.8.3.273);
[author PDF](https://users.renyi.hu/~maroti/conj4.pdf), Theorem 1.5,
author p.2: k(P)<=(38/25)^b for nilpotent P<=S_b.

Applications: the character entries of NB-EXHAUST and FIN-MENU. The nilpotent
bound applies to an actual Sylow subgroup of a common preimage. An abstract
quotient does not acquire the same faithful permutation degree automatically.
The conjectural 5^(b/4) bound is not an input.

## Primitive and affine inputs

These inputs enter the primitive and affine arguments, including the first
c=1 application. The primitive results below include CFSG-dependent theorems.

| ID and primary reference | Exact interface and consumer |
|---|---|
| **LIT-PRIM-GEN**: D. F. Holt and C. M. Roney-Dougal, *Minimal and random generation of permutation and matrix groups*, J. Algebra 387 (2013), 195–214; [repository](https://research-repository.st-andrews.ac.uk/handle/10023/3823), [DOI](https://doi.org/10.1016/j.jalgebra.2013.03.035). | Theorem 1.1, p.1: a subnormal H in a primitive group of degree w has d(H)<=log_2 w, except w=3 and H isomorphic to S3. Used in APP-C1 and the primitive relative ternary endpoints. |
| **LIT-PRIM-LENGTH**: S. P. Glasby, C. E. Praeger, K. Rosa and G. Verret, *Bounding the composition length of primitive permutation groups and completely reducible linear groups*, J. London Math. Soc. 98 (2018), 557–572; [primary PDF](https://api.research-repository.uwa.edu.au/ws/portalfiles/portal/37122320/Glasby_et_al._2018_Bounding_the_composition.pdf), [DOI](https://doi.org/10.1112/jlms.12138). | Theorem 1.3, p.2: primitive G of degree w satisfies c(G)<=(8/3)log_2 w-4/3. Same applications; the finite exceptional actions are treated separately. |
| **LIT-PRIM-ORDER**: Attila Maróti, *On the orders of primitive groups*, J. Algebra 258 (2002), 631–640; [author PDF](https://users.renyi.hu/~maroti/primitive.pdf), [DOI](https://doi.org/10.1016/S0021-8693(02)00646-4). | Theorem 1.1, p.2; exact alternatives below. |
| **LIT-AFFINE-BASE**: Zoltán Halasi and Attila Maróti, *The minimal base size for a p-solvable linear group*, Proc. AMS 144 (2016), 3231–3242; [author PDF](https://zhalasi.web.elte.hu/papers/09.PSolvableBase.pdf), [DOI](https://doi.org/10.1090/proc/12974). | Theorem 1.1, p.2: a completely reducible p-solvable linear group over F_q has strong-base size <=2 for q>=5 and <=3 for q<=4. The inequality b(G)<=b*(G) gives the order bound used in the small soluble-affine argument. |

For a primitive group G of degree w, LIT-PRIM-ORDER gives at least one of:

1. A_m^r<=G<=S_m wr S_r in product action, with each S_m acting on
   k-element subsets of {1,...,m}, and w=binomial(m,k)^r;
2. M11, M12, M23 or M24 in its respective 4-transitive action;
3. |G|<=w product_(i=0)^(floor(log_2 w)-1)(w-2^i)
   <w^(1+floor(log_2 w)).

The semisimple-normal argument uses this actual permutation embedding.
For m>=5 the normal subgroup A_m^r and the quotient bound
|G/A_m^r|<=2^r r! follow from it; m<=4 is handled by the small-order
bound. An abstract alternating socle without the specified subset action
does not supply this conclusion.

## Transitive counting and finite classifications

**LIT-TRANSITIVE-COUNT.** A. Lucchini, F. Menegazzo and
M. Morigi, *Asymptotic results for transitive permutation groups*,
Bull. London Math. Soc. 32 (2000), 191–195.
[Publisher record](https://londmathsoc.onlinelibrary.wiley.com/doi/abs/10.1112/S0024609399006591).
LIT-RDT's introduction, p.2, attributes to this paper the bound

    #{G<=S_n : G is transitive} <= 2^(C n^2/sqrt(log n))

for an absolute C and n>=2. The displayed labelled-subgroup statement is
cited here through that explicit statement in Roney-Dougal–Tracey; the
publisher link supplies the original paper's bibliographic record. This is
the precise transitive-count input used in the argument: it concerns actual
subgroups. Its statement locator is RDT's introduction, p.2.

**LIT-TRANSITIVE-CATALOGUE.**
D. F. Holt and G. Royle, *A census of small transitive groups and
vertex-transitive graphs*, J. Symbolic Computation 101 (2020), 51–60.
[DOI](https://doi.org/10.1016/j.jsc.2019.06.006);
[author manuscript](https://arxiv.org/abs/1811.09015);
[institutional repository](https://wrap.warwick.ac.uk/id/eprint/119335/).
Sections 1–4 and Table 1 classify transitive groups of degree less than 48
up to symmetric-group conjugacy, using two independently coded computations.
This covers the first-layer module-bound slice

    {2,3,...,23,25,26,28,29,31,34,37},

containing 7,259 actions. It also covers degrees 2,4,8 used by the separate
all-normal checks. This slice enters the inherited first-layer relative-rank
theorem in ASM-OLD; finite classification is not confined to the exceptional
degree-16 chart. The universal induced-module capacity theorem has its own
analytic inputs described above.

For the original degree-16 classification, the source is
Alexander Hulpke, *Constructing transitive permutation groups*,
J. Symbolic Computation 39 (2005), 1–30, §12, Table 1 and §§12.1–12.2,
[DOI](https://doi.org/10.1016/j.jsc.2004.08.002);
[author manuscript](https://www.math.colostate.edu/~hulpke/paper/ctg.pdf).
The degree-16 list has 1954 conjugacy classes. The nonbinary small-degree
exhaustion uses this classification. Coverage of binary actions alone does
not imply coverage of the nonbinary actions. The
[official TransGrp release](https://www.math.colostate.edu/~hulpke/transgrp/)
includes its catalogue manual. Classification completeness and exhaustive
normal-subgroup enumeration are distinct claims.

**LIT-PRIMITIVE-CATALOGUES.**
The finite primitive endpoints use the following slices:

| Consumer | Required finite scope |
|---|---|
| Two-ninth ternary rank | Primitive degrees 2–37 for composition density (294 actions); primitive normal pairs in degrees 2–17; transitive degree-9/18 handoffs. |
| Relative ternary stability | The preceding primitive base, extra normal pairs in degrees 19,20,21, and the transitive degree-18 seam. |
| c=1 / three-twentieths theorem | Primitive normal pairs in degrees 2–33 (253 actions, 945 normal pairs); primitive composition density in degrees 2–44 (336 actions). Analytic tails begin at 34 and 45. |
| Nonaffine primitive compression | Primitive degrees 5–29, retaining nonaffine actions. |
| Small nonsoluble affine exception | Degrees 8,16,27. |

The primitive slices displayed here are contained in degrees at most 44. The
[official PrimGrp manual](https://gap-packages.github.io/primgrp/doc/chap1.html)
gives the classification provenance, including Sims and C. M. Roney-Dougal,
*The primitive permutation groups of degree less than 2500*, J. Algebra
292 (2005), 154–183,
[DOI](https://doi.org/10.1016/j.jalgebra.2005.04.017),
[institutional record](https://research-portal.st-andrews.ac.uk/en/publications/the-primitive-permutation-groups-of-degree-less-than-2500/).
The paper's publisher abstract and institutional record state its range as
degrees below 2500; the 2011 extension is a separate publication.

### Software representatives and classification scope

The computational interfaces use GAP 4.13.1 with these releases:

| Catalogue | Release and archive | SHA-256 of the official archive |
|---|---|---|
| PrimGrp | [3.4.4, 25 February 2023](https://github.com/gap-packages/primgrp/releases/download/v3.4.4/primgrp-3.4.4.tar.gz) | `9d6fde0fa4658100f662c364f77c9fd67b1699e9f3dbb60306ed357cc5837cff` |
| TransGrp | [3.6.5, 15 December 2023](https://www.math.colostate.edu/~hulpke/transgrp/transgrp3.6.5.tar.gz) | `6f2ec142a004f9d5e3b28bfa03246472fee93ceb12837206960bcb560eb72376` |

PrimGrp's interface identifies groups up to permutation isomorphism;
the integer position is stable in that sense, not a promise that literal
generators remain unchanged between releases. Its Sims-number and
GAP-to-Magma index tables provide the cross-catalogue identification where
used. The primitive slices above have, respectively, 113, 253, 294 and
336 representatives in degrees 2–17, 2–33, 2–37 and 2–44.

TransGrp's provenance assigns degrees 16–30 to Hulpke's classification,
degrees 34–46 to Holt–Royle, and prime degrees to the primitive lists;
the older small composite degrees have the sources listed in its manual.
The 7,259-action slice uses neither the separately distributed degree-32
catalogue nor a degree-48 extension. It includes 1,954 actions in degree
16, 983 in degree 18, 1,117 in degree 20 and 1,854 in degree 28.

For both catalogue inputs, mathematical classification, correspondence with
the supplied software representatives, exhaustive normal-subgroup enumeration
and the local inequalities are four distinct claims. Verifying one literal
chart does not establish completeness of a whole catalogue.

## Cohomological and group-theoretic lemmas

**LIT-SIMPLE-INDEX — public preprint version of a journal article.**
Adolfo Ballester-Bolinches, Ramón Esteban-Romero and Paz Jiménez-Seral,
*Maximal subgroups of small index of finite almost simple groups*,
[arXiv:2203.16976v2](https://arxiv.org/abs/2203.16976v2), 2022,
[DOI](https://doi.org/10.1007/s13398-022-01327-0).
Theorem A(4), p.4, gives l(S)^2 < |S| and
|Out(S)| <= 3 log_2 l(S) for a nonabelian finite simple group S,
where l(S) is its least proper subgroup index. The manuscript uses
these two inequalities in the core-free simple-power index lemma and
the faithful quotient compression of nonaffine primitive actions.
This is a classification-based input, with its actual hypotheses retained.

The cohomological layer needs exact lift torsors, inflation–restriction,
connecting maps and their restricted annihilators, coprime vanishing,
Künneth calculations, Schur–Zassenhaus, Frattini arguments and Schur-type
filtration bounds. These are separate ordinary mathematical lemmas with
their hypotheses. In particular the macro-A4 fixed-image identity comes
from coprime cohomology and a specified ternary kernel; it is not an
application of a general numerical H1 bound.

In particular, the chosen universal annihilator/capacity route does not take
the Guralnick–Hoffman faithful H1 bound or a separate prime-power-index
classification as an additional input. Classification used inside a cited
Tracey theorem remains part of that theorem's provenance.

The mathematical assumption boundary is described in
[ASSUMPTIONS](../ASSUMPTIONS.md).
