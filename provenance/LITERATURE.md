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

The binary module-generator bounds and the general affine counting
capacities continue to use this literature input. The latter require bounds
on module generators of arbitrary submodules (including dual modules) and
asymptotic square-root decay. The ternary relative-head argument below does
not replace those stronger applications.

**Project ternary head replacement.** The ordered-transversal lemma in
`paper/sections/relative_ranks.tex` proves the needed head bound directly for
the original arbitrary fibre over every finite p-group and every subgroup
H, including nonnormal H. An actual chain from H to P with consecutive
normal index-p steps gives right-coset words. Reverse-lexicographic transport
moves every lower row below the target row. In Mathlib's coinduced convention,
q=T(b)^(-1)T(c) acts as q^(-1) to move row b to c, with the leading fibre
vector unchanged and all lower original H-twists retained. Minimizing the
sum of leading heights over lifts of all bases of the intrinsic coinvariants
of the actual submodule yields antichains in dim(V) disjoint copies of the
p-grid. This proof concerns invariant linear forms; it does not infer an
unconditional generator bound over an arbitrary ambient group from its head.

For p=3 the explicit seven-chain partition of the three-cube gives local
coefficients W(0)=W(1)=1, W(2)=3, and W(j)=7*3^(j-3) for j>=3. If s_3=3^t,
actual Sylow-3/Mackey orbit indices are 3^j with j>=t and sum s. The original
coordinate-kernel filtration therefore gives a*C(s), where C(s)=s for t=0,
s/3 for t=1,2, and 7s/27 for t>=3. Mixed orbit sizes are included.
The coprime branch needs no additional published bound: Maschke extends
submodule maps to the trivial line, Frobenius reciprocity bounds each actual
orbit contribution by the original fibre dimension, and Sylow orbit sizes
give at most s/s_q contributions. With lpp(1)=1, the resulting integer bound
is a*B(s), B(s)=min(C(s),s/lpp(s/s_3)). All local coefficients are integers
before scaling by dim(V).

This B-envelope supplies the relative ternary recurrence, stability and
three-twentieths classification. It is established independently of E(s,3);
no inequality B(s)<=E(s,3) is claimed. The old Gaussian prime-power interface
`TraceyPrimePowerModuleInput` still records the final assertion of Theorem
4.13, printed p.23, taking H1=H. Its original conclusion is stronger than
this replacement at large ternary valuations, and existing conditional Lean
modules using that interface remain conditional until their statements are
explicitly migrated to B. The new self-contained manuscript proof must not
be mistaken for a completed kernel check of its full formalization.

The ordered-transversal argument is related to Lemma 4.15 and Remark 4.17
(printed p.24) and Proposition 4.18 (pp.24–25), but their conclusions are
not imported as premises of this project proof. Neither the Gaussian estimate
nor the soluble mixed-prime chain-width refinement is needed for these
relative ternary endpoints. The complete primitive and small transitive
catalogues remain separate classification inputs. In particular all
normal pairs in degrees 6,12,18 are retained (1,300 actions, 20,410 pairs),
and the degree-18 no-high-pair result gives head at most two. The 91 actual
nonsoluble degree-18 semiregular witnesses remain in use in the separate
bounded symmetric-three counting argument, which requires module-generator
capacities; their use is not removed by the relative-head simplification.

Corollary 3.12, p.17: if a transitive group of degree 3*2^m has no soluble
transitive subgroup, there are a Mersenne prime p=2^a-1, e>=1 and
t>=t_1>=0 with m=ea+t, and a soluble subgroup with binomial(e,j)*2^t_1
orbits of size 3*p^j*2^(t-t_1), for 0<=j<=e. The preceding nonabelian
PSL_2(p) construction is additionally needed to exclude p=3 and infer a>=3;
that strengthening is not stated in the corollary alone.

Further interfaces and the local-chief construction:

* Corollaries 4.26–4.27, pp.30–31, retain the unconditional induced-module
  bound and its soluble-coset-image improvement separately. In particular,
  if [G:H]=s>=2, dim V=a and M<=Ind_H^G V, Corollary 4.27(iii) implies
  d_G(M)<=ceil(4as/sqrt(log s)). No solubility assumption on G is needed
  for this weaker displayed bound.

The local-chief filtration used for the relative ternary recurrence is now
proved directly in the project. `NormalChiefSeries` constructs an actual
normal chief series; the `LocalChief` modules form the intersections under
all original conjugate evaluations. Nonabelian layers retain their proper
subdirect correlations: actual ambient-normal coordinate images are zero
or full, then jointly faithful simple perfect quotients prove perfectness.
`RelativeSecondIsomorphism` keeps the original ambient action on the top
section. Lemma5.8, pp.35–36, gives a related wreath-product construction,
but is not an external premise for this project recurrence. Identification
of the sum of ternary chief weights with the manuscript's composition
multiplicity is a separate formalization obligation. The affine full-fibre
argument cites the related local-chief construction separately; the head
recurrence alone does not formalize that complete counting argument.

Theorem 1.1(1), p.1, also gives the uniform transitive generator bound
floor(c*n/sqrt(log n)), with c approximately 0.920581<1. It is sufficient
for the coarse affine-block estimate, but is distinct from the sharp
constant in the following input.

Applications: CAP-SECTION, the affine module-generator counting bounds in
APP-C1, and BIN-LARGE. The relative ternary head endpoints now use the
self-proved B-envelope described above; older Gaussian formal interfaces
retain their visible literature hypothesis. The numerical inequalities
5s/16, 3s/8 and the coupled annihilator/socle bound are new project deductions,
not imported theorems.

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

The formal `NilpotentConjugacyClassInput` states this bound for the actual
permutation subgroup. `BinaryCharacterEnvelope` proves the passage to
arbitrary original sources J<=S_b: maps to a binary target are determined
by their restriction to an actual Sylow subgroup, proved using the joint
image of two maps. The faithful irreducible tuple is constructed from the
target's actual central involutions; its existence is not an external input.

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
The formal outer-factor endpoint uses the following direct corollary of
LIT-PRIM-GEN.  A finite centerless simple group with a faithful permutation
action of degree `w` has a generating set of size at most `floor(log_2 w)`:
choose a nontrivial orbit, enlarge a point stabilizer to a maximal subgroup,
and apply Theorem 1.1 to the resulting faithful primitive action.  Its sole
exception is `S_3`, which is not simple.  The Lean theorem
`semisimpleOuterFactorPermutationBound_of_primitiveGenerator` then proves the
complete outer-factor product bound; that product bound is not retained as an
independent literature assumption.
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
| Two-ninth ternary rank | Primitive normal pairs through degree 33 (253 actions, 945 pairs) and primitive composition density through degree 44 (336 actions); complete transitive degree-9 normal-pair handoff. |
| Relative ternary stability | The same primitive base and complete transitive degree-9 normal pairs; the B-envelope handles every imprimitive index without an additional degree-18 stability seam. |
| c=1 / three-twentieths theorem | The same primitive slices, with tails beginning at 34 and 45; complete normal pairs in transitive degrees 6,12,18 (1,300 actions, 20,410 pairs) and the degree-9 equality list. No separate degree-54/162 transitive census or nonsoluble rank seam is required. |
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

For the affine rows below degree 1000, the direct source is C. M.
Roney-Dougal and W. R. Unger, *The affine primitive permutation groups of
degree less than 1000*, J. Symbolic Comput. 35 (2003), 421--439,
[DOI](https://doi.org/10.1016/S0747-7171(03)00031-2),
[institutional record](https://research-portal.st-andrews.ac.uk/en/publications/the-affine-primitive-permutation-groups-of-degree-less-than-1000/).
The present proof uses the following literal PrimGrp 3.4.4 affine slices:

- degree 8, rows 1--3, with complement orders `7,21,168`; the sole
  nonsoluble complement is `GL(3,2)`, hence has no abelian composition
  factor;
- degree 16, rows 1--20, with nonsoluble rows 11--20; their complement
  descriptions in `gps1.g.gz` give at most two abelian composition factors;
- degree 25, affine rows 1--22; the soluble rows use the scalar kernel in
  `GL(2,5)` and the soluble projective subgroup of `PGL(2,5) = S5`, while
  the three nonsoluble rows have at most three abelian composition factors;
- degree 27, affine rows 1--11.  The soluble complement orders in rows 1--9
  are exactly `12,13,24,24,24,26,39,48,78`; rows 10 and 11 have complements
  `SL(3,3)` and `GL(3,3)` and therefore zero and one abelian composition
  factors, respectively.

These are finite consequences of the cited published classification and
pinned software representatives.  Lean separately checks every numerical
maximum and transports the statements only after receiving the primitive
action hypothesis.

The degree-nine slice has eleven rows, of orders
`36, 72, 72, 72, 144, 216, 432, 504, 1512, 181440, 362880`; the last two are
the natural `A9` and `S9` actions.  The formal interface
`PublishedPrimitiveDegreeNineClassification` records exactly this published
slice.  `primitiveTernaryChiefWeightBound_of_published` checks the ternary
order valuations of the first nine rows and uses symbolic chief series for
`A9` and `S9`.  Thus `PrimitiveTernaryChiefWeightBound` is derived from the
already stronger three-tenths weight bound plus this published classification
slice, rather than retained as an independent research assumption.

The bounded three-tenths theorem itself is now formalized by
`PrimitiveTernaryThreeTenthsPublished`. Five generated Lean receipts cover
all 336 PrimGrp rows in degrees 2--44. Of these, 256 rows satisfy the stronger
kernel-checked order-valuation test directly. The remaining 80 catalogue rows
are the natural alternating and symmetric rows in degrees 5--44; symbolic
chains `1 < A_n` and `1 < A_n < S_n` prove zero ternary weight for every
chosen chief series. In the actual theorem range the order-valuation failures
are exactly the 72 natural rows outside the excluded degree nine. Thus the
committed GAP composition chains remain an independent replay check, but are
not a premise of the Lean proof. The only bounded external input is the
published primitive-catalogue correspondence, exposing the exact group order
or the natural `A_n`/`S_n` identification of the matched row; all ternary
inequalities are proved in Lean.

`PublishedPrimitiveSocleDichotomyInput` records the standard O'Nan--Scott
affine/nonaffine alternative at exactly the two primitive-action scopes used
by the proof (the original action and an actual minimal-block component).
`PublishedBoundedPrimitiveCatalogueCorrespondence` records only the
permutation-isomorphism locator in the degree-5--29 Roney-Dougal/PrimGrp
slice together with the exact order of the literal action and its actual
socle.  The four generated receipts store those two orders, their exact
factorization, and `2 * outerOrder <= degree` on all 116 retained rows.  Lean
proves that a profile needing this lookup has degree below 30 and derives the
socle-quotient order from Lagrange's theorem; that equality is no longer part
of the published catalogue premise.  Hence
`preE7PrimitiveCatalogueClassificationInput_of_published` derives the former
monolithic `PreE7PrimitiveCatalogueClassificationInput`; no project-owned
numerical or counting assertion is included in the published classification
premise.

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
