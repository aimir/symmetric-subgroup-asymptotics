# Primitive and relative-rank certificate schema

Version 1 is a gzip-compressed JSONL sequence: one header, action records and
one footer. It serves the exact finite inputs in the
[literature register](../../provenance/LITERATURE.md) and
[dependency specification](../../provenance/claims.json). It is a finite
certificate relative to the stated transitive and primitive classifications.

The [driver](../../computations/gap/primitive_rank.py) separates production from
replay. Both operate only on the release and pinned GAP packages. JSON is parsed
as data; the driver accepts only typed literals when forming GAP input.

## Scope and conventions

Permutations are one-based image lists of the declared degree, with GAP's
right-action convention. Generator-image lists use the original source
`generators` order. A trivial subgroup has an explicit identity generator.
Normals remain literal subgroups of their original action; equal abstract
quotients do not merge their records.

The exact classification slices are:

* TransGrp: degrees `{2,…,23,25,26,28,29,31,34,37}`.
* PrimGrp: degrees 2–44 and 54.

The header fixes GAP 4.13.1, TransGrp 3.6.5 and PrimGrp 3.4.4. An action's
`catalogue`, `degree` and `index` are coverage locators. The checker reconstructs
the supplied permutations and checks literal equality to that pinned
representative. It checks the complete set of locators, not merely its length.
The published classification premise establishes that these representatives
exhaust the relevant conjugacy classes. This checker does not independently
prove those classifications.

The two catalogue slices are combined in one package; a primitive row can also
represent a transitive action used by a different theorem. Such overlap does
not create new physical cases or additive counting terms.

## Action and rank records

Every action has its literal generators and exact group order. Transitive
records include the whole binary head rank. Their `normal_scope` is `all` at
degrees 6,9,12,18; `transitive` at degrees 2,4,8; and `none` otherwise.
Primitive records have `all` through degree 33 and `none` afterwards.

Each normal record supplies its literal generators, order, prime and relative
rank. The producer computes this rank from the abelian invariants of
N/[N,G]. The checker instead constructs `[N,G]N^p` from commutators and
p-th powers of generators, verifies ambient normality and the elementary
quotient, then computes its dimension. It checks the full prescribed normal
list against a fresh GAP `NormalSubgroups` computation and rejects omitted,
repeated, nonnormal or altered records.

The normal-list completeness boundary therefore includes the documented GAP
normal-subgroup algorithm. This package does not claim the catalogue-independent
central-involution normal-closure verification supplied by the binary package.

Primitive composition data are literal subgroup chains. The checker requires
endpoints G and 1, normal containment at every step, simple nontrivial quotients
and the exact factor-order product. The number of order-three factors is a
composition multiplicity, not the 3-adic valuation of |G|.

## Additional actual witnesses

* **Earlier c=1 acceptance:** eleven degree-6/12 actions carry an actual
  odd-index-two, cyclic binary module, prime-base, or V4-block witness.
  Cyclic modules have a literal normal base, elementary ternary complement and
  one vector whose complement orbit generates the base. Prime-base records
  retain the actual blocks, top map and top-module witness. V4-block records
  retain the proper base, complement and actual nine-vector action. These are
  sufficient earlier predicates; the package does not claim they select the
  earliest consumer in an ownership order. The conditional V4-block application
  still requires exactly one actual C3 orbit and no actual natural A4 orbit.
* **Degree-18 nonsoluble tops:** each carries a literal order-three permutation
  moving all eighteen points. Membership and semiregularity are checked.
* **Nonaffine primitive compression:** degree-5–29 records retain the actual
  socle. For a simple nonabelian socle S, an actual regular quotient map has
  kernel S and degree |G:S|, with 2|G:S|≤degree(G). Four nonsimple-socle cases
  retain their branch; their separate analytic argument remains necessary.
* **Small nonsoluble affine actions:** at degrees 8,16,27 the actual elementary
  regular socle, point stabilizer and its literal composition series are
  retained. The checker verifies the exact abelian factor constraints and
  conservative rational margin using log₂(3)/3<17/32. The cocycle and
  full-fibre theorem remain mathematical inputs.

## Conclusions checked

The finite inequalities include the four critical binary exceptions; primitive
relative 3/20 and composition 3/10 exceptions; the two-ninth equalities at
actual degree 9 and their absence at degree 18; relative one-third stability
on the supplied transitive seams; actual acceptance of every high c=1 pair;
and the nonsoluble degree-18 relative head bound.

The final checker also checks the smaller primitive composition conditions used
by the degree-54/162 argument. It does not enumerate transitive degree-54 or
162 groups. Primitive degree-54 normal rows are omitted because their earlier
use was calibration; the proof uses the analytic primitive normal-generator
bound there.

A complete replay ends with `PASS PRIMITIVE RANK VERIFY` and rejects mismatched
counts, missing catalogue locators and malformed chains or maps. Successful
checking establishes these finite premises relative to the stated GAP and
classification boundary. It is not a Lean proof or a proof of the global
subgroup asymptotic.
