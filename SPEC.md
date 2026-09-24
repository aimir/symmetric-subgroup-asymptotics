# Mathematical statements and notation

This document specifies the counting theorem, analytic corollaries and reusable
mathematical interfaces. The accompanying [blueprint](docs/blueprint/README.md)
describes their dependencies; the statements here are not self-contained proofs.

## 1. Objects and exact normalization

Let s_n be the number of actual subgroups of the symmetric group on a fixed
labelled n-element set. This counts subgroups, not conjugacy classes, abstract
isomorphism types, or only transitive subgroups.

Put R = floor(n/2), epsilon = n mod 2, and

    P(y) = y/2 + y^2/6 + y^4/384,
    G_R = sum_(k=0)^R product_(i=0)^(k-1) (2^R - 2^i)/(2^k - 2^i),
    L_n = n! G_R [y^R] (1+y/6)^epsilon exp(P(y)).

The finite sum defining G_R is evaluated in the rationals, with the empty
product at k=0 equal to one. Every denominator is positive because i<k;
subtraction and division here are rational operations. In particular G_0=1.
A separate counting theorem identifies this expression with the number of
all vector subspaces of F_2^R. That identity is a required proof bridge, not
the definition of the factor in L_n or Q_n.

All exponential functions written exp or e use base e. Powers of 2 are literal
powers of 2. All factorials and occurrence multiplicities are retained.
The coefficient c_R has the finite rational expression

    c_R = sum_(a+2b+4d=R) 1/(2^a a! 6^b b! 384^d d!).

Then the coefficient in L_n is c_R when epsilon=0, and
c_R + c_(R-1)/6 when epsilon=1, with the second summand zero at R=0.
This agrees with the displayed generating function and gives L_n>0. The
coefficient recurrence is

    R c_R = c_(R-1)/2 + c_(R-2)/3 + c_(R-4)/96

for R>=1, with negative indices contributing zero. These definitions avoid
requiring an analytic exponential merely to state the main counting theorem.

## 2. Primary theorem T1: exponential relative accuracy

The principal counting statement is:

    There exist real c>0 and C>0 and a natural N0 such that, for every
    natural n>=N0,

        abs(s_n/L_n - 1) <= C * 2^(-c*n).

Here s_n and L_n are coerced to real numbers. The SAME constants must work for
both parities. There is no hypothesis that n is even, that a residual profile is
generic, or that a subgroup is split, binary, soluble or transitive. There is no
assumption that one of the normalized subgroup-counting sequences is bounded.

This statement specifies neither an optimized numerical c nor an effective
N0, and does not assert an error O(2^(-c*n^2)).

## 3. Analytic corollaries T2 and T3

For R>0 let rho be the unique positive solution of

    R = rho/2 + rho^2/3 + rho^4/96,
    b(rho) = rho/2 + 2rho^2/3 + rho^4/24.

T2 gives the exact-saddle approximation

    Q_n = n! G_R (1+rho/6)^epsilon exp(P(rho))
          / (rho^R sqrt(2*pi*b(rho))),
    abs(s_n/Q_n - 1) <= C/n                  (n>=N0)

for suitable fixed C,N0. The saddle statement for L_n is independent of
the group-counting theorem; its transfer to s_n uses T1.
The symbol Q_n denotes only this saddle benchmark. The manuscript's A_n
continues to mean the normalized count s_n/L_n.

For the fully elementary expression, put

    phi = product_(k>=1) (1-2^(-k)),
    kappa0 = phi^(-1) sum_(j in Z) 2^(-j^2),
    kappa1 = phi^(-1) sum_(j in Z) 2^(-j*(j-1)),

    C0 = exp(-4/3) kappa0 / 2^(1/2),
    C2 = exp(-4/3) kappa1 / 2^(3/4),
    C1 = exp(-4/3) kappa0 48^(3/8) / (6*2^(7/16)),
    C3 = exp(-4/3) kappa1 48^(3/8) / (6*2^(11/16)).

These products and sums converge to positive constants. For j=n mod 4 define

    M_n = Cj n^(3*epsilon/8) 2^(n^2/16)
          * (n^7/(48*2^epsilon*e^7))^(n/8)
          * exp(2*sqrt(n/3) + (48*n)^(1/4)/2).

T3 is the precise bound

    abs(s_n/M_n - 1 - (6*epsilon-4)/(48*n)^(1/4))
        <= C*n^(-1/2)                       (n>=N0).

Thus the uncorrected M_n has relative error O(n^(-1/4)); retaining the
displayed correction improves this to O(n^(-1/2)). Neither algebraic error is
the exponential error of T1. Decimal evaluations of Cj are illustrations,
not definitions or necessary inputs to the theorem.

## 4. Reusable mathematical interfaces

T4 is the retained-annihilator capacity and original-weight fusion package.
Its structural statement is:
for any faithful transitive non-2 group T of even degree s>=24, any actual
section A=K/D of its binary permutation module, and a specified quotient B of
T through which the T-action on A factors, there exists an actual central
submodule C<=A^B with

    2 dim(C) + 4 r(A/C) <= 47*s/48,

where r(M)=max_X m_X(M)/dim_(End_B X)(X), with actual simple socle
multiplicities and r(0)=0. The invariant annihilator used to construct C and
the quotient A/C belong to the same original section.

The companion counting theorem retains concrete same-prime columns,
restricted transgression annihilators, full quotient and
extension maps, original action normalizers and occurrence factorials, later
continuation, and a single terminal attachment. Its complete aggregate must be
negligible or give a positive forward recurrence of the appropriate typed form.
Rows multiplying COMPLETE normalized counts must tend to zero, and the rows
and scalars used for T1 must have proved exponential bounds. A fixed row norm
below one alone does not preserve the main-term constant. The separately typed
H_E interface can have a bounded, nonvanishing row because its targets are the
already controlled binary ERROR sequence, not complete counts; its shifted
targets and marking row must still give the exponential bound needed for T1.
The universal structural inequality alone is not the whole counting theorem.
Its fixed-alphabet aggregation scope must not be silently promoted to a
uniform theorem for arbitrary growing menus.

The first application is the high-incidence split c=1 case, retaining the
exact surviving-character moment, shared-C3 double moment and the
inverse-complement chart when applicable. Their compatibility with the
general theorem is part of its mathematical scope.
The specialization may be an earlier-owner-or-capacity result for the complete
fusion package, rather than a direct application of the isolated inequality.
They do not provide a second copy of an already consumed reserve.

T5 is the complete binary noncritical bound. Define E_N as the number of
fixed-point-free 2-subgroups of S_(2N) with at least one actual orbit outside
the four specified critical actions C2[2], V4_regular[4], D8[4] and the
degree-eight extraspecial plus-type action 2_+^(1+4)[8], divided by
(2N)! c_N G_N. T5 asserts that there exist a,C>0 and N0 such that

    E_N <= C*2^(-a*N) for all N>=N0.

This includes unbounded orbit widths,
the entire small-width menu, arbitrary mixed words, nonsplit proper subdirect
relations, and simultaneous reversible quotient transport. Its scope is the
complete binary error family E. It supplies the binary input to the
nonbinary residual reduction and the full both-parity master.

T6 is a reusable forward-recurrence package. For nonnegative kernels on
strictly smaller indices, bounded nonnegative forcing, finite initial values
and eventual row norm at most a fixed q<1, prove boundedness first. Then a
vanishing scalar and vanishing row against a bounded complete sequence imply
vanishing error; exponential scalar and row imply exponential error. For a
recurrence directly on errors, a strictly contractive row can suffice together
with vanishing forcing and escape from each finite target set, but a rate
needs additional quantitative hypotheses. Keep this alternative distinct from
the complete-count recurrence actually used in T1. No bootstrap may assume T1
in order to establish a premise of T1.

## 5. Exact formal statement conventions

The [Lean statement module](formal/SymmetricSubgroupAsymptotics/Statements.lean)
defines the three final targets T1, T2 and T3 above, together with their
[definition obligations](formal/README.md). Their fully
quantified joint form is: there exist real c,K1,K2,K3>0 and a natural N0>=2
such that, for every natural n>=N0, all three inequalities hold:

    abs(s_n/L_n - 1) <= K1 * 2^(-c*n),
    abs(s_n/Q_n - 1) <= K2 / n,
    abs(s_n/M_n - 1 - (6*epsilon-4)/(48*n)^(1/4))
        <= K3 / sqrt(n).

Taking the maximum of three thresholds gives this common N0. Every constant
is independent of n, its parity and its residue class modulo four. The
residue-class constants C0,...,C3 in M_n are fixed by the exact products and
sums in Section 3; they are distinct from the error bounds K1,K2,K3.

The definitions and bridges required by these statements are:

* s_n is the finite cardinality of the subgroups of the permutation group on
  the labelled n-element set. It is not a sum over representatives up to
  conjugacy.
* G_R is the explicit finite rational expression
  `sum_(k=0)^R product_(i=0)^(k-1) (((2:ℚ)^R - (2:ℚ)^i) / ((2:ℚ)^k - (2:ℚ)^i))`,
  with empty product one and positive denominators on every included factor.
  It is `binaryGaussianSum R` in Lean. The separate obligation
  `DefinitionChecks.subspace_formula` requires a proof of
  `(binarySubspaceCount R : ℚ) = binaryGaussianSum R`, where
  `binarySubspaceCount R` counts all subspaces of F_2^R. The benchmarks use
  the rational expression, not the cardinality definition.
* R=floor(n/2), epsilon=n mod 2 and j=n mod 4 are natural indices. Factorials,
  s_n, the rational G_R and c_R's finite rational sum are coerced to real
  numbers before analytic arithmetic. In particular the exact benchmark is
  `(n! : ℝ) * (binaryGaussianSum R : ℝ) * (parityCoefficient n : ℝ)`;
  the saddle benchmark uses the same cast `(binaryGaussianSum R : ℝ)`.
  Every fractional or negative exponent in the asymptotic formulas is a real
  exponent; divisions such as n/8, n^2/16 and
  1/4 in such expressions are real divisions.
* Negative coefficient indices contribute zero. An implementation using
  natural indices must guard c_(R-1) when R=0 and every analogous shifted
  coefficient; truncated natural subtraction cannot replace this convention.
  In particular L_0=L_1=1. Positivity of every L_n is a proof obligation.
* rho_R is the unique positive saddle only for R>=1. Prove its existence and
  uniqueness, and positivity of Q_n for n>=2. For total sequence definitions,
  set Q_0=Q_1=1; these harmless values lie outside the asserted range.
* Prove convergence and positivity of phi and both theta sums, hence of all
  four Cj. Define M_n by the displayed formula for n>=1 and set M_0=1 to avoid
  a convention about zero to the zeroth power. Prove M_n>0.
* First prove the T2 and T3 analytic bounds with L_n in place of s_n, without
  assuming T1. Their final versions for s_n then follow from T1. Every
  O-term in the exposition must yield a quantified eventual inequality of
  the form above.

No optimized exponent c, effective onset N0, or stronger remainder is included
in these targets. Their formal trust boundary is specified in
[ASSUMPTIONS.md](ASSUMPTIONS.md).
