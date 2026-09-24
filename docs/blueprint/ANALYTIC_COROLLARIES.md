# Independent coefficient analysis and the explicit formulas

These lemmas concern the explicit coefficient benchmark. Their analytic proofs
do not use the subgroup asymptotic. Only the final transfer from L_n to s_n uses
THM-MAIN. Full definitions of the four constants and M_n are in
[SPEC.md](../../SPEC.md).

## ANA-GAUSS: all subspaces, not only the middle dimension

For every R and 0<=k<=R,

    GaussianBinomial(R,k;2)
      = product_(i=0)^(k-1) (2^(R-i)-1)/(2^(k-i)-1),
    G_R=sum_k GaussianBinomial(R,k;2).

The positive product phi=product_(j>=1)(1-2^(-j)) and the two convergent theta
sums give

    G_R=kappa_(R mod 2) 2^floor(R^2/4)
          * (1+O(R2^(-R/2))).

A uniform Gaussian-coefficient product estimate and a summable tail after
centring k at R/2 give the formula. It gives G_(R-1)/G_R=O(2^(-R/2)),
fixed-shift Gaussian exponents, and bounded exact-to-asymptotic normalization
ratios. These facts are needed inside the counting proof, independently of the
eventual elementary expansion.

## ANA-COEF: exact recurrence and coarse coefficient estimates

Let P(y)=y/2+y^2/6+y^4/384 and c_R=[y^R]exp(P(y)). Then c_0=1, negative-index
coefficients are zero, and

    R c_R=c_(R-1)/2+c_(R-2)/3+c_(R-4)/96.

Equivalently c_R is the sum over a+2b+4d=R of
1/(2^a a!6^b b!384^d d!). The separate four-colour orbit sum has degree-four
weights 1/24 and 1/8, whose sum is 1/6. Thus positivity and the exact parity
coefficient c_R+epsilon*c_(R-1)/6 are established without a saddle estimate.

For positive a1,a2,a4, the elementary quartic coefficient estimate is

    log [y^R]exp(a1*y+a2*y^2+a4*y^4)
      = -(R/4)log R + (R/4)(1+log(4a4)) + O(sqrt R).

In particular halving a4 gives the exponential critical-lift comparison.
For fixed shifts d, the required coefficient ratios have logarithms O(log R).
Growing support/profile sums require their uniform estimates separately;
fixed-d estimates cannot be applied with an unbounded d without proof.

## ANA-SADDLE: relative O(1/R), uniformly in parity

For R>0, rho is the unique positive root of

    R=rho/2+rho^2/3+rho^4/96,
    b=rho/2+2rho^2/3+rho^4/24.

The right side of the first equation is strictly increasing from zero to
infinity. Cauchy's coefficient integral gives, for epsilon in {0,1},

    [y^R](1+y/6)^epsilon exp(P(y))
      = (1+rho/6)^epsilon exp(P(rho))
          / (rho^R sqrt(2*pi*b)) * (1+O(1/R)).

On |theta|<=R^(-2/5), the exponent is
-b*theta^2/2-i*k3*theta^3/6+k4*theta^4/24+O(R|theta|^5), with kj=O(R).
The normalized odd amplitude is 1+d0(exp(i theta)-1), where
0<=d0=rho/(rho+6)<=1. The first imaginary odd terms integrate to zero;
the Gaussian expectations of theta^2, R theta^4 and R^2 theta^6 are O(1/R).
The remainder estimate uses uniform bounds on the Taylor remainders and
the truncated Gaussian tail.

For the complementary arcs use the exact real-part loss

    -sum_(d in {1,2,4}) a_d rho^d (1-cos(d theta)).

Away from the four quartic root directions, the quartic term gives loss
c R^(1/5). Near -1, the linear term gives c rho; near i and -i, the quadratic
term gives c rho^2. This suppresses all nonprincipal arcs faster than any
negative power of R. Positivity of the lower-degree terms is essential.

Keeping rho exact therefore yields the O(n^(-1)) saddle expression in SPEC.
Replacing rho prematurely by a truncated series can introduce a larger error.

## ANA-EXPLICIT: the nonzero first correction

Put x=(96R)^(1/4). Substitution into the saddle equation gives

    rho=x-8/x-12/x^2+32/x^3+184/x^5+O(x^(-6)).

Define

    T_R=exp[-R log R/4+(1-log 96)R/4
              +(2sqrt(6)/3)sqrt R+x/2-4/3] / sqrt(8*pi*R).

The controlled expansions are

    log(c_R/T_R)=-4/x+109/(9x^2)+O(x^(-3)),
    log((1+rho/6)/(x/6))=6/x-26/x^2+O(x^(-3)).

The O(R^(-1)) local saddle error is O(x^(-4)), so it does not affect these
coefficients. Combining them yields the relative first correction
(-4+6epsilon)/x with remainder O(x^(-2)). Stirling's formula and ANA-GAUSS,
with R=(n-epsilon)/2, give

    L_n/M_n=1+(6epsilon-4)/(48n)^(1/4)+O(n^(-1/2)).

The parity shift changes the square-root exponential only at order n^(-1/2)
and the fourth-root exponential at order n^(-3/4). These orders matter when
retaining the first correction. The positive residue-class constants are the
exact convergent products/sums in SPEC, not rounded decimal inputs.

## Transfer to the total count and the role of computations

After THM-MAIN proves s_n/L_n=1+O(2^(-cn)), multiplication gives both the
O(n^(-1)) exact-saddle approximation and the elementary first-correction
formula for s_n. A merely qualitative o(1) counting error would not justify
either quantitative remainder.

The local utility
[critical_coefficients.py](../../computations/python/critical_coefficients.py)
computes exact rational coefficients and integer benchmarks, compares the
recurrence with the separate four-colour orbit sum, and checks Gaussian
recurrence values against their product formula. It does not compute s_n,
prove a limit, or numerically certify an asymptotic remainder.
