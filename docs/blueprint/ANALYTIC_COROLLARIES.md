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

The exceptional critical-lift sum uses
P_tilde(y)=y/(2sqrt(2))+7y^2/48+y^4/768. Evaluate its positive series at
the original saddle rho_R from ANA-SADDLE. With c_tilde_R its coefficient,

    c_tilde_R * rho_R^R <= exp(P_tilde(rho_R)),
    c_R * rho_R^R >= const * exp(P(rho_R))/sqrt(R),
    P_tilde(rho_R) <= P(rho_R)-rho_R^4/768 <= P(rho_R)-R/16

eventually. Thus c_tilde_R/c_R=O(sqrt(R)exp(-R/16))=O(2^(-R/32)).
This comparison needs only the original independent saddle estimate;
no separate perturbed saddle or general quartic coefficient asymptotic is needed.
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

Put lambda_1=rho/2, lambda_2=rho^2/6 and lambda_4=rho^4/384. The centered
exponent is exactly -A+iB, where

    A = sum_k lambda_k (1-cos(k theta)),
    B = sum_k lambda_k (sin(k theta)-k theta),    k in {1,2,4}.

The normalized real kernel is

    H_d = exp(-A) [(1-d) cos B + d cos(theta+B)].

Even parity uses d=0, odd parity uses d=rho/(rho+6). Treating all d in [0,1]
also retains d=1 for the shifted coefficient ratio. On the fixed central
interval |theta|<=pi/4, every harmonic satisfies the elementary cosine lower
bound. With Q=b*theta^2/2, this gives

    R*theta^2/8 <= A <= Q,
    Q-A = O(R*theta^4),    |B| = O(R*|theta|^3).

The convex cosine amplitude satisfies
0<=1-[(1-d)cos B+d cos(theta+B)]<=B^2/2+|theta*B|+theta^2/2.
Consequently the central error is bounded by

    C exp(-R*theta^2/8) (theta^2+R*theta^4+R^2*theta^6).

Its integral is O(R^(-3/2)), without assuming that B is uniformly small.
On all of pi/4<=|theta|<=pi, the linear term alone gives A>=rho/16.
Thus every outer arc, including the other quartic peaks, contributes at most
2*pi*exp(-rho/16). The Gaussian complement is exponentially small in R.
Combining the three integrals and using R<=b<=4R gives relative error O(1/R),
uniformly in d. The d=1 integral divided by the d=0 integral is
c_(R-1)/(rho*c_R), proving the stated shifted coefficient ratio at the same
saddle rho_R.

Keeping rho exact therefore yields the O(n^(-1)) saddle expression in SPEC.
Replacing rho prematurely by a truncated series can introduce a larger error.

## ANA-EXPLICIT: the nonzero first correction

Put x=(96R)^(1/4) and v=x(x-rho). Substitution and the mean value theorem give

    rho=x-8/x+O(x^(-2)),    v=8+O(1/x).

This first displacement suffices. Expanding log(1-v/x^2) through its
quadratic term gives

    P(rho)-R log rho
      =R/4-R log x+x^2/6+x/2+v^2/48-v/3-v/(2x)+O(x^(-2)).

The identity v^2/48-v/3=-4/3+(v-8)^2/48 exposes the cancellation at the
saddle and gives the correction -4/x. Also b(rho)/(4R)=1+O(x^(-2)).

Define

    T_R=exp[-R log R/4+(1-log 96)R/4
              +(2sqrt(6)/3)sqrt R+x/2-4/3] / sqrt(8*pi*R).

The controlled expansions are

    log(c_R/T_R)=-4/x+O(x^(-2)),
    log((1+rho/6)/(x/6))=6/x+O(x^(-2)).

The O(R^(-1)) local saddle error is O(x^(-4)), so it is absorbed in this
remainder. Combining them yields the first correction (-4+6epsilon)/x.
For the degree conversion, let y=(48n)^(1/4) and define the logarithmic model

    Lambda_n=(n+1/2)log n-n+log(2pi)/2
             +floor(R^2/4)log 2+log kappa_(R mod 2)
             +log T_R+epsilon log(x/6)+(6epsilon-4)/x.

Stirling and ANA-GAUSS give log L_n=Lambda_n+O(n^(-1/2)). The exact
four-residue normalization yields

    Lambda_n-log M_n-(6epsilon-4)/y
      =((n-3epsilon+4)/8)log(n/(n-epsilon))-epsilon/8
        +(x^2-y^2)/6+(x-y)/2+(6epsilon-4)(1/x-1/y).

The right-hand side vanishes exactly in even degree. In odd degree the
logarithmic expression including -epsilon/8 is O(1/n), while y^4-x^4=48 bounds the other terms by
O(n^(-1/2)), O(n^(-3/4)) and O(n^(-5/4)), respectively. Exponentiating gives

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
