/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
import SymmetricSubgroupAsymptotics.CFSGCoTwoTauCetiPresentationCore

/-! Literal row port from TauCeti 6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380.
The presentation compiler is reused from the checked Co2 core. No finiteness,
order, simplicity or concrete-model recognition theorem is imported. -/
namespace TauCeti.Sporadic
private abbrev a : Relator (Fin 2) := .gen 0

private abbrev b : Relator (Fin 2) := .gen 1

@[inherit_doc Relator.mul]
local infixl:70 " ⬝ " => Relator.mul

/-- The syllable `a * b`. -/
private abbrev ab1 : Relator (Fin 2) := a ⬝ b

/-- The syllable `a * b ^ 2`. -/
private abbrev ab2 : Relator (Fin 2) := a ⬝ .pow b 2

/-- The syllable `a * b⁻¹`. -/
private abbrev abNeg1 : Relator (Fin 2) := a ⬝ .inv b

/-- The syllable `a * b⁻²`. -/
private abbrev abNeg2 : Relator (Fin 2) := a ⬝ .pow (.inv b) 2

/-- John Bray's ATLAS version 3 finite presentation of the Higman--Sims group `HS` on its standard
generators `a` and `b`.

The ATLAS lists this as a full presentation of the abstract group, separately from the
semi-presentation used to recognize standard generators inside a group already constructed. No
structural property of the presented group is asserted here: this definition records only the
cited generators and relations. -/
def hsPresentation : GroupPresentation where
  generatorNames := ["a", "b"]
  source := "R. A. Wilson, R. A. Parker, J. N. Bray et al., ATLAS of Finite Group \
    Representations, version 3; presentation contributed by John Bray"
  sourceLocator := "HSG1-P1, https://brauer.maths.qmul.ac.uk/Atlas/v3/pres/HSG1-P1, with the \
    relator list and the demonstration of correctness in the Magma source file \
    https://brauer.maths.qmul.ac.uk/Atlas/spor/HS/mag/HSG1-P1.M"
  generatorConvention := "The ATLAS standard generators a and b of HS, that is, a in class 2A and \
    b in class 5A with ab of order 11, in that order, so index 0 is a and index 1 is b. Products \
    are read left to right, negative exponents denote inverses, and [r,s] denotes r^-1 s^-1 r s."
  transcriptionNotes := "The thirteen words of the source's relator list are stored as thirteen \
    relators equal to the identity. The last three, marked R1, R2 and R3 there, are redundant, \
    and are transcribed because the source runs its coset enumerations with them. The source \
    demonstrates correctness by enumerating the 5775 cosets of a subgroup that visibly \
    centralizes a, using (a*b^2)^10 = 1 to exclude the double cover 2.HS. GAP 4.15.1 checks that \
    the thirteen compiled words vanish on five independent standard generating pairs of the \
    100-point primitive representation of HS, taking a with centralizer of order 7680, b of \
    order 5 with centralizer of order 500, and ab of order 11."
  expectedGeneratorCount := 2
  expectedRelatorCount := 13
  transcribed :=
    [ .pow a 2,
      .pow b 5,
      .pow ab1 11,
      .pow ab2 10,
      .pow (.commInvInv a b) 5,
      .pow (.commInvInv a (b ⬝ a ⬝ b)) 3,
      .pow (.commInvInv a (.pow b 2)) 6,
      ab1 ⬝ ab1 ⬝ ab2 ⬝ abNeg1 ⬝ abNeg2 ⬝ abNeg1 ⬝ ab2 ⬝ ab1 ⬝ ab1 ⬝ .pow abNeg2 4,
      ab1 ⬝ .pow (ab2 ⬝ .pow abNeg2 2) 2 ⬝ ab2 ⬝ ab1 ⬝ ab2 ⬝ .pow (abNeg1 ⬝ ab2) 2,
      ab1 ⬝ ab1 ⬝ .pow ab2 2 ⬝ ab1 ⬝ .pow abNeg1 2 ⬝ ab1 ⬝ .pow ab2 2 ⬝ ab1 ⬝ ab1 ⬝
        abNeg2 ⬝ abNeg1 ⬝ abNeg2,
      .pow (ab1 ⬝ ab1 ⬝ ab2 ⬝ abNeg1 ⬝ abNeg2 ⬝ ab1 ⬝ ab1 ⬝ abNeg1) 2,
      .pow (ab1 ⬝ ab1 ⬝ ab2) 2 ⬝ ab1 ⬝ ab1 ⬝ abNeg1 ⬝ ab1 ⬝ ab1 ⬝ .pow ab2 3 ⬝ ab1 ⬝ ab1 ⬝ abNeg1,
      ab1 ⬝ .pow (ab1 ⬝ ab2) 3 ⬝ ab1 ⬝ ab1 ⬝ ab2 ⬝ abNeg1 ⬝ ab1 ⬝ abNeg2 ⬝ ab1 ⬝ abNeg1 ⬝ ab2 ]


end TauCeti.Sporadic
