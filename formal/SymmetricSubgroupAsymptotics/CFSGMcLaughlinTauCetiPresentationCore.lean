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

/-- John Bray's ATLAS version 3 finite presentation of the McLaughlin group `McL` on its standard
generators `a` and `b`.

The ATLAS lists this as a full presentation of the abstract group, separately from the
semi-presentation used to recognize standard generators inside a group already constructed. No
structural property of the presented group is asserted here: this definition records only the
cited generators and relations. -/
def mclPresentation : GroupPresentation where
  generatorNames := ["a", "b"]
  source := "R. A. Wilson, R. A. Parker, J. N. Bray et al., ATLAS of Finite Group \
    Representations, version 3; presentation contributed by John Bray"
  sourceLocator := "McLG1-P1, https://brauer.maths.qmul.ac.uk/Atlas/v3/pres/McLG1-P1, with the \
    relator list and the demonstration of correctness in the Magma source file \
    https://brauer.maths.qmul.ac.uk/Atlas/spor/McL/mag/McLG1-P1.M"
  generatorConvention := "The ATLAS standard generators a and b of McL, that is, a in class 2A \
    and b in class 5A with ab of order 11 and ababababbababbabb of order 7, in that order, so \
    index 0 is a and index 1 is b. Products are read left to right, negative exponents denote \
    inverses, and [r,s] denotes r^-1 s^-1 r s."
  transcriptionNotes := "The fifteen words of the source's relator list are stored as fifteen \
    relators equal to the identity. Three of them, marked R0, R1 and R2 there, are redundant, and \
    are transcribed because the source's coset enumerations are easier with them. The source \
    demonstrates correctness by enumerating the 22275 cosets of a subgroup that centralizes a, \
    then excluding the triple cover 3.McL, whose standard generators have |AB| = 33 rather than \
    11. GAP 4.15.1 checks that the fifteen compiled words vanish on five independent standard \
    generating pairs of the 275-point primitive representation of McL, taking a and b with \
    centralizers of orders 40320 and 750 and imposing the two ATLAS element-order conditions."
  expectedGeneratorCount := 2
  expectedRelatorCount := 15
  transcribed :=
    [ .pow a 2,
      .pow b 5,
      .pow (.commInvInv a b) 5,
      .pow ab1 11,
      .pow ab2 12,
      .pow (.commInvInv a (.pow b 2)) 6,
      .pow (ab1 ⬝ abNeg2) 7,
      .pow (.commInvInv a (.pow (.inv b) 2 ⬝ ab1 ⬝ ab1 ⬝ ab2)) 2,
      .commInvInv a (.pow (.inv b) 2 ⬝ ab2 ⬝ abNeg1 ⬝ ab1 ⬝ .pow ab2 2 ⬝ ab1 ⬝ abNeg1),
      .pow (.commInvInv a (b ⬝ .pow ab2 3)) 2,
      .pow (.commInvInv a (.pow b 2 ⬝ ab1 ⬝ .pow ab2 2)) 2,
      ab1 ⬝ ab2 ⬝ abNeg2 ⬝ ab1 ⬝ abNeg1 ⬝ ab2 ⬝ .pow (abNeg2 ⬝ ab1) 2 ⬝
        .pow (ab2 ⬝ abNeg2 ⬝ ab2) 2,
      .pow (.commInvInv a (.pow b 2 ⬝ ab2 ⬝ abNeg1 ⬝ ab2)) 2,
      .pow (.commInvInv a (.pow b 2 ⬝ ab1)) 4,
      .pow (.commInvInv a (.pow b 2 ⬝ ab2)) 4 ]


end TauCeti.Sporadic
