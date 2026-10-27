/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
import SymmetricSubgroupAsymptotics.CFSGCoTwoTauCetiPresentationCore

/-! Literal J3 row from TauCeti 6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380,
TauCeti/GroupTheory/SpecificGroups/CFSG/Sporadic/Janko/Three.lean.
Only the row/auxiliary syntax is added. The already checked presentation compiler
is reused. No upstream finiteness/order/simplicity/recognition proof is imported. -/
namespace TauCeti.Sporadic
private abbrev a : Relator (Fin 2) := .gen 0

private abbrev b : Relator (Fin 2) := .gen 1

@[inherit_doc Relator.mul]
local infixl:70 " ⬝ " => Relator.mul

/-- The syllable `a * b`. -/
private abbrev ab1 : Relator (Fin 2) := a ⬝ b

/-- The syllable `a * b⁻¹`. -/
private abbrev abNeg1 : Relator (Fin 2) := a ⬝ .inv b

/-- The sixth relator of the source, `((abab ab⁻¹)² ab ab⁻¹ ab⁻¹ ab ab⁻¹)²`. -/
private abbrev sixthWord : Relator (Fin 2) :=
  .pow (.pow (ab1 ⬝ ab1 ⬝ abNeg1) 2 ⬝ ab1 ⬝ abNeg1 ⬝ abNeg1 ⬝ ab1 ⬝ abNeg1) 2

/-- The seventh relator of the source,
`abab (abab⁻¹)³ abab (abab⁻¹)⁴ ab⁻¹ (abab⁻¹)³`. -/
private abbrev seventhWord : Relator (Fin 2) :=
  ab1 ⬝ ab1 ⬝ .pow (ab1 ⬝ abNeg1) 3 ⬝ ab1 ⬝ ab1 ⬝ .pow (ab1 ⬝ abNeg1) 4 ⬝
    abNeg1 ⬝ .pow (ab1 ⬝ abNeg1) 3

/-- The ATLAS version 3 finite presentation of the third Janko group `J₃` on its standard
generators `a` and `b`; the ATLAS records no individual contributor for this presentation.

The ATLAS lists this as a full presentation of the abstract group, separately from the
semi-presentation used to recognize standard generators inside a group already constructed. No
structural property of the presented group is asserted here: this definition records only the
cited generators and relations. -/
def j3Presentation : GroupPresentation where
  generatorNames := ["a", "b"]
  source := "R. A. Wilson, R. A. Parker, J. N. Bray et al., ATLAS of Finite Group \
    Representations, version 3; individual presentation contributor not recorded"
  sourceLocator := "J3G1-P1, https://brauer.maths.qmul.ac.uk/Atlas/v3/pres/J3G1-P1, with the \
    relator list and the demonstration of correctness in the Magma source file \
    https://brauer.maths.qmul.ac.uk/Atlas/spor/J3/mag/J3G1-P1.M"
  generatorConvention := "The ATLAS standard generators a and b of J3, that is, a in class 2A and \
    b in class 3A with ab of order 19, in that order, so index 0 is a and index 1 is b. Products \
    are read left to right, negative exponents denote inverses, and [r,s] denotes r^-1 s^-1 r s."
  transcriptionNotes := "The eight words of the source's relator list are stored as eight \
    relators equal to the identity, in the order of the Magma file; the ATLAS page records no \
    individual contributor for this presentation. The presentation page displays the same eight \
    words with (x,y)^9 and (x*y)^19 interchanged. No word is marked redundant in either rendering. \
    The source demonstrates correctness by the coset enumeration \
    19*Index(G,K1) over the cyclic subgroup K1 = <a*b> of order 19, returning the order 50232960 \
    of J3. GAP 4.15.1 reproduces that enumeration from the eight compiled words, obtaining the \
    index 2643840, and checks that the same eight words vanish on the ATLAS 6156-point standard \
    generators of J3, which have a an involution with centralizer of order 1920, b of order 3 \
    with centralizer of order 1080, ab of order 19, and which generate a simple group of order \
    50232960."
  expectedGeneratorCount := 2
  expectedRelatorCount := 8
  transcribed :=
    [ .pow a 2,
      .pow b 3,
      .pow (.commInvInv a b) 9,
      .pow ab1 19,
      .pow (.pow ab1 6 ⬝ .pow abNeg1 5) 2,
      sixthWord,
      seventhWord,
      .pow (.pow ab1 3 ⬝ .pow (ab1 ⬝ abNeg1) 2) 4 ]


end TauCeti.Sporadic
