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

/-- The word `babab⁻¹abab` in the long commutator of Bray's presentation. -/
private abbrev commutatorWord : Relator (Fin 2) :=
  b ⬝ a ⬝ b ⬝ a ⬝ .inv b ⬝ a ⬝ b ⬝ a ⬝ b

/-- The final relator in Bray's presentation, before setting it equal to the identity. -/
private abbrev finalWord : Relator (Fin 2) :=
  .pow (a ⬝ b) 4 ⬝ a ⬝ .pow b 2 ⬝ a ⬝ .pow (.inv b) 3 ⬝
    a ⬝ b ⬝ a ⬝ b ⬝ a ⬝ .inv b ⬝ a ⬝ .pow b 3 ⬝ a ⬝
    .pow (.inv b) 2 ⬝ a ⬝ .pow b 2

/-- John Bray's ATLAS version 3 finite presentation of the Held group `He` on its standard
generators `a` and `b`.

The ATLAS lists this as a full presentation of the abstract group, separately from the
semi-presentation used to recognize standard generators in a group already constructed. No
structural property of the presented group is asserted here: this definition records only the
cited generators and relations. -/
def hePresentation : GroupPresentation where
  generatorNames := ["a", "b"]
  source := "R. A. Wilson, R. A. Parker, J. N. Bray et al., ATLAS of Finite Group \
    Representations, version 3; presentation contributed by John Bray"
  sourceLocator := "HeG1-P1, https://brauer.maths.qmul.ac.uk/Atlas/v3/pres/HeG1-P1"
  generatorConvention := "The ATLAS standard generators a and b, in that order, so index 0 is a \
    and index 1 is b. Products are read left to right, negative exponents denote inverses, and \
    [r,s] denotes r^-1 s^-1 r s."
  transcriptionNotes := "The seven displayed words are stored as seven relators equal to the \
    identity. ATLAS distinguishes HeG1-P1 from its semi-presentation. GAP 4.15.1 with AtlasRep \
    2.1.9 checks these relators on the independent ATLAS 2058-point generators, which generate a \
    simple group of order 4030387200."
  expectedGeneratorCount := 2
  expectedRelatorCount := 7
  transcribed :=
    [ .pow a 2,
      .pow b 7,
      .pow (a ⬝ b) 17,
      .pow (.commInvInv a b) 6,
      .pow (.commInvInv a (.pow b 3)) 5,
      .commInvInv a commutatorWord,
      finalWord ]


end TauCeti.Sporadic
