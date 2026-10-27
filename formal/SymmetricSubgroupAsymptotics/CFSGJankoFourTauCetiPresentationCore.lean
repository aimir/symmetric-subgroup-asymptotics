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
private abbrev x : Relator (Fin 3) := .gen 0

private abbrev y : Relator (Fin 3) := .gen 1

private abbrev t : Relator (Fin 3) := .gen 2

@[inherit_doc Relator.mul]
local infixl:70 " ⬝ " => Relator.mul

/-- The source's conjugate `r^s = s⁻¹rs`. -/
private abbrev sourceConj (r s : Relator (Fin 3)) : Relator (Fin 3) :=
  .inv s ⬝ r ⬝ s

/-- The sixth relator of the ATLAS presentation. -/
private abbrev sixthWord : Relator (Fin 3) :=
  .pow (x ⬝ y ⬝ x ⬝ y ⬝ x ⬝ .inv y) 3 ⬝
    .pow (x ⬝ y ⬝ x ⬝ .inv y ⬝ x ⬝ .inv y) 3

/-- The word conjugating `t` in the eleventh relator. -/
private abbrev firstConjugator : Relator (Fin 3) :=
  y ⬝ x ⬝ .inv y ⬝ x ⬝ y ⬝ x ⬝ .inv y ⬝ x

/-- The word conjugating `t` in the twelfth relator. -/
private abbrev secondConjugator : Relator (Fin 3) :=
  .pow (x ⬝ y) 3 ⬝ y ⬝ .pow (x ⬝ y) 6 ⬝ y

/-- John Bray's ATLAS version 3 finite presentation of the fourth Janko group `J₄` on its
type II standard generators `x`, `y`, and `t`.

The ATLAS lists this as a presentation of the abstract group, separately from the relations used
only to recognize standard generators inside an existing group. No structural property of the
presented group is asserted here: this definition records only the cited generators and relators.
-/
def j4Presentation : GroupPresentation where
  generatorNames := ["x", "y", "t"]
  source := "S. W. Bolt, J. N. Bray, and R. T. Curtis, Symmetric presentation of the Janko \
    group J4, J. London Math. Soc. 76 (2007), 683-701; R. A. Wilson, R. A. Parker, J. N. Bray \
    et al., ATLAS of Finite Group Representations, version 3"
  sourceLocator := "Bolt-Bray-Curtis, Section 5, doi:10.1112/jlms/jdm086; ATLAS presentation \
    J4G2-P1, https://brauer.maths.qmul.ac.uk/Atlas/v3/pres/J4G2-P1; relator list and \
    enumeration notes, https://brauer.maths.qmul.ac.uk/Atlas/spor/J4/mag/J4G2-P1.M"
  generatorConvention := "The ATLAS type II standard generators x, y, and t of J4, in that \
    order, so indices 0, 1, and 2 are x, y, and t. Products are read left to right, negative \
    exponents denote inverses, [r,s] denotes r^-1 s^-1 r s, and r^s denotes s^-1 r s."
  transcriptionNotes := "The twelve words are stored in the order of the ATLAS Magma file; \
    none is marked redundant. Source conjugates are expanded as s^-1*r*s, while products and \
    natural powers remain structured. GAP 4.15.1 with AtlasRep 2.1.9 checks the twelve compiled \
    words on type II generators obtained by the ATLAS restandardization program from the \
    112-dimensional characteristic-two matrix representation of J4. The source's double-coset \
    route enumerates 3980549947 cosets of the involution centralizer."
  expectedGeneratorCount := 3
  expectedRelatorCount := 12
  transcribed :=
    [ .pow x 2,
      .pow y 3,
      .pow (x ⬝ y) 23,
      .pow (.commInvInv x y) 12,
      .pow (.commInvInv x (y ⬝ x ⬝ y)) 5,
      sixthWord,
      .pow (x ⬝ y ⬝ .pow (x ⬝ y ⬝ x ⬝ .inv y) 3) 4,
      .pow t 2,
      .commInvInv t x,
      .commInvInv t (y ⬝ x ⬝ y ⬝ .pow (x ⬝ .inv y) 2 ⬝ .pow (x ⬝ y) 3),
      .pow (y ⬝ sourceConj t firstConjugator) 3,
      .pow (.pow (y ⬝ x ⬝ y ⬝ x ⬝ y ⬝ x ⬝ y) 3 ⬝ t ⬝
        sourceConj t secondConjugator) 2 ]


end TauCeti.Sporadic
