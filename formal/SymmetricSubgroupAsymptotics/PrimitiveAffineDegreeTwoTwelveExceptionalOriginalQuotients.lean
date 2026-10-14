import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveExceptionalTypewise

/-!
# Exceptional twelve-pair certificates on actual original quotients

This replaces the scalar `(topSocle = 1, natural = 3)` requirement by the
construction used in the exceptional argument. A certificate chooses one
of the five existing profiles from the existing finite states and supplies
its relative anchor on every original normal quotient. It does not accept
a final counting source, a numerical bound, or a claimed census result.

The binary/nonbinary split has separate constructors for the `S₃` and `C₃`
core arguments. The unrestricted typewise constructor also handles the
factor-nine paired-six argument; it retains its prefix kernel and every
same-type multiplicity obligation. These constructors do not discharge
the per-row obligations merely by giving their branch a name.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveExceptionalOriginalQuotients

open DegreeTwoTwelveExceptionalTypewise

/-- The certificate is uniform over realizations of a literal top. Every
anchor is attached to the actual original `N`; the finite states select
only its profile. The published Zmud input may construct the characters. -/
structure RowCertificate (D : DegreeTwoPairTopFiniteInterface 12) : Type 1 where
  kindOfState : D.normalRegistry.State → D.ModuleState → ProfileKind
  anchor : ZmudFaithfulCharacterTupleInput →
    ∀ {p : PreE7PairActionClass 12} (R : DegreeTwoPairTopRealization D p)
      (N : {N : Subgroup (preE7PairAction 12 p) // N.Normal}),
    DegreeTwoPairRelativeKernelAnchor (preE7PairAction 12 p ⧸ N.1)
      (kindOfState (R.topNormalState N) (R.moduleState N)).profile

namespace RowCertificate

variable {D : DegreeTwoPairTopFiniteInterface 12} (C : RowCertificate D)

def stateProfile {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p) : DegreeTwoPairTopStateProfile D p R where
  profileOfState := fun i j ↦ (C.kindOfState i j).profile
  allowedProfiles := degreeTwoTwelvePairExceptionalProfiles
  allowed_capacity := degreeTwoTwelvePairExceptionalProfiles_capacity
  profile_mem N := (C.kindOfState (R.topNormalState N) (R.moduleState N)).profile_mem

def liftConclusion (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p) : DegreeTwoPairTopRelativeLiftConclusion D p :=
  (C.stateProfile R).relativeKernelLiftConclusion lit (C.anchor hZmud R)

def resolvedData (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {p : PreE7PairActionClass 12}
    (R : DegreeTwoPairTopRealization D p) :
    DegreeTwoPairTopRelativeResolvedData D degreeTwoTwelvePairExceptionalProfiles p :=
  { lift := C.liftConclusion hZmud lit R
    profiles_eq := rfl
    numerics := degreeTwoTwelvePairRelativeNumerics (C.liftConclusion hZmud lit R).lift }

/-- Install an actual original-quotient certificate at an exceptional
catalogue row. Membership in the branch supplies only the profile menu. -/
def catalogueResolvedRow {row : DegreeTwoTwelvePairTopRow}
    (C : RowCertificate row.finite) (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (hbranch : row.branch = .core ∨ row.branch = .paired)
    {p : PreE7PairActionClass 12} (R : DegreeTwoPairTopRealization row.finite p) :
    DegreeTwoPairTopResolvedRow row.finite row.expectedProfiles p := by
  have hprofiles : row.expectedProfiles = degreeTwoTwelvePairExceptionalProfiles := by
    rcases hbranch with hcore | hpaired
    · rw [row.expectedProfiles_eq, hcore]
    · rw [row.expectedProfiles_eq, hpaired]
  rw [hprofiles]
  exact (C.resolvedData hZmud lit R).toResolvedRow

/-- Assemble binary and nonbinary top-quotient branches. The hypotheses
are actual anchors for all original normals, not scalar top bounds. -/
def ofBinaryTopSplit
    (binaryKind nonbinaryKind : ProfileKind)
    (binary : ZmudFaithfulCharacterTupleInput →
      ∀ {p : PreE7PairActionClass 12} (R : DegreeTwoPairTopRealization D p)
        (N : {N : Subgroup (preE7PairAction 12 p) // N.Normal}),
      IsPGroup 2 (D.top ⧸ D.normalRegistry.state (R.topNormalState N)) →
      DegreeTwoPairRelativeKernelAnchor (preE7PairAction 12 p ⧸ N.1) binaryKind.profile)
    (nonbinary : ZmudFaithfulCharacterTupleInput →
      ∀ {p : PreE7PairActionClass 12} (R : DegreeTwoPairTopRealization D p)
        (N : {N : Subgroup (preE7PairAction 12 p) // N.Normal}),
      (¬ IsPGroup 2 (D.top ⧸ D.normalRegistry.state (R.topNormalState N))) →
      DegreeTwoPairRelativeKernelAnchor (preE7PairAction 12 p ⧸ N.1) nonbinaryKind.profile) :
    RowCertificate D where
  kindOfState i _ :=
    if IsPGroup 2 (D.top ⧸ D.normalRegistry.state i) then binaryKind else nonbinaryKind
  anchor hZmud _p R N := by
    split
    · rename_i h
      exact binary hZmud R N h
    · rename_i h
      exact nonbinary hZmud R N h

/-- The S₃ core argument uses a binary-primary prefix for binary images
and one ordinary prefix for nonbinary images. -/
abbrev ofSymmetricThreeCore :=
  @ofBinaryTopSplit D .binaryFour .ordinaryThree

/-- The manuscript C₃ core argument twists its full-order binary-primary
character by an odd character in the nonbinary case. That branch still
has to supply the actual linear-prefix anchor. -/
abbrev ofTernaryCore :=
  @ofBinaryTopSplit D .binaryFour .linearFour

/-- An exact typewise prefix certificate supplies the required anchor.
This includes paired-six towers with odd part nine; no one-factor-three
order hypothesis is silently imposed on that route. -/
def ofTypewise
    (kind : D.normalRegistry.State → D.ModuleState → ProfileKind)
    (data : ZmudFaithfulCharacterTupleInput →
      ∀ {p : PreE7PairActionClass 12} (R : DegreeTwoPairTopRealization D p)
        (N : {N : Subgroup (preE7PairAction 12 p) // N.Normal}),
      QuotientData (preE7PairAction 12 p ⧸ N.1)
        (kind (R.topNormalState N) (R.moduleState N))) : RowCertificate D where
  kindOfState := kind
  anchor hZmud _p R N := (data hZmud R N).toOrbitInput.anchor

end RowCertificate

/-- Corrected exceptional catalogue payload. Each field retains original
normal ownership through `RowCertificate`; no final source is a premise.
The eight ternary comparator rows remain in their separate interface. -/
structure CatalogueData (T : DegreeTwoTwelvePairTopFiniteCatalogue) : Type 1 where
  core : ∀ j : Fin 301, (T.row j).branch = .core → RowCertificate (T.row j).finite
  paired : ∀ j : Fin 301, (T.row j).branch = .paired → RowCertificate (T.row j).finite

namespace CatalogueData

variable {T : DegreeTwoTwelvePairTopFiniteCatalogue} (C : CatalogueData T)

def coreResolvedRow (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) (j : Fin 301)
    {p : PreE7PairActionClass 12} (R : DegreeTwoPairTopRealization (T.row j).finite p)
    (hbranch : (T.row j).branch = .core) :
    DegreeTwoPairTopResolvedRow (T.row j).finite (T.row j).expectedProfiles p :=
  (C.core j hbranch).catalogueResolvedRow hZmud lit (Or.inl hbranch) R

def pairedResolvedRow (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) (j : Fin 301)
    {p : PreE7PairActionClass 12} (R : DegreeTwoPairTopRealization (T.row j).finite p)
    (hbranch : (T.row j).branch = .paired) :
    DegreeTwoPairTopResolvedRow (T.row j).finite (T.row j).expectedProfiles p :=
  (C.paired j hbranch).catalogueResolvedRow hZmud lit (Or.inr hbranch) R

end CatalogueData
end DegreeTwoTwelveExceptionalOriginalQuotients
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
