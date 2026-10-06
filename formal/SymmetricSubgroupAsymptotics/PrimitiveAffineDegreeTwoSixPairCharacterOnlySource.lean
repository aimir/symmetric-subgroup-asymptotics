import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairCatalogueDispatcher
import SymmetricSubgroupAsymptotics.ZmudFaithfulCharacterInput

/-!
# Character-only six-pair catalogue rows

Of the 182 physical six-pair actions, 151 have no binary or repeated-head
target in their selected normal-quotient list.  Every quotient in such a row
uses the existing character route.  This file isolates the reusable Lean
adapter for those rows.

The counting input is exactly the already-proved character API:

* `CharacterSlotTuple` retains designated binary-linear, linear and general
  irreducible positions and their joint faithfulness;
* `CharacterQuotientCertificate.slope_le_four_thirds_of_mixed` turns the
  finite profile inequality `3^l 5^t ≤ 15` into the B6 cold slope;
* `ZmudFaithfulCharacterTupleInput.generalCertificate` supplies the common
  one-general-position case from a checked socle normal generator.

Thus an emitted finite row need only build the literal quotient certificate
and the small profile inequality.  This adapter does not assume a census,
character-table completeness, or an owner-order statement.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- The block chart underlying a literal six-pair frame, with the binary
coordinate written as `Fin 2` as required by the B6 interface. -/
def BinaryPairFrame.sixPairBlockChart
    {U : Subgroup (Equiv.Perm (Fin 12))}
    (F : BinaryPairFrame U (Fin 6)) : Fin 12 ≃ Fin 6 × Fin 2 :=
  F.frame.symm.trans
    (Equiv.prodCongr (Equiv.refl (Fin 6))
      (ZMod.finEquiv 2).symm.toEquiv)

/-- A binary pair frame proves literal preservation of its displayed block
chart. -/
theorem BinaryPairFrame.sixPairBlockChart_preserves
    {U : Subgroup (Equiv.Perm (Fin 12))}
    (F : BinaryPairFrame U (Fin 6)) :
    ∀ u ∈ U, ∀ x y : Fin 12,
      (F.sixPairBlockChart x).1 = (F.sixPairBlockChart y).1 →
        (F.sixPairBlockChart (u x)).1 =
          (F.sixPairBlockChart (u y)).1 := by
  intro u hu x y hxy
  let g : U := ⟨u, hu⟩
  have hx := F.intertwine g (F.frame.symm x)
  have hy := F.intertwine g (F.frame.symm y)
  change (F.frame.symm (u x)).1 = (F.frame.symm (u y)).1
  change (F.frame.symm x).1 = (F.frame.symm y).1 at hxy
  calc
    (F.frame.symm (u x)).1 = F.top g (F.frame.symm x).1 := by
      simpa only [F.frame.apply_symm_apply] using hx
    _ = F.top g (F.frame.symm y).1 := congrArg (F.top g) hxy
    _ = (F.frame.symm (u y)).1 := by
      simpa only [F.frame.apply_symm_apply] using hy.symm

/-- The finite datum retained by a character-only catalogue row.  Each
literal normal quotient carries its fixed jointly faithful tuple, and the
two small fields state precisely the hypotheses of the common slope lemma.
The tuple is chosen before the complementary source group is inspected. -/
structure PreE7B6CharacterOnlyQuotientData
    (U : Subgroup (Equiv.Perm (Fin 12))) : Type 1 where
  certificate : ∀ N : {N : Subgroup U // N.Normal},
    CharacterQuotientCertificate (U ⧸ N.1)
  mixed : ∀ N, (certificate N).mode = .mixed
  noBinary : ∀ N, (certificate N).tuple.binaryCount = 0
  profile : ∀ N,
    3 ^ (certificate N).tuple.linearCount *
      5 ^ (certificate N).tuple.generalCount ≤ 15

/-- Structural input for the historical one-linear/one-general profile.
The general position is faithful after quotienting by `generalKernel`; its
inflation and the literal linear character are jointly faithful because
their kernels have trivial intersection. -/
structure LinearZmudCharacterPairData (Q : Type) [Group Q] : Type 1 where
  linear : Q →* ℂˣ
  generalKernel : Subgroup Q
  [generalKernel_normal : generalKernel.Normal]
  generalSocleGenerator :
    SocleNormalGeneratorBound (Q ⧸ generalKernel) 1
  kernel_inf : linear.ker ⊓ generalKernel = ⊥

attribute [instance] LinearZmudCharacterPairData.generalKernel_normal

namespace LinearZmudCharacterPairData

variable {Q : Type} [Group Q] [Finite Q]
  (D : LinearZmudCharacterPairData Q)

/-- Inflate the Zmud irreducible representation from the literal quotient;
surjectivity of the quotient map preserves irreducibility. -/
noncomputable def inflatedGeneral
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    FiniteIrreducibleRepresentation ℂ Q := by
  let ρ := (hZmud.generalTuple D.generalSocleGenerator).general 0
  exact
    { Space := ρ.Space
      addCommGroup := inferInstance
      module := inferInstance
      finiteDimensional := inferInstance
      action := ρ.action.comp (QuotientGroup.mk' D.generalKernel)
      irreducible := representation_irreducible_comp ρ.action
        (QuotientGroup.mk' D.generalKernel)
        (QuotientGroup.mk'_surjective D.generalKernel) }

/-- The literal one-linear/one-general tuple on `Q`. -/
noncomputable def tuple (hZmud : ZmudFaithfulCharacterTupleInput) :
    CharacterSlotTuple Q where
  binaryCount := 0
  linearCount := 1
  generalCount := 1
  binary := Fin.elim0
  binary_twoGroup := fun i => Fin.elim0 i
  linear := fun _ => D.linear
  general := fun _ => D.inflatedGeneral hZmud
  faithful := by
    intro q _ hlinear hgeneral
    let T := hZmud.generalTuple D.generalSocleGenerator
    have hquot : QuotientGroup.mk' D.generalKernel q = 1 := by
      apply T.faithful
      · exact fun i => Fin.elim0 i
      · exact fun i => Fin.elim0 i
      · intro i
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        simpa only [inflatedGeneral, T, MonoidHom.comp_apply] using
          hgeneral 0
    have hK : q ∈ D.linear.ker :=
      (MonoidHom.mem_ker).2 (hlinear 0)
    have hL : q ∈ D.generalKernel := by
      simpa only [QuotientGroup.eq_one_iff] using hquot
    have hbot : q ∈ D.linear.ker ⊓ D.generalKernel := ⟨hK, hL⟩
    rw [D.kernel_inf] at hbot
    simpa only [Subgroup.mem_bot] using hbot

/-- The mixed certificate consumed by the common character counting
theorem. -/
noncomputable def certificate (hZmud : ZmudFaithfulCharacterTupleInput) :
    CharacterQuotientCertificate Q where
  mode := .mixed
  tuple := D.tuple hZmud
  prime := 2
  known := by
    intro h
    cases h

@[simp] theorem certificate_binaryCount
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    (D.certificate hZmud).tuple.binaryCount = 0 := rfl

@[simp] theorem certificate_linearCount
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    (D.certificate hZmud).tuple.linearCount = 1 := rfl

@[simp] theorem certificate_generalCount
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    (D.certificate hZmud).tuple.generalCount = 1 := rfl

end LinearZmudCharacterPairData

/-- The two finite character-only shapes used by the selected catalogue:
one Zmud general position, or one literal linear position together with one
inflated Zmud general position. -/
inductive PreE7B6CharacterAxisData (Q : Type) [Group Q] : Type 1
  | oneGeneral (socleGenerator : SocleNormalGeneratorBound Q 1)
  | linearGeneral (data : LinearZmudCharacterPairData Q)

namespace PreE7B6CharacterAxisData

variable {Q : Type} [Group Q] [Finite Q]
  (A : PreE7B6CharacterAxisData Q)

noncomputable def certificate (hZmud : ZmudFaithfulCharacterTupleInput) :
    CharacterQuotientCertificate Q :=
  match A with
  | .oneGeneral h => hZmud.generalCertificate h
  | .linearGeneral D => D.certificate hZmud

@[simp] theorem certificate_mixed
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    (A.certificate hZmud).mode = .mixed := by
  cases A <;> rfl

@[simp] theorem certificate_noBinary
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    (A.certificate hZmud).tuple.binaryCount = 0 := by
  cases A <;> rfl

theorem certificate_profile
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    3 ^ (A.certificate hZmud).tuple.linearCount *
      5 ^ (A.certificate hZmud).tuple.generalCount ≤ 15 := by
  cases A with
  | oneGeneral h =>
      change 3 ^ 0 * 5 ^ 1 ≤ 15
      norm_num
  | linearGeneral D =>
      change 3 ^ 1 * 5 ^ 1 ≤ 15
      norm_num

end PreE7B6CharacterAxisData

namespace PreE7B6CharacterOnlyQuotientData

variable {U : Subgroup (Equiv.Perm (Fin 12))}
  (D : PreE7B6CharacterOnlyQuotientData U)

/-- Assemble the complete character-only source from the finite per-normal
axis alternatives. -/
noncomputable def ofAxes
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (axis : ∀ N : {N : Subgroup U // N.Normal},
      PreE7B6CharacterAxisData (U ⧸ N.1)) :
    PreE7B6CharacterOnlyQuotientData U where
  certificate N := (axis N).certificate hZmud
  mixed N := (axis N).certificate_mixed hZmud
  noBinary N := (axis N).certificate_noBinary hZmud
  profile N := (axis N).certificate_profile hZmud

/-- The common one-character row: a checked one-element normal generator of
the quotient socle is converted by Zmud's published theorem into one
faithful general position. -/
noncomputable def ofOneGeneral
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (hgen : ∀ N : {N : Subgroup U // N.Normal},
      SocleNormalGeneratorBound (U ⧸ N.1) 1) :
    PreE7B6CharacterOnlyQuotientData U where
  certificate N := hZmud.generalCertificate (hgen N)
  mixed := fun _ => rfl
  noBinary := fun _ => rfl
  profile := by
    intro N
    change 3 ^ 0 * 5 ^ 1 ≤ 15
    norm_num

/-- Every selected character tuple has the B6 slope `≤ 4/3`. -/
theorem slope_le (N : {N : Subgroup U // N.Normal}) :
    (D.certificate N).slope ≤ 4 / 3 :=
  CharacterQuotientCertificate.slope_le_four_thirds_of_mixed
    (D.certificate N) (D.mixed N) (D.noBinary N) (D.profile N)

/-- Install all character-only quotient rows in the existing B6 action
certificate. -/
noncomputable def toB6ActionCertificate (F : BinaryPairFrame U (Fin 6)) :
    PreE7B6ActionCertificate U where
  blockChart := F.sixPairBlockChart
  preserves := F.sixPairBlockChart_preserves
  quotient N := .character (D.certificate N) (D.slope_le N)

end PreE7B6CharacterOnlyQuotientData

/-- One character-only owner row after its checked literal action has been
bound to the chosen pre-E7 pair representative.  The quotient data live on
that literal representative, so no abstract action is substituted for the
physical source. -/
structure PrimitiveAffineDegreeTwoSixPairCharacterOnlyOwnerData
    (p : PreE7PairActionClass 6) : Type 1 where
  literal : PrimitiveAffineDegreeTwoSixPairCheckedLiteralAction
  pointRelabel : Equiv.Perm (Fin 12)
  correspondence :
    relabelSubgroup pointRelabel literal.G = preE7PairAction 6 p
  quotients : PreE7B6CharacterOnlyQuotientData (preE7PairAction 6 p)

/-- The exact finite payload required from an emitted character-only row.
It contains no complex representation and hence is independent of the
published Zmud input.  For every literal normal quotient the emitter must
prove exactly one of:

* its socle is normally generated by one element; or
* there is a literal linear character `chi`, a literal normal subgroup `K`,
  `Soc(Q/K)` is normally generated by one element, and
  `ker(chi) ⊓ K = ⊥`.

The second alternative replaces each of the historical profiles
`(linear,general) = (1,t)`, `1 ≤ t ≤ 4`, by the sharper one-linear,
one-general tuple obtained by applying Zmud to `Q/K`.  Thus the old profile
count is not trusted as a certificate and the finite checker need only bind
the displayed character, subgroup, quotient generator, and intersection to
the literal quotient. -/
structure PrimitiveAffineDegreeTwoSixPairCharacterOnlyFiniteRowData
    (p : PreE7PairActionClass 6) : Type 1 where
  literal : PrimitiveAffineDegreeTwoSixPairCheckedLiteralAction
  pointRelabel : Equiv.Perm (Fin 12)
  correspondence :
    relabelSubgroup pointRelabel literal.G = preE7PairAction 6 p
  axis : ∀ N : {N : Subgroup (preE7PairAction 6 p) // N.Normal},
    PreE7B6CharacterAxisData ((preE7PairAction 6 p) ⨸ N.1)

namespace PrimitiveAffineDegreeTwoSixPairCharacterOnlyFiniteRowData

variable {p : PreE7PairActionClass 6}
  (D : PrimitiveAffineDegreeTwoSixPairCharacterOnlyFiniteRowData p)

/-- Apply the published Zmud theorem after all literal finite obligations
have been checked. -/
noncomputable def toOwnerData
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    PrimitiveAffineDegreeTwoSixPairCharacterOnlyOwnerData p where
  literal := D.literal
  pointRelabel := D.pointRelabel
  correspondence := D.correspondence
  quotients := PreE7B6CharacterOnlyQuotientData.ofAxes hZmud D.axis

end PrimitiveAffineDegreeTwoSixPairCharacterOnlyFiniteRowData

namespace PrimitiveAffineDegreeTwoSixPairCharacterOnlyOwnerData

variable {p : PreE7PairActionClass 6}
  (D : PrimitiveAffineDegreeTwoSixPairCharacterOnlyOwnerData p)

/-- The common character-only construction of a complete six-pair owner
row. -/
noncomputable def toOwnerRow : PrimitiveAffineDegreeTwoSixPairOwnerRow p where
  literal := D.literal
  pointRelabel := D.pointRelabel
  correspondence := D.correspondence
  source := D.quotients.toB6ActionCertificate (preE7PairFrame 6 p)

end PrimitiveAffineDegreeTwoSixPairCharacterOnlyOwnerData

namespace PrimitiveAffineDegreeTwoSixPairCharacterOnlyFiniteRowData

variable {p : PreE7PairActionClass 6}
  (D : PrimitiveAffineDegreeTwoSixPairCharacterOnlyFiniteRowData p)

/-- The checked finite row and the published Zmud theorem produce the owner
row expected by the 182-row catalogue dispatcher. -/
noncomputable def toOwnerRow
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    PrimitiveAffineDegreeTwoSixPairOwnerRow p :=
  (D.toOwnerData hZmud).toOwnerRow

end PrimitiveAffineDegreeTwoSixPairCharacterOnlyFiniteRowData

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
