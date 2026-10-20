import SymmetricSubgroupAsymptotics.AlternatingSymmetricChiefCertificateFactories
import SymmetricSubgroupAsymptotics.PrimitiveSixteenRows11And20ChiefBounds
import SymmetricSubgroupAsymptotics.PrimitiveSixteenRows13And15ChiefBounds
import SymmetricSubgroupAsymptotics.PrimitiveSixteenRows16And17ChiefBounds
import SymmetricSubgroupAsymptotics.PrimitiveSixteenRows18And19ChiefBounds
import SymmetricSubgroupAsymptotics.PrimitiveSixteenRows12And14KernelOrders

/-! Ten structural receipts on the unchanged actual degree16 complement
carriers. Only explicit source maps, their proved faithfulness, and
projective scalar-kernel order3 are used. The scalar cases are quotient
receipts and make no unique-core claim in the original complement. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
namespace PrimitiveSixteenNonsolubleChiefCertificates
open AlternatingSymmetricChiefCertificateFactories

private abbrev C11 := PrimitiveAffineDegreeTwoPrimitiveSixteenRows11And20Complements.R11
private abbrev C12 := PrimitiveAffineDegreeTwoPrimitiveSixteenRows12And14Complements.R12
private abbrev C13 := PrimitiveAffineDegreeTwoPrimitiveSixteenRows13And15Complements.R13
private abbrev C14 := PrimitiveAffineDegreeTwoPrimitiveSixteenRows12And14Complements.R14
private abbrev C15 := PrimitiveAffineDegreeTwoPrimitiveSixteenRows13And15Complements.R15
private abbrev C16 := PrimitiveAffineDegreeTwoPrimitiveSixteenRows16And17Complements.R16
private abbrev C17 := PrimitiveAffineDegreeTwoPrimitiveSixteenRows16And17Complements.R17
private abbrev C18 := PrimitiveAffineDegreeTwoPrimitiveSixteenRows18And19Complements.R18
private abbrev C19 := PrimitiveAffineDegreeTwoPrimitiveSixteenRows18And19Complements.R19
private abbrev C20 := PrimitiveAffineDegreeTwoPrimitiveSixteenRows11And20Complements.R20

def row11 : SmallAffineChiefOrderSavingCertificate C11 0 :=
  alternatingEquiv 8 (by decide) PrimitiveSixteenRows11And20ChiefBounds.complementEquiv11.symm

def row12 : SmallAffineChiefOrderSavingCertificate C12 2 := by
  apply symmetricQuotient 5 (by decide) 2
    PrimitiveAffineDegreeTwoPrimitiveSixteenRows12And14Complements.projective12
    (MonoidHom.range_eq_top.mp
      PrimitiveAffineDegreeTwoPrimitiveSixteenRows12And14Complements.projective12_range)
  have ha : Nat.card (alternatingGroup (Fin 5))=60 := by
    simpa only [Nat.card_fin] using (nat_card_alternatingGroup (α := Fin 5))
  rw [PrimitiveSixteenRows12And14KernelOrders.card12,ha]
  decide +kernel

def row13 : SmallAffineChiefOrderSavingCertificate C13 1 :=
  symmetricEquiv 5 (by decide) PrimitiveSixteenRows13And15ChiefBounds.complementEquiv13.symm

def row14 : SmallAffineChiefOrderSavingCertificate C14 1 := by
  apply alternatingQuotient 5 (by decide) 1
    PrimitiveAffineDegreeTwoPrimitiveSixteenRows12And14Complements.evenProjective14
    PrimitiveAffineDegreeTwoPrimitiveSixteenRows12And14Complements.evenProjective14_surjective
  have ha : Nat.card (alternatingGroup (Fin 5))=60 := by
    simpa only [Nat.card_fin] using (nat_card_alternatingGroup (α := Fin 5))
  rw [PrimitiveSixteenRows12And14KernelOrders.card14,ha]
  decide +kernel

def row15 : SmallAffineChiefOrderSavingCertificate C15 0 :=
  alternatingEquiv 5 (by decide) PrimitiveSixteenRows13And15ChiefBounds.complementEquiv15.symm

def row16 : SmallAffineChiefOrderSavingCertificate C16 1 :=
  symmetricEquiv 6 (by decide) PrimitiveSixteenRows16And17ChiefBounds.complementEquiv16.symm

def row17 : SmallAffineChiefOrderSavingCertificate C17 0 :=
  alternatingEquiv 6 (by decide) PrimitiveSixteenRows16And17ChiefBounds.complementEquiv17.symm

def row18 : SmallAffineChiefOrderSavingCertificate C18 1 :=
  symmetricEquiv 5 (by decide) PrimitiveSixteenRows18And19ChiefBounds.complementEquiv18.symm

def row19 : SmallAffineChiefOrderSavingCertificate C19 0 :=
  alternatingEquiv 5 (by decide) PrimitiveSixteenRows18And19ChiefBounds.complementEquiv19.symm

def row20 : SmallAffineChiefOrderSavingCertificate C20 0 :=
  alternatingEquiv 7 (by decide) PrimitiveSixteenRows11And20ChiefBounds.complementEquiv20.symm

end PrimitiveSixteenNonsolubleChiefCertificates
end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
