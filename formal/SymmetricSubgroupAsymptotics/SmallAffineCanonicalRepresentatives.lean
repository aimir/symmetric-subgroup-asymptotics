import SymmetricSubgroupAsymptotics.PrimitiveAffineSmallPublishedCatalogue
import SymmetricSubgroupAsymptotics.StandardThreeDimensionalLinearGroups
import SymmetricSubgroupAsymptotics.SmallAffineSoluble8Row1Order
import SymmetricSubgroupAsymptotics.SmallAffineSoluble8Row2Order
import SymmetricSubgroupAsymptotics.SmallAffineSoluble16Row1Order
import SymmetricSubgroupAsymptotics.SmallAffineSoluble16Row2Order
import SymmetricSubgroupAsymptotics.SmallAffineSoluble16Row3Order
import SymmetricSubgroupAsymptotics.SmallAffineSoluble16Row4Order
import SymmetricSubgroupAsymptotics.SmallAffineSoluble16Row5Order
import SymmetricSubgroupAsymptotics.SmallAffineSoluble16Row6Order
import SymmetricSubgroupAsymptotics.SmallAffineSoluble16Row7Order
import SymmetricSubgroupAsymptotics.SmallAffineSoluble16Row8Order
import SymmetricSubgroupAsymptotics.SmallAffineSoluble16Row9Order
import SymmetricSubgroupAsymptotics.SmallAffineSoluble16Row10Order
import SymmetricSubgroupAsymptotics.SmallAffineSoluble27Row1Order
import SymmetricSubgroupAsymptotics.SmallAffineSoluble27Row2Order
import SymmetricSubgroupAsymptotics.SmallAffineSoluble27Row3Order
import SymmetricSubgroupAsymptotics.SmallAffineSoluble27Row4Order
import SymmetricSubgroupAsymptotics.SmallAffineSoluble27Row5Order
import SymmetricSubgroupAsymptotics.SmallAffineSoluble27Row6Order
import SymmetricSubgroupAsymptotics.SmallAffineSoluble27Row7Order
import SymmetricSubgroupAsymptotics.SmallAffineSoluble27Row8Order
import SymmetricSubgroupAsymptotics.SmallAffineSoluble27Row9Order
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRows11And20Complements
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRows12And14Complements
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRows13And15Complements
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRows16And17Complements
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRows18And19Complements

/-! Fixed representatives for the 34 small affine complement rows.
The soluble groups retain the literal point-1-fixing generators of the
pinned primitive data. The ten nonsoluble binary complements retain the
existing exact linear charts. The remaining three are the standard named
GL3(F2), SL3(F3), GL3(F3) models in the published classification.

The only classification premise below is isomorphism coverage of this
fixed list; it carries no order, solubility, chief bound or certificate.
All representative properties are proved in separate modules.
-/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
namespace SmallAffineCanonicalRepresentatives

def degreeEight : Fin 3 → SmallAffineCatalogueRepresentative :=
  ![{ Carrier := SmallAffineSoluble8Row1Order.R },
    { Carrier := SmallAffineSoluble8Row2Order.R },
    { Carrier := StandardThreeDimensionalLinearGroups.GeneralThree 2 }]

def degreeSixteen : Fin 20 → SmallAffineCatalogueRepresentative :=
  ![{ Carrier := SmallAffineSoluble16Row1Order.R },
    { Carrier := SmallAffineSoluble16Row2Order.R },
    { Carrier := SmallAffineSoluble16Row3Order.R },
    { Carrier := SmallAffineSoluble16Row4Order.R },
    { Carrier := SmallAffineSoluble16Row5Order.R },
    { Carrier := SmallAffineSoluble16Row6Order.R },
    { Carrier := SmallAffineSoluble16Row7Order.R },
    { Carrier := SmallAffineSoluble16Row8Order.R },
    { Carrier := SmallAffineSoluble16Row9Order.R },
    { Carrier := SmallAffineSoluble16Row10Order.R },
    { Carrier := PrimitiveAffineDegreeTwoPrimitiveSixteenRows11And20Complements.R11 },
    { Carrier := PrimitiveAffineDegreeTwoPrimitiveSixteenRows12And14Complements.R12 },
    { Carrier := PrimitiveAffineDegreeTwoPrimitiveSixteenRows13And15Complements.R13 },
    { Carrier := PrimitiveAffineDegreeTwoPrimitiveSixteenRows12And14Complements.R14 },
    { Carrier := PrimitiveAffineDegreeTwoPrimitiveSixteenRows13And15Complements.R15 },
    { Carrier := PrimitiveAffineDegreeTwoPrimitiveSixteenRows16And17Complements.R16 },
    { Carrier := PrimitiveAffineDegreeTwoPrimitiveSixteenRows16And17Complements.R17 },
    { Carrier := PrimitiveAffineDegreeTwoPrimitiveSixteenRows18And19Complements.R18 },
    { Carrier := PrimitiveAffineDegreeTwoPrimitiveSixteenRows18And19Complements.R19 },
    { Carrier := PrimitiveAffineDegreeTwoPrimitiveSixteenRows11And20Complements.R20 }]

def degreeTwentySeven : Fin 11 → SmallAffineCatalogueRepresentative :=
  ![{ Carrier := SmallAffineSoluble27Row1Order.R },
    { Carrier := SmallAffineSoluble27Row2Order.R },
    { Carrier := SmallAffineSoluble27Row3Order.R },
    { Carrier := SmallAffineSoluble27Row4Order.R },
    { Carrier := SmallAffineSoluble27Row5Order.R },
    { Carrier := SmallAffineSoluble27Row6Order.R },
    { Carrier := SmallAffineSoluble27Row7Order.R },
    { Carrier := SmallAffineSoluble27Row8Order.R },
    { Carrier := SmallAffineSoluble27Row9Order.R },
    { Carrier := StandardThreeDimensionalLinearGroups.SpecialThree 3 },
    { Carrier := StandardThreeDimensionalLinearGroups.GeneralThree 3 }]

def representative : SmallAffineCatalogueRow → SmallAffineCatalogueRepresentative
  | .degreeEight i => degreeEight i
  | .degreeSixteen i => degreeSixteen i
  | .degreeTwentySeven i => degreeTwentySeven i

/-- Bare Roney--Dougal--Unger/PrimGrp coverage of the fixed named models.
No representative certificate or numerical consequence is an input. -/
def PublishedClassification : Prop :=
  ∀ {G Ω : Type} [Group G] [Finite G] [Fintype Ω]
    [MulAction G Ω] [FaithfulSMul G Ω],
    MulAction.IsPreprimitive G Ω →
    (P : PrimitiveAffineProfile G Ω) → (x : Ω) →
    (Nat.card Ω = 8 ∨ Nat.card Ω = 16 ∨ Nat.card Ω = 27) →
    ∃ r : SmallAffineCatalogueRow,
      r.degree = Nat.card Ω ∧
      Nonempty (P.complement x ≃* (representative r).Carrier)

def locator (h : PublishedClassification) : PublishedSmallAffineCatalogueLocator where
  representative := representative
  locate := h

end SmallAffineCanonicalRepresentatives
end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
