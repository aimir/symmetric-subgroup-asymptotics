import SymmetricSubgroupAsymptotics.SmallAffineCanonicalRepresentatives
import SymmetricSubgroupAsymptotics.StandardThreeLinearChiefCertificates
import SymmetricSubgroupAsymptotics.PrimitiveSixteenNonsolubleChiefCertificates
import SymmetricSubgroupAsymptotics.SmallAffineChiefCertificateNonsolvable
import SymmetricSubgroupAsymptotics.BurnsideTwoPrimeSolvability
import SymmetricSubgroupAsymptotics.ProjectiveThreeSimplicity

/-! Fixed small-affine representative facts do not require any catalogue
coverage. This factors the existing checked representative proof away
from its old dependent full-locator packaging. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
namespace SmallAffineCanonicalFixedFacts
open SmallAffineCanonicalRepresentatives

structure Certificate (r : SmallAffineCatalogueRow) where
  card_eq : Nat.card (representative r).Carrier=r.complementOrder
  solvable_iff : IsSolvable (representative r).Carrier ↔ r.nonsoluble=false
  nonsolubleCore : r.nonsoluble=true → SmallAffineChiefOrderSavingCertificate
    (representative r).Carrier r.nonsolubleAbelianCap

private def solubleRow (r : SmallAffineCatalogueRow)
    (hc : Nat.card (representative r).Carrier = r.complementOrder)
    (hs : IsSolvable (representative r).Carrier) (hr : r.nonsoluble = false) :
    Certificate r where
  card_eq := hc
  solvable_iff := ⟨fun _ => hr, fun _ => hs⟩
  nonsolubleCore hn := by rw [hr] at hn; contradiction

private def nonsolubleRow (r : SmallAffineCatalogueRow)
    (hc : Nat.card (representative r).Carrier = r.complementOrder)
    (C : SmallAffineChiefOrderSavingCertificate (representative r).Carrier
      r.nonsolubleAbelianCap) (hr : r.nonsoluble = true) :
    Certificate r where
  card_eq := hc
  solvable_iff := by
    rw [hr]
    exact iff_of_false C.not_isSolvable (by decide)
  nonsolubleCore _ := C

/-- All 34 representative facts. Burnside is used only in its classical
order form; the three semilinear exceptions are proved directly. -/
def receipt
    (hSimple : StandardThreeDimensionalLinearGroups.PublishedSimplicity)
    (hBurnside : PublishedBurnsideTwoPrimeSolvabilityInput) :
    ∀ r : SmallAffineCatalogueRow,Certificate r := by
  intro r
  apply Classical.choice
  cases r with
  | degreeEight i =>
    fin_cases i
    · exact ⟨solubleRow (.degreeEight 0) SmallAffineSoluble8Row1Order.card
        (SmallAffineTwoPrimeOrders.certificate hBurnside 0 SmallAffineSoluble8Row1Order.card).solvable rfl⟩
    · exact ⟨solubleRow (.degreeEight 1) SmallAffineSoluble8Row2Order.card
        (SmallAffineTwoPrimeOrders.certificate hBurnside 1 SmallAffineSoluble8Row2Order.card).solvable rfl⟩
    · exact ⟨nonsolubleRow (.degreeEight 2) StandardThreeDimensionalLinearGroups.card_GL_two
        (StandardThreeDimensionalLinearGroups.generalTwoCertificate hSimple) rfl⟩
  | degreeSixteen i =>
    fin_cases i
    · exact ⟨solubleRow (.degreeSixteen 0) SmallAffineSoluble16Row1Order.card
        (SmallAffineTwoPrimeOrders.certificate hBurnside 2 SmallAffineSoluble16Row1Order.card).solvable rfl⟩
    · exact ⟨solubleRow (.degreeSixteen 1) SmallAffineSoluble16Row2Order.card
        (SmallAffineTwoPrimeOrders.certificate hBurnside 3 SmallAffineSoluble16Row2Order.card).solvable rfl⟩
    · exact ⟨solubleRow (.degreeSixteen 2) SmallAffineSoluble16Row3Order.card
        (SmallAffineTwoPrimeOrders.certificate hBurnside 4 SmallAffineSoluble16Row3Order.card).solvable rfl⟩
    · exact ⟨solubleRow (.degreeSixteen 3) SmallAffineSoluble16Row4Order.card
        (SmallAffineTwoPrimeOrders.certificate hBurnside 5 SmallAffineSoluble16Row4Order.card).solvable rfl⟩
    · exact ⟨solubleRow (.degreeSixteen 4) SmallAffineSoluble16Row5Order.card
        (SmallAffineTwoPrimeOrders.certificate hBurnside 6 SmallAffineSoluble16Row5Order.card).solvable rfl⟩
    · exact ⟨solubleRow (.degreeSixteen 5) SmallAffineSoluble16Row6Order.card
        SmallAffineSoluble16Row6Order.soluble rfl⟩
    · exact ⟨solubleRow (.degreeSixteen 6) SmallAffineSoluble16Row7Order.card
        (SmallAffineTwoPrimeOrders.certificate hBurnside 7 SmallAffineSoluble16Row7Order.card).solvable rfl⟩
    · exact ⟨solubleRow (.degreeSixteen 7) SmallAffineSoluble16Row8Order.card
        (SmallAffineTwoPrimeOrders.certificate hBurnside 8 SmallAffineSoluble16Row8Order.card).solvable rfl⟩
    · exact ⟨solubleRow (.degreeSixteen 8) SmallAffineSoluble16Row9Order.card
        SmallAffineSoluble16Row9Order.soluble rfl⟩
    · exact ⟨solubleRow (.degreeSixteen 9) SmallAffineSoluble16Row10Order.card
        (SmallAffineTwoPrimeOrders.certificate hBurnside 9 SmallAffineSoluble16Row10Order.card).solvable rfl⟩
    · exact ⟨nonsolubleRow (.degreeSixteen 10) PrimitiveSixteenRows11And20ChiefBounds.card11
        (PrimitiveSixteenNonsolubleChiefCertificates.row11) rfl⟩
    · exact ⟨nonsolubleRow (.degreeSixteen 11) PrimitiveSixteenRows12And14KernelOrders.card12
        (PrimitiveSixteenNonsolubleChiefCertificates.row12) rfl⟩
    · exact ⟨nonsolubleRow (.degreeSixteen 12) PrimitiveSixteenRows13And15ChiefBounds.card13
        (PrimitiveSixteenNonsolubleChiefCertificates.row13) rfl⟩
    · exact ⟨nonsolubleRow (.degreeSixteen 13) PrimitiveSixteenRows12And14KernelOrders.card14
        (PrimitiveSixteenNonsolubleChiefCertificates.row14) rfl⟩
    · exact ⟨nonsolubleRow (.degreeSixteen 14) PrimitiveSixteenRows13And15ChiefBounds.card15
        (PrimitiveSixteenNonsolubleChiefCertificates.row15) rfl⟩
    · exact ⟨nonsolubleRow (.degreeSixteen 15) PrimitiveSixteenRows16And17ChiefBounds.card16
        (PrimitiveSixteenNonsolubleChiefCertificates.row16) rfl⟩
    · exact ⟨nonsolubleRow (.degreeSixteen 16) PrimitiveSixteenRows16And17ChiefBounds.card17
        (PrimitiveSixteenNonsolubleChiefCertificates.row17) rfl⟩
    · exact ⟨nonsolubleRow (.degreeSixteen 17) PrimitiveSixteenRows18And19ChiefBounds.card18
        (PrimitiveSixteenNonsolubleChiefCertificates.row18) rfl⟩
    · exact ⟨nonsolubleRow (.degreeSixteen 18) PrimitiveSixteenRows18And19ChiefBounds.card19
        (PrimitiveSixteenNonsolubleChiefCertificates.row19) rfl⟩
    · exact ⟨nonsolubleRow (.degreeSixteen 19) PrimitiveSixteenRows11And20ChiefBounds.card20
        (PrimitiveSixteenNonsolubleChiefCertificates.row20) rfl⟩
  | degreeTwentySeven i =>
    fin_cases i
    · exact ⟨solubleRow (.degreeTwentySeven 0) SmallAffineSoluble27Row1Order.card
        (SmallAffineTwoPrimeOrders.certificate hBurnside 10 SmallAffineSoluble27Row1Order.card).solvable rfl⟩
    · exact ⟨solubleRow (.degreeTwentySeven 1) SmallAffineSoluble27Row2Order.card
        (SmallAffineTwoPrimeOrders.certificate hBurnside 11 SmallAffineSoluble27Row2Order.card).solvable rfl⟩
    · exact ⟨solubleRow (.degreeTwentySeven 2) SmallAffineSoluble27Row3Order.card
        (SmallAffineTwoPrimeOrders.certificate hBurnside 12 SmallAffineSoluble27Row3Order.card).solvable rfl⟩
    · exact ⟨solubleRow (.degreeTwentySeven 3) SmallAffineSoluble27Row4Order.card
        (SmallAffineTwoPrimeOrders.certificate hBurnside 13 SmallAffineSoluble27Row4Order.card).solvable rfl⟩
    · exact ⟨solubleRow (.degreeTwentySeven 4) SmallAffineSoluble27Row5Order.card
        (SmallAffineTwoPrimeOrders.certificate hBurnside 14 SmallAffineSoluble27Row5Order.card).solvable rfl⟩
    · exact ⟨solubleRow (.degreeTwentySeven 5) SmallAffineSoluble27Row6Order.card
        (SmallAffineTwoPrimeOrders.certificate hBurnside 15 SmallAffineSoluble27Row6Order.card).solvable rfl⟩
    · exact ⟨solubleRow (.degreeTwentySeven 6) SmallAffineSoluble27Row7Order.card
        (SmallAffineTwoPrimeOrders.certificate hBurnside 16 SmallAffineSoluble27Row7Order.card).solvable rfl⟩
    · exact ⟨solubleRow (.degreeTwentySeven 7) SmallAffineSoluble27Row8Order.card
        (SmallAffineTwoPrimeOrders.certificate hBurnside 17 SmallAffineSoluble27Row8Order.card).solvable rfl⟩
    · exact ⟨solubleRow (.degreeTwentySeven 8) SmallAffineSoluble27Row9Order.card
        SmallAffineSoluble27Row9Order.soluble rfl⟩
    · exact ⟨nonsolubleRow (.degreeTwentySeven 9) StandardThreeDimensionalLinearGroups.card_SL_three
        (StandardThreeDimensionalLinearGroups.specialThreeCertificate hSimple) rfl⟩
    · exact ⟨nonsolubleRow (.degreeTwentySeven 10) StandardThreeDimensionalLinearGroups.card_GL_three
        (StandardThreeDimensionalLinearGroups.generalThreeCertificate hSimple) rfl⟩

/-- The fixed receipt is unconditional; no catalogue-completeness field
is supplied or hidden in its construction. -/
def proved : ∀ r : SmallAffineCatalogueRow,Certificate r :=
  receipt ProjectiveThreeSimplicity.proved burnsideTwoPrimeSolvability

end SmallAffineCanonicalFixedFacts
end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
