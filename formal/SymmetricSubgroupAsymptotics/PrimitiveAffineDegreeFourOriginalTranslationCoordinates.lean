import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourA4OriginalGroupChart
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourS4OriginalGroupChart
import SymmetricSubgroupAsymptotics.BinaryFourOriginalScalarCharts
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourPairFrameSource

/-! The actual original correlated translation module in the canonical
A4/S4 eight-coordinate action. All local maps and scalar transport are
constructed internally from the original affine profile. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]

local instance : Fact P.p.Prime := (chart block P).primeFact

namespace DegreeFourA4OriginalPointChart

variable (C : DegreeFourA4OriginalPointChart block)

def translationCoordinates
    (hr : Nat.card block.Fibre = 4) (hD : degreeFourTernaryCore block P = ⊥) :
    (elementaryChart block P).quotientRepresentation.ρ.IntertwiningMap
      (BinaryFourOriginalScalarCharts.a4Frame (degreeFour_profilePrime_eq_two block P hr)
        ((groupEquiv (block := block) (P := P) (C := C) hr hD))) := by
  let i := C.sourcePoint
  let H := fullFrameInducedStabilizer block P i
  let theta := (binaryAffineLocalLinearRepresentation block P).ρ
  let f := binaryAffineStabilizerComponent block P i
  have hdim : Module.finrank (ZMod P.p) (chart block P).V = 2 := by
    change (chart block P).d = 2
    exact (degreeFour_translationDimension block P hr).2
  let e := BinaryFourOriginalScalarCharts.a4Chart
    (degreeFour_profilePrime_eq_two block P hr) H ((groupEquiv (block := block) (P := P) (C := C) hr hD))
    ((stabilizerEquiv (block := block) (P := P) (C := C) hr hD)) ((stabilizerEquiv_commutes (block := block) (P := P) (C := C) hr hD))
    f (binaryAffineStabilizerComponent_surjective block P i)
    (degreeFourZeroCoreTopStabilizerLocalTarget_card block P hr)
    theta hdim (binaryAffineLocalLinearRepresentation_injective block P)
  exact e.toIntertwiningMap.comp (translationSubmoduleToCoinduced block P i)

theorem translationCoordinates_injective
    (hr : Nat.card block.Fibre = 4) (hD : degreeFourTernaryCore block P = ⊥) :
    Function.Injective ((translationCoordinates (block := block) (P := P) (C := C) hr hD)) := by
  let i := C.sourcePoint
  let H := fullFrameInducedStabilizer block P i
  let theta := (binaryAffineLocalLinearRepresentation block P).ρ
  let f := binaryAffineStabilizerComponent block P i
  have hdim : Module.finrank (ZMod P.p) (chart block P).V = 2 := by
    change (chart block P).d = 2
    exact (degreeFour_translationDimension block P hr).2
  let e := BinaryFourOriginalScalarCharts.a4Chart
    (degreeFour_profilePrime_eq_two block P hr) H ((groupEquiv (block := block) (P := P) (C := C) hr hD))
    ((stabilizerEquiv (block := block) (P := P) (C := C) hr hD)) ((stabilizerEquiv_commutes (block := block) (P := P) (C := C) hr hD))
    f (binaryAffineStabilizerComponent_surjective block P i)
    (degreeFourZeroCoreTopStabilizerLocalTarget_card block P hr)
    theta hdim (binaryAffineLocalLinearRepresentation_injective block P)
  change Function.Injective (fun x =>
    e.toLinearEquiv (translationSubmoduleToCoinduced block P i x))
  exact e.toLinearEquiv.injective.comp
    (translationSubmoduleToCoinduced_injective block P i)

end DegreeFourA4OriginalPointChart

namespace DegreeFourS4OriginalPointChart

variable (C : DegreeFourS4OriginalPointChart block)

def translationCoordinates
    (hr : Nat.card block.Fibre = 4) (hD : degreeFourTernaryCore block P = ⊥) :
    (elementaryChart block P).quotientRepresentation.ρ.IntertwiningMap
      (BinaryFourOriginalScalarCharts.s4Frame (degreeFour_profilePrime_eq_two block P hr)
        ((groupEquiv (block := block) (P := P) (C := C) hr hD))) := by
  let i := C.sourcePoint
  let H := fullFrameInducedStabilizer block P i
  let theta := (binaryAffineLocalLinearRepresentation block P).ρ
  let f := binaryAffineStabilizerComponent block P i
  have hdim : Module.finrank (ZMod P.p) (chart block P).V = 2 := by
    change (chart block P).d = 2
    exact (degreeFour_translationDimension block P hr).2
  let e := BinaryFourOriginalScalarCharts.s4Chart
    (degreeFour_profilePrime_eq_two block P hr) H ((groupEquiv (block := block) (P := P) (C := C) hr hD))
    ((stabilizerEquiv (block := block) (P := P) (C := C) hr hD)) ((stabilizerEquiv_commutes (block := block) (P := P) (C := C) hr hD))
    f (binaryAffineStabilizerComponent_surjective block P i)
    (degreeFourZeroCoreTopStabilizerLocalTarget_card block P hr)
    theta hdim (binaryAffineLocalLinearRepresentation_injective block P)
  exact e.toIntertwiningMap.comp (translationSubmoduleToCoinduced block P i)

theorem translationCoordinates_injective
    (hr : Nat.card block.Fibre = 4) (hD : degreeFourTernaryCore block P = ⊥) :
    Function.Injective ((translationCoordinates (block := block) (P := P) (C := C) hr hD)) := by
  let i := C.sourcePoint
  let H := fullFrameInducedStabilizer block P i
  let theta := (binaryAffineLocalLinearRepresentation block P).ρ
  let f := binaryAffineStabilizerComponent block P i
  have hdim : Module.finrank (ZMod P.p) (chart block P).V = 2 := by
    change (chart block P).d = 2
    exact (degreeFour_translationDimension block P hr).2
  let e := BinaryFourOriginalScalarCharts.s4Chart
    (degreeFour_profilePrime_eq_two block P hr) H ((groupEquiv (block := block) (P := P) (C := C) hr hD))
    ((stabilizerEquiv (block := block) (P := P) (C := C) hr hD)) ((stabilizerEquiv_commutes (block := block) (P := P) (C := C) hr hD))
    f (binaryAffineStabilizerComponent_surjective block P i)
    (degreeFourZeroCoreTopStabilizerLocalTarget_card block P hr)
    theta hdim (binaryAffineLocalLinearRepresentation_injective block P)
  change Function.Injective (fun x =>
    e.toLinearEquiv (translationSubmoduleToCoinduced block P i x))
  exact e.toLinearEquiv.injective.comp
    (translationSubmoduleToCoinduced_injective block P i)

end DegreeFourS4OriginalPointChart

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics

end
