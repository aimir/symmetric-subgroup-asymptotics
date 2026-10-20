import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairAction025RegularPilot
import SymmetricSubgroupAsymptotics.CubicRegularLiteralFaithfulness
import SymmetricSubgroupAsymptotics.CubicAllNormalB6Transport
import SymmetricSubgroupAsymptotics.BinaryPairFrameGenerators

/-! Exact original action25-to-retained-subgroup equivalence and original
six-pair chart, checked from five literal generators only. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoSixPairAction025RegularOriginal
open PrimitiveAffineDegreeTwoSixPairAction025RegularPilot
open BinaryThreeQuartetCubicImageSocles
open LinearSemidirectCoprimeSocleBounds LinearSemidirectSubgroupKernelChart

private def f : K →* Equiv.Perm (Fin 12) :=
  (literalAction pointChart).comp K.subtype

def toOriginal : K →* Original :=
  GeneratedLiteralImage.toTop f (closureGenerators lifted) generators (Equiv.refl _)
    (closureGenerators_full lifted) binding

theorem toOriginal_surjective : Function.Surjective toOriginal :=
  GeneratedLiteralImage.toTop_surjective f (closureGenerators lifted) generators (Equiv.refl _)
    (closureGenerators_full lifted) binding

theorem toOriginal_injective : Function.Injective toOriginal := by
  intro x y he
  apply Subtype.ext
  apply regular_literalAction_injective pointChart
  exact congrArg Subtype.val he

def originalEquiv : Original ≃* K :=
  (MulEquiv.ofBijective toOriginal ⟨toOriginal_injective,toOriginal_surjective⟩).symm

def pairPoints : Fin 6 × ZMod 2 ≃ Fin 12 :=
  (Equiv.prodCongr (Equiv.refl (Fin 6)) (ZMod.finEquiv 2).symm.toEquiv).trans finProdFinEquiv

private def pairTop0 : Equiv.Perm (Fin 6) where
  toFun x := (#[0, 1, 2, 3, 4, 5] : Array (Fin 6))[x.val]!
  invFun x := (#[0, 1, 2, 3, 4, 5] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def pairTop1 : Equiv.Perm (Fin 6) where
  toFun x := (#[0, 1, 2, 3, 4, 5] : Array (Fin 6))[x.val]!
  invFun x := (#[0, 1, 2, 3, 4, 5] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def pairTop2 : Equiv.Perm (Fin 6) where
  toFun x := (#[5, 3, 1, 2, 0, 4] : Array (Fin 6))[x.val]!
  invFun x := (#[4, 2, 3, 1, 5, 0] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def pairTop3 : Equiv.Perm (Fin 6) where
  toFun x := (#[0, 4, 5, 3, 1, 2] : Array (Fin 6))[x.val]!
  invFun x := (#[0, 4, 5, 3, 1, 2] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def pairTop4 : Equiv.Perm (Fin 6) where
  toFun x := (#[3, 1, 5, 0, 4, 2] : Array (Fin 6))[x.val]!
  invFun x := (#[3, 1, 5, 0, 4, 2] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pairTops : Fin 5 → Equiv.Perm (Fin 6) :=
  ![pairTop0,pairTop1,pairTop2,pairTop3,pairTop4]

private theorem pair_binding : ∀ j,
    BinaryPairFrame.Preserves pairPoints (generators j) (pairTops j) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

def pairFrame : BinaryPairFrame Original (Fin 6) :=
  BinaryPairFrame.ofGenerators pairPoints generators pairTops pair_binding

/-- All actual normal quotients of the original action, with no census. -/
def actionCertificate (hKP : KovacsPraegerAbelianizationBound) :
    Non2UnipotentPrefixFiniteMenu.PreE7B6ActionCertificate Original :=
  CubicAllNormalB6Transport.originalActionCertificate
    (top := projection linear K)
    (A := CubicRegularSubgroupKernelCoordinates.moduleRep K projection_surjective)
    (E := CubicRegularSubgroupKernelCoordinates.originalKernelChart K projection_surjective)
    originalEquiv projection_surjective
    (CubicRegularSubgroupKernelCoordinates.coordinates K projection_surjective)
    scalar_nonzero hKP pairFrame

end PrimitiveAffineDegreeTwoSixPairAction025RegularOriginal
end SymmetricSubgroupAsymptotics
end
