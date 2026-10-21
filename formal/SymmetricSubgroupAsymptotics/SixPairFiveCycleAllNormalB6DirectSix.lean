import SymmetricSubgroupAsymptotics.SixPairFiveCycleAllNormalB6
import SymmetricSubgroupAsymptotics.SixPairPrimitiveAllNormalB6DirectSix

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.SixPairFiveCycleAllNormalB6.DirectSix
open BinarySixPointFiveCyclePolynomial Non2UnipotentPrefixFiniteMenu

variable {U : Subgroup (Equiv.Perm (Fin 12))} (F : BinaryPairFrame U (Fin 6))

def actionCertificate (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (a b : U) (q : Equiv.Perm (Fin 6))
    (ha : F.top a=SixPointFiveCyclePrimitive.cycle) (hb : F.top b=q)
    (hmoves : q 5≠5)
    (hmatrix : ∀ i x : Fin 6,
      actualOperator representation SixPointFiveCyclePrimitive.cycle q (Pi.single i 1) x=
        operator 0 (Pi.single i 1) x) : PreE7B6ActionCertificate U := by
  have haction (g : U) (p : Equiv.Perm (Fin 6)) (hg : F.top g=p) :
      permutationFunctionRepresentation (ZMod 2) F.top.range (Fin 6)
        (F.top.rangeRestrict g)=representation p := by
    apply LinearMap.ext
    intro v
    funext x
    change v ((F.top g)⁻¹ x)=v (p⁻¹ x)
    rw [hg]
  have hu : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) F.top.range (Fin 6)) 1 :=
    uniform_of_actions 0 _ (F.top.rangeRestrict a) (F.top.rangeRestrict b)
      SixPointFiveCyclePrimitive.cycle q (haction a _ ha) (haction b _ hb) hmatrix
  letI : MulAction.IsPreprimitive F.top.range (Fin 6) :=
    SixPointFiveCyclePrimitive.preprimitive F.top.range
      (F.top.rangeRestrict a) (F.top.rangeRestrict b) ha
      (by change F.top b 5≠5; rwa [hb])
  exact SixPairPrimitiveAllNormalB6.DirectSix.actionCertificate F hindex hZmud hu


end SymmetricSubgroupAsymptotics.SixPairFiveCycleAllNormalB6.DirectSix
