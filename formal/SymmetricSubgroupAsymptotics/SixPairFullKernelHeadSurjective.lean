import SymmetricSubgroupAsymptotics.SixPairCoarseWreathHeadKernel
import SymmetricSubgroupAsymptotics.TwoBinaryThreeWreathKernel

/-! Full physical independence surjects onto the SAME actual head base.
No normal quotient is assigned an independent transitive action. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SixPairFullKernelHeadSurjective
open SixPairCoarseWreathHead BinaryTwoLayerLocalHead

variable {X I : Type} {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U I)
  (E : ProductBlockFrame F.top.range (Fin 3) (ZMod 2))

def headKernel : (SixPairNestedTopFrames.nestedFrame F E).top.ker →*
    (TwoBinaryThreeWreathKernel.top
      (SixPairNestedTopFrames.nestedFrame F E).top.range).ker where
  toFun k := ⟨headHom F E k.val,Subtype.ext k.property⟩
  map_one' := Subtype.ext (headHom F E).map_one
  map_mul' a b := Subtype.ext ((headHom F E).map_mul a.val b.val)

theorem head_base_surjective
    (hfull : SixPairIndependentKernelNormalCommutators.Independent F E) :
    Function.Surjective
      ((TwoBinaryThreeWreathKernel.base
        (SixPairNestedTopFrames.nestedFrame F E).top.range).comp (headKernel F E)) := by
  intro v
  choose a ha hp using fun j : Fin 3 => head_surjective (v j).toAdd
  obtain ⟨k,hk⟩ := hfull a ha
  refine ⟨k,?_⟩
  funext j
  change Multiplicative.ofAdd
    (head (((SixPairNestedTopFrames.nestedFrame F E).wreathEmbedding k.val).left j))=v j
  rw [local_of_kernel F E k j,hk j,hp j]
  rfl

end SymmetricSubgroupAsymptotics.SixPairFullKernelHeadSurjective
