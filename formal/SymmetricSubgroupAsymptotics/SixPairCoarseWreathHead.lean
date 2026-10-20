import SymmetricSubgroupAsymptotics.BinaryTwoLayerLocalHead
import SymmetricSubgroupAsymptotics.SixPairFullKernelCenter
import SymmetricSubgroupAsymptotics.ProductBlockFrameWreathEmbedding

/-! Two head bits on every ACTUAL four-point fibre, together with the SAME
actual coarse top. This is a homomorphism from the original group, not a
new transitive action assigned to a quotient. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SixPairCoarseWreathHead
open BinaryTwoLayerLocalClassTwo BinaryTwoLayerLocalHead

variable {X I J : Type} {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U I) (E : ProductBlockFrame F.top.range J (ZMod 2))

/-- The actual local transition between source and destination fibres
preserves their two original physical pairs. -/
theorem local_preserves (u : U) (j : J) :
    Preserves (((SixPairNestedTopFrames.nestedFrame F E).wreathEmbedding u).left j) := by
  let C := SixPairNestedTopFrames.nestedFrame F E
  intro x y hxy
  change
    (E.frame.symm ((F.frame.symm ((u : Equiv.Perm X)
      (F.frame (E.frame ((C.top u)⁻¹ j,x.1),x.2)))).1)).2 =
    (E.frame.symm ((F.frame.symm ((u : Equiv.Perm X)
      (F.frame (E.frame ((C.top u)⁻¹ j,y.1),y.2)))).1)).2
  rw [F.intertwine,F.intertwine,hxy]

/-- The two original head bits per coarse fibre and the actual top map. -/
def headHom : U →*
    PermutationalWreathProduct (Multiplicative Points)
      (SixPairNestedTopFrames.nestedFrame F E).top.range J where
  toFun u :=
    ⟨fun j => Multiplicative.ofAdd
      (head (((SixPairNestedTopFrames.nestedFrame F E).wreathEmbedding u).left j)),
      (SixPairNestedTopFrames.nestedFrame F E).top.rangeRestrict u⟩
  map_one' := by
    let C := SixPairNestedTopFrames.nestedFrame F E
    apply PermutationalWreathProduct.ext
    · funext j
      change Multiplicative.ofAdd (head ((C.wreathEmbedding 1).left j))=1
      rw [C.wreathEmbedding.map_one]
      exact congrArg Multiplicative.ofAdd head_one
    · exact C.top.rangeRestrict.map_one
  map_mul' u v := by
    let C := SixPairNestedTopFrames.nestedFrame F E
    apply PermutationalWreathProduct.ext
    · funext j
      change Multiplicative.ofAdd (head ((C.wreathEmbedding (u*v)).left j)) =
        Multiplicative.ofAdd (head ((C.wreathEmbedding u).left j)) *
          Multiplicative.ofAdd (head ((C.wreathEmbedding v).left ((C.top u)⁻¹ j)))
      rw [C.wreathEmbedding.map_mul]
      change Multiplicative.ofAdd
        (head (((C.wreathEmbedding u).left j)*((C.wreathEmbedding v).left ((C.top u)⁻¹ j)))) = _
      rw [head_mul _ _ (local_preserves F E u j)
        (local_preserves F E v ((C.top u)⁻¹ j))]
      rfl
    · exact C.top.rangeRestrict.map_mul u v

@[simp] theorem headHom_top (u : U) :
    (headHom F E u).right=(SixPairNestedTopFrames.nestedFrame F E).top.rangeRestrict u := rfl

/-- On the original kernel, the global wreath transition is precisely the
already retained physical fibre restriction. -/
theorem local_of_kernel
    (u : (SixPairNestedTopFrames.nestedFrame F E).top.ker) (j : J) :
    (((SixPairNestedTopFrames.nestedFrame F E).wreathEmbedding u.val).left j)=
      (SixPairNestedTopFrames.nestedFrame F E).kernelCoordinate j u := by
  let C := SixPairNestedTopFrames.nestedFrame F E
  apply Equiv.ext
  intro p
  change (C.frame.symm ((u.val : Equiv.Perm X) (C.frame ((C.top u.val)⁻¹ j,p)))).2 =
    (C.frame.symm ((u.val : Equiv.Perm X) (C.frame (j,p)))).2
  rw [u.property]
  rfl

end SymmetricSubgroupAsymptotics.SixPairCoarseWreathHead
