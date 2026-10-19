import SymmetricSubgroupAsymptotics.SixPairActualTopGeometry
import SymmetricSubgroupAsymptotics.ProductBlockFrameKernelCoordinates

/-! Lift the ACTUAL top block system through the original pair frame.
Three top pairs give three original four-point blocks; two top triples
give two original six-point blocks. Offsets and correlated kernels remain
in the same physical action; no split wreath model is substituted. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SixPairNestedTopFrames

variable {X I J A : Type} {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U I) (E : ProductBlockFrame F.top.range J A)

def nestedFrame : ProductBlockFrame U J (A × ZMod 2) where
  frame := ((Equiv.prodAssoc J A (ZMod 2)).symm.trans
    (Equiv.prodCongr E.frame (Equiv.refl (ZMod 2)))).trans F.frame
  top := E.top.comp F.top.rangeRestrict
  intertwine u p := by
    change (E.frame.symm ((F.frame.symm ((u : Equiv.Perm X)
      (F.frame (E.frame (p.1,p.2.1),p.2.2)))).1)).1=E.top (F.top.rangeRestrict u) p.1
    rw [F.intertwine]
    exact E.intertwine (F.top.rangeRestrict u) (p.1,p.2.1)

@[simp] theorem nestedFrame_top : (nestedFrame F E).top=E.top.comp F.top.rangeRestrict := rfl

/-- In the three-top-pairs branch, the new original kernel is binary,
although it need not be elementary or split. Its exact extension is kept. -/
theorem threePairs_kernel_binary [Finite X] [Fintype I]
    (E : ProductBlockFrame F.top.range (Fin 3) (ZMod 2)) :
    IsPGroup 2 (nestedFrame F E).top.ker := by
  let B : BinaryPairFrame F.top.range (Fin 3) :=
    { frame := E.frame,top := E.top,intertwine := E.intertwine }
  have hk : IsPGroup 2 F.top.rangeRestrict.ker := by
    have he : F.top.rangeRestrict.ker=F.top.ker := by
      ext u
      change F.top.rangeRestrict u=1 ↔ F.top u=1
      constructor
      · exact fun h => congrArg Subtype.val h
      · exact fun h => Subtype.ext h
    rw [he]
    exact F.kernel_isPGroup
  have hp := B.kernel_isPGroup.comap_of_ker_isPGroup F.top.rangeRestrict hk
  exact hp

/-- The two-triples original kernel is retained as a literal injective
subdirect coordinate map into two original six-point local actions. -/
theorem twoTriples_kernel_coordinates_injective
    (E : ProductBlockFrame F.top.range (Fin 2) (ZMod 3)) :
    Function.Injective (nestedFrame F E).twoKernelMap :=
  (nestedFrame F E).twoKernelMap_injective

end SymmetricSubgroupAsymptotics.SixPairNestedTopFrames
