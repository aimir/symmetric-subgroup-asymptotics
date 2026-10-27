import SymmetricSubgroupAsymptotics.ActualWreathKernelSupportCover

/-! The ambient compression kernel really is the full local-kernel power.
Its intersections with actual subgroups are retained literally. Full local
components prove normal simple-coordinate images; they do not assert that
an intersection fills this ambient product. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ActualWreathMapBaseKernelChart
open PermutationalWreathProduct PermutationalWreathProduct.Compression

variable {D D' Q I : Type} [Group D] [Group D'] [Group Q] [MulAction Q I]
variable (phi : D →* D') (C : SemisimpleNormalChart phi.ker)

abbrev W := PermutationalWreathProduct D Q I

def chart : (mapBase (Q := Q) (I := I) phi).ker ≃*
    (∀ p : I × C.ι, C.factor p.2) where
  toFun n p := C.equiv ⟨n.val.left p.1,
    ((mem_mapBase_ker_iff phi n.val).mp n.property).2 p.1⟩ p.2
  invFun f := ⟨⟨fun i => (C.equiv.symm (fun j => f (i,j))).val,1⟩,
    (mem_mapBase_ker_iff phi _).mpr ⟨rfl,fun i => (C.equiv.symm (fun j => f (i,j))).property⟩⟩
  left_inv n := by
    apply Subtype.ext
    apply PermutationalWreathProduct.ext
    · funext i
      change (C.equiv.symm (C.equiv
        ⟨n.val.left i,((mem_mapBase_ker_iff phi n.val).mp n.property).2 i⟩)).val=n.val.left i
      exact congrArg Subtype.val (C.equiv.symm_apply_apply _)
    · exact ((mem_mapBase_ker_iff phi n.val).mp n.property).1.symm
  right_inv f := by
    funext p
    exact congrFun (C.equiv.apply_symm_apply (fun j => f (p.1,j))) p.2
  map_mul' n m := by
    exact (ActualWreathKernelSupportCover.coordinates
      (MonoidHom.id (W (D := D) (Q := Q) (I := I))) phi C).map_mul n m

/-- Exact image equality for the SAME original subgroup/intersection. -/
theorem intersection_image (L : Subgroup (W (D := D) (Q := Q) (I := I))) :
    (((L ⊓ (mapBase phi).ker).subgroupOf (mapBase phi).ker).map
      (chart phi C).toMonoidHom)=
    (ActualWreathKernelSupportCover.coordinates L.subtype phi C).range := by
  ext f
  constructor
  · rintro ⟨n,hn,rfl⟩
    refine ⟨⟨⟨n.val,hn.1⟩,n.property⟩,?_⟩
    rfl
  · rintro ⟨n,rfl⟩
    refine ⟨⟨n.val.val,n.property⟩,⟨n.val.property,n.property⟩,?_⟩
    rfl

/-- The normal-image condition is discharged by actual FullComponent. -/
theorem intersection_coordinate_normal
    (L : Subgroup (W (D := D) (Q := Q) (I := I)))
    (hfull : FullComponent L.subtype) (p : I × C.ι) :
    (SimpleCoordinateSupportCover.coordinate (fun p : I × C.ι => C.factor p.2)
      (((L ⊓ (mapBase phi).ker).subgroupOf (mapBase phi).ker).map
        (chart phi C).toMonoidHom) p).range.Normal := by
  rw [intersection_image phi C L]
  exact (ActualWreathKernelSupportCover.kernelImage L.subtype phi C hfull).property p

end SymmetricSubgroupAsymptotics.ActualWreathMapBaseKernelChart
