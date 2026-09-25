import SymmetricSubgroupAsymptotics.BinaryPairFiniteRows
import SymmetricSubgroupAsymptotics.BinaryPairOriginalCapacity

/-! Simultaneous transport of every literal object in a pair certificate.
The fixed preimage, cut, normal, pair action and cover all use the same
original group equivalence. No numerical signature substitutes for a map. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {G H T : Type*} [Group G] [Group H] [Group T]

theorem binaryPair_ker_comp_equiv (f : G→*T) (e : G≃*H) :
    (f.comp e.symm.toMonoidHom).ker=f.ker.map e.toMonoidHom := by
  ext x
  change f (e.symm x)=1 ↔ x∈f.ker.map e.toMonoidHom
  constructor
  · intro h
    exact ⟨e.symm x,h,e.apply_symm_apply x⟩
  · rintro ⟨y,hy,rfl⟩
    simpa using hy

theorem binaryPair_card_map_equiv (e : G≃*H) (K : Subgroup G) :
    Nat.card (K.map e.toMonoidHom)=Nat.card K :=
  (Nat.card_congr (e.subgroupMap K).toEquiv).symm

theorem binaryPairFixedSubgroup_map_equiv (e : G≃*H) (K C : Subgroup G)
    [C.Normal] : letI : (C.map e.toMonoidHom).Normal :=
      Subgroup.Normal.map inferInstance _ e.surjective
    binaryPairFixedSubgroup (K.map e.toMonoidHom) (C.map e.toMonoidHom)=
      (binaryPairFixedSubgroup K C).map e.toMonoidHom := by
  letI : (C.map e.toMonoidHom).Normal := Subgroup.Normal.map inferInstance _ e.surjective
  ext x
  rw [Subgroup.map_equiv_eq_comap_symm' e (binaryPairFixedSubgroup K C)]
  change x∈binaryPairFixedSubgroup (K.map e.toMonoidHom) (C.map e.toMonoidHom) ↔
    e.symm x∈binaryPairFixedSubgroup K C
  rw [binaryPairFixedSubgroup_mem_iff _ _ (fun h:H=>h) (by simp),
    binaryPairFixedSubgroup_mem_iff _ _ (fun g:G=>g) (by simp)]
  simp only [Subgroup.map_equiv_eq_comap_symm',Subgroup.mem_comap,
    MulEquiv.coe_toMonoidHom,map_mul,map_inv]
  constructor
  · rintro ⟨hx,hcomm⟩
    refine ⟨hx,fun j=>?_⟩
    simpa only [e.symm_apply_apply] using hcomm (e j)
  · rintro ⟨hx,hcomm⟩
    exact ⟨hx,fun j=>hcomm (e.symm j)⟩

namespace BinaryPairLocalCertificate
variable {ι I : Type*} {generators : ι→G} {top : G→*Equiv.Perm I} {N : Subgroup G}

/-- The certificate transports all its data and checked assertions through
one faithful original group chart. The physical degree and gap are unchanged. -/
def transport (C : BinaryPairLocalCertificate generators top N) (e : G≃*H) :
    BinaryPairLocalCertificate (fun j=>e (generators j))
      (top.comp e.symm.toMonoidHom) (N.map e.toMonoidHom) := by
  letI : C.cut.Normal := C.cut_normal
  letI : (C.cut.map e.toMonoidHom).Normal := Subgroup.Normal.map inferInstance _ e.surjective
  refine {
    cut := C.cut.map e.toMonoidHom
    cut_normal := inferInstance
    cut_le_kernel := ?_
    intersection_le_cut := ?_
    central := ?_
    cutDimension := C.cutDimension
    fixedDimension := C.fixedDimension
    cut_card := ?_
    fixed_card := ?_
    coverDegree := C.coverDegree
    cover := C.cover.comp e.symm.toMonoidHom
    cover_kernel := ?_
    width := C.width
    gap := C.gap }
  · rw [binaryPair_ker_comp_equiv]
    exact Subgroup.map_mono C.cut_le_kernel
  · rw [binaryPair_ker_comp_equiv,←Subgroup.map_inf _ _ _ e.injective]
    exact Subgroup.map_mono C.intersection_le_cut
  · intro j x
    obtain ⟨y,hy,he⟩ := x.2
    refine ⟨y⁻¹*(generators j*y*(generators j)⁻¹),C.central j ⟨y,hy⟩,?_⟩
    simp only [map_mul,map_inv,he,MulEquiv.coe_toMonoidHom]
  · rw [binaryPair_ker_comp_equiv,←Subgroup.map_inf _ _ _ e.injective,
      binaryPair_card_map_equiv,binaryPair_card_map_equiv]
    exact C.cut_card
  · rw [binaryPair_ker_comp_equiv,binaryPairFixedSubgroup_map_equiv,
      binaryPair_card_map_equiv,binaryPair_card_map_equiv]
    exact C.fixed_card
  · rw [binaryPair_ker_comp_equiv,C.cover_kernel,Subgroup.map_sup,
      binaryPair_ker_comp_equiv]

end BinaryPairLocalCertificate
end SymmetricSubgroupAsymptotics
