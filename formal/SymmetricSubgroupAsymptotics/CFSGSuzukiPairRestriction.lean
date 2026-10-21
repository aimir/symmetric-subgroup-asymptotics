import SymmetricSubgroupAsymptotics.CFSGSuzukiFixedRootKernel

/-! The subgroup of original-model automorphisms preserving both actual
opposite unipotent groups restricts faithfully to the original U. All
subtype transports retain the same original matrices. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGSuzukiPairRestriction
open CFSGSuzukiFieldParameters CFSGSuzukiUnipotent CFSGSuzukiSylowOfNormalizer
open CFSGSuzukiGoodSylow CFSGSuzukiBorelIntersection CFSGSuzukiAlignedAutomorphisms
open CFSGSuzukiFixedRootKernel

private theorem map_mul_aut {G : Type*} [Group G] (H : Subgroup G) (f g : MulAut G) :
    H.map (f*g).toMonoidHom=(H.map g.toMonoidHom).map f.toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

private theorem map_inv_aut {G : Type*} [Group G] (H : Subgroup G) (f : MulAut G)
    (hf : H.map f.toMonoidHom=H) : H.map (f⁻¹).toMonoidHom=H := by
  have he : (H.map f.toMonoidHom).map (f⁻¹).toMonoidHom=H := by
    rw [Subgroup.map_map]
    have hh : (f⁻¹).toMonoidHom.comp f.toMonoidHom=MonoidHom.id G := by
      ext x
      exact f.symm_apply_apply x
    rw [hh,Subgroup.map_id]
  rwa [hf] at he

def pairStabilizer (m : ℕ) : Subgroup (MulAut (ActualGroup m)) where
  carrier := {f | (modelUnipotent m).map f.toMonoidHom=modelUnipotent m ∧
    (modelOppositeUnipotent m).map f.toMonoidHom=modelOppositeUnipotent m}
  one_mem' := by constructor <;> exact Subgroup.map_id _
  mul_mem' := by
    rintro f g ⟨hf,hf'⟩ ⟨hg,hg'⟩
    constructor
    · rw [map_mul_aut,hg,hf]
    · rw [map_mul_aut,hg',hf']
  inv_mem' := by
    rintro f ⟨hf,hf'⟩
    exact ⟨map_inv_aut _ f hf,map_inv_aut _ f hf'⟩

def modelUnipotentEquiv (m : ℕ) : modelUnipotent m ≃* unipotentSubgroup m where
  toFun g := ⟨g.val.val,g.property⟩
  invFun u := ⟨⟨u.val,unipotentSubgroup_le_model m u.property⟩,u.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

def restrictUnipotent (m : ℕ) (f : MulAut (ActualGroup m))
    (hf : (modelUnipotent m).map f.toMonoidHom=modelUnipotent m) :
    MulAut (unipotentSubgroup m) :=
  (modelUnipotentEquiv m).symm.trans
    (((f.subgroupMap (modelUnipotent m)).trans (MulEquiv.subgroupCongr hf)).trans
      (modelUnipotentEquiv m))

def pairRestriction (m : ℕ) : pairStabilizer m→*MulAut (unipotentSubgroup m) where
  toFun f := restrictUnipotent m f.val f.property.1
  map_one' := by
    apply MulEquiv.ext
    intro u
    apply Subtype.ext
    rfl
  map_mul' f g := by
    apply MulEquiv.ext
    intro u
    apply Subtype.ext
    rfl

theorem pairRestriction_injective (m : ℕ) : Function.Injective (pairRestriction m) := by
  apply (MonoidHom.ker_eq_bot_iff (pairRestriction m)).mp
  apply bot_unique
  intro f hf
  apply (Subgroup.mem_bot).mpr
  apply Subtype.ext
  apply eq_one_of_fixed_unipotent_and_weyl_coset m f.val
  · intro u
    have he := congrArg (fun A : MulAut (unipotentSubgroup m) => A (modelUnipotentEquiv m u)) hf
    apply Subtype.ext
    exact congrArg (fun z : unipotentSubgroup m => z.val) he
  · exact weyl_displacement_mem_torus m f.val f.property.1 f.property.2

end SymmetricSubgroupAsymptotics.CFSGSuzukiPairRestriction
