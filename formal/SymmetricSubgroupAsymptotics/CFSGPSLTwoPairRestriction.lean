import SymmetricSubgroupAsymptotics.CFSGPSLTwoSylowAlignment
import SymmetricSubgroupAsymptotics.CFSGPSLTwoFixedRootKernel
import SymmetricSubgroupAsymptotics.CFSGPSLTwoRootAutomorphisms

/-! Faithful restriction of the actual PSL2 opposite-pair stabilizer to
its actual upper root group. All torus conjugations remain literal in
the original projective quotient. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGPSLTwoPairRestriction
open CFSGPSLTwoRootCoordinates CFSGPSLTwoGeometry
variable {F : Type*} [Field F] [Finite F]

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

def pairStabilizer : Subgroup (MulAut (PSL (F:=F))) where
  carrier := {f | (projectiveRoot (F:=F)).map f.toMonoidHom=projectiveRoot ∧
    (oppositeRoot (F:=F)).map f.toMonoidHom=oppositeRoot}
  one_mem' := by constructor <;> exact Subgroup.map_id _
  mul_mem' := by
    rintro f g ⟨hf,hf'⟩ ⟨hg,hg'⟩
    constructor
    · rw [map_mul_aut,hg,hf]
    · rw [map_mul_aut,hg',hf']
  inv_mem' := by
    rintro f ⟨hf,hf'⟩
    exact ⟨map_inv_aut _ f hf,map_inv_aut _ f hf'⟩

def restrictRoot (f : MulAut (PSL (F:=F)))
    (hf : (projectiveRoot (F:=F)).map f.toMonoidHom=projectiveRoot) :
    MulAut (projectiveRoot (F:=F)) :=
  (f.subgroupMap (projectiveRoot (F:=F))).trans (MulEquiv.subgroupCongr hf)

def pairRestriction : pairStabilizer (F:=F)→*MulAut (projectiveRoot (F:=F)) where
  toFun f := restrictRoot f.val f.property.1
  map_one' := by apply MulEquiv.ext;intro u;apply Subtype.ext;rfl
  map_mul' f g := by apply MulEquiv.ext;intro u;apply Subtype.ext;rfl

theorem pairRestriction_injective : Function.Injective (pairRestriction (F:=F)) := by
  apply (MonoidHom.ker_eq_bot_iff (pairRestriction (F:=F))).mp
  apply bot_unique
  intro f hf
  apply (Subgroup.mem_bot).mpr
  apply Subtype.ext
  apply eq_one_of_fixed_root_and_weyl_coset f.val
  · intro u
    exact congrArg (fun A : MulAut (projectiveRoot (F:=F)) => (A u).val) hf
  · exact weyl_displacement_mem_torus f.val f.property.1 f.property.2

theorem pairRestriction_conjugate_torus (f : pairStabilizer (F:=F)) (c : Fˣ) :
    ∃ d : Fˣ,pairRestriction f*rootTorusActionHom c*(pairRestriction f)⁻¹=rootTorusActionHom d := by
  have hT := map_torus_of_fix_opposite_pair f.val f.property.1 f.property.2
  have ht : f.val (projectiveTorus c)∈pairTorus (F:=F) := by
    rw [←hT]
    exact ⟨projectiveTorus c,⟨c,rfl⟩,rfl⟩
  obtain ⟨d,hd⟩ := ht
  have hd' : f.val (projectiveTorus c)=projectiveTorus d := hd.symm
  refine ⟨d,?_⟩
  apply MulEquiv.ext
  intro u
  apply Subtype.ext
  change f.val ((rootTorusActionHom c ((pairRestriction f).symm u)).val)=
    (rootTorusActionHom d u).val
  rw [rootTorusActionHom_val,rootTorusActionHom_val,map_mul,map_mul,map_inv,hd']
  have hv := congrArg (fun z : projectiveRoot (F:=F) => z.val) ((pairRestriction f).apply_symm_apply u)
  change f.val (((pairRestriction f).symm u).val)=u.val at hv
  rw [hv]

theorem pairRestriction_mem_torus_normalizer (f : pairStabilizer (F:=F)) :
    pairRestriction f∈Subgroup.normalizer ((rootTorusActionHom (F:=F)).range :
      Set (MulAut (projectiveRoot (F:=F)))) := by
  have hforward : ∀ (a : pairStabilizer (F:=F)) (A : MulAut (projectiveRoot (F:=F))),
      A∈(rootTorusActionHom (F:=F)).range→pairRestriction a*A*(pairRestriction a)⁻¹∈
        (rootTorusActionHom (F:=F)).range := by
    rintro a A ⟨c,rfl⟩
    obtain ⟨d,hd⟩ := pairRestriction_conjugate_torus a c
    exact ⟨d,hd.symm⟩
  apply Subgroup.mem_normalizer_iff.mpr
  intro A
  constructor
  · exact hforward f A
  · intro hA
    have he := hforward f⁻¹ _ hA
    have hc : pairRestriction f⁻¹*(pairRestriction f*A*(pairRestriction f)⁻¹)*
        (pairRestriction f⁻¹)⁻¹=A := by rw [map_inv];group
    rwa [hc] at he

theorem pairStabilizer_card_le :
    Nat.card (pairStabilizer (F:=F))≤Nat.card Fˣ*Nat.card (F ≃+* F) := by
  let j : pairStabilizer (F:=F)→Subgroup.normalizer ((rootTorusActionHom (F:=F)).range :
      Set (MulAut (projectiveRoot (F:=F)))) :=
    fun f => ⟨pairRestriction f,pairRestriction_mem_torus_normalizer f⟩
  have hj : Function.Injective j := by
    intro f g he
    exact pairRestriction_injective (congrArg Subtype.val he)
  exact (Nat.card_le_card_of_injective j hj).trans (card_rootTorusNormalizer_le (F:=F))

end SymmetricSubgroupAsymptotics.CFSGPSLTwoPairRestriction
