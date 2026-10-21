import SymmetricSubgroupAsymptotics.CFSGPSLTwoRootCoordinates
import SymmetricSubgroupAsymptotics.CFSGAdditiveAutomorphismTransport
import SymmetricSubgroupAsymptotics.CFSGFiniteFieldSquareScalarNormalizerCard

/-! The actual projective root group has precisely the additive-field
automorphisms. Its original torus is the square-scalar subgroup under
this exact transport, so its intrinsic automorphism normalizer has at
most (q-1) times the actual field-automorphism order elements. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGPSLTwoRootCoordinates
open CFSGFiniteFieldScalarNormalizer CFSGAdditiveAutomorphismTransport
variable {F : Type*} [Field F]

def rootAutEquiv : MulAut (projectiveRoot (F:=F)) ≃* AddAut F :=
  (MulAut.congr (projectiveRootEquiv (F:=F)).symm).trans (multiplicativeAddAutEquiv F)

def rootTorusActionHom : Fˣ→*MulAut (projectiveRoot (F:=F)) :=
  (rootAutEquiv (F:=F)).symm.toMonoidHom.comp (squareScalarHom F)

theorem rootTorusActionHom_coordinate (c : Fˣ) (a : F) :
    rootTorusActionHom c (projectiveRootEquiv (Multiplicative.ofAdd a))=
      projectiveRootEquiv (Multiplicative.ofAdd ((c : F)^2*a)) := by
  simp [rootTorusActionHom,rootAutEquiv,multiplicativeAddAutEquiv,MulAut.congr]

/-- This coordinate action is exactly conjugation by the original
projective determinant-one torus, not just an isomorphic scalar action. -/
theorem rootTorusActionHom_val (c : Fˣ) (u : projectiveRoot (F:=F)) :
    (rootTorusActionHom c u).val=projectiveTorus c*u.val*(projectiveTorus c)⁻¹ := by
  obtain ⟨a,rfl⟩ := (projectiveRootEquiv (F:=F)).surjective u
  change (rootTorusActionHom c (projectiveRootEquiv (Multiplicative.ofAdd a.toAdd))).val=
    projectiveTorus c*(projectiveRootEquiv (Multiplicative.ofAdd a.toAdd)).val*(projectiveTorus c)⁻¹
  rw [rootTorusActionHom_coordinate c a.toAdd]
  exact (projective_torus_conjugation c a.toAdd).symm

theorem rootAut_map_torus :
    (rootTorusActionHom (F:=F)).range.map (rootAutEquiv (F:=F)).toMonoidHom=
      squareScalarSubgroup F := by
  ext A
  constructor
  · rintro ⟨f,⟨c,rfl⟩,rfl⟩
    refine ⟨c,?_⟩
    exact ((rootAutEquiv (F:=F)).apply_symm_apply (squareScalarHom F c)).symm
  · rintro ⟨c,rfl⟩
    refine ⟨rootTorusActionHom c,⟨c,rfl⟩,?_⟩
    exact (rootAutEquiv (F:=F)).apply_symm_apply _

theorem rootAut_mem_squareScalarNormalizer (f : MulAut (projectiveRoot (F:=F)))
    (hf : f∈Subgroup.normalizer ((rootTorusActionHom (F:=F)).range : Set (MulAut (projectiveRoot (F:=F))))) :
    rootAutEquiv f∈Subgroup.normalizer (squareScalarSubgroup F : Set (AddAut F)) := by
  have he := Subgroup.le_normalizer_map (H:=(rootTorusActionHom (F:=F)).range)
    (rootAutEquiv (F:=F)).toMonoidHom
    (show rootAutEquiv f∈
      (Subgroup.normalizer ((rootTorusActionHom (F:=F)).range : Set (MulAut (projectiveRoot (F:=F))))).map
        (rootAutEquiv (F:=F)).toMonoidHom from ⟨f,hf,rfl⟩)
  rw [rootAut_map_torus] at he
  exact he

variable [Finite F]

theorem card_rootTorusNormalizer_le :
    Nat.card (Subgroup.normalizer ((rootTorusActionHom (F:=F)).range : Set (MulAut (projectiveRoot (F:=F)))))≤
      Nat.card Fˣ*Nat.card (F ≃+* F) := by
  let j : (Subgroup.normalizer ((rootTorusActionHom (F:=F)).range : Set (MulAut (projectiveRoot (F:=F)))))→
      Subgroup.normalizer (squareScalarSubgroup F : Set (AddAut F)) :=
    fun f => ⟨rootAutEquiv f.val,rootAut_mem_squareScalarNormalizer f.val f.property⟩
  have hj : Function.Injective j := by
    intro f g he
    apply Subtype.ext
    exact (rootAutEquiv (F:=F)).injective (congrArg Subtype.val he)
  exact (Nat.card_le_card_of_injective j hj).trans (card_squareScalarNormalizer_le F)

end SymmetricSubgroupAsymptotics.CFSGPSLTwoRootCoordinates
