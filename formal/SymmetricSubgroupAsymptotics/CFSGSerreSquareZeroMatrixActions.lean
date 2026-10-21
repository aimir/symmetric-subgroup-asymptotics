import SymmetricSubgroupAsymptotics.CFSGSerreSquareZeroMatrixOperators
import SymmetricSubgroupAsymptotics.CFSGSquareZeroConjugation
import SymmetricSubgroupAsymptotics.CFSGSerreImageRepresentation
import SymmetricSubgroupAsymptotics.CFSGSerreModelRootGeneration
import SymmetricSubgroupAsymptotics.CFSGInvariantSubmoduleAction
import SymmetricSubgroupAsymptotics.CFSGAlgebraConjugationAction
import SymmetricSubgroupAsymptotics.CFSGGeneratedActionRange

/-! Shared original-Serre-image and literal elementary-root actions.
They have exactly the same range on the same integral tensor image. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped TensorProduct BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGSerreSquareZeroMatrix
open CFSG.Models.Chevalley CFSGSerreLocalNilpotence CFSGSerreModelRootGeneration
open CFSGInvariantQuotientAction CFSGInvariantSubmoduleAction
variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}
    {I : Type*} [Fintype I] [DecidableEq I]
    (D : Data A I) (K : Type) [Field K]

theorem baseChange_rootOperator (neg : Bool) (i : Fin n) (t : K) (x : Space A K) :
    baseChange D K (rootOperator A K neg i t x)=
      (1+t • fieldRoot D K neg i)*baseChange D K x*(1-t • fieldRoot D K neg i) := by
  rw [rootOperator]
  simp only [LinearMap.sum_apply,LinearMap.smul_apply,map_sum,map_smul,baseChange_operator]
  exact CFSGSquareZeroConjugation.operator_sum_eq_conjugation t _ _

def imageRepresentation : Model A K→*((baseChange D K).range≃ₗ[K](baseChange D K).range) :=
  CFSGSerreImageRepresentation.imageRepresentation A K (baseChange D K)
    (fun neg i k => CFSGIntegralSquareZeroOperators.operator K (fieldRoot D K neg i) k)
    (baseChange_operator D K)

theorem imageRepresentation_intertwines (g : Model A K) (x : Space A K) :
    (imageRepresentation D K g ((baseChange D K).rangeRestrict x)).val=baseChange D K (g.val x) :=
  CFSGSerreImageRepresentation.imageRepresentation_intertwines A K (baseChange D K)
    (fun neg i k => CFSGIntegralSquareZeroOperators.operator K (fieldRoot D K neg i) k)
    (baseChange_operator D K) g x

theorem imageRepresentation_root (neg : Bool) (i : Fin n) (t : K) (y : (baseChange D K).range) :
    (imageRepresentation D K (modelRoot A K neg i t) y).val=
      (1+t • fieldRoot D K neg i)*y.val*(1-t • fieldRoot D K neg i) := by
  obtain ⟨x,hx⟩ := y.property
  have hy : y=(baseChange D K).rangeRestrict x := Subtype.ext hx.symm
  rw [hy,imageRepresentation_intertwines]
  change baseChange D K (rootOperator A K neg i t x)=_
  exact baseChange_rootOperator D K neg i t x

variable (U : Bool→Fin n→K→(Matrix I I K)ˣ)
    (hU : ∀neg i t,(U neg i t : Matrix I I K)=1+t • fieldRoot D K neg i)
    (hUi : ∀neg i t,(↑((U neg i t)⁻¹) : Matrix I I K)=1-t • fieldRoot D K neg i)

def elementaryGroup : Subgroup ((Matrix I I K)ˣ) :=
  Subgroup.closure {u | ∃neg i t,u=U neg i t}

def elementaryRoot (neg : Bool) (i : Fin n) (t : K) : elementaryGroup K U :=
  ⟨U neg i t,Subgroup.subset_closure ⟨neg,i,t,rfl⟩⟩

def elementaryRootSet : Set (elementaryGroup K U) := {u | ∃neg i t,u=elementaryRoot K U neg i t}

theorem elementaryRootSet_generate : Subgroup.closure (elementaryRootSet K U)=⊤ := by
  let R := Subgroup.closure (elementaryRootSet K U)
  have hmap : R.map (elementaryGroup K U).subtype=elementaryGroup K U := by
    apply le_antisymm
    · rintro u ⟨x,hx,rfl⟩
      exact x.property
    · apply (Subgroup.closure_le _).mpr
      rintro u ⟨neg,i,t,rfl⟩
      exact ⟨elementaryRoot K U neg i t,Subgroup.subset_closure ⟨neg,i,t,rfl⟩,rfl⟩
  apply top_unique
  intro x _
  have hx : x.val∈R.map (elementaryGroup K U).subtype := by rw [hmap];exact x.property
  obtain ⟨y,hy,he⟩ := hx
  exact (Subtype.ext he : y=x) ▸ hy

include hU hUi
private theorem root_inv (neg : Bool) (i : Fin n) (t : K) : (U neg i t)⁻¹=U neg i (-t) := by
  apply Units.ext
  rw [hUi,hU]
  simp only [neg_smul,sub_eq_add_neg]

theorem root_preserves_image (neg : Bool) (i : Fin n) (t : K)
    (y : Matrix I I K) (hy : y∈(baseChange D K).range) :
    CFSGAlgebraConjugationAction.action K (Matrix I I K) (U neg i t) y∈(baseChange D K).range := by
  obtain ⟨x,rfl⟩ := hy
  refine ⟨rootOperator A K neg i t x,?_⟩
  change baseChange D K (rootOperator A K neg i t x)=
    (U neg i t : Matrix I I K)*baseChange D K x*(↑((U neg i t)⁻¹) : Matrix I I K)
  rw [hU,hUi]
  exact baseChange_rootOperator D K neg i t x

theorem elementaryGroup_le_imageStabilizer :
    elementaryGroup K U≤(stabilizer (baseChange D K).range).comap
      (CFSGAlgebraConjugationAction.action K (Matrix I I K)) := by
  apply (Subgroup.closure_le _).mpr
  rintro u ⟨neg,i,t,rfl⟩
  constructor
  · exact root_preserves_image D K U hU hUi neg i t
  · intro y hy
    have hh : CFSGAlgebraConjugationAction.action K (Matrix I I K)
        ((U neg i t)⁻¹) y∈(baseChange D K).range := by
      rw [root_inv D K U hU hUi]
      exact root_preserves_image D K U hU hUi neg i (-t) y hy
    simpa only [map_inv] using hh

def elementaryToImageStabilizer : elementaryGroup K U→*stabilizer (baseChange D K).range where
  toFun u := ⟨CFSGAlgebraConjugationAction.action K (Matrix I I K) u.val,
    elementaryGroup_le_imageStabilizer D K U hU hUi u.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' u v := Subtype.ext (map_mul _ u.val v.val)

def elementaryImageAction : elementaryGroup K U→*((baseChange D K).range≃ₗ[K](baseChange D K).range) :=
  (restrictionAction (baseChange D K).range).comp (elementaryToImageStabilizer D K U hU hUi)

@[simp] theorem elementaryImageAction_apply (u : elementaryGroup K U) (y : (baseChange D K).range) :
    (elementaryImageAction D K U hU hUi u y).val=
      (u.val : Matrix I I K)*y.val*(↑(u.val⁻¹) : Matrix I I K) := rfl

theorem source_root_action_eq_elementary (neg : Bool) (i : Fin n) (t : K) :
    imageRepresentation D K (modelRoot A K neg i t)=
      elementaryImageAction D K U hU hUi (elementaryRoot K U neg i t) := by
  apply LinearEquiv.ext
  intro y
  apply Subtype.ext
  rw [elementaryImageAction_apply]
  change (imageRepresentation D K (modelRoot A K neg i t) y).val=
    (U neg i t : Matrix I I K)*y.val*(↑((U neg i t)⁻¹) : Matrix I I K)
  rw [hU,hUi]
  exact imageRepresentation_root D K neg i t y

theorem action_ranges_eq : (imageRepresentation D K).range=(elementaryImageAction D K U hU hUi).range := by
  apply le_antisymm
  · apply CFSGGeneratedActionRange.range_le_of_generators (rootSet A K) (rootSet_generate A K)
      (imageRepresentation D K) (elementaryImageAction D K U hU hUi).range
    rintro u ⟨neg,i,t,rfl⟩
    exact ⟨elementaryRoot K U neg i t,(source_root_action_eq_elementary D K U hU hUi neg i t).symm⟩
  · apply CFSGGeneratedActionRange.range_le_of_generators (elementaryRootSet K U)
      (elementaryRootSet_generate K U) (elementaryImageAction D K U hU hUi) (imageRepresentation D K).range
    rintro u ⟨neg,i,t,rfl⟩
    exact ⟨modelRoot A K neg i t,source_root_action_eq_elementary D K U hU hUi neg i t⟩

end SymmetricSubgroupAsymptotics.CFSGSerreSquareZeroMatrix
