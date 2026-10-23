import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalExceptionalRootCovariance
import SymmetricSubgroupAsymptotics.CFSGGTwoSingularPointAction
import SymmetricSubgroupAsymptotics.CFSGInvariantQuotientAction
import SymmetricSubgroupAsymptotics.CFSGSerreModelRootGeneration

/-! The ORIGINAL G2 Model acts on its actual seven-dimensional quotient.
Both directions of kernel invariance follow from the proved signed root
covariance and the invertible native action. The model action is descended
through the surjective source projection; its faithfulness is not assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGGTwoOriginalExceptionalRepresentation
open CFSG.Models.Chevalley CFSGSerreLocalNilpotence CFSGSerreModelRootGeneration
open CFSGGTwoSerreMatrices CFSGGTwoAxisCoordinates CFSGGTwoSingularPointAction
open CFSGGTwoOriginalSevenProjection CFSGGTwoOriginalExceptionalRootCovariance
open CFSGInvariantQuotientAction

private theorem mem_stabilizer_of_intertwines
    {R M V : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup V] [Module R V] (β : M →ₗ[R] V)
    (g : M ≃ₗ[R] M) (h : V ≃ₗ[R] V)
    (he : ∀x,β (g x)=h (β x)) : g∈stabilizer (LinearMap.ker β) := by
  constructor
  · intro x hx
    change β x=0 at hx
    change β (g x)=0
    rw [he,hx,map_zero]
  · intro x hx
    change β x=0 at hx
    change β (g.symm x)=0
    apply h.injective
    calc
      h (β (g.symm x))=β (g (g.symm x)) := (he (g.symm x)).symm
      _=β x := congrArg β (g.apply_symm_apply x)
      _=0 := hx
      _=h 0 := (map_zero h).symm

variable (K : Type) [Field K] [CharP K 3]
local notation "A" => CartanMatrix.G₂

theorem root_intertwines (neg : Bool) (i : Fin 2) (t : K) (x : Space A K) :
    sevenProjection K (rootEquiv A K neg i t x)=
      hyperplaneLinearHom K (naturalRoot K neg (exchangedNode i)
        (exceptionalParameter K i t)) (sevenProjection K x) := by
  apply Subtype.ext
  change (sevenProjection K (rootOperator A K neg i t x)).val=
    (rootTransvection K neg (exchangedNode i) (exceptionalParameter K i t) : Mat K) *ᵥ
      (sevenProjection K x).val
  exact root_covariance K neg i t x

theorem root_mem_stabilizer (neg : Bool) (i : Fin 2) (t : K) :
    rootEquiv A K neg i t∈stabilizer (LinearMap.ker (sevenProjection K)) :=
  mem_stabilizer_of_intertwines (sevenProjection K) (rootEquiv A K neg i t)
    (hyperplaneLinearHom K (naturalRoot K neg (exchangedNode i)
      (exceptionalParameter K i t))) (root_intertwines K neg i t)

theorem model_le_stabilizer :
    subgroup A K≤stabilizer (LinearMap.ker (sevenProjection K)) := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨neg,i,t,hg⟩
  have he : g=rootEquiv A K neg i t := by
    apply LinearEquiv.toLinearMap_injective
    exact hg
  subst g
  exact root_mem_stabilizer K neg i t

def modelToStabilizer : Model A K →* stabilizer (LinearMap.ker (sevenProjection K)) where
  toFun g := ⟨g.val,model_le_stabilizer K g.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

def representation : Model A K →* (axisHyperplane K ≃ₗ[K] axisHyperplane K) :=
  (descendedAction (sevenProjection K) (sevenProjection_surjective K)).comp
    (modelToStabilizer K)

theorem representation_intertwines (g : Model A K) (x : Space A K) :
    representation K g (sevenProjection K x)=sevenProjection K (g.val x) :=
  descendedAction_intertwines (sevenProjection K) (sevenProjection_surjective K)
    (modelToStabilizer K g) x

theorem representation_root (neg : Bool) (i : Fin 2) (t : K) :
    representation K (modelRoot A K neg i t)=
      hyperplaneLinearHom K (naturalRoot K neg (exchangedNode i)
        (exceptionalParameter K i t)) := by
  apply descendedAction_unique (sevenProjection K) (sevenProjection_surjective K)
    (modelToStabilizer K (modelRoot A K neg i t))
  intro x
  exact (root_intertwines K neg i t x).symm

end SymmetricSubgroupAsymptotics.CFSGGTwoOriginalExceptionalRepresentation
