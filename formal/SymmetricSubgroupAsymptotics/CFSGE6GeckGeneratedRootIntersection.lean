import SymmetricSubgroupAsymptotics.CFSGE6GeckOppositeParabolicRootIntersection
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRootGeneratedPGroup

/-! The opposite-parabolic intersection is retained inside the actual
fixed-root generated group J. The root chart is the image of its literal
fixed parameter subgroup under inclusion, not a chosen quotient lift. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckGeneratedRootIntersection
open CFSGE6GeckOppositeParabolicRootIntersection CFSGE6GeckOppositeOrbitParabolic
open CFSGE6GeckFixedOrbitRootGroups CFSGTwistedE6GeckRootGeneratedPGroup
open CFSGTwistedE6GeckRelativeRootGenerated CFSGTwistedE6GeckDiagramCovariance
variable (K : Type) [Field K] (sigma : K≃+*K)
local notation "J" => fixedRootGenerated K sigma

def oppositeParabolicGenerated (a : Fin 4) : Subgroup J :=
  (oppositeOrbitParabolic K sigma a).subgroupOf J

def orbitRootGenerated (a : Fin 4) : Subgroup J :=
  (fixedOrbitPositive K sigma a).map (Subgroup.inclusion (signedFixed_le_generated K sigma false))

theorem oppositeParabolicGenerated_map (a : Fin 4) :
    (oppositeParabolicGenerated K sigma a).map (J).subtype=oppositeOrbitParabolic K sigma a :=
  Subgroup.map_subgroupOf_eq_of_le (oppositeOrbitParabolic_le_generated K sigma a)

theorem negative_normalizer_le_oppositeParabolicGenerated (a : Fin 4) :
    Subgroup.normalizer (rootPart K sigma true : Set J)≤oppositeParabolicGenerated K sigma a := by
  have hn : (Subgroup.normalizer
      (signedFixed K sigma true : Set (Matrix GeckIndex GeckIndex K)ˣ)).subgroupOf J=
      Subgroup.normalizer (rootPart K sigma true : Set J) :=
    Subgroup.subgroupOf_normalizer_eq (signedFixed_le_generated K sigma true)
  intro x hx
  have hxN : x.val∈Subgroup.normalizer
      (signedFixed K sigma true : Set (Matrix GeckIndex GeckIndex K)ˣ) := by
    change x∈(Subgroup.normalizer
      (signedFixed K sigma true : Set (Matrix GeckIndex GeckIndex K)ˣ)).subgroupOf J
    rwa [hn]
  exact (show negativeGeneratedNormalizer K sigma≤oppositeOrbitParabolic K sigma a from
    le_sup_left) ⟨hxN,x.property⟩

theorem rootPart_inf_oppositeParabolicGenerated [Finite K]
    (hsigma : Function.Involutive sigma) (a : Fin 4) :
    rootPart K sigma false⊓oppositeParabolicGenerated K sigma a=orbitRootGenerated K sigma a := by
  apply Subgroup.ext
  intro x
  constructor
  · rintro ⟨hxU,hxP⟩
    let u : signedFixed K sigma false := ⟨x.val,hxU⟩
    have hu : u∈fixedOrbitPositive K sigma a := by
      rw [←fixed_positive_inf_oppositeOrbitParabolic K sigma hsigma a]
      exact hxP
    exact ⟨u,hu,Subtype.ext rfl⟩
  · rintro ⟨u,hu,rfl⟩
    refine ⟨u.property,?_⟩
    exact fixedOrbitPositive_le_oppositeOrbitParabolic K sigma hsigma a hu

end SymmetricSubgroupAsymptotics.CFSGE6GeckGeneratedRootIntersection
