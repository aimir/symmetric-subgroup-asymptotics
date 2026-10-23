import SymmetricSubgroupAsymptotics.CFSGTwistedE6OriginalGoodSylow
import SymmetricSubgroupAsymptotics.CFSGCentralKernelPElements
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOppositeIntersection
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateHeight

/-! Opposite E6 action images are disjoint. This uses the proved central
kernel and injectivity on one actual ambient Sylow to separate ALL
p-elements; separate injectivity of U and V alone is not used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOppositeActionImages
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckSourceAction
open CFSGTwistedE6GeckPositiveTwist CFSGTwistedE6GeckPositiveActionInjective
open CFSGTwistedE6GeckAmbientPositiveSylow CFSGTwistedE6GeckFixedRangePreimage
open CFSGTwistedE6GeckRelativeRootGenerated CFSGTwistedE6GeckRootGeneratedPGroup
open CFSGTwistedE6GeckDerivedRootGeneration CFSGTwistedE6OriginalGoodSylow
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoCoordinatePositivePGroup
open CFSGNormTwoGeckOppositeIntersection CFSGNormTwoCoordinateHeight
open CFSGSerreOrdinaryTwists CFSGTwistedE6FixedA2
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos

abbrev AmbientSigned (K : Type) [Field K] (neg : Bool) : Subgroup (MatrixGroup K) :=
  (SignedUpper K neg).subgroupOf (MatrixGroup K)

theorem ambient_signed_isPGroup (K : Type) [Field K] (p : ℕ)
    [Fact p.Prime] [CharP K p] (neg : Bool) : IsPGroup p (AmbientSigned K neg) := by
  let f : AmbientSigned K neg →* SignedUpper K neg :=
    { toFun:=fun x=>⟨x.val.val,x.property⟩
      map_one':=rfl
      map_mul':=fun _ _=>rfl }
  have hf : Function.Injective f := by
    intro x y he
    have hunit := congrArg (fun z : SignedUpper K neg=>z.val) he
    change x.val.val=y.val.val at hunit
    exact Subtype.ext (Subtype.ext hunit)
  exact (rootGroup_isPGroup A hd hs hp ho E6Index K p neg).of_injective f hf

theorem ambient_signed_inf (K : Type) [Field K] :
    AmbientSigned K false ⊓ AmbientSigned K true=⊥ := by
  apply le_antisymm _ bot_le
  intro u hu
  have hh : u.val∈Positive K ⊓ Negative K := hu
  change u.val∈rootGroup A hs hp E6Base E6Index K false ⊓
    rootGroup A hs hp E6Base E6Index K true at hh
  rw [positive_inf_negative A hs hp E6Base E6Index coordinateHeight
    (simple_height A hd hs hp ho) K,Subgroup.mem_bot] at hh
  exact Subgroup.mem_bot.mpr (Subtype.ext hh)

theorem ambient_sylow_action_injective (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    Function.Injective ((matrixAction K).comp (ambientPositiveSylow K p : Subgroup (MatrixGroup K)).subtype) := by
  change Function.Injective ((matrixAction K).comp (AmbientPositive K).subtype)
  intro x y he
  let u : Positive K := ⟨x.val.val,x.property⟩
  let v : Positive K := ⟨y.val.val,y.property⟩
  have hxy : positiveAction K u=positiveAction K v := he
  have hroot := positiveAction_injective K p hxy
  have hunit := congrArg (fun z : Positive K=>z.val) hroot
  change x.val.val=y.val.val at hunit
  exact Subtype.ext (Subtype.ext hunit)

theorem ambient_opposite_action_inf (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    (AmbientSigned K false).map (matrixAction K) ⊓
      (AmbientSigned K true).map (matrixAction K)=⊥ :=
  CFSGCentralKernelPElements.disjoint_map (matrixAction K) (ambientPositiveSylow K p)
    (ambient_sylow_action_injective K p) (matrixAction_kernel_le_center K)
    (AmbientSigned K false) (AmbientSigned K true)
    (ambient_signed_isPGroup K p false) (ambient_signed_isPGroup K p true) (ambient_signed_inf K)

theorem generated_opposite_action_inf (K : Type) [Field K] [Finite K]
    (sigma : K≃+*K) (p : ℕ) [Fact p.Prime] [CharP K p] :
    (rootPart K sigma false).map (generatedAction K sigma) ⊓
      (rootPart K sigma true).map (generatedAction K sigma)=⊥ := by
  apply le_antisymm _ bot_le
  rintro a ⟨⟨u,hu,rfl⟩,v,hv,he⟩
  let x : MatrixGroup K := Subgroup.inclusion (fixedRootGenerated_le_matrixGroup K sigma) u
  let y : MatrixGroup K := Subgroup.inclusion (fixedRootGenerated_le_matrixGroup K sigma) v
  have hx : x∈AmbientSigned K false := hu.1
  have hy : y∈AmbientSigned K true := hv.1
  have hh : matrixAction K x∈(AmbientSigned K false).map (matrixAction K) ⊓
      (AmbientSigned K true).map (matrixAction K) :=
    ⟨⟨x,hx,rfl⟩,⟨y,hy,he⟩⟩
  rw [ambient_opposite_action_inf K p,Subgroup.mem_bot] at hh
  exact Subgroup.mem_bot.mpr hh

local instance (q : CFSG.PrimePower) : Fact q.prime.Prime := ⟨q.prime_isPrime⟩

theorem original_derived_opposite_parts_inf (q : CFSG.PrimePower) :
    (rootPart (q.Extension 2) (definingFieldAutomorphism q 2) false).map (generatedToDerived q) ⊓
      (rootPart (q.Extension 2) (definingFieldAutomorphism q 2) true).map (generatedToDerived q)=⊥ := by
  apply Subgroup.map_injective (f:=(derivedImageAction q).range.subtype) Subtype.val_injective
  rw [Subgroup.map_inf _ _ _ Subtype.val_injective,Subgroup.map_bot]
  simp only [Subgroup.map_map]
  change (rootPart (q.Extension 2) (definingFieldAutomorphism q 2) false).map
      (generatedAction (q.Extension 2) (definingFieldAutomorphism q 2)) ⊓
    (rootPart (q.Extension 2) (definingFieldAutomorphism q 2) true).map
      (generatedAction (q.Extension 2) (definingFieldAutomorphism q 2))=⊥
  exact generated_opposite_action_inf (q.Extension 2) (definingFieldAutomorphism q 2) q.prime

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOppositeActionImages
