import SymmetricSubgroupAsymptotics.CFSGProjectiveAffineFieldLaws
import SymmetricSubgroupAsymptotics.CFSGProjectiveAffineDetermination

/-! An actual collineation fixing the standard projective frame is
faithfully determined by an automorphism of the original field. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGProjectiveFrameCoordinates
open CFSGProjectiveAffineChart
variable {F n : Type*} [Field F] [Fintype n] [DecidableEq n]

def frameFieldMap (b : Unit⊕n) (i j : n) (hij : i≠j) :
    frameStabilizer (F:=F) b→(F≃+*F) := fun f =>
  let h := (mem_frameStabilizer_iff b f.val).mp f.property
  coordinateRingAut f.val h.1 b h.2 i j hij

theorem frameFieldMap_injective (b : Unit⊕n) (i j : n) (hij : i≠j) :
    Function.Injective (frameFieldMap (F:=F) b i j hij) := by
  intro f g he
  have hf := (mem_frameStabilizer_iff b f.val).mp f.property
  have hg := (mem_frameStabilizer_iff b g.val).mp g.property
  apply Subtype.ext
  apply collineation_ext_of_affine f.val g.val hf.1 hg.1
  apply Equiv.ext
  intro v
  funext k
  calc
    affinePermutation f.val hf.1 v k=frameFieldMap b i j hij f (v k) :=
      affinePermutation_coordinateRingAut f.val hf.1 b hf.2 i j hij v k
    _=frameFieldMap b i j hij g (v k) := congrArg (fun s : F≃+*F => s (v k)) he
    _=affinePermutation g.val hg.1 v k :=
      (affinePermutation_coordinateRingAut g.val hg.1 b hg.2 i j hij v k).symm

theorem frameStabilizer_card_le [Finite F] (b : Unit⊕n) (i j : n) (hij : i≠j) :
    Nat.card (frameStabilizer (F:=F) b)≤Nat.card (F≃+*F) := by
  letI : Finite (F≃+*F) := Finite.of_injective
    (fun a : F≃+*F => (a : F→F)) DFunLike.coe_injective
  exact Nat.card_le_card_of_injective (frameFieldMap b i j hij) (frameFieldMap_injective b i j hij)

end SymmetricSubgroupAsymptotics.CFSGProjectiveFrameCoordinates
