import SymmetricSubgroupAsymptotics.BinaryElementary32FiniteCapacity
import SymmetricSubgroupAsymptotics.BinaryLinearSolutionChart

/-! An eight-coordinate solution chart and four actual scalar displacement
rows bound every fixed vector for one literal derived hyperplane. No
assignment enumeration or externally supplied rank bound is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryElementary32FiniteCapacity
local instance elementaryHyperplaneCertificateFactPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
open BinaryElementary16GraphHeadRigidity

def hyperplaneInputFunctional (c : Fin 32) (i : Fin 4) :
    (Fin 11 → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  ((binaryRowFunctional (binaryVectorOfMask 5 c.val)).comp
    BinaryElementaryPhiZeroIntrinsicRadical.radical.coordinates).comp
      ((action i-LinearMap.id).comp K.inclusion)

theorem hyperplane_fixed_card_le_of_certificate (c : Fin 32)
    (C : BinaryCoordinateSpace 11 8) (input : Fin 4 → Fin 11 → ZMod 2)
    (cert : BinaryLinearConstraintCertificate input (binaryCoordinateDefectRows C))
    (hinput : ∀ i,binaryRowFunctional (input i)=hyperplaneInputFunctional c i) :
    Nat.card (fixedVectors (binaryFiveHyperplane BinaryElementaryPhiZeroIntrinsicRadical.radical c))≤256 := by
  let A := binaryFiveHyperplane BinaryElementaryPhiZeroIntrinsicRadical.radical c
  have hsol (v : fixedVectors A) : K.coordinates v.val∈C.space := by
    apply binaryCoordinate_mem_of_constraints C input cert
    intro i
    change binaryRowFunctional (input i) (K.coordinates v.val)=0
    rw [hinput]
    change binaryRowFunctional (binaryVectorOfMask 5 c.val)
      (BinaryElementaryPhiZeroIntrinsicRadical.radical.coordinates
        (action i (K.inclusion (K.coordinates v.val))-K.inclusion (K.coordinates v.val)))=0
    rw [(K.mem_iff v.val).mp v.property.1]
    exact (v.property.2 i).2
  let f : fixedVectors A → (Fin 8 → ZMod 2) := fun v => C.coordinates (K.coordinates v.val)
  have hf : Function.Injective f := by
    intro v z he
    have hcoord : K.coordinates v.val=K.coordinates z.val := by
      calc
        K.coordinates v.val=C.inclusion (C.coordinates (K.coordinates v.val)) :=
          ((C.mem_iff _).mp (hsol v)).symm
        _ = C.inclusion (C.coordinates (K.coordinates z.val)) := congrArg C.inclusion he
        _ = K.coordinates z.val := (C.mem_iff _).mp (hsol z)
    apply Subtype.ext
    calc
      v.val=K.inclusion (K.coordinates v.val) := ((K.mem_iff _).mp v.property.1).symm
      _ = K.inclusion (K.coordinates z.val) := congrArg K.inclusion hcoord
      _ = z.val := (K.mem_iff _).mp z.property.1
  have hc := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_fun,Nat.card_fin,Nat.card_zmod] using hc

end SymmetricSubgroupAsymptotics.BinaryElementary32FiniteCapacity
