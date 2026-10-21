import SymmetricSubgroupAsymptotics.BinaryElementary16GraphHeadRigidity
import SymmetricSubgroupAsymptotics.BinaryElementaryPhiZeroIntrinsicRadical
import SymmetricSubgroupAsymptotics.BinaryLinearConstraintCertificate
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! One selected derived-hyperplane pilot. The larger lower-layer space
already gives the required joint capacity512, so only three scalar
constraints on the actual11 kernel coordinates are needed. No2048-vector
assignment table, source group, or normal subgroup census is used. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.BinaryElementary32DerivedHyperplaneOne
local instance hyperplaneOneFactPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
abbrev V := Fin 16 → ZMod 2
abbrev K := BinaryElementary16GraphHeadRigidity.stateChart 0

def upperProjection : V →ₗ[ZMod 2] (Fin 8 → ZMod 2) where
  toFun v i := v ⟨8+i.val,by omega⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def lowerLayer : Submodule (ZMod 2) V := upperProjection.ker

def hyperplane : Submodule (ZMod 2) V :=
  BinaryElementaryPhiZeroIntrinsicRadical.radical.space ⊓ lowerLayer

private def inputMask : Fin 3 → ℕ := ![6,10,15]
private def generatorIndex : Fin 3 → Fin 4 := ![1,2,3]
private def constraint (i : Fin 3) : (Fin 11 → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  binaryRowFunctional (binaryVectorOfMask 11 (inputMask i))
private def actualConstraint (i : Fin 3) : (Fin 11 → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  (LinearMap.proj (0 : Fin 8)).comp (upperProjection.comp
    (((BinaryElementary16GraphHeadRigidity.action (generatorIndex i))-LinearMap.id).comp K.inclusion))
private theorem constraint_basis : ∀ i : Fin 3, ∀ j : Fin 11,
    constraint i (Pi.single j 1)=actualConstraint i (Pi.single j 1) := by decide +kernel
private theorem constraint_eq (i : Fin 3) : constraint i=actualConstraint i :=
  binaryLinearFunctional_ext_basis (constraint_basis i)

private abbrev proj11 (j : Fin 11) : (Fin 11 → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  LinearMap.proj j
private theorem constraint_zero : constraint 0=proj11 1+proj11 2 :=
  binaryLinearFunctional_ext_basis (by decide +kernel)
private theorem constraint_one : constraint 1=proj11 1+proj11 3 :=
  binaryLinearFunctional_ext_basis (by decide +kernel)
private theorem constraint_two : constraint 2=((proj11 0+proj11 1)+proj11 2)+proj11 3 :=
  binaryLinearFunctional_ext_basis (by decide +kernel)

private theorem four_relations : ∀ a : Fin 4 → ZMod 2,
    a 1+a 2=0 → a 1+a 3=0 → a 0+a 1+a 2+a 3=0 → ∀ i, a i=a 0 := by decide +kernel

private theorem first_four_equal (a : Fin 11 → ZMod 2)
    (ha : ∀ i, constraint i a=0) :
    a 1=a 0 ∧ a 2=a 0 ∧ a 3=a 0 := by
  have h6 := ha 0
  have h10 := ha 1
  have h15 := ha 2
  rw [constraint_zero] at h6
  rw [constraint_one] at h10
  rw [constraint_two] at h15
  change a 1+a 2=0 at h6
  change a 1+a 3=0 at h10
  change a 0+a 1+a 2+a 3=0 at h15
  have he := four_relations (fun i => a ⟨i.val,by omega⟩) h6 h10 h15
  exact ⟨he 1,he 2,he 3⟩

/-- Only the four actual original generators are tested. Any vector fixed
modulo the actual hyperplane satisfies these weaker lower-layer tests. -/
def FixedVectors := {v : V // v∈K.space ∧ ∀ i : Fin 4,
  upperProjection (BinaryElementary16GraphHeadRigidity.action i v-v)=0}

private def freeCoordinates (v : FixedVectors) : Fin 8 → ZMod 2 :=
  let a := K.coordinates v.val
  ![a 0,a 4,a 5,a 6,a 7,a 8,a 9,a 10]

private theorem fixed_first_four (v : FixedVectors) :
    (K.coordinates v.val) 1=(K.coordinates v.val) 0 ∧
    (K.coordinates v.val) 2=(K.coordinates v.val) 0 ∧
    (K.coordinates v.val) 3=(K.coordinates v.val) 0 := by
  apply first_four_equal
  intro i
  rw [constraint_eq]
  change (upperProjection
    (BinaryElementary16GraphHeadRigidity.action (generatorIndex i)
      (K.inclusion (K.coordinates v.val))-K.inclusion (K.coordinates v.val))) 0=0
  rw [(K.mem_iff v.val).mp v.property.1]
  exact congrFun (v.property.2 (generatorIndex i)) 0

private theorem freeCoordinates_injective : Function.Injective freeCoordinates := by
  intro v w he
  have hv := fixed_first_four v
  have hw := fixed_first_four w
  have hcoord : K.coordinates v.val=K.coordinates w.val := by
    funext i
    fin_cases i
    · exact congrFun he 0
    · exact hv.1.trans ((congrFun he 0).trans hw.1.symm)
    · exact hv.2.1.trans ((congrFun he 0).trans hw.2.1.symm)
    · exact hv.2.2.trans ((congrFun he 0).trans hw.2.2.symm)
    · exact congrFun he 1
    · exact congrFun he 2
    · exact congrFun he 3
    · exact congrFun he 4
    · exact congrFun he 5
    · exact congrFun he 6
    · exact congrFun he 7
  apply Subtype.ext
  calc
    v.val=K.inclusion (K.coordinates v.val) := ((K.mem_iff v.val).mp v.property.1).symm
    _ = K.inclusion (K.coordinates w.val) := congrArg K.inclusion hcoord
    _ = w.val := (K.mem_iff w.val).mp w.property.1

theorem fixed_card_le : Nat.card FixedVectors≤256 := by
  have hc := Nat.card_le_card_of_injective freeCoordinates freeCoordinates_injective
  simpa only [Nat.card_fun,Nat.card_fin,Nat.card_zmod] using hc

/-- Literal products of the four original generator operators; the
actual-source bridge will retain these SAME word masks. -/
def rowAction (i : Fin 16) : V →ₗ[ZMod 2] V :=
  (if i.val.testBit 0 then BinaryElementary16GraphHeadRigidity.action 0 else LinearMap.id).comp
  ((if i.val.testBit 1 then BinaryElementary16GraphHeadRigidity.action 1 else LinearMap.id).comp
  ((if i.val.testBit 2 then BinaryElementary16GraphHeadRigidity.action 2 else LinearMap.id).comp
   (if i.val.testBit 3 then BinaryElementary16GraphHeadRigidity.action 3 else LinearMap.id)))

def allowedTop : Finset (Fin 16) := Finset.univ.filter fun i =>
  ∀ j : Fin 11, upperProjection (rowAction i (K.inclusion (Pi.single j 1))-
    K.inclusion (Pi.single j 1))=0

theorem allowedTop_card : allowedTop.card=2 := by decide +kernel

theorem joint_capacity_le : Nat.card FixedVectors*allowedTop.card≤512 := by
  rw [allowedTop_card]
  have h := fixed_card_le
  omega

end SymmetricSubgroupAsymptotics.BinaryElementary32DerivedHyperplaneOne
