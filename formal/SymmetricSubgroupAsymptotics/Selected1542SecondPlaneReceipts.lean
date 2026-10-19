import SymmetricSubgroupAsymptotics.Selected1542FirstCenterData

/-! The same original N8 modulo the literal central involution has three
nonzero cosets, cyclically conjugate by the actual first source generator. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Selected1542QuotientStructure

def secondPlaneIndex (j : Fin 3) : Fin 8 := (![2,1,4] : Fin 3 → Fin 8) j

def secondPlaneRepresentative (j : Fin 3) : Equiv.Perm (Fin 16) :=
  normalElements (secondPlaneIndex j)

set_option maxHeartbeats 1000000 in
theorem secondPlane_cover : ∀ n : Fin 8,
    (∀ p : Fin 16, normalElements n p=p) ∨
    (∀ p : Fin 16, normalElements n p=firstCenterZ p) ∨
    ∃ j : Fin 3,
      (∀ p : Fin 16, normalElements n p=secondPlaneRepresentative j p) ∨
      (∀ p : Fin 16, normalElements n p=(secondPlaneRepresentative j*firstCenterZ) p) := by
  decide +kernel

set_option maxHeartbeats 1000000 in
theorem secondPlane_cycle : ∀ j : Fin 3,
    (∀ p : Fin 16, (sourceGenerators 0*secondPlaneRepresentative j*(sourceGenerators 0)⁻¹) p=
      secondPlaneRepresentative (j+1) p) ∨
    (∀ p : Fin 16, (sourceGenerators 0*secondPlaneRepresentative j*(sourceGenerators 0)⁻¹) p=
      (secondPlaneRepresentative (j+1)*firstCenterZ) p) := by
  decide +kernel

set_option maxHeartbeats 1000000 in
theorem secondPlane_distinct : ∀ (i j : Fin 3),
    ((∀ p : Fin 16, secondPlaneRepresentative i p=secondPlaneRepresentative j p) ∨
      (∀ p : Fin 16, secondPlaneRepresentative i p=(secondPlaneRepresentative j*firstCenterZ) p)) → i=j := by
  decide +kernel

set_option maxHeartbeats 1000000 in
theorem secondPlane_nonzero : ∀ j : Fin 3,
    (∃ p : Fin 16, secondPlaneRepresentative j p≠p) ∧
      (∃ p : Fin 16, secondPlaneRepresentative j p≠firstCenterZ p) := by
  decide +kernel

set_option maxHeartbeats 1000000 in
theorem secondPlane_top_powers : ∀ t : CyclicThree, ∃ r : Fin 3,
    (NaturalA4ScalarFourHead.top (alternatingGenerator 0 0))^r.val=t := by
  decide +kernel

end SymmetricSubgroupAsymptotics.Selected1542QuotientStructure
