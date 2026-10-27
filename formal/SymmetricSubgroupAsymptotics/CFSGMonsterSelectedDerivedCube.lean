import SymmetricSubgroupAsymptotics.CFSGMonsterSelectedDerivedInvolution

/-! A genuine order3 element in the ACTUAL Monster derived centralizer.
This is the anchored tail c*d, not a class name or root-image assertion.
Its nontriviality follows from the already proved actual c*e involution:
if c=d, that same involution has cube1 and hence is trivial. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMonsterSelectedDerivedCube
open CFSG.Models.MonsterConstruction CFSGMonsterSelectedDerivedInvolution

 theorem selected_mem_commutator : centralArm 0*centralArm 1∈commutator ↥nodeCentralizer := by
  have hab : Abelianization.of (centralArm 0)=Abelianization.of (centralArm 1) := by
    apply CFSGGeneration.commutative_involutions_eq_of_product_cube
    · rw [←map_pow,centralArm_square,map_one]
    · rw [←map_pow,centralArm_square,map_one]
    · rw [←map_mul,←map_pow,centralArm_cube 0 1 (by decide),map_one]
  rw [←Abelianization.ker_of ↥nodeCentralizer]
  change Abelianization.of (centralArm 0*centralArm 1)=1
  rw [map_mul,hab,←map_mul,←pow_two,centralArm_square,map_one]

 def selectedCube : CFSG.Models.Monster :=
  ⟨centralArm 0*centralArm 1,selected_mem_commutator⟩

 theorem selected_cube : selectedCube^3=1 := by
  apply Subtype.ext
  exact centralArm_cube 0 1 (by decide)

 theorem selected_ne_one (hn : ¬IsMulCommutative CFSG.Models.Monster) : selectedCube≠1 := by
  intro he
  have habprod := congrArg (fun z : CFSG.Models.Monster => z.val) he
  change centralArm 0*centralArm 1=1 at habprod
  have hab : centralArm 0=centralArm 1 := by
    calc
      centralArm 0=centralArm 0*1 := (mul_one _).symm
      _=centralArm 0*(centralArm 1*centralArm 1) := by rw [←pow_two,centralArm_square]
      _=(centralArm 0*centralArm 1)*centralArm 1 := (mul_assoc _ _ _).symm
      _=centralArm 1 := by rw [habprod,one_mul]
  have h3 : CFSGMonsterSelectedDerivedInvolution.selectedInvolution^3=1 := by
    apply Subtype.ext
    change (centralArm 0*centralArm 2)^3=1
    rw [hab]
    exact centralArm_cube 1 2 (by decide)
  have h : CFSGMonsterSelectedDerivedInvolution.selectedInvolution^2*
      CFSGMonsterSelectedDerivedInvolution.selectedInvolution=1 := by
    simpa only [pow_succ] using h3
  rw [CFSGMonsterSelectedDerivedInvolution.selected_square,one_mul] at h
  exact CFSGMonsterSelectedDerivedInvolution.selected_ne_one hn h

 theorem selected_order_three (hn : ¬IsMulCommutative CFSG.Models.Monster) :
    orderOf selectedCube=3 := by
  have hd := orderOf_dvd_of_pow_eq_one selected_cube
  have hn1 : orderOf selectedCube≠1 := by
    intro h
    exact selected_ne_one hn (orderOf_eq_one_iff.mp h)
  exact ((Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd).resolve_left hn1

end SymmetricSubgroupAsymptotics.CFSGMonsterSelectedDerivedCube
