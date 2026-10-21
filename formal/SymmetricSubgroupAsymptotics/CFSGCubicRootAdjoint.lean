import SymmetricSubgroupAsymptotics.CFSGSquareZeroAdjoint

/-! An actual cube-zero matrix and a vanishing sandwich give the
length-three adjoint identity needed at a short B root. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGCubicRootAdjoint
variable {B : Type*} [Ring B]

theorem lie_lie_lie (e x : B) (he : e^3=0) (hex : e*x*e=0) :
    ⁅e,⁅e,⁅e,x⁆⁆⁆=0 := by
  have hleft : (e*e)*e=0 := by simpa only [pow_succ,pow_two,pow_zero,one_mul] using he
  have hl : (e*e)*x*e=0 := by
    calc
      (e*e)*x*e=e*(e*x*e) := by noncomm_ring
      _=0 := by rw [hex,mul_zero]
  have hr : e*x*(e*e)=0 := by
    calc
      e*x*(e*e)=(e*x*e)*e := by noncomm_ring
      _=0 := by rw [hex,zero_mul]
  have hh : ⁅e,⁅e,⁅e,x⁆⁆⁆=
      ((e*e)*e)*x-((e*e)*x*e+(e*e)*x*e+(e*e)*x*e)+
      (e*x*(e*e)+e*x*(e*e)+e*x*(e*e))-x*((e*e)*e) := by
    simp only [Ring.lie_def]
    noncomm_ring
  rw [hh,hleft,hl,hr]
  simp only [zero_mul,mul_zero,zero_add,add_zero,sub_zero]

end SymmetricSubgroupAsymptotics.CFSGCubicRootAdjoint
