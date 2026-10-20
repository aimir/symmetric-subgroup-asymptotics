import SymmetricSubgroupAsymptotics.OriginalKernelCenter

/-! A genuine order-three lift through an ORIGINAL elementary binary
kernel is obtained from any lift by its fourth power. No split extension
or abstract complement is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalKernelModuleChart
variable {G B : Type} [Group G] [Group B]
  (pi : G →* B) (A : Rep.{0} (ZMod 2) B) (E : OriginalKernelModuleChart pi A)

include E in
theorem exists_original_cubic_lift (hpi : Function.Surjective pi)
    (a : B) (ha : a^3=1) : ∃ g : G, g^3=1 ∧ pi g=a := by
  obtain ⟨u,hu⟩ := hpi a
  have hk : u^3∈pi.ker := by
    change pi (u^3)=1
    rw [map_pow,hu,ha]
  obtain ⟨z,hz⟩ := E.equiv.surjective ⟨u^3,hk⟩
  have hzc : E.element z.toAdd=u^3 := congrArg Subtype.val hz
  have h6 : u^6=1 := by
    change u^(3*2)=1
    rw [pow_mul,← hzc]
    exact E.element_sq z.toAdd
  refine ⟨u^4,?_,?_⟩
  · calc
      (u^4)^3=u^12 := by rw [← pow_mul]
      _=(u^6)^2 := by rw [← pow_mul]
      _=1 := by rw [h6,one_pow]
  · rw [map_pow,hu]
    change a^(3+1)=a
    rw [pow_succ,ha,one_mul]

end SymmetricSubgroupAsymptotics.OriginalKernelModuleChart
