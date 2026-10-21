import SymmetricSubgroupAsymptotics.CFSGPSLTwoGeometry
import SymmetricSubgroupAsymptotics.CFSGPSLTwoWeylWordRigidity
import SymmetricSubgroupAsymptotics.CFSGPSLTwoRootGenerationRigidity

/-! The actual PSL2 opposite-pair restriction kernel is killed by the
constant Weyl word. The residual torus parameter is killed in the original
central quotient, rather than falsely forced to be a particular SL scalar. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGPSLTwoRootCoordinates
open CFSGTypeASLTwoWeyl CFSGTypeARootTorus CFSGPSLTwoGeometry
variable {F : Type*} [Field F]

theorem projective_weyl_torus (c : Fˣ) :
    projectiveWeyl*projectiveTorus c*(projectiveWeyl (F:=F))⁻¹=projectiveTorus c⁻¹ := by
  change projection (weyl (F:=F))*projection (torus (by decide : (0 : Fin 2)≠1) c)*
    (projection (weyl (F:=F)))⁻¹=projection (torus (by decide : (0 : Fin 2)≠1) c⁻¹)
  rw [←map_inv,←map_mul,←map_mul,weyl_torus]

theorem eq_one_of_fixed_root_and_weyl_coset (f : MulAut (PSL (F:=F)))
    (hfix : ∀ u : projectiveRoot (F:=F),f u.val=u.val)
    (hY : f projectiveWeyl*(projectiveWeyl (F:=F))⁻¹∈pairTorus (F:=F)) : f=1 := by
  have hfu : f (projectiveUpper (1 : F))=projectiveUpper 1 :=
    hfix ⟨projectiveUpper 1,projectiveUpper_mem 1⟩
  have hword := congrArg f (projectiveWeyl_word (F:=F))
  simp only [map_mul,map_inv,hfu] at hword
  obtain ⟨c,hc⟩ := hY
  have hfc : f projectiveWeyl=projectiveTorus c*projectiveWeyl := by
    have hc' : projectiveTorus c=f projectiveWeyl*projectiveWeyl⁻¹ := hc
    calc
      _=(f projectiveWeyl*projectiveWeyl⁻¹)*projectiveWeyl := by group
      _=projectiveTorus c*projectiveWeyl := by rw [←hc']
  have hmove : projectiveTorus c*projectiveWeyl=projectiveWeyl*projectiveTorus c⁻¹ := by
    calc
      _=(projectiveWeyl*projectiveTorus c⁻¹*projectiveWeyl⁻¹)*projectiveWeyl := by
        rw [projective_weyl_torus,inv_inv]
      _=projectiveWeyl*projectiveTorus c⁻¹ := by group
  rw [hmove] at hfc
  rw [hfc] at hword
  have ht : projectiveTorus c⁻¹=1 := projective_weyl_torus_word_rigidity c⁻¹ hword
  apply automorphism_eq_one_of_root_and_weyl f hfix
  rw [hfc,ht,mul_one]

end SymmetricSubgroupAsymptotics.CFSGPSLTwoRootCoordinates
