import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckSimpleParameters
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalProjection
import SymmetricSubgroupAsymptotics.CFSGCentralKernelPElements

/-! All four literal signed simple charts inject into the same
original G2 model. The original central kernel is separated on actual
p-subgroups by the checked positive Sylow injection. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalSimpleParameters
open CFSGGTwoD4GeckSimpleParameters CFSGGTwoD4GeckOriginalProjection
open CFSGTrialityGeckGeneratedSylow CFSGTrialityGeckRootGeneratedPGroup
open CFSGTrialityGeckRelativeRootGenerated CFSG.Models.Chevalley
variable (K : Type) [Field K] [Finite K] [IsSimpleGroup (Projective CartanMatrix.G₂ K)]

theorem original_injective_on_rootPart (isNegative : Bool) :
    Function.Injective ((generatedToOriginal K).comp
      (rootPart K (RingEquiv.refl K) isNegative).subtype) := by
  letI : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K (ringChar K)⟩
  let P := positiveSylow K (RingEquiv.refl K) (ringChar K)
  have hpinj : Function.Injective ((generatedToOriginal K).comp (P : Subgroup
      (fixedRootGenerated K (RingEquiv.refl K))).subtype) := by
    intro x y he
    apply Subtype.ext
    apply generatedToOriginal_injOn_positive K
    · rw [←positiveSylow_coe K (RingEquiv.refl K) (ringChar K)]
      exact x.property
    · rw [←positiveSylow_coe K (RingEquiv.refl K) (ringChar K)]
      exact y.property
    · exact he
  exact CFSGCentralKernelPElements.p_subgroup_injective (generatedToOriginal K)
    P hpinj (generatedToOriginal_kernel_le_center K) _
    (rootPart_isPGroup K (RingEquiv.refl K) (ringChar K) isNegative)

def originalSimpleHom (isNegative a : Bool) : Multiplicative K →* Projective CartanMatrix.G₂ K :=
  (generatedToOriginal K).comp (simpleGeneratedHom K isNegative a)

theorem originalSimpleHom_apply (isNegative a : Bool) (t : Multiplicative K) :
    originalSimpleHom K isNegative a t =
      generatedToOriginal K (simpleGeneratedHom K isNegative a t) := rfl

theorem originalSimpleHom_injective (isNegative a : Bool) :
    Function.Injective (originalSimpleHom K isNegative a) := by
  intro t u he
  have hh := original_injective_on_rootPart K isNegative
    (show (generatedToOriginal K).comp (rootPart K (RingEquiv.refl K) isNegative).subtype
        ⟨simpleGeneratedHom K isNegative a t, simpleGeneratedHom_mem_rootPart K isNegative a t⟩ =
      (generatedToOriginal K).comp (rootPart K (RingEquiv.refl K) isNegative).subtype
        ⟨simpleGeneratedHom K isNegative a u, simpleGeneratedHom_mem_rootPart K isNegative a u⟩
      from he)
  apply simpleGeneratedHom_injective K isNegative a
  exact congrArg (fun z : rootPart K (RingEquiv.refl K) isNegative => z.val) hh

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalSimpleParameters
