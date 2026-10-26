import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoElevenGeneration
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoOrderFour
import SymmetricSubgroupAsymptotics.External.CFSG.Certificates.Mathieu22.GeneratedSubgroup
import Mathlib.Tactic.FinCases

/-! Necessary equations on images of the SAME original generating pair.
The first image is the selected firstElement; the second is variable u.
The originalA fifth-power identity is checked at every original point,
not inferred from the older point-period assertion. These necessary
equations are not asserted to define a presentation or an automorphism. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoRecoveredPairRelations
open CFSGMathieuTwentyTwoElevenGeneration CFSGMathieuTwentyTwoElevenWords

theorem originalA_fifth : originalA ^ 5 = 1 := by
  apply Subtype.ext
  change CFSG.Models.Mathieu22Construction.a ^ 5 = (1 : Equiv.Perm (Fin 22))
  ext p
  fin_cases p <;> decide +kernel

def relationValue {G : Type*} [Group G] (r : Fin 5) (v u : G) : G :=
  match r.val with
  | 0 => u ^ 11
  | 1 => (recoverA v u) ^ 5
  | 2 => (recoverB v u) ^ 8
  | 3 => (recoverA v u) ^ 3 * (recoverB v u) ^ 2 * v⁻¹
  | _ => recoverA v u * v * (recoverA v u)⁻¹ * u⁻¹

theorem relationValue_map {G H : Type*} [Group G] [Group H]
    (f : G →* H) (r : Fin 5) (v u : G) :
    f (relationValue r v u) = relationValue r (f v) (f u) := by
  fin_cases r <;> simp only [relationValue,recoverA,recoverB,map_pow,map_mul,map_inv]

theorem relationValue_coe (r : Fin 5) (v u : CFSG.Models.Mathieu22) :
    (relationValue r v u).val = relationValue r v.val u.val :=
  relationValue_map CFSG.Certificates.Mathieu22.M22Subgroup.subtype r v u

theorem original_pair_relations (r : Fin 5) :
    relationValue r firstElement secondElement = 1 := by
  fin_cases r
  · exact secondElement_pow_eleven
  · change (recoverA firstElement secondElement) ^ 5 = 1
    rw [recover_originalA]
    exact originalA_fifth
  · change (recoverB firstElement secondElement) ^ 8 = 1
    rw [recover_originalB]
    apply Subtype.ext
    exact CFSGMathieuTwentyTwoOrderFour.b_eighth
  · change (recoverA firstElement secondElement) ^ 3 *
      (recoverB firstElement secondElement) ^ 2 * firstElement⁻¹ = 1
    rw [recover_originalA,recover_originalB]
    change firstElement * firstElement⁻¹ = 1
    exact mul_inv_cancel _
  · change recoverA firstElement secondElement * firstElement *
      (recoverA firstElement secondElement)⁻¹ * secondElement⁻¹ = 1
    rw [recover_originalA]
    change secondElement * secondElement⁻¹ = 1
    exact mul_inv_cancel _

def Accepts (u : CFSG.Models.Mathieu22) : Prop :=
  ∀ r : Fin 5, relationValue r firstElement u = 1

theorem accepts_of_fixed_first (f : MulAut CFSG.Models.Mathieu22)
    (hf : f firstElement = firstElement) : Accepts (f secondElement) := by
  intro r
  have h := congrArg f (original_pair_relations r)
  have hm := relationValue_map f.toMonoidHom r firstElement secondElement
  have he : relationValue r (f firstElement) (f secondElement) = 1 :=
    hm.symm.trans (by simpa only [map_one] using h)
  simpa only [hf] using he

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoRecoveredPairRelations
