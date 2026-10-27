import SymmetricSubgroupAsymptotics.CFSGCommutingBinaryFrameGeneration
import SymmetricSubgroupAsymptotics.External.CFSG.Models.Presentation

/-! A square relator for the commutator of an actual involution and an
arbitrary word supplies a genuine commuting binary frame. This does not
assert ordinary generation by that frame and one of its conjugates. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.InvolutoryCommutatorBinaryFrame

variable {G : Type*} [Group G]

theorem conjugate_square (a g : G) (ha : a ^ 2 = 1) :
    (g⁻¹ * a * g) ^ 2 = 1 := by
  calc
    (g⁻¹ * a * g) ^ 2 = g⁻¹ * a ^ 2 * g := by
      simp only [pow_two]
      group
    _ = 1 := by rw [ha, mul_one, inv_mul_cancel]

theorem commute_of_commutator_square (a g : G) (ha : a ^ 2 = 1)
    (hcomm : CFSG.Models.commWord a g ^ 2 = 1) :
    Commute a (g⁻¹ * a * g) := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right
    (by simpa only [pow_two] using ha)
  have hti : (g⁻¹ * a * g)⁻¹ = g⁻¹ * a * g :=
    inv_eq_of_mul_eq_one_right
      (by simpa only [pow_two] using conjugate_square a g ha)
  have hp : (a * (g⁻¹ * a * g)) ^ 2 = 1 := by
    simpa only [CFSG.Models.commWord, hai, mul_assoc] using hcomm
  have hi : (a * (g⁻¹ * a * g))⁻¹ = a * (g⁻¹ * a * g) :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hp)
  rw [mul_inv_rev, hti, hai] at hi
  exact hi.symm

def frame (a g : G) (ha : a ^ 2 = 1)
    (hcomm : CFSG.Models.commWord a g ^ 2 = 1) :
    CFSGCommutingBinaryFrameGeneration.Frame
      (CFSGCommutingBinaryFrameGeneration.pair a (g⁻¹ * a * g)) :=
  CFSGCommutingBinaryFrameGeneration.pairFrame a (g⁻¹ * a * g)
    ha (conjugate_square a g ha) (commute_of_commutator_square a g ha hcomm)

end SymmetricSubgroupAsymptotics.InvolutoryCommutatorBinaryFrame
