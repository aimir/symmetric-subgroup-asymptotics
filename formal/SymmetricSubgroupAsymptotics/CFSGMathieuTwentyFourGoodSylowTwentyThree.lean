import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourActualRepresentation
import SymmetricSubgroupAsymptotics.SimpleInvolutionPrimeDegreeGoodSylow
import Mathlib.Tactic.FinCases

/-! The exact pinned M24 presentation has good Sylow prime23, using its
faithful24-point action and singleton23-cycle product. Prime-square
nondivisibility comes from the degree-factorial wrapper internally.
No heavy actual-order certificate, recovery, or surjectivity is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourGoodSylowTwentyThree
open CFSG.Models.Presentations.M24 CFSGMathieuTwentyFourActualRepresentation
local instance : Fact (Nat.Prime 23) := ⟨by decide⟩

def pinnedX : Model := PresentedGroup.of (0 : Fin 2)
def pinnedY : Model := PresentedGroup.of (1 : Fin 2)

theorem pinnedX_square : pinnedX ^ 2 = 1 := by
  have h := PresentedGroup.one_of_mem
    (rels := {w | w ∈ relators}) (x := (FreeGroup.of (0 : Fin 2)) ^ 2)
    (by change _ ∈ relators; exact List.mem_cons_self)
  simpa only [pinnedX, map_pow, PresentedGroup.of] using h

theorem presentation_pair_closure : Subgroup.closure ({pinnedX, pinnedY} : Set Model) = ⊤ := by
  apply top_unique
  rw [← PresentedGroup.closure_range_of {w | w ∈ relators}]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact Subgroup.subset_closure (by simp [pinnedX])
  · exact Subgroup.subset_closure (by simp [pinnedY])

theorem pinnedProduct_cycleType :
    (permutationRepresentation (pinnedX * pinnedY)).cycleType = {23} := by
  change (permutationRepresentation
    ((PresentedGroup.of (0 : Fin 2)) * (PresentedGroup.of (1 : Fin 2)))).cycleType = _
  rw [map_mul, permutationRepresentation_of_zero, permutationRepresentation_of_one]
  exact CFSGMathieuTwentyFourPresentationWords.product_cycleType

theorem goodSylowPrime [Finite Model] [IsSimpleGroup Model] :
    CFSGReduction.GoodSylowPrime Model 23 := by
  letI : MulAction Model (Fin 24) := MulAction.compHom (Fin 24) permutationRepresentation
  letI : FaithfulSMul Model (Fin 24) := {
    eq_of_smul_eq_smul := fun {a b} hab =>
      permutationRepresentation_injective (Equiv.Perm.ext hab) }
  apply SimpleInvolutionPrimeCycleGoodSylow.goodSylowPrime_of_prime_degree (p := 23) (n := 24)
    pinnedX pinnedY pinnedX_square presentation_pair_closure (Or.inr rfl)
  have he : MulAction.toPermHom Model (Fin 24) (pinnedX * pinnedY) =
      permutationRepresentation (pinnedX * pinnedY) := by
    ext i
    rfl
  rw [he]
  exact pinnedProduct_cycleType

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourGoodSylowTwentyThree
