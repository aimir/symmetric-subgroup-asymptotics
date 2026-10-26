import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeActualRepresentation
import SymmetricSubgroupAsymptotics.SimpleInvolutionPrimeCycleGoodSylow
import Mathlib.Tactic.FinCases

/-! The actual pinned M23 presentation has good Sylow prime23. The literal
injective23-action makes the product of its presentation generators one
23-cycle, and23² does not divide the actual order bound10200960. The
generic simple-group argument supplies two generating23-subgroups and a
soluble cyclic Sylow normalizer. No recovery or surjectivity is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeGoodSylowTwentyThree
open CFSG.Models.Presentations.M23 CFSGMathieuTwentyThreeActualRepresentation
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
  decide +kernel

theorem prime_square_not_dvd [IsSimpleGroup Model] : ¬ (23 : ℕ) ^ 2 ∣ Nat.card Model := by
  intro h
  exact (by decide : ¬ (23 : ℕ) ^ 2 ∣ 10200960) (h.trans card_dvd)

theorem goodSylowPrime [Finite Model] [IsSimpleGroup Model] :
    CFSGReduction.GoodSylowPrime Model 23 := by
  letI : MulAction Model (Fin 23) := MulAction.compHom (Fin 23) permutationRepresentation
  letI : FaithfulSMul Model (Fin 23) := {
    eq_of_smul_eq_smul := fun {a b} hab =>
      permutationRepresentation_injective (Equiv.Perm.ext hab) }
  apply SimpleInvolutionPrimeCycleGoodSylow.goodSylowPrime (p := 23) (n := 23)
    pinnedX pinnedY pinnedX_square presentation_pair_closure (Or.inl rfl) prime_square_not_dvd
  have he : MulAction.toPermHom Model (Fin 23) (pinnedX * pinnedY) =
      permutationRepresentation (pinnedX * pinnedY) := by
    ext i
    rfl
  rw [he]
  exact pinnedProduct_cycleType

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeGoodSylowTwentyThree
