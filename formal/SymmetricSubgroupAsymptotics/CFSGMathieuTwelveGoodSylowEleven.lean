import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveGoodSylowThree
import SymmetricSubgroupAsymptotics.SimpleInvolutionPrimeCycleGoodSylow

/-! A second, direct good-Sylow proof for the same pinned M12 model uses
its11-cycle product in the faithful12-action. The checked ternary proof is
retained; this optional adapter exhibits the shared prime-cycle argument.
No surjectivity or recovery certificate is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwelveGoodSylowEleven
open CFSG.Models.Presentations.M12 CFSGMathieuTwelveActualRepresentation
open CFSGMathieuTwelveGoodSylowThree
local instance : Fact (Nat.Prime 11) := ⟨by decide⟩

theorem pinnedProduct_cycleType :
    (permutationRepresentation (pinnedX * pinnedY)).cycleType = {11} := by
  change (permutationRepresentation
    ((PresentedGroup.of (0 : Fin 2)) * (PresentedGroup.of (1 : Fin 2)))).cycleType = _
  rw [map_mul, permutationRepresentation_of_zero, permutationRepresentation_of_one]
  decide +kernel

theorem prime_square_not_dvd [IsSimpleGroup Model] : ¬ (11 : ℕ) ^ 2 ∣ Nat.card Model := by
  intro h
  exact (by decide : ¬ (11 : ℕ) ^ 2 ∣ 95040) (h.trans card_dvd)

theorem goodSylowPrime [Finite Model] [IsSimpleGroup Model] :
    CFSGReduction.GoodSylowPrime Model 11 := by
  letI : MulAction Model (Fin 12) := MulAction.compHom (Fin 12) permutationRepresentation
  letI : FaithfulSMul Model (Fin 12) := {
    eq_of_smul_eq_smul := fun {a b} hab =>
      permutationRepresentation_injective (Equiv.Perm.ext hab) }
  apply SimpleInvolutionPrimeCycleGoodSylow.goodSylowPrime (p := 11) (n := 12)
    pinnedX pinnedY pinnedX_square presentation_pair_closure (Or.inr rfl) prime_square_not_dvd
  have he : MulAction.toPermHom Model (Fin 12) (pinnedX * pinnedY) =
      permutationRepresentation (pinnedX * pinnedY) := by
    ext i
    rfl
  rw [he]
  exact pinnedProduct_cycleType

end SymmetricSubgroupAsymptotics.CFSGMathieuTwelveGoodSylowEleven
