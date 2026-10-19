import SymmetricSubgroupAsymptotics.BinaryPlaneWreathNormalGenerators
import SymmetricSubgroupAsymptotics.BinaryPlaneScalarFourKernel

/-! The actual local binary linear group is S3, with the same displayed
cubic used by the scalar central-repeat coordinate constructor. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPlaneLinearSymmetricEquiv
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathNormalGenerators

theorem linear_card_six : Nat.card Linear=6 := by
  have hp : Nat.card Plane=4 := by simp [Plane]
  have he := Nat.card_congr BinaryPlanePermutationAffineEquiv.equiv.toEquiv
  change Nat.card (Equiv.Perm Plane)=Nat.card Model at he
  rw [Nat.card_perm,hp,SemidirectProduct.card,Nat.card_congr Multiplicative.toAdd,hp] at he
  norm_num only [show Nat.factorial 4=24 by decide] at he
  omega

def equivalence : Linear ≃* Equiv.Perm (Fin 3) := by
  letI : Fintype Linear := Fintype.ofFinite _
  have hc : Fintype.card Linear=Fintype.card (Equiv.Perm (Fin 3)) := by
    rw [←Nat.card_eq_fintype_card,←Nat.card_eq_fintype_card,linear_card_six,
      Nat.card_perm,Nat.card_fin]
    norm_num
  exact MulEquiv.ofBijective toThree
    ((Fintype.bijective_iff_injective_and_card toThree).mpr ⟨toThree_injective,hc⟩)

theorem cubic_order_three : orderOf BinaryPlaneScalarFourKernel.cubic=3 := by
  have hp : BinaryPlaneScalarFourKernel.cubic^3=1 := by
    apply LinearEquiv.ext
    intro v
    change BinaryPlaneScalarFourKernel.cubic
      (BinaryPlaneScalarFourKernel.cubic (BinaryPlaneScalarFourKernel.cubic v))=v
    revert v
    decide +kernel
  have hn : BinaryPlaneScalarFourKernel.cubic≠1 := by
    intro h
    have hv := congrArg (fun L : Linear => L ![1,0] 0) h
    norm_num [BinaryPlaneScalarFourKernel.cubic] at hv
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact orderOf_eq_prime hp hn

end SymmetricSubgroupAsymptotics.BinaryPlaneLinearSymmetricEquiv
