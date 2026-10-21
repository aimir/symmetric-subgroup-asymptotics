import SymmetricSubgroupAsymptotics.PermutationBinaryLargeSection
import SymmetricSubgroupAsymptotics.PermutationBinaryFourSection

/-! A small actual invariant denominator cannot hide a nonidentity
original permutation. This is the full-permutation-module case of the
checked large-section faithfulness theorem. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
noncomputable section
attribute [local instance] Fintype.ofFinite
namespace SymmetricSubgroupAsymptotics
local instance smallDenominatorFaithfulPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {G X : Type} [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] [MulAction.IsPretransitive G X]

theorem binary_permutation_eq_one_of_small_denominator
    (hG : IsPGroup 2 G) (x : X)
    (A : Subrepresentation (permutationFunctionRepresentation (ZMod 2) G X))
    (hsmall : 2*Module.finrank (ZMod 2) A.toSubmodule < Nat.card X)
    (g : G)
    (hdisplacement : ∀ v : X → ZMod 2,
      permutationFunctionRepresentation (ZMod 2) G X g v-v ∈ A.toSubmodule) : g=1 := by
  let sigma := PermutationBinaryFourSection.quotientRepresentation A
  let M : Subrepresentation (permutationFunctionRepresentation (ZMod 2) G X) := ⊤
  let q : M.toRepresentation.IntertwiningMap sigma := {
    toLinearMap := A.toSubmodule.mkQ.comp M.toSubmodule.subtype
    isIntertwining' _ := rfl }
  have hq : Function.Surjective q := by
    intro a
    obtain ⟨v,rfl⟩ := A.toSubmodule.mkQ_surjective a
    exact ⟨⟨v,Submodule.mem_top⟩,rfl⟩
  have hdim := A.toSubmodule.finrank_quotient_add_finrank
  have hlarge : Nat.card X < 2*Module.finrank (ZMod 2) ((X → ZMod 2) ⧸ A.toSubmodule) := by
    have hd : Module.finrank (ZMod 2) (X → ZMod 2)=Nat.card X := by
      rw [Module.finrank_pi,Fintype.card_eq_nat_card]
    rw [hd] at hdim
    omega
  have hi := permutationSection_injective_of_half_lt hG x sigma M q hq hlarge
  apply hi
  rw [map_one]
  apply LinearMap.ext
  intro a
  obtain ⟨v,rfl⟩ := A.toSubmodule.mkQ_surjective a
  change A.toSubmodule.mkQ
    (permutationFunctionRepresentation (ZMod 2) G X g v)=A.toSubmodule.mkQ v
  apply sub_eq_zero.mp
  rw [←map_sub]
  exact (Submodule.Quotient.mk_eq_zero A.toSubmodule).mpr (hdisplacement v)

end SymmetricSubgroupAsymptotics
