import SymmetricSubgroupAsymptotics.BinaryPairLiftCarryExponent
import SymmetricSubgroupAsymptotics.PGroupElementaryAbelianizationRank

/-! Full original abelianization order saturation identifies the actual
pair-kernel radical. Only after an actual carry theorem proves exponent
two does order 1024 force ten ordinary generators. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

namespace BinaryPairFrame
variable {X : Type} [Finite X] {w : ℕ} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin w))

theorem relativeRadical_eq_inf_commutator_of_actual_abelianization_saturation
    (hU : IsPGroup 2 U)
    (hsat : Nat.card (Abelianization U) =
      2 ^ MarkedC4.normalGen F.top.ker * Nat.card (Abelianization F.top.range)) :
    primeRelativeRadical 2 F.top.ker = F.top.ker ⊓ commutator U := by
  have he := pGroup_relativeRadical_eq_inf_commutator_of_abelianization_saturation
    2 hU F.top.rangeRestrict F.top.rangeRestrict_surjective
    (fun k => F.physical_kernel_pow_two ⟨k.val,by
      simpa only [MonoidHom.ker_rangeRestrict] using k.property⟩)
    (by simpa only [MonoidHom.ker_rangeRestrict] using hsat)
  simpa only [MonoidHom.ker_rangeRestrict] using he

end BinaryPairFrame

theorem binary_genRank_ge_ten_of_full_abelianization_card_and_exponent
    {G : Type} [Group G] [Finite G] (hG : IsPGroup 2 G)
    (hcard : Nat.card (Abelianization G) = 1024)
    (hexp : ∀ a : Abelianization G, a ^ 2 = 1) : 10 ≤ MarkedC4.genRank G := by
  have he := pGroup_abelianization_card_eq_pow_genRank 2 hG hexp
  rw [hcard] at he
  by_contra h
  have hn : MarkedC4.genRank G ≤ 9 := by omega
  have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hn
  norm_num at hp
  omega

end SymmetricSubgroupAsymptotics
