import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralFullImageHead
import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralSymmetricTop

/-! Joint rather than independently added bounds for actual signed S4
extensions. The proper-image and full-image branches use different retained
kernel information. Literal adapters must prove both kernel inputs. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TwelvePointRemainingStructural
local instance signedTopHead_binaryPrimeFact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable {G : Type} [Group G] [Finite G]

theorem signed_symmetric_top_relative_head_le_two
    (beta : G →* Equiv.Perm (Fin 4)) (hbeta : Function.Surjective beta)
    (hK : IsMulCommutative beta.ker)
    (hkernel : ∀ (L : Subgroup G) [L.Normal], L ≤ beta.ker →
      Module.finrank (ZMod 2) (primeRelativeCharacters 2 L) ≤ 2)
    (hab : Nat.card (G ⧸ commutator G) ≤ 4)
    (M : Subgroup G) [M.Normal] :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 M) ≤ 2 := by
  let I := M.map beta
  letI : I.Normal := Subgroup.Normal.map inferInstance beta hbeta
  by_cases hfull : I = ⊤
  · have hsup : M ⊔ beta.ker = ⊤ := by
      have h := congrArg (Subgroup.comap beta) hfull
      simpa only [I, Subgroup.comap_map_eq, Subgroup.comap_top] using h
    have hp := (relativeHead_pow_le_abelianization_card 2 beta.ker M
      (by simpa only [sup_comm] using hsup) hK).trans hab
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hp
  · let e := QuotientGroup.quotientKerEquivOfSurjective beta hbeta
    have he : (normalChainQuotient beta.ker M).map e.toMonoidHom = I := by
      change (M.map (QuotientGroup.mk' beta.ker)).map e.toMonoidHom = M.map beta
      rw [Subgroup.map_map]
      rfl
    have hzero : Module.finrank (ZMod 2)
        (primeRelativeCharacters 2 (normalChainQuotient beta.ker M)) = 0 :=
      (relativeCharacterAmbientCongr 2 e (normalChainQuotient beta.ker M) I he).finrank_eq.symm.trans
        (proper_normal_binary_relative_head_zero I hfull)
    calc
      _ ≤ Module.finrank (ZMod 2) (primeRelativeCharacters 2 (M ⊓ beta.ker)) +
          Module.finrank (ZMod 2)
            (primeRelativeCharacters 2 (normalChainQuotient (M ⊓ beta.ker) M)) :=
        primeRelativeHead_chain_le (M ⊓ beta.ker) M 2 inf_le_left
      _ = Module.finrank (ZMod 2) (primeRelativeCharacters 2 (M ⊓ beta.ker)) +
          Module.finrank (ZMod 2)
            (primeRelativeCharacters 2 (normalChainQuotient beta.ker M)) :=
        congrArg (Module.finrank (ZMod 2) (primeRelativeCharacters 2 (M ⊓ beta.ker)) + ·)
          (primeRelativeHead_second_isomorphism 2 M beta.ker)
      _ ≤ 2 := by
        rw [hzero, Nat.add_zero]
        exact hkernel (M ⊓ beta.ker) inf_le_right

end SymmetricSubgroupAsymptotics.TwelvePointRemainingStructural
