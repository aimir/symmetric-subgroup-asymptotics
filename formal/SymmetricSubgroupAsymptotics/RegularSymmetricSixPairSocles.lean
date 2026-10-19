import SymmetricSubgroupAsymptotics.BinarySixPointSymmetricMatrixBlocks
import SymmetricSubgroupAsymptotics.BinaryPairUniformQuotientSocles
import SymmetricSubgroupAsymptotics.OddPrimeDihedralNormalChain
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.RegularSymmetricSixPairSocles
local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

def action : DihedralGroup 3 →* Equiv.Perm (Fin 6) where
  toFun
    | .r i => BinarySixPointSymmetricMatrixBlocks.rotation^i.val
    | .sr i => BinarySixPointSymmetricMatrixBlocks.reflection*BinarySixPointSymmetricMatrixBlocks.rotation^i.val
  map_one' := rfl
  map_mul' := by
    rintro (i | i) (j | j) <;> apply Equiv.ext <;> intro x <;>
      revert i j x <;> decide +kernel

variable {U : Subgroup (Equiv.Perm (Fin 12))} (F : BinaryPairFrame U (Fin 6))
    (c b : U) (hc : F.top c=BinarySixPointSymmetricMatrixBlocks.rotation) (hb : F.top b=BinarySixPointSymmetricMatrixBlocks.reflection)
    (hle : F.top.range≤action.range)

include hc hb hle in
theorem image : F.top.range=action.range := by
  apply le_antisymm hle
  rintro _ ⟨g,rfl⟩
  have hr : BinarySixPointSymmetricMatrixBlocks.rotation∈F.top.range := ⟨c,hc⟩
  have hs : BinarySixPointSymmetricMatrixBlocks.reflection∈F.top.range := ⟨b,hb⟩
  cases g with
  | r i => exact F.top.range.pow_mem hr i.val
  | sr i => exact F.top.range.mul_mem hs (F.top.range.pow_mem hr i.val)

include hc hb hle in
theorem quotientSocle (N : Subgroup U) [N.Normal] : SocleNormalGeneratorBound (U ⧸ N) 2 := by
  have hu := BinarySixPointSymmetricMatrixBlocks.uniform_subgroup F.top.range
    (F.top.rangeRestrict c) (F.top.rangeRestrict b) hc hb
  apply F.quotientSocle_of_uniform_pair_action 1 1 hu ?_ N
  intro L hL
  letI := hL
  let e : action.range ≃* F.top.range := (MulEquiv.subgroupCongr (image F c b hc hb hle)).symm
  let f := e.toMonoidHom.comp action.rangeRestrict
  have hf : Function.Surjective f := e.surjective.comp action.rangeRestrict_surjective
  have htotal := normalSubgroups_total_of_surjective f hf
    (OddPrimeDihedralNormalChain.normal_total (p := 3) (by decide))
  obtain ⟨x,hx⟩ := normal_generating_singletons_of_finite_normal_total htotal L hL
  exact normalGen_le_of_fin_tuple x hx
end SymmetricSubgroupAsymptotics.RegularSymmetricSixPairSocles
