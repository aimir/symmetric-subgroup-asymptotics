import SymmetricSubgroupAsymptotics.SixPairCoarseWreathHead

/-! The original action preserving three physical pairs of pairs embeds
in eight local permutations per fibre and its actual three-point top.
The order bound is 8^3*6, with no normal or transitive-group census. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SixPairThreePairOriginalOrder
open BinaryTwoLayerLocalClassTwo

abbrev Local := {a : Equiv.Perm Points // Preserves a}

private theorem local_card : Nat.card Local=8 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

variable {X I : Type} {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U I)
  (E : ProductBlockFrame F.top.range (Fin 3) (ZMod 2))

def encoding (u : U) : (Fin 3 → Local) × Equiv.Perm (Fin 3) :=
  (fun j => ⟨((SixPairNestedTopFrames.nestedFrame F E).wreathEmbedding u).left j,
    SixPairCoarseWreathHead.local_preserves F E u j⟩,
    ((SixPairNestedTopFrames.nestedFrame F E).wreathEmbedding u).right)

theorem encoding_injective : Function.Injective (encoding F E) := by
  intro u v h
  apply (SixPairNestedTopFrames.nestedFrame F E).wreathEmbedding_injective
  apply PermutationalWreathProduct.ext
  · funext j
    exact congrArg (fun z : (Fin 3 → Local) × Equiv.Perm (Fin 3) => (z.1 j).val) h
  · exact congrArg Prod.snd h

include F E in
theorem card_le : Nat.card U≤3072 := by
  calc
    Nat.card U≤Nat.card ((Fin 3 → Local) × Equiv.Perm (Fin 3)) :=
      Nat.card_le_card_of_injective (encoding F E) (encoding_injective F E)
    _=3072 := by rw [Nat.card_prod,Nat.card_fun,local_card,Nat.card_perm,Nat.card_fin]; norm_num

include F E in
theorem card_le_two_pow_twelve : Nat.card U≤2^12 := (card_le F E).trans (by norm_num)

end SymmetricSubgroupAsymptotics.SixPairThreePairOriginalOrder
