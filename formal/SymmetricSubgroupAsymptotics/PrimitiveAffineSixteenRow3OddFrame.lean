import SymmetricSubgroupAsymptotics.BinaryCoinducedFifteenPointHead
import SymmetricSubgroupAsymptotics.PrimeRelativeHeadNormalGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow3AffineSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow3OrbitWitness

/-! Selected primitive-sixteen row3 pilot. The original first generator
has order15 and a fifteen-point orbit. Its actual cyclic subgroup has
index16 in the checked original affine group. Hence it contains an
ambient Sylow3, and the odd-orbit head argument applies to every original
point stabilizer epimorphism. Only bounded point equalities are decided. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenRow3OddFrame

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open BinaryFourAffineImage
open PrimitiveAffineDegreeTwoPrimitiveSixteenRows3And6And9LinearRelations

abbrev Top := DegreeTwoPrimitiveSixteenInterfaces.row3.top
abbrev element := PrimitiveAffineDegreeTwoPrimitiveSixteenRow3OrbitWitness.element
abbrev oddSubgroup : Subgroup Top := Subgroup.zpowers element

private theorem generator_pow_fifteen :
    (DegreeTwoPrimitiveSixteenInterfaces.row3Generators 0) ^ 15 = 1 := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel

private theorem generator_short_power :
    ∀ m : Fin 15, 0 < m.val →
      ((DegreeTwoPrimitiveSixteenInterfaces.row3Generators 0) ^ m.val) (1 : Fin 16) ≠ 1 := by
  decide +kernel

theorem generator_order :
    orderOf (DegreeTwoPrimitiveSixteenInterfaces.row3Generators 0) = 15 := by
  apply (orderOf_eq_iff (by decide : 0 < 15)).mpr
  refine ⟨generator_pow_fifteen, ?_⟩
  intro m hm hmpos he
  apply generator_short_power ⟨m, hm⟩ hmpos
  rw [he]
  rfl

theorem element_order : orderOf element = 15 := by
  exact (orderOf_injective Top.subtype Subtype.coe_injective element).symm.trans generator_order

theorem oddSubgroup_card : Nat.card oddSubgroup = 15 := by
  rw [Nat.card_zpowers, element_order]

private theorem linearPerm_injective : Function.Injective linearPerm := by
  intro a b h
  have ha : PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.linearAction a =
      PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.linearAction b :=
    pointEquiv.permCongrHom.injective h
  apply LinearEquiv.ext
  intro v
  exact Equiv.congr_fun ha v

theorem linearGroup_card :
    Nat.card PrimitiveAffineDegreeTwoPrimitiveSixteenRow3AffineSocles.linearGroup = 15 := by
  rw [Nat.card_zpowers]
  have h := orderOf_injective linearPerm linearPerm_injective a3
  rw [a3_original, generator_order] at h
  exact h.symm

theorem top_card : Nat.card Top = 240 := by
  have hv : Nat.card (Multiplicative Vector) = 16 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  calc
    Nat.card Top =
        Nat.card (AffineModel.Aff PrimitiveAffineDegreeTwoPrimitiveSixteenRow3AffineSocles.linearGroup) :=
      Nat.card_congr PrimitiveAffineDegreeTwoPrimitiveSixteenRow3AffineSocles.modelEquiv.toEquiv
    _ = 240 := by rw [SemidirectProduct.card, hv, linearGroup_card]

theorem oddSubgroup_index : oddSubgroup.index = 16 := by
  have h := oddSubgroup.card_mul_index
  rw [oddSubgroup_card, top_card] at h
  omega

private theorem powers_injective :
    Function.Injective (fun m : Fin 15 =>
      ((DegreeTwoPrimitiveSixteenInterfaces.row3Generators 0) ^ m.val) (1 : Fin 16)) := by
  decide +kernel

theorem orbit_card_lower : 15 ≤ Nat.card (MulAction.orbit oddSubgroup (1 : Fin 16)) := by
  let f : Fin 15 → MulAction.orbit oddSubgroup (1 : Fin 16) := fun m =>
    ⟨((DegreeTwoPrimitiveSixteenInterfaces.row3Generators 0) ^ m.val) 1,
      MulAction.mem_orbit_iff.mpr
        ⟨⟨element ^ m.val, oddSubgroup.pow_mem (Subgroup.mem_zpowers element) m.val⟩, rfl⟩⟩
  have hf : Function.Injective f := by
    intro m n h
    exact powers_injective (congrArg Subtype.val h)
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f hf

instance top_pretransitive : MulAction.IsPretransitive Top (Fin 16) := by
  constructor
  intro x y
  let v : Multiplicative Vector :=
    Multiplicative.ofAdd (pointEquiv.symm y - pointEquiv.symm x)
  refine ⟨⟨translationPerm v,
    PrimitiveAffineDegreeTwoPrimitiveSixteenRow3AffineSocles.translation_mem v⟩, ?_⟩
  change pointEquiv ((pointEquiv.symm y - pointEquiv.symm x) + pointEquiv.symm x) = y
  rw [sub_add_cancel, pointEquiv.apply_symm_apply]

theorem original_head_le_two
    {L V : Type} [Group L] [Finite L] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (x : Fin 16) (f : MulAction.stabilizer Top x →* L) (hf : Function.Surjective f)
    (rho : Representation (ZMod 2) L V) (hL : Nat.card L = 3 ∨ Nat.card L = 6)
    (hdim : Module.finrank (ZMod 2) V = 2) (hrho : Function.Injective rho)
    (B : Subrepresentation
      (Representation.coind (MulAction.stabilizer Top x).subtype (rho.comp f))) :
    Module.finrank (ZMod 2)
      (B.toRepresentation.IntertwiningMap (Representation.trivial (ZMod 2) Top (ZMod 2))) ≤ 2 :=
  BinaryCoinducedOddOvergroupHead.head_le_two_on_points oddSubgroup
    (by rw [oddSubgroup_card]; decide)
    (by rw [oddSubgroup_index]; decide)
    (by simp) 1 orbit_card_lower x f hf rho hL hdim hrho B

theorem original_frame_sum_le_four
    {L V : Type} [Group L] [Finite L] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (x : Fin 16) (f : MulAction.stabilizer Top x →* L) (hf : Function.Surjective f)
    (rho : Representation (ZMod 2) L V) (hL : Nat.card L = 3 ∨ Nat.card L = 6)
    (hdim : Module.finrank (ZMod 2) V = 2) (hrho : Function.Injective rho)
    (N : Subgroup Top) [N.Normal]
    (B : Subrepresentation
      (Representation.coind (MulAction.stabilizer Top x).subtype (rho.comp f))) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) +
      Module.finrank (ZMod 2)
        (B.toRepresentation.IntertwiningMap (Representation.trivial (ZMod 2) Top (ZMod 2))) ≤ 4 := by
  obtain ⟨z, hz⟩ :=
    PrimitiveAffineDegreeTwoPrimitiveSixteenRow3AffineSocles.top_normal_generating_pairs N inferInstance
  have hn := primeRelativeHead_le_normal_generating_tuple 2 N z hz
  have hb := original_head_le_two x f hf rho hL hdim hrho B
  omega

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenRow3OddFrame

end
