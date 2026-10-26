import SymmetricSubgroupAsymptotics.TernaryFourSignedStabilizerCapacity

/-! The zero-vector term keeps the actual signed group. Its original
binary four-fibre action gives 42 classes for any transitive top; a small
permutation kernel also gives the literal extension bound 5*|ker top|. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.TernaryFourTransitiveSignedClassBound
open TernarySignedWreathLinearEquiv TernaryFourProperModuleSignKernel

theorem class_card_le_fortyTwo (R : Subgroup Signed)
    (htrans : ∀ i j : Fin 4,∃g : R,topHom R g i=j) :
    Nat.card (ConjClasses R)≤42 := by
  letI : MulAction R (Fin 4) := MulAction.compHom _ (topHom R)
  letI : MulAction.IsPretransitive R (Fin 4) := ⟨htrans⟩
  let π : Multiplicative (ZMod 2) × Fin 4 → Fin 4 := Prod.snd
  have hπ : ∀ (g : R) (ω : Multiplicative (ZMod 2) × Fin 4),
      π (g • ω)=g • π ω := fun _ _ => rfl
  have hsize (i : Fin 4) : Nat.card (originalBlockFibre π i)≤2 := by
    let e : originalBlockFibre π i ≃ Multiplicative (ZMod 2) := {
      toFun := fun ω => ω.val.1
      invFun := fun z => ⟨(z,i),rfl⟩
      left_inv := fun ω => Subtype.ext (Prod.ext rfl ω.property.symm)
      right_inv := fun _ => rfl }
    exact ((Nat.card_congr e).trans
      ((Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 2) ≃ ZMod 2)).trans
        (Nat.card_zmod 2))).le
  exact OriginalBinaryFourTopClassCubeBound.class_card_le_fortyTwo π hπ hsize (Nat.card_fin 4)

theorem class_card_le_sign_kernel_mul_five (R : Subgroup Signed) :
    Nat.card (ConjClasses R)≤Nat.card (topHom R).ker*5 := by
  have hk : Nat.card (ConjClasses (topHom R).ker)≤Nat.card (topHom R).ker :=
    Nat.card_le_card_of_surjective (@ConjClasses.mk (topHom R).ker _)
      ConjClasses.mk_surjective
  have hr : Nat.card (ConjClasses (topHom R).range)≤5 :=
    FourPointPermutationClassBound.subgroup_class_card_le_five (topHom R).range
  exact (conjugacyClass_card_le_kernel_mul_range (topHom R)).trans (Nat.mul_le_mul hk hr)

end SymmetricSubgroupAsymptotics.TernaryFourTransitiveSignedClassBound
