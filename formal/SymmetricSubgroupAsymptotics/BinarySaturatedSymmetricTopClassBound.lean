import SymmetricSubgroupAsymptotics.BinaryFullWreathClassBound
import SymmetricSubgroupAsymptotics.BinaryBlockWreathSaturation
import SymmetricSubgroupAsymptotics.PermutationalWreathTransport

/-! The ORIGINAL saturated binary block action with actual full symmetric
top satisfies the GM cube uniformly from seven blocks onward. The group
equivalence uses the actual saturated embedding and existing equivariant
wreath transport. No split extension or wreath class bound is a premise. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics.BinarySaturatedSymmetricTopClassBound
open OriginalBlockClassBound BinaryBlockWreathCodimension BinaryBlockWreathSaturation
  PermutationWreathBaseConjugacy

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [MulAction.IsPretransitive A X] [FaithfulSMul A Ω]
    [Finite A] [Finite Ω] [Finite X]
    (b : Ω → X) (hb : ∀ (a : A) (ω : Ω),b (a • ω)=a • b ω) (x0 : X)
    (htwo : Nat.card (originalBlockFibre b x0)=2)
    (hfull : Nat.card (Kernel (A := A) (X := X))=2^Nat.card X)
    (hTop : Top (A := A) (X := X)=⊤)

def symmetricTopEquiv : A ≃* Wreath (Equiv.Perm (originalBlockFibre b x0)) X := by
  let eTop : Top (A := A) (X := X) ≃* Equiv.Perm X :=
    (MulEquiv.subgroupCongr hTop).trans Subgroup.topEquiv
  exact (fullWreathEquiv b hb x0 htwo hfull).trans
    (PermutationalWreathProduct.transport eTop (Equiv.refl X) (by intro q i; rfl))

include hb htwo hfull hTop in
theorem class_cube_le_garonziMaroti (hX : 7≤Nat.card X) :
    Nat.card (ConjClasses A)^3≤5^(Nat.card Ω-1) := by
  letI : IsMulCommutative (Equiv.Perm (originalBlockFibre b x0)) :=
    Equiv.Perm.isMulCommutative_iff_card_le_two.mpr htwo.le
  letI : CommGroup (Equiv.Perm (originalBlockFibre b x0)) := inferInstance
  have hD : Nat.card (Equiv.Perm (originalBlockFibre b x0))=2 := by
    rw [Nat.card_perm,htwo]
    rfl
  let e := symmetricTopEquiv b hb x0 htwo hfull hTop
  have hc : Nat.card (ConjClasses A)≤
      Nat.card (ConjClasses (Wreath (Equiv.Perm (originalBlockFibre b x0)) X)) :=
    Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
      (ConjClasses.map_surjective e.symm.surjective)
  have hw := BinaryFullWreathClassBound.class_cube_le_garonziMaroti (I := X) hD hX
  have hd : 2*Nat.card X=Nat.card Ω := by
    have h := Nat.card_congr (ActualBlockWreathEmbedding.productEquiv b hb x0)
    rw [Nat.card_prod,htwo] at h
    exact h
  simpa only [hd] using (Nat.pow_le_pow_left hc 3).trans hw

end SymmetricSubgroupAsymptotics.BinarySaturatedSymmetricTopClassBound
