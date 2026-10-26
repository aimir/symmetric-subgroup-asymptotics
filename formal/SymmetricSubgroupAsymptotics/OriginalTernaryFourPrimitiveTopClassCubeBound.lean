import SymmetricSubgroupAsymptotics.TernaryFourWreathSymmetricTopClassBound
import SymmetricSubgroupAsymptotics.OriginalTernaryFourPrimitiveTopResidual
import SymmetricSubgroupAsymptotics.OriginalBinaryBlockSubnormalClassGap
import SymmetricSubgroupAsymptotics.PermutationalWreathTransport
import Mathlib.Data.Finite.Perm

/-! The same original ternary block action with primitive four-point top
pays the ordinary class cube. The full-S4 case is transported through
its genuine wreath embedding; the earlier cap-four case is retained.
This is a bound for the transitive original source, not for arbitrary
subnormal restrictions that may lose top transitivity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.OriginalTernaryFourPrimitiveTopClassCubeBound
open OriginalBlockClassBound

private theorem mapBase_injective {D E Q I : Type}
    [Group D] [Group E] [Group Q] [MulAction Q I]
    (e : D ≃* E) : Function.Injective
      (PermutationalWreathProduct.mapBase (Q:=Q) (I:=I) e.toMonoidHom) := by
  intro a b hab
  apply PermutationalWreathProduct.ext
  · funext i
    apply e.injective
    exact congrArg (fun w : PermutationalWreathProduct E Q I => w.left i) hab
  · exact congrArg (fun w : PermutationalWreathProduct E Q I => w.right) hab

theorem class_card_le_threeThirty_of_symmetric_top
    {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]
    [MulAction.IsPretransitive A X]
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω),π (g • ω)=g • π ω)
    (x₀ : X) (hthree : Nat.card (originalBlockFibre π x₀)=3)
    (hn : Nat.card X=4)
    (htop : Function.Surjective (topMap (A:=A) (X:=X))) :
    Nat.card (ConjClasses A)≤330 := by
  let c : X ≃ Fin 4 := Finite.equivFinOfCardEq hn
  let d : originalBlockFibre π x₀ ≃ Fin 3 := Finite.equivFinOfCardEq hthree
  let e := c.permCongrHom
  have he : ∀ (q : Equiv.Perm X) (x : X),c (q • x)=e q • c x := by
    intro q x
    change c (q x)=c (q (c.symm (c x)))
    rw [c.symm_apply_apply]
  let t := PermutationalWreathProduct.transport
    (D:=Equiv.Perm (Fin 3)) e c he
  let b := PermutationalWreathProduct.mapBase
    (Q:=Equiv.Perm X) (I:=X) d.permCongrHom.toMonoidHom
  let f : A →* TernaryWreathAffineSemidirectEquiv.Wreath (Fin 4) :=
    t.toMonoidHom.comp (b.comp
      (OriginalBinaryBlockSubnormalClassGap.ambientEmbedding π hπ x₀))
  have hf : Function.Injective f := t.injective.comp
    ((mapBase_injective d.permCongrHom).comp
      (OriginalBinaryBlockSubnormalClassGap.ambientEmbedding_injective π hπ x₀))
  have ht : Function.Surjective
      ((PermutationalWreathProduct.rightHom :
        TernaryWreathAffineSemidirectEquiv.Wreath (Fin 4) →* Equiv.Perm (Fin 4)).comp f) := by
    intro s
    obtain ⟨a,ha⟩ := htop (e.symm s)
    refine ⟨a,?_⟩
    change e (topMap (A:=A) (X:=X) a)=s
    rw [ha]
    exact e.apply_symm_apply s
  exact TernaryFourWreathSymmetricTopClassBound.class_card_le_threeThirty f hf ht

theorem class_cube_le_of_four_ternary_blocks
    {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]
    [MulAction.IsPretransitive A X]
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω),π (g • ω)=g • π ω)
    (hsize : ∀ x,Nat.card (originalBlockFibre π x)=3)
    (hn : Nat.card X=4)
    (hprimitive : MulAction.IsPreprimitive (Top (A:=A) (X:=X)) X) :
    Nat.card (ConjClasses A)^3≤5^(Nat.card Ω-1) := by
  rcases OriginalTernaryFourPrimitiveTopResidual.class_cube_le_or_symmetric_top
    π hπ hsize hn hprimitive with hpaid|he
  · exact hpaid
  · obtain ⟨e⟩ := he
    have hcard : Nat.card (Top (A:=A) (X:=X))=Nat.card (Equiv.Perm X) := by
      rw [Nat.card_congr e.toEquiv,Nat.card_perm,Nat.card_perm,hn,Nat.card_fin]
    have hfull : Top (A:=A) (X:=X)=⊤ := Subgroup.eq_top_of_card_eq _ hcard
    have ht : Function.Surjective (topMap (A:=A) (X:=X)) := by
      intro s
      have hs : s∈Top (A:=A) (X:=X) := by rw [hfull]; trivial
      exact hs
    have hX : Nonempty X := Finite.card_pos_iff.mp (by omega : 0<Nat.card X)
    obtain ⟨x₀⟩ := hX
    have hc := class_card_le_threeThirty_of_symmetric_top π hπ x₀ (hsize x₀) hn ht
    have hd : Nat.card Ω=12 := by
      have h := GaronziMarotiLargeBlockReduction.card_eq_blocks_mul_fibre π 3 hsize
      simpa only [hn] using h
    calc
      _≤330^3 := Nat.pow_le_pow_left hc 3
      _≤5^(Nat.card Ω-1) := by rw [hd]; decide

end SymmetricSubgroupAsymptotics.OriginalTernaryFourPrimitiveTopClassCubeBound

namespace SymmetricSubgroupAsymptotics.OriginalMinimalBlock

variable {A Ω : Type} [Group A] [MulAction A Ω] [MulAction.IsPretransitive A Ω]
    [Finite A] [Finite Ω] [FaithfulSMul A Ω]
    {ω₀ : Ω} (D : OriginalMinimalBlock (A:=A) ω₀)

theorem class_cube_le_of_four_ternary_blocks_with_primitive_top
    (hthree : Nat.card D.Fibre=3) (hn : Nat.card D.Points=4)
    (hprimitive : MulAction.IsPreprimitive D.Top D.Points) :
    Nat.card (ConjClasses A)^3≤5^(Nat.card Ω-1) :=
  OriginalTernaryFourPrimitiveTopClassCubeBound.class_cube_le_of_four_ternary_blocks
    D.map D.map_equivariant (by intro x; exact (D.fibre_card_at x).trans hthree) hn hprimitive

end SymmetricSubgroupAsymptotics.OriginalMinimalBlock
