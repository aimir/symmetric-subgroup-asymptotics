import SymmetricSubgroupAsymptotics.TernaryFourTransitiveWreathClassBound
import SymmetricSubgroupAsymptotics.OriginalBinaryBlockSubnormalClassGap
import SymmetricSubgroupAsymptotics.PermutationalWreathTransport
import SymmetricSubgroupAsymptotics.OriginalMinimalBlockComponentTransport
import SymmetricSubgroupAsymptotics.GaronziMarotiLargeBlockReduction

/-! Every ORIGINAL faithful ternary four-block action with transitive
top pays the ordinary class cube. Only the actual fibre and block labels
are charted. The original group, action and point degree are retained;
no primitive-top hypothesis or subnormal-transitivity assertion occurs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.OriginalTernaryFourTopClassCubeBound

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

theorem class_card_le_threeSixty
    {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]
    [MulAction.IsPretransitive A X]
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω),π (g • ω)=g • π ω)
    (x₀ : X) (hthree : Nat.card (originalBlockFibre π x₀)=3)
    (hn : Nat.card X=4) : Nat.card (ConjClasses A)≤360 := by
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
  have ht : ∀ i j : Fin 4,∃g : A,(f g).right i=j := by
    intro i j
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq A (c.symm i) (c.symm j)
    refine ⟨g,?_⟩
    change c (g • c.symm i)=j
    rw [hg,c.apply_symm_apply]
  exact TernaryFourTransitiveWreathClassBound.class_card_le_threeSixty f hf ht

theorem class_cube_le_of_four_ternary_blocks
    {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]
    [MulAction.IsPretransitive A X]
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω),π (g • ω)=g • π ω)
    (hsize : ∀ x,Nat.card (originalBlockFibre π x)=3)
    (hn : Nat.card X=4) :
    Nat.card (ConjClasses A)^3≤5^(Nat.card Ω-1) := by
  have hX : Nonempty X := Finite.card_pos_iff.mp (by omega : 0<Nat.card X)
  obtain ⟨x₀⟩ := hX
  have hc := class_card_le_threeSixty π hπ x₀ (hsize x₀) hn
  have hd : Nat.card Ω=12 := by
    have h := GaronziMarotiLargeBlockReduction.card_eq_blocks_mul_fibre π 3 hsize
    simpa only [hn] using h
  calc
    _≤360^3 := Nat.pow_le_pow_left hc 3
    _≤5^(Nat.card Ω-1) := by rw [hd]; decide

end SymmetricSubgroupAsymptotics.OriginalTernaryFourTopClassCubeBound

namespace SymmetricSubgroupAsymptotics.OriginalMinimalBlock

variable {A Ω : Type} [Group A] [MulAction A Ω] [MulAction.IsPretransitive A Ω]
    [Finite A] [Finite Ω] [FaithfulSMul A Ω]
    {ω₀ : Ω} (D : OriginalMinimalBlock (A:=A) ω₀)

theorem class_cube_le_of_four_ternary_blocks
    (hthree : Nat.card D.Fibre=3) (hn : Nat.card D.Points=4) :
    Nat.card (ConjClasses A)^3≤5^(Nat.card Ω-1) :=
  OriginalTernaryFourTopClassCubeBound.class_cube_le_of_four_ternary_blocks
    D.map D.map_equivariant (by intro x; exact (D.fibre_card_at x).trans hthree) hn

end SymmetricSubgroupAsymptotics.OriginalMinimalBlock
