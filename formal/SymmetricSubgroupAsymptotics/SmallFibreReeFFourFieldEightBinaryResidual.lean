import SymmetricSubgroupAsymptotics.SmallFibreReeFFourFieldEightSingleIndexResidual
import SymmetricSubgroupAsymptotics.SmallFibreReeFFourFieldEightTernaryClassGap

/-! The exact remaining ordinary small-fibre state for the original
field-eight Ree model: binary fibre, one socle factor, and the SAME
proper subgroup of index109. All ternary and other degree forms pay. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SmallFibreReeFFourFieldEightBinaryResidual
open PrimitiveSocleRawStructure OriginalBlockClassBound

def BinarySingleIndex {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (E : NonaffineData G X) (c : ℕ) : Prop :=
  c=2 ∧ E.factorCount=1 ∧ ∃ K : Subgroup E.Simple,K≠⊤ ∧
    Nat.card X=K.index ∧ K.index=109

theorem subnormal_ordinary_gap_or_binary_single_index
    {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]
    (π : Ω → X) (hπ : ∀ (g:A) (ω:Ω),π (g•ω)=g•π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x,Nat.card (originalBlockFibre π x)=c)
    (E : NonaffineData (Top (A:=A) (X:=X)) X)
    (e : E.Simple≃*CFSG.Models.ReeF4 1)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3≤5^(Nat.card Ω-1) ∨ BinarySingleIndex E c := by
  rcases hc with rfl|rfl
  · rcases SmallFibreReeFFourFieldEightSingleIndexResidual.subnormal_gap_or_same_index_oneOhNine
        π hπ 2 (Or.inl rfl) hsize E e H hH with hgap|hindex
    · exact Or.inl (hgap.trans (Nat.pow_le_pow_right (by decide) (by omega)))
    · exact Or.inr ⟨rfl,hindex⟩
  · exact Or.inl
      ((SmallFibreReeFFourFieldEightTernaryClassGap.subnormal_class_cube_gap
        π hπ hsize E e H hH).trans (Nat.pow_le_pow_right (by decide) (by omega)))

end SymmetricSubgroupAsymptotics.SmallFibreReeFFourFieldEightBinaryResidual
