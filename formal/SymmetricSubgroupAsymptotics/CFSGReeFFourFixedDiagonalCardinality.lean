import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedDiagonalTorus

/-! Exact order of the actual retained Ree fixed diagonal subgroup.
The count uses the proved original torus realization and injectivity,
including at m=0, without simplicity or two-conjugate generation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourFixedDiagonalCardinality
open CFSGReeFFourFieldParameters CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourFixedTorus CFSGReeFFourFixedDiagonalTorus CFSGReeFFourFixedBruhatCover
open CFSGFFourOriginalDiagonalTorus CFSGFFourOriginalProductTorus
open CFSGFFourOriginalProductTorusInjective

theorem fixedTorus_mem_diagonal (m : ℕ) (a b : (Field m)ˣ) :
    fixedTorus m a b ∈ fixedDiagonal m :=
  modelProductTorus_mem_diagonal (Field m) (fixedTorusTuple m a b)

theorem fixedTorus_injective (m : ℕ) :
    Function.Injective (fun p : (Field m)ˣ × (Field m)ˣ => fixedTorus m p.1 p.2) := by
  intro p q h
  have hv := congrArg (fun x : originalModelFixed m => x.val) h
  have ht : fixedTorusTuple m p.1 p.2 = fixedTorusTuple m q.1 q.2 :=
    modelProductTorusHom_injective (Field m) hv
  exact Prod.ext (congrFun ht 0) (congrFun ht 1)

def torusParametersEquiv (m : ℕ) :
    ((Field m)ˣ × (Field m)ˣ) ≃ fixedDiagonal m :=
  Equiv.ofBijective
    (fun p => ⟨fixedTorus m p.1 p.2, fixedTorus_mem_diagonal m p.1 p.2⟩)
    ⟨by
      intro p q h
      exact fixedTorus_injective m (congrArg Subtype.val h),
    by
      intro d
      obtain ⟨a, b, he⟩ := exists_fixedDiagonal_torus m d.val d.property
      exact ⟨(a,b), Subtype.ext he.symm⟩⟩

theorem fixedDiagonal_card (m : ℕ) :
    Nat.card (fixedDiagonal m) = (2^(2*m+1)-1)^2 := by
  rw [← Nat.card_congr (torusParametersEquiv m), Nat.card_prod,
    Nat.card_units, field_card, ← pow_two]

end SymmetricSubgroupAsymptotics.CFSGReeFFourFixedDiagonalCardinality
