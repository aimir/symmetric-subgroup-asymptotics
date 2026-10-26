import SymmetricSubgroupAsymptotics.SmallFibreAlternatingFiveOrdinaryClassGap
import SymmetricSubgroupAsymptotics.CFSGPSLTwoCardFourAlternatingEquiv
import SymmetricSubgroupAsymptotics.CFSGPSLTwoCardFiveAlternatingEquiv

/-! The original PSL2 fields four and five inherit the A5-marked
ordinary small-fibre bound through the already proved literal Borel
coset equivalences. All original source data and socle factors remain
in the statement; no natural-action or numerical-capacity premise is
introduced. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SmallFibrePSLTwoAlternatingFiveOrdinaryClassGap
open PrimitiveSocleRawStructure OriginalBlockClassBound CFSGReduction

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]

theorem subnormal_class_cube_le_of_typeA_rank_one_order_four
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω),π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x,Nat.card (originalBlockFibre π x)=c)
    (E : NonaffineData (Top (A:=A) (X:=X)) X)
    (q : CFSG.PrimePower) (hq : q.order=4)
    (e : E.Simple ≃* CFSG.Models.A 1 q)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3≤5^(Nat.card Ω-1) := by
  letI : IsSimpleGroup (CFSG.Models.A 1 q) := e.symm.isSimpleGroup
  let e₅ : E.Simple ≃* alternatingGroup (Fin 5) := e.trans
    (CFSGPSLTwoCardFourAlternatingEquiv.equivAlternatingFive
      (F := q.Field) (by simpa only [q.card_field] using hq))
  exact SmallFibreAlternatingFiveOrdinaryClassGap.subnormal_class_cube_le_at_original_degree
    π hπ c hc hsize E e₅ H hH

theorem subnormal_class_cube_le_of_typeA_rank_one_order_five
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω),π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x,Nat.card (originalBlockFibre π x)=c)
    (E : NonaffineData (Top (A:=A) (X:=X)) X)
    (q : CFSG.PrimePower) (hq : q.order=5)
    (e : E.Simple ≃* CFSG.Models.A 1 q)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3≤5^(Nat.card Ω-1) := by
  letI : IsSimpleGroup (CFSG.Models.A 1 q) := e.symm.isSimpleGroup
  let e₅ : E.Simple ≃* alternatingGroup (Fin 5) := e.trans
    (CFSGPSLTwoCardFiveAlternatingEquiv.equivAlternatingFive
      (F := q.Field) (by simpa only [q.card_field] using hq))
  exact SmallFibreAlternatingFiveOrdinaryClassGap.subnormal_class_cube_le_at_original_degree
    π hπ c hc hsize E e₅ H hH

theorem subnormal_class_cube_le_of_typeA_rank_one_order_four_or_five
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω),π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x,Nat.card (originalBlockFibre π x)=c)
    (E : NonaffineData (Top (A:=A) (X:=X)) X)
    (q : CFSG.PrimePower) (hq : q.order=4 ∨ q.order=5)
    (e : E.Simple ≃* CFSG.Models.A 1 q)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3≤5^(Nat.card Ω-1) := by
  rcases hq with hq|hq
  · exact subnormal_class_cube_le_of_typeA_rank_one_order_four π hπ c hc hsize E q hq e H hH
  · exact subnormal_class_cube_le_of_typeA_rank_one_order_five π hπ c hc hsize E q hq e H hH

end SymmetricSubgroupAsymptotics.SmallFibrePSLTwoAlternatingFiveOrdinaryClassGap
