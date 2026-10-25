import SymmetricSubgroupAsymptotics.SmallFibreLargeIndexOrderClassResidual
import SymmetricSubgroupAsymptotics.PrimitiveSocleExceptionalAllDegreesClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleTwistedE6CompleteClassBound
import SymmetricSubgroupAsymptotics.CFSGExceptionalIndexSquare
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalIndexSquare

/-! Whole original E6/E7/E8/twisted-E6 top families supply one shared
per-index packet. Every index is at least2048, but the component class
budget is evaluated at its ACTUAL index, which can grow with the field.
All source subgroups and short-index witnesses remain in the original
top/simple factor. There are no field or action rows. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SmallFibreExceptionalLargeIndexClassResidual
open PrimitiveSocleRawStructure OriginalBlockClassBound CFSGReduction

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]

private theorem of_model {S : Type} [Group S]
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x)=c)
    (E : NonaffineData (Top (A := A) (X := X)) X) (e : E.Simple ≃* S)
    (hindex : ∀ K : Subgroup S, K ≠ ⊤ → 2048 ≤ K.index)
    (horder : ∀ K : Subgroup E.Simple, K ≠ ⊤ →
      Nat.card E.Simple*Nat.card (Outer E.Simple) ≤ K.index^66)
    (hsquare : ∀ ell : ℕ, LeastProperIndex S ell → ell^2 < Nat.card S)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-2) ∨
      (E.factorCount=1 ∧ ∃ ell : ℕ, LeastProperIndex E.Simple ell ∧
        ∃ K : Subgroup E.Simple, K ≠ ⊤ ∧ Nat.card X=K.index ∧
          ell ≤ K.index ∧ K.index < 2*ell+2) := by
  apply SmallFibreLargeIndexOrderClassResidual.subnormal_gap_or_least_short_index_of_order_index_power
    π hπ c hc hsize E ?_ horder ?_ H hH
  · intro K hK
    have hmap : K.map e.toMonoidHom ≠ ⊤ := by
      intro ht
      apply hK
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
    have hi : (K.map e.toMonoidHom).index=K.index := K.index_map_equiv e
    have hh := hindex (K.map e.toMonoidHom) hmap
    rw [hi] at hh
    exact (by decide : 1024 ≤ 2048).trans hh
  · intro ell hell
    rw [Nat.card_congr e.toEquiv]
    exact hsquare ell (leastProperIndex_of_mulEquiv e ell hell)

theorem subnormal_gap_or_eSix_single_least_short_index
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x)=c)
    (E : NonaffineData (Top (A := A) (X := X)) X)
    (q : CFSG.PrimePower) (e : E.Simple ≃* CFSG.Models.E6 q)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-2) ∨
      (E.factorCount=1 ∧ ∃ ell : ℕ, LeastProperIndex E.Simple ell ∧
        ∃ K : Subgroup E.Simple, K ≠ ⊤ ∧ Nat.card X=K.index ∧
          ell ≤ K.index ∧ K.index < 2*ell+2) := by
  letI : IsSimpleGroup (CFSG.Models.E6 q) := e.symm.isSimpleGroup
  exact of_model π hπ c hc hsize E e (typeE6_2048_le_index q)
    (E.e6_simple_order_outer_budget q e)
    (CFSGExceptionalIndexSquare.typeE6_leastIndex_square_lt q) H hH

theorem subnormal_gap_or_eSeven_single_least_short_index
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x)=c)
    (E : NonaffineData (Top (A := A) (X := X)) X)
    (q : CFSG.PrimePower) (e : E.Simple ≃* CFSG.Models.E7 q)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-2) ∨
      (E.factorCount=1 ∧ ∃ ell : ℕ, LeastProperIndex E.Simple ell ∧
        ∃ K : Subgroup E.Simple, K ≠ ⊤ ∧ Nat.card X=K.index ∧
          ell ≤ K.index ∧ K.index < 2*ell+2) := by
  letI : IsSimpleGroup (CFSG.Models.E7 q) := e.symm.isSimpleGroup
  exact of_model π hπ c hc hsize E e (typeE7_2048_le_index q)
    (E.e7_simple_order_outer_budget q e)
    (CFSGExceptionalIndexSquare.typeE7_leastIndex_square_lt q) H hH

theorem subnormal_gap_or_eEight_single_least_short_index
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x)=c)
    (E : NonaffineData (Top (A := A) (X := X)) X)
    (q : CFSG.PrimePower) (e : E.Simple ≃* CFSG.Models.E8 q)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-2) ∨
      (E.factorCount=1 ∧ ∃ ell : ℕ, LeastProperIndex E.Simple ell ∧
        ∃ K : Subgroup E.Simple, K ≠ ⊤ ∧ Nat.card X=K.index ∧
          ell ≤ K.index ∧ K.index < 2*ell+2) := by
  letI : IsSimpleGroup (CFSG.Models.E8 q) := e.symm.isSimpleGroup
  exact of_model π hπ c hc hsize E e (typeE8_2048_le_index q)
    (E.e8_simple_order_outer_budget q e)
    (CFSGExceptionalIndexSquare.typeE8_leastIndex_square_lt q) H hH

theorem subnormal_gap_or_twistedESix_single_least_short_index
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x)=c)
    (E : NonaffineData (Top (A := A) (X := X)) X)
    (q : CFSG.PrimePower) (e : E.Simple ≃* CFSG.Models.TwistedE6 q)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-2) ∨
      (E.factorCount=1 ∧ ∃ ell : ℕ, LeastProperIndex E.Simple ell ∧
        ∃ K : Subgroup E.Simple, K ≠ ⊤ ∧ Nat.card X=K.index ∧
          ell ≤ K.index ∧ K.index < 2*ell+2) := by
  letI : IsSimpleGroup (CFSG.Models.TwistedE6 q) := e.symm.isSimpleGroup
  exact of_model π hπ c hc hsize E e (CFSGTwistedE6HeisenbergIndex.proper_index_ge_2048 q)
    (E.twistedE6_simple_order_outer_budget q e)
    (CFSGTwistedE6GeckOriginalIndexSquare.original_index_square q) H hH

end SymmetricSubgroupAsymptotics.SmallFibreExceptionalLargeIndexClassResidual
