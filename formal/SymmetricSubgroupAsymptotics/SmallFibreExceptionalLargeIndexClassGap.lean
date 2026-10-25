import SymmetricSubgroupAsymptotics.SmallFibreLargeIndexOrderClassGap
import SymmetricSubgroupAsymptotics.PrimitiveSocleExceptionalAllDegreesClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleTwistedE6CompleteClassBound
import SymmetricSubgroupAsymptotics.CFSGExceptionalIndexSquare
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalIndexSquare

/-! Every original E6/E7/E8/twisted-E6 top pays the actual binary/ternary
subnormal class gap, including one-factor short-index actions. The proved
order-at-index and original least-index-square packets are used uniformly
over fields and socle multiplicities. No comparison action is substituted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SmallFibreExceptionalLargeIndexClassGap
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
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-2) := by
  apply SmallFibreLargeIndexOrderClassGap.subnormal_class_cube_gap_of_order_index_power
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
    exact hh
  · intro ell hell
    rw [Nat.card_congr e.toEquiv]
    exact hsquare ell (leastProperIndex_of_mulEquiv e ell hell)

theorem subnormal_class_cube_gap_of_eSix
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x)=c)
    (E : NonaffineData (Top (A := A) (X := X)) X)
    (q : CFSG.PrimePower) (e : E.Simple ≃* CFSG.Models.E6 q)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-2) := by
  letI : IsSimpleGroup (CFSG.Models.E6 q) := e.symm.isSimpleGroup
  exact of_model π hπ c hc hsize E e (typeE6_2048_le_index q)
    (E.e6_simple_order_outer_budget q e)
    (CFSGExceptionalIndexSquare.typeE6_leastIndex_square_lt q) H hH

theorem subnormal_class_cube_gap_of_eSeven
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x)=c)
    (E : NonaffineData (Top (A := A) (X := X)) X)
    (q : CFSG.PrimePower) (e : E.Simple ≃* CFSG.Models.E7 q)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-2) := by
  letI : IsSimpleGroup (CFSG.Models.E7 q) := e.symm.isSimpleGroup
  exact of_model π hπ c hc hsize E e (typeE7_2048_le_index q)
    (E.e7_simple_order_outer_budget q e)
    (CFSGExceptionalIndexSquare.typeE7_leastIndex_square_lt q) H hH

theorem subnormal_class_cube_gap_of_eEight
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x)=c)
    (E : NonaffineData (Top (A := A) (X := X)) X)
    (q : CFSG.PrimePower) (e : E.Simple ≃* CFSG.Models.E8 q)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-2) := by
  letI : IsSimpleGroup (CFSG.Models.E8 q) := e.symm.isSimpleGroup
  exact of_model π hπ c hc hsize E e (typeE8_2048_le_index q)
    (E.e8_simple_order_outer_budget q e)
    (CFSGExceptionalIndexSquare.typeE8_leastIndex_square_lt q) H hH

theorem subnormal_class_cube_gap_of_twistedESix
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x)=c)
    (E : NonaffineData (Top (A := A) (X := X)) X)
    (q : CFSG.PrimePower) (e : E.Simple ≃* CFSG.Models.TwistedE6 q)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-2) := by
  letI : IsSimpleGroup (CFSG.Models.TwistedE6 q) := e.symm.isSimpleGroup
  exact of_model π hπ c hc hsize E e (CFSGTwistedE6HeisenbergIndex.proper_index_ge_2048 q)
    (E.twistedE6_simple_order_outer_budget q e)
    (CFSGTwistedE6GeckOriginalIndexSquare.original_index_square q) H hH

end SymmetricSubgroupAsymptotics.SmallFibreExceptionalLargeIndexClassGap
