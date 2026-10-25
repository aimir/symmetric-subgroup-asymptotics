import SymmetricSubgroupAsymptotics.SmallFibreNonaffinePerIndexClassResidual
import SymmetricSubgroupAsymptotics.CFSGGTwoProperIndexComponentCube
import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalIndexSquare
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport

/-! The whole original G2 family supplies the per-index class packet
for an actual binary/ternary block action. Its existing order-times-outer
cube and actual index-square theorem already cover every admissible field.
Only an actual one-factor short-index action can be returned. The original
source subgroup, top descriptor and proper-index witness are unchanged. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SmallFibreGTwoClassPacketResidual
open PrimitiveSocleRawStructure OriginalBlockClassBound CFSGReduction

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]

theorem subnormal_gap_or_gTwo_single_least_short_index
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x)=c)
    (E : NonaffineData (Top (A := A) (X := X)) X)
    (q : CFSG.PrimePower) (hs : q.order ≠ 2)
    (e : E.Simple ≃* CFSG.Models.G2 q)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-2) ∨
      (E.factorCount=1 ∧ ∃ ell : ℕ, LeastProperIndex E.Simple ell ∧
        ∃ K : Subgroup E.Simple, K ≠ ⊤ ∧ Nat.card X=K.index ∧
          ell ≤ K.index ∧ K.index < 2*ell+2) := by
  letI : IsSimpleGroup (CFSG.Models.G2 q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.G2 q) := Finite.of_equiv E.Simple e.toEquiv
  have hn : ¬IsMulCommutative (CFSG.Models.G2 q) :=
    fun h => E.noncommutative ((isMulCommutative_congr e).mpr h)
  apply SmallFibreNonaffinePerIndexClassResidual.subnormal_gap_or_least_short_index
    π hπ c hc hsize E ?_ ?_ H hH
  · intro K hK
    have hmap : K.map e.toMonoidHom ≠ ⊤ := by
      intro ht
      apply hK
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
    have hmodel := CFSGGTwoProperIndexComponentCube.order_mul_outer_cube_le_proper_index
      q hs hn (K.map e.toMonoidHom) hmap
    have hi : (K.map e.toMonoidHom).index=K.index := K.index_map_equiv e
    rw [hi] at hmodel
    have horder : (Nat.card E.Simple*Nat.card (Outer E.Simple))^3 ≤ 5^(K.index-1) := by
      rw [Nat.card_congr e.toEquiv,outer_card_congr e]
      exact hmodel
    have hclass : Nat.card (ConjClasses E.Simple) ≤ Nat.card E.Simple :=
      Nat.card_le_card_of_surjective ConjClasses.mk ConjClasses.mk_surjective
    exact ((Nat.pow_le_pow_left (Nat.mul_le_mul_right _ hclass) 3).trans horder).trans
      (Nat.pow_le_pow_right (by decide) (by omega : K.index-1 ≤ K.index+1))
  · intro ell hell
    rw [Nat.card_congr e.toEquiv]
    exact CFSGGTwoOriginalIndexSquare.typeGTwo_index_square q hs ell
      (leastProperIndex_of_mulEquiv e ell hell)

end SymmetricSubgroupAsymptotics.SmallFibreGTwoClassPacketResidual
