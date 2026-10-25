import SymmetricSubgroupAsymptotics.SmallFibreScaledClassPacketGap
import SymmetricSubgroupAsymptotics.CFSGSymplecticCharTwoScaledClassPacket
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBCharTwoProjectiveEquiv
import SymmetricSubgroupAsymptotics.CFSGSymplecticLeastIndexSquare
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport

/-! One literal symplectic packet pays the SAME original C and B
characteristic-two small-fibre actions in ranks at least three, except
literal binary rank three. Simplicity is transported from the actual
original source; no independent original-C simplicity is assumed for B. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SmallFibreCharTwoClassicalClassGap
open PrimitiveSocleRawStructure OriginalBlockClassBound CFSGReduction
open CFSGSymplecticSerreMatrices

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]

private theorem of_model {S : Type} [Group S] [Finite S]
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x)=c)
    (E : NonaffineData (Top (A := A) (X := X)) X) (e : E.Simple ≃* S)
    (hscaled : ∀ K : Subgroup S, K ≠ ⊤ →
      25*(Nat.card (ConjClasses S)*Nat.card (Outer S))^3 ≤ 3^K.index)
    (hsquare : ∀ ell : ℕ, LeastProperIndex S ell → ell^2 < Nat.card S)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-2) := by
  have hclasses : Nat.card (ConjClasses E.Simple)=Nat.card (ConjClasses S) := by
    apply Nat.le_antisymm
    · exact Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
        (ConjClasses.map_surjective e.symm.surjective)
    · exact Nat.card_le_card_of_surjective (ConjClasses.map e.toMonoidHom)
        (ConjClasses.map_surjective e.surjective)
  apply SmallFibreScaledClassPacketGap.subnormal_class_cube_gap_of_scaled_class_packet
    π hπ c hc hsize E ?_ ?_ H hH
  · intro K hK
    have hmap : K.map e.toMonoidHom ≠ ⊤ := by
      intro ht
      apply hK
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
    have hh := hscaled (K.map e.toMonoidHom) hmap
    have hi : (K.map e.toMonoidHom).index=K.index := K.index_map_equiv e
    rw [hi] at hh
    rw [hclasses,outer_card_congr e]
    exact hh
  · intro ell hell
    rw [Nat.card_congr e.toEquiv]
    exact hsquare ell (leastProperIndex_of_mulEquiv e ell hell)

private theorem of_literal
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x)=c)
    (E : NonaffineData (Top (A := A) (X := X)) X)
    (r : ℕ) (hr : 3 ≤ r) (q : CFSG.PrimePower) (hp : q.prime=2)
    (hhead : ¬(r=3 ∧ q.order=2)) (e : E.Simple ≃* elementaryProjective q.Field r)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-2) := by
  obtain ⟨s,rfl⟩ : ∃ s : ℕ, r=s+3 := ⟨r-3,by omega⟩
  letI : IsSimpleGroup (elementaryProjective q.Field (s+3)) := e.symm.isSimpleGroup
  letI : Finite (elementaryProjective q.Field (s+3)) := Finite.of_equiv E.Simple e.toEquiv
  have hn : ¬IsMulCommutative (elementaryProjective q.Field (s+3)) :=
    fun h => E.noncommutative ((isMulCommutative_congr e).mpr h)
  exact of_model π hπ c hc hsize E e
    (CFSGSymplecticCharTwoScaledClassPacket.elementary_scaled_class_cube_le_proper_index
      (s+3) (by omega) q hp hn hhead)
    (elementary_leastProperIndex_square_lt_card q.Field (s+2) (by omega) (by omega)) H hH

theorem subnormal_gap_or_charTwo_typeC_binary_rank_three
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x)=c)
    (E : NonaffineData (Top (A := A) (X := X)) X)
    (r : ℕ) (hr : 3 ≤ r) (q : CFSG.PrimePower) (hp : q.prime=2)
    (e : E.Simple ≃* CFSG.Models.C r q)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-2) ∨ (r=3 ∧ q.order=2) := by
  by_cases hhead : r=3 ∧ q.order=2
  · exact Or.inr hhead
  · apply Or.inl
    obtain ⟨s,rfl⟩ : ∃ s : ℕ, r=s+3 := ⟨r-3,by omega⟩
    letI : IsSimpleGroup (CFSG.Models.C (s+3) q) := e.symm.isSimpleGroup
    exact of_literal π hπ c hc hsize E (s+3) (by omega) q hp hhead
      (e.trans (serreProjectiveEquivElementaryProjective q.Field (s+2))) H hH

theorem subnormal_gap_or_charTwo_typeB_binary_rank_three
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x)=c)
    (E : NonaffineData (Top (A := A) (X := X)) X)
    (r : ℕ) (hr : 3 ≤ r) (q : CFSG.PrimePower) (hp : q.prime=2)
    (e : E.Simple ≃* CFSG.Models.B r q)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-2) ∨ (r=3 ∧ q.order=2) := by
  by_cases hhead : r=3 ∧ q.order=2
  · exact Or.inr hhead
  · apply Or.inl
    obtain ⟨s,rfl⟩ : ∃ s : ℕ, r=s+3 := ⟨r-3,by omega⟩
    letI : IsSimpleGroup (CFSG.Models.B (s+3) q) := e.symm.isSimpleGroup
    letI : CharP q.Field 2 := by rw [←hp]; infer_instance
    exact of_literal π hπ c hc hsize E (s+3) (by omega) q hp hhead
      (e.trans (CFSGOrthogonalBSerreMatrices.serreProjectiveEquivSymplecticProjective_charTwo
        q.Field (s+2) (by omega))) H hH

end SymmetricSubgroupAsymptotics.SmallFibreCharTwoClassicalClassGap
