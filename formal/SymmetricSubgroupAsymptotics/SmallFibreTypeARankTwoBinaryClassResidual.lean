import SymmetricSubgroupAsymptotics.CFSGTypeARankTwoBinaryClassPacket
import SymmetricSubgroupAsymptotics.SmallFibreTwelveClassEnvelope
import SymmetricSubgroupAsymptotics.SmallFibreNonaffinePerIndexClassResidual
import SymmetricSubgroupAsymptotics.CFSGTypeALeastIndexSquare
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport

/-! The genuine six-class binary rank-two factor eliminates all
ternary fibres and binary actions with at least ten blocks. Every other
factor/degree form is discharged before retaining the SAME actual
one-factor subgroup of index seven or eight. Index nine is excluded by
its actual order168, not by a representation classification. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SmallFibreTypeARankTwoBinaryClassResidual
open PrimitiveSocleRawStructure OriginalBlockClassBound CFSGReduction

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]

theorem subnormal_gap_or_binary_seven_eight
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x)=c)
    (E : NonaffineData (Top (A := A) (X := X)) X)
    (q : CFSG.PrimePower) (hq : q.order=2) (e : E.Simple ≃* CFSG.Models.A 2 q)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-2) ∨
      (c=2 ∧ E.factorCount=1 ∧ ∃ K : Subgroup E.Simple,
        K≠⊤ ∧ Nat.card X=K.index ∧ (K.index=7 ∨ K.index=8)) := by
  letI : IsSimpleGroup (CFSG.Models.A 2 q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.A 2 q) := Finite.of_equiv E.Simple e.toEquiv
  let B := Nat.card (ConjClasses E.Simple)*Nat.card (Outer E.Simple)
  have hclasses : Nat.card (ConjClasses E.Simple)=Nat.card (ConjClasses (CFSG.Models.A 2 q)) := by
    apply Nat.le_antisymm
    · exact Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
        (ConjClasses.map_surjective e.symm.surjective)
    · exact Nat.card_le_card_of_surjective (ConjClasses.map e.toMonoidHom)
        (ConjClasses.map_surjective e.surjective)
  have hB : B ≤ 12 := by
    dsimp only [B]
    rw [hclasses,outer_card_congr e]
    exact CFSGTypeARankTwoBinaryClassPacket.component_class_card_le_twelve q hq
  have hcardS : Nat.card E.Simple=168 :=
    (Nat.card_congr e.toEquiv).trans (CFSGTypeARankTwoCardTwo.order_eq_168 q hq)
  have hindex : ∀ K : Subgroup E.Simple, K≠⊤ → 7 ≤ K.index := by
    intro K hK
    apply CFSGTypeARankTwoCardTwo.prime_le_proper_index 7 (by decide) ?_ K hK
    rw [hcardS]
    decide
  have hbudget : ∀ K : Subgroup E.Simple, K≠⊤ → B^3 ≤ 5^(K.index+1) := by
    intro K hK
    have hi := hindex K hK
    exact (Nat.pow_le_pow_left hB 3).trans
      ((by decide : (12:ℕ)^3 ≤ 5^8).trans
        (Nat.pow_le_pow_right (by decide) (by omega)))
  have hsquare : ∀ ell : ℕ, LeastProperIndex E.Simple ell → ell^2 < Nat.card E.Simple := by
    intro ell hell
    rw [Nat.card_congr e.toEquiv]
    exact CFSGTypeALeastIndexSquare.typeA_leastProperIndex_square_lt_card 2 (by decide) q ell
      (leastProperIndex_of_mulEquiv e ell hell)
  rcases SmallFibreNonaffinePerIndexClassResidual.subnormal_gap_or_least_short_index
      π hπ c hc hsize E hbudget hsquare H hH with hgap | ⟨hk,ell,hell,K,hK,hdegree,hlo,hhi⟩
  · exact Or.inl hgap
  · have hn : 7 ≤ Nat.card X := by rw [hdegree]; exact hindex K hK
    have hnine : Nat.card X≠9 := by
      intro he
      have hd : K.index ∣ 168 := by simpa only [hcardS] using K.index_dvd_card
      rw [←hdegree,he] at hd
      exact (by decide : ¬ (9:ℕ)∣168) hd
    by_cases hsmall : c=2 ∧ Nat.card X<10
    · exact Or.inr ⟨hsmall.1,hk,K,hK,hdegree,by rw [←hdegree]; omega⟩
    · have htop : ∀ L : Subgroup (Top (A := A) (X := X)), L.IsSubnormal →
          Nat.card (ConjClasses L) ≤ 12 := by
        intro L hL
        have hh : Nat.card (ConjClasses L) ≤ B := by
          simpa only [hk,pow_one,Nat.factorial_one,mul_one] using
            E.subnormal_class_card_le_outer_wreath L hL
        exact hh.trans hB
      have hlocal : ∀ x (L : Subgroup (Equiv.Perm (originalBlockFibre π x))),
          Nat.card (ConjClasses L) ≤ c := by
        rcases hc with rfl | rfl
        · exact fun x L => SmallPermutationClassBudgets.subgroup_class_card_le_two (hsize x).le L
        · exact fun x L => SmallPermutationClassBudgets.subgroup_class_card_le_three (hsize x).le L
      have hbound := SubnormalSmallFibreTopClassBound.subnormal_class_card_le_power_mul_top_budget
        π hπ c hlocal 12 htop H hH
      have hnum : (c^Nat.card X*12)^3 ≤ 5^(c*Nat.card X-2) := by
        rcases hc with rfl | rfl
        · exact SmallFibreTwelveClassEnvelope.binary_gap (Nat.card X) (by omega)
        · exact SmallFibreTwelveClassEnvelope.ternary_gap (Nat.card X) hn
      have hcard := GaronziMarotiLargeBlockReduction.card_eq_blocks_mul_fibre π c hsize
      have hh := (Nat.pow_le_pow_left hbound 3).trans hnum
      exact Or.inl (by simpa only [hcard,Nat.mul_comm (Nat.card X) c] using hh)

theorem ternary_subnormal_class_cube_gap
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω)=g • π ω)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x)=3)
    (E : NonaffineData (Top (A := A) (X := X)) X)
    (q : CFSG.PrimePower) (hq : q.order=2) (e : E.Simple ≃* CFSG.Models.A 2 q)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-2) := by
  rcases subnormal_gap_or_binary_seven_eight π hπ 3 (Or.inr rfl) hsize E q hq e H hH with h | h
  · exact h
  · omega

theorem binary_subnormal_class_cube_gap_of_ten_le
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω)=g • π ω)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x)=2)
    (hn : 10 ≤ Nat.card X)
    (E : NonaffineData (Top (A := A) (X := X)) X)
    (q : CFSG.PrimePower) (hq : q.order=2) (e : E.Simple ≃* CFSG.Models.A 2 q)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-2) := by
  rcases subnormal_gap_or_binary_seven_eight π hπ 2 (Or.inl rfl) hsize E q hq e H hH with h | h
  · exact h
  · obtain ⟨_,_,K,hK,he,hidx⟩ := h
    omega

end SymmetricSubgroupAsymptotics.SmallFibreTypeARankTwoBinaryClassResidual
