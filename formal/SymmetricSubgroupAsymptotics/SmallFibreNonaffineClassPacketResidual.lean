import SymmetricSubgroupAsymptotics.SmallFibreComponentClassWreathGapNumerics
import SymmetricSubgroupAsymptotics.SubnormalSmallFibreTopClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleSubnormalClassBound

/-! A component class packet pays the SAME original binary/ternary
block action and each actual subnormal source subgroup. All multiplicities
and both raw degree forms are retained. The only alternative is a literal
one-factor index form in the short interval; no natural-action recognition,
splitting, full-base comparison or bounded-degree class callback is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.SmallFibreNonaffineClassPacketResidual
open PrimitiveSocleRawStructure OriginalBlockClassBound

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]

theorem subnormal_gap_or_single_short_index
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x)=c)
    (E : NonaffineData (Top (A := A) (X := X)) X)
    (b : ℕ) (hb : 5 ≤ b)
    (hindex : ∀ K : Subgroup E.Simple, K ≠ ⊤ → b ≤ K.index)
    (hsquare : b^2 ≤ Nat.card E.Simple)
    (hbase : (Nat.card (ConjClasses E.Simple)*Nat.card (Outer E.Simple))^3 ≤ 5^(b+1))
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-2) ∨
      (E.factorCount=1 ∧ ∃ K : Subgroup E.Simple, K ≠ ⊤ ∧
        Nat.card X=K.index ∧ b ≤ K.index ∧ K.index < 2*b+2) := by
  let B := Nat.card (ConjClasses E.Simple)*Nat.card (Outer E.Simple)
  have hB : B^3 ≤ 5^(b+1) := hbase
  have htop : ∀ L : Subgroup (Top (A := A) (X := X)), L.IsSubnormal →
      Nat.card (ConjClasses L) ≤ B^E.factorCount*E.factorCount.factorial := by
    intro L hL
    exact E.subnormal_class_card_le_outer_wreath L hL
  have hlocal : ∀ x (L : Subgroup (Equiv.Perm (originalBlockFibre π x))),
      Nat.card (ConjClasses L) ≤ c := by
    rcases hc with rfl | rfl
    · exact fun x L => SmallPermutationClassBudgets.subgroup_class_card_le_two (hsize x).le L
    · exact fun x L => SmallPermutationClassBudgets.subgroup_class_card_le_three (hsize x).le L
  have hbound := SubnormalSmallFibreTopClassBound.subnormal_class_card_le_power_mul_top_budget
    π hπ c hlocal (B^E.factorCount*E.factorCount.factorial) htop H hH
  have hcard := GaronziMarotiLargeBlockReduction.card_eq_blocks_mul_fibre π c hsize
  have finish (hnum : (c^Nat.card X*(B^E.factorCount*E.factorCount.factorial))^3 ≤
      5^(c*Nat.card X-2)) : Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-2) := by
    have h := (Nat.pow_le_pow_left hbound 3).trans hnum
    simpa only [hcard,Nat.mul_comm (Nat.card X) c] using h
  by_cases hk : 2 ≤ E.factorCount
  · have hpower : b^E.factorCount ≤ Nat.card X := by
      rcases E.indexForm with ⟨K,hK,hdegree⟩ | ⟨a,hka,hdegree⟩
      · exact (Nat.pow_le_pow_left (hindex K hK) _).trans_eq hdegree.symm
      · rw [hdegree]
        calc
          b^E.factorCount ≤ b^(2*a) := Nat.pow_le_pow_right (by omega) hka
          _ = (b^2)^a := pow_mul b 2 a
          _ ≤ (Nat.card E.Simple)^a := Nat.pow_le_pow_left hsquare a
    left
    apply finish
    rcases hc with rfl | rfl
    · exact SmallFibreComponentClassWreathGapNumerics.binary_multi_product_cube_gap
        B b E.factorCount (Nat.card X) hb hk hB hpower
    · exact SmallFibreComponentClassWreathGapNumerics.ternary_multi_product_cube_gap
        B b E.factorCount (Nat.card X) hb hk hB hpower
  · have hk1 : E.factorCount=1 := by have hp := E.factorCount_pos; omega
    by_cases hfar : 2*b+2 ≤ Nat.card X
    · left
      apply finish
      rcases hc with rfl | rfl
      · simpa only [hk1,pow_one,Nat.factorial_one,mul_one] using
          SmallFibreComponentClassWreathGapNumerics.binary_far_product_cube_gap
            B b (Nat.card X) hb hB hfar
      · simpa only [hk1,pow_one,Nat.factorial_one,mul_one] using
          SmallFibreComponentClassWreathGapNumerics.ternary_far_product_cube_gap
            B b (Nat.card X) hb hB hfar
    · right
      rcases E.indexForm with ⟨K,hK,hdegree⟩ | ⟨a,hka,hdegree⟩
      · have hd : Nat.card X=K.index := by simpa only [hk1,pow_one] using hdegree
        exact ⟨hk1,K,hK,hd,hindex K hK,by omega⟩
      · have ha : 1 ≤ a := by omega
        have hpower : b^2 ≤ Nat.card X := by
          rw [hdegree]
          exact hsquare.trans (Nat.le_self_pow (by omega : a ≠ 0) (Nat.card E.Simple))
        have hfar' : 2*b+2 ≤ Nat.card X := (by nlinarith : 2*b+2 ≤ b^2).trans hpower
        exact (hfar hfar').elim

end SymmetricSubgroupAsymptotics.SmallFibreNonaffineClassPacketResidual
