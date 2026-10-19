import SymmetricSubgroupAsymptotics.AlternatingSymmetricComplementChiefBounds
import SymmetricSubgroupAsymptotics.SmallAffineChiefOrderSavingCertificate

/-! Structural receipts for actual simple or alternating-monolithic
quotients. The premises concern literal maps and numerical order budgets;
no chief-series or affine-capacity conclusion is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
namespace AlternatingSymmetricChiefCertificateFactories

variable {G S : Type} [Group G] [Finite G] [Group S] [Finite S]

private theorem top_noncommutative (h : ¬ IsMulCommutative S) :
    ¬ IsMulCommutative (⊤ : Subgroup S) := by
  intro hc
  letI := hc
  apply h
  refine ⟨⟨?_⟩⟩
  intro x y
  exact congrArg Subtype.val (mul_comm (⟨x,by trivial⟩ : (⊤ : Subgroup S)) ⟨y,by trivial⟩)

def simpleQuotient [IsSimpleGroup S] (cap : ℕ)
    (f : G →* S) (hf : Function.Surjective f) (hnc : ¬ IsMulCommutative S)
    (hbudget : ArithmeticFunction.cardFactors (Nat.card G) ≤
      ArithmeticFunction.cardFactors (Nat.card S)+cap) :
    SmallAffineChiefOrderSavingCertificate G cap :=
  .monolithicQuotient
    { Target := S
      targetGroup := inferInstance
      targetFinite := inferInstance
      quotientMap := f
      quotient_surjective := hf
      core := ⊤
      normal := inferInstance
      noncommutative := top_noncommutative hnc
      le_every_nontrivial_normal := by
        intro K hK hne
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K hK with hb | ht
        · exact False.elim (hne hb)
        · rw [ht]
      order_budget := by
        have hc : Nat.card (⊤ : Subgroup S)=Nat.card S :=
          Nat.card_congr Subgroup.topEquiv.toEquiv
        rw [hc]
        exact hbudget }

private theorem alternating_noncommutative (n : ℕ) (hn : 5 ≤ n) :
    ¬ IsMulCommutative (alternatingGroup (Fin n)) := by
  rw [alternatingGroup.isMulCommutative_iff_card_le_three]
  simpa using (show ¬ n ≤ 3 by omega)

def alternatingQuotient (n : ℕ) (hn : 5 ≤ n) (cap : ℕ)
    (f : G →* alternatingGroup (Fin n)) (hf : Function.Surjective f)
    (hbudget : ArithmeticFunction.cardFactors (Nat.card G) ≤
      ArithmeticFunction.cardFactors (Nat.card (alternatingGroup (Fin n)))+cap) :
    SmallAffineChiefOrderSavingCertificate G cap := by
  letI := alternatingGroup.isSimpleGroup (α := Fin n) (by simpa using hn)
  exact simpleQuotient cap f hf (alternating_noncommutative n hn) hbudget

def symmetricQuotient (n : ℕ) (hn : 5 ≤ n) (cap : ℕ)
    (f : G →* Equiv.Perm (Fin n)) (hf : Function.Surjective f)
    (hbudget : ArithmeticFunction.cardFactors (Nat.card G) ≤
      ArithmeticFunction.cardFactors (Nat.card (alternatingGroup (Fin n)))+cap) :
    SmallAffineChiefOrderSavingCertificate G cap :=
  .monolithicQuotient
    { Target := Equiv.Perm (Fin n)
      targetGroup := inferInstance
      targetFinite := inferInstance
      quotientMap := f
      quotient_surjective := hf
      core := alternatingGroup (Fin n)
      normal := inferInstance
      noncommutative := alternating_noncommutative n hn
      le_every_nontrivial_normal := by
        intro K hK hne
        letI : K.Normal := hK
        letI : Nontrivial K := K.nontrivial_iff_ne_bot.mpr hne
        exact Equiv.Perm.alternatingGroup_le_of_normal (by simpa using hn) inferInstance
      order_budget := hbudget }

def alternatingEquiv (n : ℕ) (hn : 5 ≤ n) (e : G ≃* alternatingGroup (Fin n)) :
    SmallAffineChiefOrderSavingCertificate G 0 :=
  alternatingQuotient n hn 0 e.toMonoidHom e.surjective (by
    rw [Nat.card_congr e.toEquiv]
    omega)

def symmetricEquiv (n : ℕ) (hn : 5 ≤ n) (e : G ≃* Equiv.Perm (Fin n)) :
    SmallAffineChiefOrderSavingCertificate G 1 := by
  apply symmetricQuotient n hn 1 e.toMonoidHom e.surjective
  letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hc : Nat.card G=2*Nat.card (alternatingGroup (Fin n)) :=
    (Nat.card_congr e.toEquiv).trans (two_mul_nat_card_alternatingGroup (α := Fin n)).symm
  rw [hc,ArithmeticFunction.cardFactors_mul (by decide)
    (Nat.card_pos (α := alternatingGroup (Fin n))).ne']
  rw [ArithmeticFunction.cardFactors_apply_prime Nat.prime_two]
  omega

end AlternatingSymmetricChiefCertificateFactories
end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
