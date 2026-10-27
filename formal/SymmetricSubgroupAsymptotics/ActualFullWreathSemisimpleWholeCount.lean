import SymmetricSubgroupAsymptotics.ActualFullWreathSemisimpleQuotientFibreCount
import SymmetricSubgroupAsymptotics.ActualFullWreathSameTopRank
import SymmetricSubgroupAsymptotics.ActualFullWreathSmallBaseCount
import SymmetricSubgroupAsymptotics.ActualFullWreathFamilyFibreSum
import SymmetricSubgroupAsymptotics.FiniteSubgroupSmallOrderCount

/-! Whole actual family bound, including every compressed image and every
semisimple intersection/lift. The ONLY top cost is its genuine tuple. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ActualFullWreathSemisimpleWholeCount

theorem exists_tuple {G : Type} [Group G] [Finite G] (d : ℕ)
    (hd : MarkedC4.genRank G≤d) : ∃ f : Fin d → G,Subgroup.closure (Set.range f)=⊤ := by
  apply FiniteSubgroupSmallOrderCount.exists_ambient_tuple (⊤ : Subgroup G) d
  rw [CoprimeNilpotentProductGenerators.genRank_mulEquiv (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G)]
  exact hd

variable {R Q I J T : Type} [Group R] [Finite R] [Group Q] [Finite Q]
    [MulAction Q I] [Finite I] [Group T] [Finite T] [IsSimpleGroup T] [Fintype J]
    (N : Subgroup R) [N.Normal] (eN : N ≃* (J → T)) (hZ : IsCenterless T)

include eN hZ in
theorem card_family_le (a : ℕ) (ha : Nat.card (R ⧸ N)≤2^a) {q : ℕ}
    (fQ : Fin q → Q) (hfQ : Subgroup.closure (Set.range fQ)=⊤) :
    Nat.card (ActualFullWreathFamily.Family R Q I)≤
      (2^((Nat.card I*a)*(Nat.card I*a))*Nat.card (R ⧸ N)^(Nat.card I*q))*
      ((2^(Nat.card I*Nat.card J)*
        (2*(1+(Nat.card I*Nat.card J)*Nat.card (T ≃* T)))^(Nat.card I*Nat.card J))*
        Nat.card T^((Nat.card I*Nat.card J)*(Nat.card I*a+q))) := by
  classical
  have hq : MarkedC4.genRank Q≤q := by
    have hh : Subgroup.closure ((Finset.univ.image fQ : Finset Q) : Set Q)=⊤ := by
      simpa only [Finset.coe_image,Finset.coe_univ,Set.image_univ] using hfQ
    have hc : (Finset.univ.image fQ).card≤q := by
      calc
        _≤(Finset.univ : Finset (Fin q)).card := Finset.card_image_le
        _=q := by simp only [Finset.card_univ,Fintype.card_fin]
    exact (MarkedC4.genRank_le hh).trans hc
  have hfibre : ∀ H : ActualFullWreathFamily.Family (R ⧸ N) Q I,
      Nat.card (ActualFullWreathPreimage.Fibre (QuotientGroup.mk' N)
        (QuotientGroup.mk'_surjective N) H)≤
      (2^(Nat.card I*Nat.card J)*
        (2*(1+(Nat.card I*Nat.card J)*Nat.card (T ≃* T)))^(Nat.card I*Nat.card J))*
        Nat.card T^((Nat.card I*Nat.card J)*(Nat.card I*a+q)) := by
    intro H
    have hH := (ActualFullWreathSameTopRank.genRank_le H a ha).trans (Nat.add_le_add_left hq _)
    obtain ⟨f,hf⟩ := exists_tuple (Nat.card I*a+q) hH
    exact ActualFullWreathSemisimpleQuotientFibreCount.card_fibre_le N eN hZ H f hf
  have hall := ActualFullWreathFamilyFibreSum.card_le_mul (QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N) _ hfibre
  exact hall.trans (Nat.mul_le_mul_right _ (ActualFullWreathSmallBaseCount.card_family_le a ha fQ hfQ))

end SymmetricSubgroupAsymptotics.ActualFullWreathSemisimpleWholeCount
