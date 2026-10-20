import SymmetricSubgroupAsymptotics.NormalSubgroupCentralizerProjection

/-! Three commuting-pair rectangles give a class-number estimate for any
actual normal subgroup whose outside centralizers admit one fixed projection. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.NormalSubgroupConjugacyClassCount

variable {G H : Type} [Group G] [Group H]
    (K : Subgroup G) (f : K →* H)

private abbrev Outside := {x : G // x ∉ K}
private abbrev Inner := {p : K × K // Commute p.1 p.2}
private abbrev OuterWhole := Σ x : Outside K, {y : G // Commute (x : G) y}
private abbrev OuterInner := Σ x : Outside K, {y : K // Commute (x : G) (y : G)}

private def encode (p : {p : G × G // Commute p.1 p.2}) :
    Inner K ⊕ (OuterWhole K ⊕ OuterInner K) :=
  if hy : p.1.2 ∈ K then
    if hx : p.1.1 ∈ K then
      .inl ⟨(⟨p.1.1,hx⟩,⟨p.1.2,hy⟩),Subtype.ext p.2.eq⟩
    else .inr (.inr ⟨⟨p.1.1,hx⟩,⟨⟨p.1.2,hy⟩,p.2⟩⟩)
  else .inr (.inl ⟨⟨p.1.2,hy⟩,⟨p.1.1,p.2.symm⟩⟩)

private theorem encode_injective : Function.Injective (encode K) := by
  rintro ⟨⟨x,y⟩,hc⟩ ⟨⟨u,v⟩,hd⟩ he
  by_cases hy : y ∈ K <;> by_cases hv : v ∈ K
  · by_cases hx : x ∈ K <;> by_cases hu : u ∈ K
    · simp only [encode,dif_pos hx,dif_pos hy,dif_pos hu,dif_pos hv] at he
      have hp := congrArg Subtype.val (Sum.inl.inj he)
      exact Subtype.ext (Prod.ext
        (congrArg (fun p : K × K => (p.1 : G)) hp)
        (congrArg (fun p : K × K => (p.2 : G)) hp))
    · simp only [encode,dif_pos hx,dif_pos hy,dif_neg hu,dif_pos hv] at he
      cases he
    · simp only [encode,dif_neg hx,dif_pos hy,dif_pos hu,dif_pos hv] at he
      cases he
    · simp only [encode,dif_neg hx,dif_pos hy,dif_neg hu,dif_pos hv] at he
      have hs := Sigma.mk.inj_iff.mp (Sum.inr.inj (Sum.inr.inj he))
      have hx : x = u := congrArg Subtype.val hs.1
      subst u
      have hh := eq_of_heq hs.2
      have hyv : y = v := congrArg
        (fun z : {y : K // Commute x (y : G)} => ((z.1 : K) : G)) hh
      exact Subtype.ext (Prod.ext rfl hyv)
  · by_cases hx : x ∈ K <;> simp [encode,hx,hy,hv] at he
  · by_cases hu : u ∈ K <;> simp [encode,hy,hu,hv] at he
  · simp only [encode,dif_neg hy,dif_neg hv] at he
    have hs := Sigma.mk.inj_iff.mp (Sum.inl.inj (Sum.inr.inj he))
    have hyv : y = v := congrArg Subtype.val hs.1
    subst v
    have hh := eq_of_heq hs.2
    have hxu : x = u := congrArg (fun z : {z : G // Commute y z} => z.1) hh
    exact Subtype.ext (Prod.ext hxu rfl)

variable [Finite G] [Finite H] [K.Normal]
    (hinj : ∀ x : G, x ∉ K → ∀ y z : K,
      Commute x (y : G) → Commute x (z : G) → f y = f z → y = z)

include hinj in
/-- The index is retained literally. For index three this is the estimate
`3*k(G) ≤ k(K)+8*|H|`, before any numerical class bound is substituted. -/
theorem index_mul_class_card_le :
    K.index * Nat.card (ConjClasses G) + Nat.card H ≤
      Nat.card (ConjClasses K) + K.index ^ 2 * Nat.card H := by
  letI : Fintype (Outside K) := Fintype.ofFinite _
  have hw : Nat.card (OuterWhole K) ≤
      Nat.card (Outside K) * (K.index * Nat.card H) := by
    rw [Nat.card_sigma]
    calc
      _ ≤ ∑ _x : Outside K, K.index * Nat.card H :=
        Finset.sum_le_sum (fun x _ =>
          NormalSubgroupCentralizerProjection.whole_partner_card_le K f hinj x.1 x.2)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
          Fintype.card_eq_nat_card,Nat.cast_id]
  have hi : Nat.card (OuterInner K) ≤
      Nat.card (Outside K) * Nat.card H := by
    rw [Nat.card_sigma]
    calc
      _ ≤ ∑ _x : Outside K, Nat.card H :=
        Finset.sum_le_sum (fun x _ =>
          NormalSubgroupCentralizerProjection.kernel_partner_card_le K f hinj x.1 x.2)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
          Fintype.card_eq_nat_card,Nat.cast_id]
  have hr := Nat.card_le_card_of_injective (encode K) (encode_injective K)
  simp only [Nat.card_sum] at hr
  change Nat.card {p : G × G // Commute p.1 p.2} ≤
    Nat.card {p : K × K // Commute p.1 p.2} +
      (Nat.card (OuterWhole K) + Nat.card (OuterInner K)) at hr
  rw [card_comm_eq_card_conjClasses_mul_card,
    card_comm_eq_card_conjClasses_mul_card] at hr
  have hpart : Nat.card K + Nat.card (Outside K) = Nat.card G := by
    simpa only [Nat.card_sum] using Nat.card_congr (Equiv.Set.sumCompl (K : Set G))
  have hwhole := K.card_mul_index
  have hpositive := Nat.card_pos (α := K)
  have hscaled := congrArg
    (fun z : ℕ => z * ((K.index + 1) * Nat.card H)) (hpart.trans hwhole.symm)
  rw [← hwhole] at hr
  have hraw : Nat.card K *
      (K.index * Nat.card (ConjClasses G) + Nat.card H) ≤
      Nat.card K * (Nat.card (ConjClasses K) + K.index ^ 2 * Nat.card H) := by
    nlinarith
  exact Nat.le_of_mul_le_mul_left hraw hpositive

end SymmetricSubgroupAsymptotics.NormalSubgroupConjugacyClassCount
