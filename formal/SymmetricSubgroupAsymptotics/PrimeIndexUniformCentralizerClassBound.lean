import SymmetricSubgroupAsymptotics.PrimeIndexAbelianClassCount
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finite.Sum
import Mathlib.Tactic.Linarith

/-! Coupled prime-index class bounds from the cardinalities of the
ACTUAL outside fixed kernels. The detecting coordinate may depend on
the outside element: no one fixed projection or splitting is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.PrimeIndexUniformCentralizerClassBound
open PrimeIndexAbelianCentralizers PrimeIndexOutsideCentralizerCard
variable {G : Type} [Group G] (K : Subgroup G)

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


def kernelPartnerEquiv (x : G) :
    {y : K // Commute x (y:G)}≃fixedKernel K x where
  toFun y := ⟨y.val,Subgroup.mem_centralizer_singleton_iff.mpr y.property.eq.symm⟩
  invFun y := ⟨y.val,(Subgroup.mem_centralizer_singleton_iff.mp y.property).symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable [Finite G] [K.Normal]

theorem index_mul_class_card_le (p : ℕ) (hp : p.Prime) (hindex : K.index=p)
    (c : ℕ) (hc : ∀x : G,x∉K→Nat.card (fixedKernel K x)≤c) :
    p*Nat.card (ConjClasses G)+c≤Nat.card (ConjClasses K)+p^2*c := by
  letI : Fintype (Outside K) := Fintype.ofFinite _
  letI : Finite (Inner K) := by unfold Inner; infer_instance
  letI : Finite (OuterWhole K) := by unfold OuterWhole; infer_instance
  letI : Finite (OuterInner K) := by unfold OuterInner; infer_instance
  have hw : Nat.card (OuterWhole K)≤Nat.card (Outside K)*(p*c) := by
    rw [Nat.card_sigma]
    calc
      _≤∑_x : Outside K,p*c := by
        apply Finset.sum_le_sum
        intro x _
        have he : Nat.card {y : G // Commute (x:G) y}=p*Nat.card (fixedKernel K x) :=
          (Nat.card_congr (partnerEquivCentralizer x.val)).trans
            (outside_centralizer_card K p hp hindex x.val x.property)
        rw [he]
        exact Nat.mul_le_mul_left _ (hc x.val x.property)
      _=_ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
        Fintype.card_eq_nat_card,Nat.cast_id]
  have hi : Nat.card (OuterInner K)≤Nat.card (Outside K)*c := by
    rw [Nat.card_sigma]
    calc
      _≤∑_x : Outside K,c := by
        apply Finset.sum_le_sum
        intro x _
        exact (Nat.card_congr (kernelPartnerEquiv K x.val)).le.trans (hc x.val x.property)
      _=_ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
        Fintype.card_eq_nat_card,Nat.cast_id]
  have hr := Nat.card_le_card_of_injective (encode K) (encode_injective K)
  simp only [Nat.card_sum] at hr
  change Nat.card {v : G×G // Commute v.1 v.2}≤
    Nat.card {v : K×K // Commute v.1 v.2}+
      (Nat.card (OuterWhole K)+Nat.card (OuterInner K)) at hr
  rw [card_comm_eq_card_conjClasses_mul_card,
    card_comm_eq_card_conjClasses_mul_card] at hr
  have hpart : Nat.card K+Nat.card (Outside K)=Nat.card G := by
    simpa only [Nat.card_sum] using Nat.card_congr (Equiv.Set.sumCompl (K : Set G))
  have hwhole := K.card_mul_index
  rw [hindex] at hwhole
  have hscaled := congrArg (fun z : ℕ=>z*((p+1)*c)) (hpart.trans hwhole.symm)
  rw [←hwhole] at hr
  have hraw : Nat.card K*(p*Nat.card (ConjClasses G)+c)≤
      Nat.card K*(Nat.card (ConjClasses K)+p^2*c) := by nlinarith
  exact Nat.le_of_mul_le_mul_left hraw (Nat.card_pos (α:=K))

end SymmetricSubgroupAsymptotics.PrimeIndexUniformCentralizerClassBound
