import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Order.MinMax

/-! Upper cardinal bounds for dependent coordinates fixed by an
involution with injective coordinate transports. Only one value per
orbit is free; singleton transports need not be the identity. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFiniteInvolutionCoordinatesCardinality
variable {I:Type*} [Fintype I] [LinearOrder I]

def representatives (p:Equiv.Perm I) : Finset I := Finset.univ.filter (fun i=>i≤p i)

theorem twice_representatives_card (p:Equiv.Perm I) (hp:Function.Involutive p) :
    2*(representatives p).card=Nat.card I+Nat.card {i:I // p i=i} := by
  classical
  let L := Finset.univ.filter (fun i:I=>i<p i)
  let F := Finset.univ.filter (fun i:I=>i=p i)
  let N := Finset.univ.filter (fun i:I=>¬i≤p i)
  have hR : representatives p=L∪F := by
    ext i
    simp only [representatives,L,F,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union]
    exact le_iff_lt_or_eq
  have hdis : Disjoint L F := by
    apply Finset.disjoint_left.mpr
    intro i hi hf
    have hl : i<p i := (Finset.mem_filter.mp hi).2
    have he : i=p i := (Finset.mem_filter.mp hf).2
    exact (ne_of_lt hl) he
  let e : {i:I // ¬i≤p i}≃{i:I // i<p i} := {
    toFun i:=⟨p i,by rw [hp];exact lt_of_not_ge i.property⟩
    invFun i:=⟨p i,by rw [hp];exact not_le.mpr i.property⟩
    left_inv i:=Subtype.ext (hp i.val)
    right_inv i:=Subtype.ext (hp i.val) }
  have hLN : L.card=N.card := by
    simpa only [L,N,Nat.card_eq_fintype_card,Fintype.card_subtype] using (Nat.card_congr e).symm
  have hsplit : (representatives p).card+N.card=Nat.card I := by
    simpa only [representatives,N,Nat.card_eq_fintype_card] using
      Finset.card_filter_add_card_filter_not (s:=Finset.univ) (fun i:I=>i≤p i)
  have hfixed : F.card=Nat.card {i:I // p i=i} := by
    simp only [F,Nat.card_eq_fintype_card,Fintype.card_subtype]
    congr 1
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact eq_comm
  rw [hR,Finset.card_union_of_disjoint hdis] at hsplit ⊢
  omega

def fixedCoordinates (C:I→Type*) (p:Equiv.Perm I) (T:∀i,C i→C (p i)) :=
  {c:∀i,C i // ∀i,T i (c i)=c (p i)}

theorem fixedCoordinates_card_le (C:I→Type*) [∀i,Finite (C i)]
    (p:Equiv.Perm I) (hp:Function.Involutive p) (T:∀i,C i→C (p i))
    (hT:∀i,Function.Injective (T i)) (q:ℕ) (hc:∀i,Nat.card (C i)=q) :
    Nat.card (fixedCoordinates C p T)≤q^(representatives p).card := by
  let restrict : fixedCoordinates C p T→∀i:{i // i∈representatives p},C i.val :=
    fun c i=>c.val i.val
  have hi : Function.Injective restrict := by
    intro c d he
    apply Subtype.ext
    funext i
    by_cases h:i≤p i
    · exact congrFun he ⟨i,by simp only [representatives,Finset.mem_filter,Finset.mem_univ,true_and];exact h⟩
    · have hr : p i∈representatives p := by
        simp only [representatives,Finset.mem_filter,Finset.mem_univ,true_and]
        rw [hp i]
        exact le_of_lt (lt_of_not_ge h)
      apply hT i
      exact (c.property i).trans ((congrFun he ⟨p i,hr⟩).trans (d.property i).symm)
  have hb := Nat.card_le_card_of_injective restrict hi
  calc
    Nat.card (fixedCoordinates C p T)≤Nat.card (∀i:{i // i∈representatives p},C i.val) := hb
    _=q^(representatives p).card := by
      rw [Nat.card_pi]
      simp only [hc,Finset.prod_const,Finset.card_univ,Fintype.card_coe]

theorem fixedCoordinates_card_sq_le (C:I→Type*) [∀i,Finite (C i)]
    (p:Equiv.Perm I) (hp:Function.Involutive p) (T:∀i,C i→C (p i))
    (hT:∀i,Function.Injective (T i)) (q:ℕ) (hc:∀i,Nat.card (C i)=q) :
    Nat.card (fixedCoordinates C p T)^2≤q^(Nat.card I+Nat.card {i:I // p i=i}) := by
  have h := Nat.pow_le_pow_left (fixedCoordinates_card_le C p hp T hT q hc) 2
  rw [←pow_mul,Nat.mul_comm _ 2,twice_representatives_card p hp] at h
  exact h

end SymmetricSubgroupAsymptotics.CFSGFiniteInvolutionCoordinatesCardinality
