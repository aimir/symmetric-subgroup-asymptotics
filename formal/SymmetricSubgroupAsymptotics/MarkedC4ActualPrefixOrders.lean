import SymmetricSubgroupAsymptotics.MarkedC4ActualEfficientRowIncidence

/-! Exact orders of the actual prefix kernels. These orders, and hence the
recovering-array multiplicity, are constant on a fixed actual-diagonal
family. The resulting row inequality permits multiplicity cancellation. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualPrefixOrders
open ActualSubdirectFiltration ActualEfficientRowIncidence

variable {t : ℕ} (F : Fin t → Type) [∀ i,Group (F i)] [∀ i,Finite (F i)]
  (H : Subgroup (∀ i,F i))

/-- The exact sequence uses the actual coordinate restriction and its
actual kernel, rather than an abstract diagonal model. -/
theorem card_prefix_step (i : Fin t) :
    Nat.card («prefix» F H (i.val+1))=
      Nat.card (diagonal F H i)*Nat.card («prefix» F H i.val) := by
  let U := «prefix» F H (i.val+1)
  let ρ : U →* F i := (coordinate F H i).comp U.subtype
  have hrange : ρ.range=diagonal F H i := by
    ext q
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨x.val,x.property,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x,hx⟩,rfl⟩
  let e : ρ.ker ≃ «prefix» F H i.val :=
    { toFun := fun x => ⟨x.val.val,prefix_kernel F H i x.val.val x.val.property
        (show coordinate F H i x.val.val=1 from x.property)⟩
      invFun := fun x => ⟨⟨x.val,prefix_mono F H i.val x.property⟩,
        (show coordinate F H i x.val=1 from
          (mem_prefix F H i.val x.val).mp x.property i le_rfl)⟩
      left_inv := fun x => Subtype.ext (Subtype.ext rfl)
      right_inv := fun x => Subtype.ext rfl }
  have hker := Nat.card_congr e
  have hquot : Nat.card (U ⧸ ρ.ker)=Nat.card (diagonal F H i) := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv,hrange]
  have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker
  rw [hquot,hker] at hc
  exact hc

/-- Equal actual diagonal tuples force equal actual prefix orders. -/
theorem card_prefix_eq (K : Subgroup (∀ i,F i))
    (hD : ∀ i,diagonal F H i=diagonal F K i) (m : ℕ) (hm : m≤t) :
    Nat.card («prefix» F H m)=Nat.card («prefix» F K m) := by
  induction m with
  | zero => simp [prefix_zero]
  | succ m ih =>
    let i : Fin t := ⟨m,by omega⟩
    have hH := card_prefix_step F H i
    have hK := card_prefix_step F K i
    change Nat.card («prefix» F H (m+1))=_ at hH
    change Nat.card («prefix» F K (m+1))=_ at hK
    rw [hH,hK,hD i,ih (by omega)]

variable (D : ∀ i,Subgroup (F i))
local instance : Fintype (Family F D) := Fintype.ofFinite _

def multiplicity (H : Family F D) : ℕ :=
  ∏ i : Fin t,Nat.card («prefix» F H.val i.val)^normalGen (D i)

theorem multiplicity_eq (H K : Family F D) :
    multiplicity F D H=multiplicity F D K := by
  apply Finset.prod_congr rfl
  intro i _
  rw [card_prefix_eq F H.val K.val
    (fun j => (H.property.2.2 j).trans (K.property.2.2 j).symm) i.val (Nat.le_of_lt i.isLt)]

/-- Actual row enumeration with one common multiplicity factor. Division
may now be done once after passing to positive real cardinalities. -/
theorem card_mul_multiplicity_le (H : Family F D) :
    Nat.card (Family F D)*multiplicity F D H ≤
      ∏ i : Fin t,Nat.card
        {x : ∀ j,F j // ∀ j : Fin t,i.val<j.val → x j=1}^normalGen (D i) := by
  have h := weighted_card_le F D
  have hs : (∑ K : Family F D,multiplicity F D K)=
      Nat.card (Family F D)*multiplicity F D H := by
    calc
      _ = ∑ _K : Family F D,multiplicity F D H :=
        Finset.sum_congr rfl (fun K _ => multiplicity_eq F D K H)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,
        nsmul_eq_mul,Nat.card_eq_fintype_card,Nat.cast_id]
  change (∑ K : Family F D,multiplicity F D K)≤_ at h
  rw [hs] at h
  exact h

end SymmetricSubgroupAsymptotics.MarkedC4.ActualPrefixOrders
