import SymmetricSubgroupAsymptotics.CFSGConjugateSubgroupDegree

/-! A weighted Burnside degree bound for equally sized nonidentity
classes. The sum retains the actual fixed-point counts before cancelling
the group-order factor; k=2 is suited to square-scalar orbits. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGConjugateSubgroupDegree
open MulAction

theorem card_le_mul_of_fixedBy_average {P X : Type*} [Group P]
    [Fintype P] [Fintype X] [MulAction P X] (k F : ℕ)
    (hF : F < k*Fintype.card X)
    (haverage : k*(∑ a ∈ (Finset.univ : Finset P).erase 1,
      Fintype.card (fixedBy X a))=(Fintype.card P-1)*F) :
    Nat.card P ≤ k*Nat.card X := by
  letI : Fintype (Quotient (orbitRel P X)) := Fintype.ofFinite _
  have hone : Fintype.card (fixedBy X (1 : P))=Fintype.card X :=
    Fintype.card_congr
      { toFun := fun y => y.val
        invFun := fun y => ⟨y,one_smul P y⟩
        left_inv := fun y => Subtype.ext rfl
        right_inv := fun _ => rfl }
  have hburn := sum_card_fixedBy_eq_card_orbits_mul_card_group P X
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : P)),hone] at hburn
  have hw : k*Fintype.card X+(Fintype.card P-1)*F=
      Fintype.card P*(k*Fintype.card (Quotient (orbitRel P X))) := by
    calc
      _ = k*(Fintype.card X+∑ a ∈ (Finset.univ : Finset P).erase 1,
          Fintype.card (fixedBy X a)) := by rw [Nat.mul_add,haverage]
      _ = k*(Fintype.card (Quotient (orbitRel P X))*Fintype.card P) :=
        congrArg (fun n : ℕ => k*n) hburn
      _ = _ := by ac_rfl
  have hq : 1≤Fintype.card P := Fintype.card_pos
  have hsplit : (Fintype.card P-1)*F+F=Fintype.card P*F := by
    calc
      _ = ((Fintype.card P-1)+1)*F := by rw [Nat.add_mul,one_mul]
      _ = _ := by rw [Nat.sub_add_cancel hq]
  have hdecomp : (k*Fintype.card X-F)+Fintype.card P*F=
      k*Fintype.card X+(Fintype.card P-1)*F := by omega
  have hd : Fintype.card P ∣ (k*Fintype.card X-F)+Fintype.card P*F := by
    rw [hdecomp,hw]
    exact dvd_mul_right _ _
  have hdiv : Fintype.card P ∣ k*Fintype.card X-F := by
    have h := Nat.dvd_sub hd (dvd_mul_right (Fintype.card P) F)
    simpa only [Nat.add_sub_cancel] using h
  have hle := Nat.le_of_dvd (by omega : 0<k*Fintype.card X-F) hdiv
  simpa only [Nat.card_eq_fintype_card] using
    hle.trans (Nat.sub_le (k*Fintype.card X) F)

end SymmetricSubgroupAsymptotics.CFSGConjugateSubgroupDegree
