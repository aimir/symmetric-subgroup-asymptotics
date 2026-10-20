import SymmetricSubgroupAsymptotics.MarkedC4ActualPrefixOrders

/-! Actual efficient row incidence with the ENTIRE literal tableau retained.
Every row coordinate is restricted to its actual prefix image. In contrast
to the coarse physical row count, this preserves the off-diagonal entropy
gain needed by the Case-I splice and retains the same diagonal tuple. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualTableauRowIncidence
open ActualSubdirectFiltration ActualEfficientLiftRecovery
open ActualEfficientRowIncidence ActualPrefixOrders

variable {t : ℕ} (F : Fin t → Type) [∀ i,Group (F i)] [∀ i,Finite (F i)]
  (D : ∀ i,Subgroup (F i)) (T : ∀ i j : Fin t,Subgroup (F j))

/-- All actual nilpotent subdirect subgroups with this ENTIRE actual
prefix-image tableau. There is no enumeration or encoding premise. -/
abbrev TableauFamily := {H : Family F D // ∀ i j : Fin t,
  («prefix» F H.val (i.val+1)).map (coordinate F H.val j)=T i j}
local instance : Fintype (TableauFamily F D T) := Fintype.ofFinite _

abbrev Arrays := ∀ i : Fin t,Fin (normalGen (D i)) → ∀ j : Fin t,T i j

def code (z : Σ H : TableauFamily F D T,
    LiftArray F H.val.val H.val.property.1) : Arrays F D T :=
  fun i k j =>
    ⟨(z.2 i ((labels F D z.1.val i).symm k)).val.val j,by
      rw [← z.1.property i j]
      exact ⟨(z.2 i ((labels F D z.1.val i).symm k)).val,
        (z.2 i ((labels F D z.1.val i).symm k)).property.1,rfl⟩⟩

/-- The tableau restrictions preserve every recovering array choice. -/
theorem code_injective : Function.Injective (code F D T) := by
  rintro ⟨H,a⟩ ⟨K,b⟩ he
  have hrow : ActualEfficientRowIncidence.code F D ⟨H.val,a⟩=
      ActualEfficientRowIncidence.code F D ⟨K.val,b⟩ := by
    funext i k
    apply Subtype.ext
    funext j
    exact congrArg Subtype.val (congrFun (congrFun (congrFun he i) k) j)
  have hz := ActualEfficientRowIncidence.code_injective F D hrow
  have hHK : H=K := Subtype.ext (congrArg Sigma.fst hz)
  cases hHK
  have hab : a=b := eq_of_heq (Sigma.mk.inj_iff.mp hz).2
  cases hab
  rfl

/-- The sharp finite incidence numerator uses actual tableau entries,
not whole physical factors and not independently maximal abstract types. -/
theorem weighted_card_le :
    (∑ H : TableauFamily F D T,multiplicity F D H.val) ≤
      ∏ i : Fin t,(∏ j : Fin t,Nat.card (T i j))^normalGen (D i) := by
  have h := Nat.card_le_card_of_injective (code F D T) (code_injective F D T)
  rw [Nat.card_sigma] at h
  have hs : (∑ H : TableauFamily F D T,
      Nat.card (LiftArray F H.val.val H.val.property.1))=
        ∑ H : TableauFamily F D T,multiplicity F D H.val := by
    apply Finset.sum_congr rfl
    intro H _
    rw [ActualEfficientLiftMultiplicity.card_liftArray]
    apply Finset.prod_congr rfl
    intro i _
    rw [H.val.property.2.2 i]
  have ht : Nat.card (Arrays F D T)=
      ∏ i : Fin t,(∏ j : Fin t,Nat.card (T i j))^normalGen (D i) := by
    rw [Nat.card_pi]
    apply Finset.prod_congr rfl
    intro i _
    rw [Nat.card_fun,Nat.card_fin,Nat.card_pi]
  rw [hs,ht] at h
  exact h

/-- The same exact actual-diagonal multiplicity divides this sharper
tableau numerator. All tableau dependence stays correlated in this row. -/
theorem card_mul_multiplicity_le (H : TableauFamily F D T) :
    Nat.card (TableauFamily F D T)*multiplicity F D H.val ≤
      ∏ i : Fin t,(∏ j : Fin t,Nat.card (T i j))^normalGen (D i) := by
  have h := weighted_card_le F D T
  have hs : (∑ K : TableauFamily F D T,multiplicity F D K.val)=
      Nat.card (TableauFamily F D T)*multiplicity F D H.val := by
    calc
      _ = ∑ _K : TableauFamily F D T,multiplicity F D H.val :=
        Finset.sum_congr rfl (fun K _ => multiplicity_eq F D K.val H.val)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,
        nsmul_eq_mul,Nat.card_eq_fintype_card,Nat.cast_id]
  rw [hs] at h
  exact h

end SymmetricSubgroupAsymptotics.MarkedC4.ActualTableauRowIncidence
