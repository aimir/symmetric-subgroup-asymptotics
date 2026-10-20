import SymmetricSubgroupAsymptotics.MarkedC4ActualEfficientLiftRecovery

/-! Exact multiplicity of the actual efficient-lift incidence fibres.
Each lift of a fixed diagonal generator is a coset of the actual previous
prefix kernel. The product below retains the SAME diagonals and generator
numbers used for recovery of the literal subgroup. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualEfficientLiftMultiplicity
open ActualSubdirectFiltration ActualEfficientLiftRecovery

variable {t : ℕ} (F : Fin t → Type) [∀ i,Group (F i)] [∀ i,Finite (F i)]
  (H : Subgroup (∀ i,F i))
  (hsurj : ∀ i,Function.Surjective (coordinate F H i))

abbrev CoordinateLift (i : Fin t)
    (q : {q : F i // q∈normalGenerators F H hsurj i}) :=
  {h : H // h∈«prefix» F H (i.val+1) ∧ coordinate F H i h=q.val}

/-- Multiplication by an actual fixed lift identifies the whole fibre
with the actual previous prefix. No quotient-coordinate order is substituted. -/
def coordinateLiftEquiv (i : Fin t)
    (q : {q : F i // q∈normalGenerators F H hsurj i})
    (a : CoordinateLift F H hsurj i q) :
    «prefix» F H i.val ≃ CoordinateLift F H hsurj i q where
  toFun k := ⟨k.val*a.val,
    («prefix» F H (i.val+1)).mul_mem (prefix_mono F H i.val k.property) a.property.1,
    by
      have hk : coordinate F H i k.val=1 :=
        (mem_prefix F H i.val k.val).mp k.property i le_rfl
      rw [map_mul,hk,one_mul,a.property.2]⟩
  invFun x := ⟨x.val*a.val⁻¹,by
    apply prefix_kernel F H i
    · exact («prefix» F H (i.val+1)).mul_mem x.property.1
        ((«prefix» F H (i.val+1)).inv_mem a.property.1)
    · rw [map_mul,map_inv,x.property.2,a.property.2,mul_inv_cancel]⟩
  left_inv k := by
    apply Subtype.ext
    exact mul_inv_cancel_right k.val a.val
  right_inv x := by
    apply Subtype.ext
    exact inv_mul_cancel_right x.val a.val

theorem card_coordinateLift (i : Fin t)
    (q : {q : F i // q∈normalGenerators F H hsurj i}) :
    Nat.card (CoordinateLift F H hsurj i q)=Nat.card («prefix» F H i.val) := by
  let a := Classical.choice (liftArray_nonempty F H hsurj)
  exact (Nat.card_congr (coordinateLiftEquiv F H hsurj i q (a i q))).symm

/-- The exact number of recovering arrays is the product of previous-prefix
orders raised to the actual diagonal normal-generator numbers. -/
theorem card_liftArray :
    Nat.card (LiftArray F H hsurj)=
      ∏ i : Fin t,Nat.card («prefix» F H i.val)^normalGen (diagonal F H i) := by
  rw [Nat.card_pi]
  apply Finset.prod_congr rfl
  intro i _
  rw [Nat.card_pi]
  simp only [card_coordinateLift F H hsurj,Finset.prod_const,Finset.card_univ]
  congr 1
  rw [Fintype.card_coe]
  exact (normalGenerators_spec F H hsurj i).1

/-- Forgetting prefix membership and lift equations loses no array choices. -/
theorem ambientArray_injective :
    Function.Injective (ambientArray F H hsurj) := by
  intro a b hab
  funext i q
  apply Subtype.ext
  apply Subtype.ext
  exact congrFun hab ⟨i,q⟩

/-- The exact multiplicity is still present among literal ambient arrays;
it is not an artefact of proof fields in the lift subtypes. -/
theorem card_ambientArray_range :
    Nat.card (Set.range (ambientArray F H hsurj))=
      ∏ i : Fin t,Nat.card («prefix» F H i.val)^normalGen (diagonal F H i) := by
  rw [← Nat.card_congr (Equiv.ofInjective (ambientArray F H hsurj)
    (ambientArray_injective F H hsurj))]
  exact card_liftArray F H hsurj

end SymmetricSubgroupAsymptotics.MarkedC4.ActualEfficientLiftMultiplicity
