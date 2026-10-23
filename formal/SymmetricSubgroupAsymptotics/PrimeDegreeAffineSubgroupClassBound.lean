import SymmetricSubgroupAsymptotics.PrimitiveAffineProfileStructure
import SymmetricSubgroupAsymptotics.QuadraticOrderClassNumerics
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.GroupAction.CardCommute

/-! Prime-degree actual affine profiles have order at most n(n-1):
the literal regular subgroup is cyclic and its actual complement embeds
in its automorphism group. Every subgroup therefore meets the GM cube
for prime ambient degree at least eleven, without a finite catalogue. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimeDegreeAffineSubgroupClassBound

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] (P : PrimitiveAffineProfile G X)

include P in
theorem card_le_degree_mul_pred (x : X) (hp : Nat.Prime (Nat.card X)) :
    Nat.card G ≤ Nat.card X*(Nat.card X-1) := by
  letI : Fact (Nat.Prime (Nat.card X)) := ⟨hp⟩
  letI : IsCyclic P.V := isCyclic_of_prime_card (P.card_eq x)
  have hAut : Nat.card (P.V ≃* P.V) = Nat.card X-1 := by
    rw [IsCyclic.card_mulAut, P.card_eq x, Nat.totient_prime hp]
  have hcomp : Nat.card (P.complement x) ≤ Nat.card X-1 :=
    (P.complement_card_le_mulEquiv x).trans_eq hAut
  calc
    Nat.card G = Nat.card P.V*Nat.card (P.complement x) :=
      (PrimitiveAffineProfile.isComplement'_complement P x).card_mul.symm
    _ ≤ Nat.card P.V*(Nat.card X-1) := Nat.mul_le_mul_left _ hcomp
    _ = Nat.card X*(Nat.card X-1) := by rw [P.card_eq x]

include P in
theorem subgroup_class_cube_le_garonziMaroti (x : X)
    (hp : Nat.Prime (Nat.card X)) (hn : 11 ≤ Nat.card X) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  have hc : Nat.card (ConjClasses H) ≤ Nat.card H :=
    Nat.card_le_card_of_surjective ConjClasses.mk ConjClasses.mk_surjective
  have hsub : Nat.card H ≤ Nat.card G :=
    Nat.card_le_card_of_injective H.subtype Subtype.val_injective
  have hquadratic : Nat.card (ConjClasses H) ≤ (Nat.card X)^2 := by
    calc
      Nat.card (ConjClasses H) ≤ Nat.card X*(Nat.card X-1) :=
        (hc.trans hsub).trans (card_le_degree_mul_pred P x hp)
      _ ≤ Nat.card X*Nat.card X := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = (Nat.card X)^2 := by ring
  have h := (Nat.pow_le_pow_left hquadratic 3).trans
    (show ((Nat.card X)^2)^3 ≤ 5^(Nat.card X-1) by
      rw [← pow_mul]
      exact QuadraticOrderClassNumerics.sixth_power_le_garonziMaroti _ (by omega))
  exact h

include P in
theorem class_cube_le_garonziMaroti (x : X)
    (hp : Nat.Prime (Nat.card X)) (hn : 11 ≤ Nat.card X) :
    Nat.card (ConjClasses G)^3 ≤ 5^(Nat.card X-1) := by
  have hc : Nat.card (ConjClasses G) ≤ Nat.card G :=
    Nat.card_le_card_of_surjective ConjClasses.mk ConjClasses.mk_surjective
  have hquadratic : Nat.card (ConjClasses G) ≤ (Nat.card X)^2 := by
    calc
      Nat.card (ConjClasses G) ≤ Nat.card X*(Nat.card X-1) :=
        hc.trans (card_le_degree_mul_pred P x hp)
      _ ≤ Nat.card X*Nat.card X := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = (Nat.card X)^2 := by ring
  have h := Nat.pow_le_pow_left hquadratic 3
  rw [← pow_mul] at h
  exact h.trans (QuadraticOrderClassNumerics.sixth_power_le_garonziMaroti _ (by omega))

end SymmetricSubgroupAsymptotics.PrimeDegreeAffineSubgroupClassBound
