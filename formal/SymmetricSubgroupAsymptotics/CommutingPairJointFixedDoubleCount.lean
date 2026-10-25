import SymmetricSubgroupAsymptotics.AbelianActionClassBound
import Mathlib.GroupTheory.GroupAction.Quotient

/-! Joint fixed commuting pairs are counted through the ACTUAL point
stabilizers. A transitive orbit contributes exactly |G| times the class
count of one stabilizer. No character theory or orbit representatives
are assumed; the statement applies to arbitrary finite group actions. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.CommutingPairJointFixedDoubleCount
open AbelianActionClassBound MulAction
variable {G X : Type*} [Group G] [MulAction G X]

abbrev JointFixed :=
  (p : CommutingPairs G) × {x : X // p.val.1 • x = x ∧ p.val.2 • x = x}

def jointFixedEquiv : JointFixed (G := G) (X := X) ≃
    ((x : X) × CommutingPairs (stabilizer G x)) where
  toFun z := ⟨z.2.val,⟨(⟨z.1.val.1,z.2.property.1⟩,
    ⟨z.1.val.2,z.2.property.2⟩),Subtype.ext z.1.property⟩⟩
  invFun z := ⟨⟨(z.2.val.1.val,z.2.val.2.val),
    congrArg Subtype.val z.2.property⟩,
    ⟨z.1,z.2.val.1.property,z.2.val.2.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable [Finite G] [Finite X]
local instance : Fintype X := Fintype.ofFinite _
local instance : Fintype (CommutingPairs G) := Fintype.ofFinite _

theorem joint_fixed_card :
    Nat.card (JointFixed (G := G) (X := X)) =
      ∑ x : X, Nat.card (stabilizer G x) * Nat.card (ConjClasses (stabilizer G x)) := by
  letI : Fintype X := Fintype.ofFinite _
  rw [Nat.card_congr (jointFixedEquiv (G := G) (X := X)),Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro x _hx
  simp only [CommutingPairs,card_comm_eq_card_conjClasses_mul_card,Nat.mul_comm]

theorem sum_joint_fixed_card :
    (∑ p : CommutingPairs G,
      Nat.card {x : X // p.val.1 • x = x ∧ p.val.2 • x = x}) =
      ∑ x : X, Nat.card (stabilizer G x) * Nat.card (ConjClasses (stabilizer G x)) := by
  letI : Fintype (CommutingPairs G) := Fintype.ofFinite _
  exact Nat.card_sigma.symm.trans joint_fixed_card

theorem joint_fixed_card_eq_of_pretransitive [IsPretransitive G X] (x₀ : X) :
    Nat.card (JointFixed (G := G) (X := X)) =
      Nat.card G * Nat.card (ConjClasses (stabilizer G x₀)) := by
  letI : Fintype X := Fintype.ofFinite _
  have hsize : Nat.card X * Nat.card (stabilizer G x₀) = Nat.card G := by
    simpa only [Nat.card_prod,orbit_eq_univ,Nat.card_univ] using
      Nat.card_congr (orbitProdStabilizerEquivGroup G x₀)
  rw [joint_fixed_card]
  calc
    _ = ∑ _x : X,
        Nat.card (stabilizer G x₀) * Nat.card (ConjClasses (stabilizer G x₀)) := by
      apply Finset.sum_congr rfl
      intro x _hx
      obtain ⟨g,hg⟩ := exists_smul_eq G x₀ x
      let e := stabilizerEquivStabilizer hg.symm
      have hc : Nat.card (ConjClasses (stabilizer G x)) =
          Nat.card (ConjClasses (stabilizer G x₀)) := Nat.le_antisymm
        (Nat.card_le_card_of_surjective (ConjClasses.map e.toMonoidHom)
          (ConjClasses.map_surjective e.surjective))
        (Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
          (ConjClasses.map_surjective e.symm.surjective))
      rw [Nat.card_congr e.symm.toEquiv,hc]
    _ = Nat.card X * (Nat.card (stabilizer G x₀) *
        Nat.card (ConjClasses (stabilizer G x₀))) := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
        Nat.card_eq_fintype_card,Nat.cast_id]
    _ = _ := by rw [← mul_assoc,hsize]

end SymmetricSubgroupAsymptotics.CommutingPairJointFixedDoubleCount
