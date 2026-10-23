import SymmetricSubgroupAsymptotics.ConjugacyClassSubgroupIndexBound
import Mathlib.Tactic.Ring

/-! Gallagher's subgroup geometric-mean estimate, proved from the
actual subgroup index bound and the quotient map onto conjugacy classes.
No monotonicity of class count under inclusion is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ConjugacyClassSubgroupSquareBound

theorem class_square_le_order_mul_class {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) :
    Nat.card (ConjClasses H)^2 ≤ Nat.card G * Nat.card (ConjClasses G) := by
  have horder : Nat.card (ConjClasses H) ≤ Nat.card H :=
    Nat.card_le_card_of_surjective ConjClasses.mk ConjClasses.mk_surjective
  have hindex := ConjugacyClassSubgroupIndexBound.class_card_le_index_mul H
  calc
    Nat.card (ConjClasses H)^2 =
        Nat.card (ConjClasses H)*Nat.card (ConjClasses H) := by ring
    _ ≤ Nat.card H*(H.index*Nat.card (ConjClasses G)) := Nat.mul_le_mul horder hindex
    _ = Nat.card G*Nat.card (ConjClasses G) := by
      rw [← Nat.mul_assoc, H.card_mul_index]

theorem class_square_le_injective_order_mul_class {A G : Type*}
    [Group A] [Group G] [Finite A] [Finite G]
    (f : A →* G) (hf : Function.Injective f) :
    Nat.card (ConjClasses A)^2 ≤ Nat.card G*Nat.card (ConjClasses G) := by
  let e := MonoidHom.ofInjective hf
  have he : Nat.card (ConjClasses A) ≤ Nat.card (ConjClasses f.range) :=
    Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
      (ConjClasses.map_surjective e.symm.surjective)
  exact (Nat.pow_le_pow_left he 2).trans (class_square_le_order_mul_class f.range)

end SymmetricSubgroupAsymptotics.ConjugacyClassSubgroupSquareBound
