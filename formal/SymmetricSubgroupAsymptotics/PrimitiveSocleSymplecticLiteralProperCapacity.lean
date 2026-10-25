import SymmetricSubgroupAsymptotics.PrimitiveSocleSymplecticLiteralCapacity
import SymmetricSubgroupAsymptotics.PrimitiveSocleModelProperClassCapacity

/-! Proper-subnormal extra capacity for the actual elementary
symplectic quotient. Simplicity and finiteness are transported through
the displayed same-source equivalence, including for later type-B use.
The scalar inequality is the already-proved packet's sufficient test. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open CFSGSymplecticSerreMatrices CFSGSymplecticLiteralCapacity
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.proper_subnormal_class_cube_le_of_symplectic_literal_budget
    (D : NonaffineData G X) (r : ℕ) (hr : 3 ≤ r) (q : CFSG.PrimePower)
    (e : D.Simple ≃* elementaryProjective q.Field r) (b : ℕ) (hb : 32 ≤ b)
    (hindex : ∀ K : Subgroup (elementaryProjective q.Field r), K ≠ ⊤ → b ≤ K.index)
    (hcube : q.order^(3*(2*r^2+r+3)) ≤ 5^(b-1))
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  letI : IsSimpleGroup (elementaryProjective q.Field r) := e.symm.isSimpleGroup
  letI : Finite (elementaryProjective q.Field r) := Finite.of_equiv D.Simple e.toEquiv
  refine D.proper_subnormal_class_cube_le_of_model_order_capacity
    (elementaryProjective q.Field r) e b (by omega) hindex ?_
    (order_ge_1024_of_proper_index r hr q b hb hindex) H hH hne
  have hp := Nat.pow_le_pow_left (component_le_field_power r (by omega) q) 3
  rw [← pow_mul, Nat.mul_comm (2*r^2+r+3) 3] at hp
  exact hp.trans hcube

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
