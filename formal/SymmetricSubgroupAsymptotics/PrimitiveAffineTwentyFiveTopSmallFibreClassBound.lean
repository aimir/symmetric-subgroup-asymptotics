import SymmetricSubgroupAsymptotics.PrimitiveTopSmallFibreClassBudget
import SymmetricSubgroupAsymptotics.AffinePrimePowerOrderBound
import SymmetricSubgroupAsymptotics.OriginalMinimalBlockComponentTransport

/-! Degree25 affine tops need no finite action catalogue or new class
estimate: their actual prime-log order bound is already small enough
when the binary unsigned motion reserve is retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineTwentyFiveTopSmallFibreClassBound
open OriginalBlockClassBound

theorem order_le_fifteenThousandSixTwentyFive
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] (P : PrimitiveAffineProfile G X)
    (hdegree : Nat.card X = 25) : Nat.card G ≤ 15625 := by
  letI : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let x : X := Classical.arbitrary X
  letI : Fact P.p.Prime := ⟨P.p_prime⟩
  letI : Nontrivial P.V := (P.pointEquiv x).symm.injective.nontrivial
  obtain ⟨n, hnpos, hn⟩ := P.V_pgroup.nontrivial_iff_card.mp inferInstance
  have hpdiv : P.p ∣ (5 : ℕ) ^ 2 := by
    rw [show (5 : ℕ) ^ 2 = Nat.card P.V by rw [P.card_eq x, hdegree]; decide]
    rw [hn]
    exact dvd_pow_self P.p hnpos.ne'
  have hp : P.p = 5 := by
    rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp
      (P.p_prime.dvd_of_dvd_pow hpdiv) with h | h
    · exact (P.p_prime.ne_one h).elim
    · exact h
  have ho := AffinePrimePowerOrderBound.card_le_degree_mul_prime_log_power P x
  rw [hdegree, hp, show Nat.log 5 25 = 2 by decide +kernel] at ho
  exact ho

theorem subnormal_class_cube_le_at_original_degree
    {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω) = g • π ω)
    (c : ℕ) (hc : c = 2 ∨ c = 3)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x) = c)
    (P : PrimitiveAffineProfile (Top (A := A) (X := X)) X)
    (hprimitive : MulAction.IsPreprimitive (Top (A := A) (X := X)) X)
    (hdegree : Nat.card X = 25)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H) ^ 3 ≤ 5 ^ (Nat.card Ω - 1) := by
  have ho := order_le_fifteenThousandSixTwentyFive P hdegree
  apply PrimitiveTopSmallFibreClassBudget.subnormal_class_cube_le_at_original_degree
    π hπ c hc hsize (by omega) hprimitive
    (ho.trans_lt (by rw [hdegree]; decide +kernel)) 15625 (by decide)
    ?_ ?_ ?_ H hH
  · intro L _
    exact (Nat.card_le_card_of_surjective ConjClasses.mk ConjClasses.mk_surjective).trans
      ((Nat.card_le_card_of_injective L.subtype Subtype.val_injective).trans ho)
  · rw [hdegree]
    decide +kernel
  · rw [hdegree]
    decide +kernel

end SymmetricSubgroupAsymptotics.PrimitiveAffineTwentyFiveTopSmallFibreClassBound

namespace SymmetricSubgroupAsymptotics.OriginalMinimalBlock
variable {A Ω : Type} [Group A] [MulAction A Ω] [MulAction.IsPretransitive A Ω]
    [Finite A] [Finite Ω] [FaithfulSMul A Ω]
    {ω₀ : Ω} (D : OriginalMinimalBlock (A := A) ω₀)

theorem subnormal_class_cube_le_of_primitive_twentyFive_affine_top
    (hc : Nat.card D.Fibre = 2 ∨ Nat.card D.Fibre = 3)
    (P : PrimitiveAffineProfile D.Top D.Points)
    (hprimitive : MulAction.IsPreprimitive D.Top D.Points)
    (hdegree : Nat.card D.Points = 25)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H) ^ 3 ≤ 5 ^ (Nat.card Ω - 1) :=
  PrimitiveAffineTwentyFiveTopSmallFibreClassBound.subnormal_class_cube_le_at_original_degree
    D.map D.map_equivariant (Nat.card D.Fibre) hc D.fibre_card_at P hprimitive hdegree H hH

end SymmetricSubgroupAsymptotics.OriginalMinimalBlock
