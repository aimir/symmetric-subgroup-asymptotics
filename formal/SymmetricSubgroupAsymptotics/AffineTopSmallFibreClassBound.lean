import SymmetricSubgroupAsymptotics.AffineTopSmallFibreOrderNumerics
import SymmetricSubgroupAsymptotics.PrimitiveAffineProfileStructure
import SymmetricSubgroupAsymptotics.SubnormalSmallFibreTopClassBound
import SymmetricSubgroupAsymptotics.GaronziMarotiLargeBlockReduction

/-! An actual affine top pays the ordinary binary/ternary block bound
from128 blocks. Its order is derived from the same regular subgroup and
complement profile. The original source H and its projected top image
are retained; no transitivity of H, splitting, or class monotonicity is
assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.AffineTopSmallFibreClassBound
open OriginalBlockClassBound

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]

theorem subnormal_class_cube_le_of_affine_top
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω),π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x,Nat.card (originalBlockFibre π x)=c)
    (hn : 128≤Nat.card X)
    (P : PrimitiveAffineProfile (Top (A:=A) (X:=X)) X)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3≤5^(Nat.card Ω-1) := by
  letI : Nonempty X := Finite.card_pos_iff.mp (by omega)
  let x₀ : X := Classical.arbitrary X
  have horder : Nat.card (Top (A:=A) (X:=X))≤
      Nat.card X^(Nat.log 2 (Nat.card X)+1) := by
    calc
      _≤Nat.card X*Nat.card X^Nat.log 2 (Nat.card X) := P.card_le_domain_pow_log x₀
      _=_ := by rw [pow_succ,Nat.mul_comm]
  have htop : ∀ L : Subgroup (Top (A:=A) (X:=X)),L.IsSubnormal →
      Nat.card (ConjClasses L)≤Nat.card (Top (A:=A) (X:=X)) := by
    intro L _
    exact (Nat.card_le_card_of_surjective ConjClasses.mk ConjClasses.mk_surjective).trans
      (Nat.card_le_card_of_injective L.subtype Subtype.val_injective)
  rcases hc with rfl|rfl
  · have hlocal : ∀ x (L : Subgroup (Equiv.Perm (originalBlockFibre π x))),
        Nat.card (ConjClasses L)≤2 :=
      fun x L => SmallPermutationClassBudgets.subgroup_class_card_le_two (hsize x).le L
    have hbound := SubnormalSmallFibreTopClassBound.subnormal_class_card_le_power_mul_top_budget
      π hπ 2 hlocal (Nat.card (Top (A:=A) (X:=X))) htop H hH
    have hnum := AffineTopSmallFibreOrderNumerics.binary_product_cube_le
      (Nat.card X) (Nat.card (Top (A:=A) (X:=X))) hn horder
    have hh := (Nat.pow_le_pow_left hbound 3).trans hnum
    have hcard := GaronziMarotiLargeBlockReduction.card_eq_blocks_mul_fibre π 2 hsize
    simpa only [hcard,Nat.mul_comm (Nat.card X) 2] using hh
  · have hlocal : ∀ x (L : Subgroup (Equiv.Perm (originalBlockFibre π x))),
        Nat.card (ConjClasses L)≤3 :=
      fun x L => SmallPermutationClassBudgets.subgroup_class_card_le_three (hsize x).le L
    have hbound := SubnormalSmallFibreTopClassBound.subnormal_class_card_le_power_mul_top_budget
      π hπ 3 hlocal (Nat.card (Top (A:=A) (X:=X))) htop H hH
    have hnum := AffineTopSmallFibreOrderNumerics.ternary_product_cube_le
      (Nat.card X) (Nat.card (Top (A:=A) (X:=X))) hn horder
    have hh := (Nat.pow_le_pow_left hbound 3).trans hnum
    have hcard := GaronziMarotiLargeBlockReduction.card_eq_blocks_mul_fibre π 3 hsize
    simpa only [hcard,Nat.mul_comm (Nat.card X) 3] using hh

end SymmetricSubgroupAsymptotics.AffineTopSmallFibreClassBound
