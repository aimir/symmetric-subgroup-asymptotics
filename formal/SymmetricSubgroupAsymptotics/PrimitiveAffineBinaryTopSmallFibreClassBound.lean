import SymmetricSubgroupAsymptotics.BinaryParabolicTopSmallFibreNumerics
import SymmetricSubgroupAsymptotics.BinaryBlockUnsignedGeneralClassReserve
import SymmetricSubgroupAsymptotics.QuasiprimitiveSwapRecognition
import SymmetricSubgroupAsymptotics.GaronziMarotiLargeBlockReduction
import SymmetricSubgroupAsymptotics.OriginalMinimalBlockComponentTransport

/-! Original binary/ternary fibres with actual primitive affine tops on
8/16/32 points. The binary case uses the actual unsigned motion reserve;
the ternary case uses the actual projected class budget. Primitivity is
explicitly supplied for the original top, never inferred from the bare
regular p-subgroup profile. The original subnormal H is retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineBinaryTopSmallFibreClassBound
open OriginalBlockClassBound PrimitiveAffineBinaryParabolicClassBound

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]

theorem subnormal_class_cube_le_at_original_degree
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x)=c)
    (P : PrimitiveAffineProfile (Top (A:=A) (X:=X)) X)
    (hprimitive : MulAction.IsPreprimitive (Top (A:=A) (X:=X)) X)
    (hdegree : Nat.card X=8 ∨ Nat.card X=16 ∨ Nat.card X=32)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-1) := by
  have hn : 8 ≤ Nat.card X := by rcases hdegree with h|h|h <;> omega
  letI : Nonempty X := Finite.card_pos_iff.mp (by omega)
  let x₀ : X := Classical.arbitrary X
  have htop : ∀ L : Subgroup (Top (A:=A) (X:=X)), L.IsSubnormal →
      Nat.card (ConjClasses L) ≤ classBudget (Nat.card X) :=
    fun L _ => PrimitiveAffineBinaryParabolicClassBound.subgroup_class_card_le
      P hprimitive x₀ hdegree L
  rcases hc with rfl|rfl
  · letI : Fintype X := Fintype.ofFinite X
    letI : DecidableEq X := Classical.decEq X
    letI : MulAction.IsPreprimitive (Top (A:=A) (X:=X)) X := hprimitive
    have horder : Nat.card (Top (A:=A) (X:=X)) < (Nat.card X).factorial :=
      (P.card_le_domain_pow_log x₀).trans_lt
        (BinaryParabolicTopSmallFibreNumerics.affine_order_lt_factorial _ hdegree)
    have hns : ∀ a:A, ¬(topMap (A:=A) (X:=X) a).IsSwap := by
      intro a ha
      have ht : Top (A:=A) (X:=X)=⊤ :=
        QuasiprimitiveSwapRecognition.eq_top_of_isSwap_mem
          (Top (A:=A) (X:=X)) (topMap (A:=A) (X:=X) a) ha ⟨a,rfl⟩
      have hs : Nat.card (Top (A:=A) (X:=X))=(Nat.card X).factorial := by
        rw [ht,Nat.card_congr Subgroup.topEquiv.toEquiv,Nat.card_perm]
      rw [hs] at horder
      exact (lt_irrefl _ horder)
    have hb := BinaryBlockUnsignedGeneralClassReserve.subnormal_class_card_le_class_budget_add_one_mul
      π hπ (fun x => (hsize x).le) (by omega) (classBudget (Nat.card X))
      (BinaryParabolicTopSmallFibreNumerics.classBudget_ge_eleven _) htop hns H hH
    have hh := (Nat.pow_le_pow_left hb 3).trans
      (BinaryParabolicTopSmallFibreNumerics.binary_unsigned_capacity _ hdegree)
    have hcard := GaronziMarotiLargeBlockReduction.card_eq_blocks_mul_fibre π 2 hsize
    simpa only [hcard,Nat.mul_comm (Nat.card X) 2] using hh
  · have hlocal : ∀ x (L : Subgroup (Equiv.Perm (originalBlockFibre π x))),
        Nat.card (ConjClasses L) ≤ 3 :=
      fun x L => SmallPermutationClassBudgets.subgroup_class_card_le_three (hsize x).le L
    have hb := SubnormalSmallFibreTopClassBound.subnormal_class_card_le_power_mul_top_budget
      π hπ 3 hlocal (classBudget (Nat.card X)) htop H hH
    have hh := (Nat.pow_le_pow_left hb 3).trans
      (BinaryParabolicTopSmallFibreNumerics.ternary_capacity _ hdegree)
    have hcard := GaronziMarotiLargeBlockReduction.card_eq_blocks_mul_fibre π 3 hsize
    simpa only [hcard,Nat.mul_comm (Nat.card X) 3] using hh

end SymmetricSubgroupAsymptotics.PrimitiveAffineBinaryTopSmallFibreClassBound

namespace SymmetricSubgroupAsymptotics.OriginalMinimalBlock

variable {A Ω : Type} [Group A] [MulAction A Ω] [MulAction.IsPretransitive A Ω]
    [Finite A] [Finite Ω] [FaithfulSMul A Ω]
    {ω₀ : Ω} (D : OriginalMinimalBlock (A:=A) ω₀)

theorem subnormal_class_cube_le_of_primitive_binary_affine_top
    (hc : Nat.card D.Fibre=2 ∨ Nat.card D.Fibre=3)
    (P : PrimitiveAffineProfile D.Top D.Points)
    (hprimitive : MulAction.IsPreprimitive D.Top D.Points)
    (hdegree : Nat.card D.Points=8 ∨ Nat.card D.Points=16 ∨ Nat.card D.Points=32)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-1) :=
  PrimitiveAffineBinaryTopSmallFibreClassBound.subnormal_class_cube_le_at_original_degree
    D.map D.map_equivariant (Nat.card D.Fibre) hc D.fibre_card_at P hprimitive hdegree H hH

theorem class_cube_le_of_primitive_binary_affine_top
    (hc : Nat.card D.Fibre=2 ∨ Nat.card D.Fibre=3)
    (P : PrimitiveAffineProfile D.Top D.Points)
    (hprimitive : MulAction.IsPreprimitive D.Top D.Points)
    (hdegree : Nat.card D.Points=8 ∨ Nat.card D.Points=16 ∨ Nat.card D.Points=32) :
    Nat.card (ConjClasses A)^3 ≤ 5^(Nat.card Ω-1) := by
  have h := D.subnormal_class_cube_le_of_primitive_binary_affine_top hc P hprimitive hdegree ⊤
    (Subgroup.Normal.isSubnormal inferInstance)
  have hc : Nat.card (ConjClasses A) ≤ Nat.card (ConjClasses (⊤ : Subgroup A)) :=
    Nat.card_le_card_of_surjective
      (ConjClasses.map (Subgroup.topEquiv : (⊤ : Subgroup A) ≃* A).toMonoidHom)
      (ConjClasses.map_surjective Subgroup.topEquiv.surjective)
  exact (Nat.pow_le_pow_left hc 3).trans h

end SymmetricSubgroupAsymptotics.OriginalMinimalBlock
