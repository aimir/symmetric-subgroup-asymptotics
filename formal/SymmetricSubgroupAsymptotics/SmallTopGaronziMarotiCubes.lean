import SymmetricSubgroupAsymptotics.TransitiveSmallTopClassFusion
import SymmetricSubgroupAsymptotics.GaronziMarotiLargeBlockReduction

/-! Exact GM cubes for binary/ternary fibres over two or three blocks.
The degree is the cardinality of the ORIGINAL point set, proved from
its literal equal fibres. Every group-theoretic bound is discharged;
the remaining comparisons are closed integer arithmetic. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SmallTopGaronziMarotiCubes
open TransitiveSmallTopClassFusion GaronziMarotiLargeBlockReduction
variable {A Ω : Type} [Group A] [MulAction A Ω] [Finite A] [Finite Ω] [FaithfulSMul A Ω]

section Two
variable [MulAction A (Fin 2)] [MulAction.IsPretransitive A (Fin 2)]
    (b:Ω→Fin 2) (hb:∀(a:A)(ω:Ω),b (a•ω)=a•b ω)

include hb in
theorem binary_two_blocks_cube (hsize:∀x,Nat.card (originalBlockFibre b x)=2) :
    Nat.card (ConjClasses A)^3≤5^(Nat.card Ω-1) := by
  have hd := card_eq_blocks_mul_fibre b 2 hsize
  rw [Nat.card_fin] at hd
  calc
    Nat.card (ConjClasses A)^3≤5^3 :=
      Nat.pow_le_pow_left (binary_two_blocks b hb (fun x=>(hsize x).le)) 3
    _≤5^(Nat.card Ω-1) := by rw [hd]

include hb in
theorem ternary_two_blocks_cube (hsize:∀x,Nat.card (originalBlockFibre b x)=3) :
    Nat.card (ConjClasses A)^3≤5^(Nat.card Ω-1) := by
  have hd := card_eq_blocks_mul_fibre b 3 hsize
  rw [Nat.card_fin] at hd
  calc
    Nat.card (ConjClasses A)^3≤13^3 :=
      Nat.pow_le_pow_left (ternary_two_blocks b hb (fun x=>(hsize x).le)) 3
    _≤5^(Nat.card Ω-1) := by rw [hd]; decide
end Two

section Three
variable [MulAction A (Fin 3)] [MulAction.IsPretransitive A (Fin 3)]
    (b:Ω→Fin 3) (hb:∀(a:A)(ω:Ω),b (a•ω)=a•b ω)

include hb in
theorem binary_three_blocks_cube (hsize:∀x,Nat.card (originalBlockFibre b x)=2) :
    Nat.card (ConjClasses A)^3≤5^(Nat.card Ω-1) := by
  have hd := card_eq_blocks_mul_fibre b 2 hsize
  rw [Nat.card_fin] at hd
  calc
    Nat.card (ConjClasses A)^3≤10^3 :=
      Nat.pow_le_pow_left (binary_three_blocks b hb (fun x=>(hsize x).le)) 3
    _≤5^(Nat.card Ω-1) := by rw [hd]; decide

include hb in
theorem ternary_three_blocks_cube (hsize:∀x,Nat.card (originalBlockFibre b x)=3) :
    Nat.card (ConjClasses A)^3≤5^(Nat.card Ω-1) := by
  have hd := card_eq_blocks_mul_fibre b 3 hsize
  rw [Nat.card_fin] at hd
  calc
    Nat.card (ConjClasses A)^3≤66^3 :=
      Nat.pow_le_pow_left (ternary_three_blocks b hb (fun x=>(hsize x).le)) 3
    _≤5^(Nat.card Ω-1) := by rw [hd]; decide
end Three

end SymmetricSubgroupAsymptotics.SmallTopGaronziMarotiCubes
