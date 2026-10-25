import SymmetricSubgroupAsymptotics.SubnormalCoordinateClassPowerBound
import SymmetricSubgroupAsymptotics.SubnormalPermutationBlockClassReduction
import SymmetricSubgroupAsymptotics.GaronziMarotiLargeBlockReduction

/-! Integer-cube form of the genuine large-block induction step. The
hypothesis is the strict-smaller GENERAL permutation-degree induction
hypothesis. The original correlated kernel and literal top are retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.GaronziMarotiLargeBlockCubeReduction
open OriginalBlockClassBound SubnormalPermutationBlockClassReduction
open SubnormalCoordinateClassPowerBound

theorem cube_le_of_finite_permutation_bound (Y : Type) [Finite Y] (B : ℕ)
    (hbound : ∀ L : Subgroup (Equiv.Perm (Fin (Nat.card Y))),
      Nat.card (ConjClasses L) ^ 3 ≤ B) (L : Subgroup (Equiv.Perm Y)) :
    Nat.card (ConjClasses L) ^ 3 ≤ B := by
  let e : Y ≃ Fin (Nat.card Y) := Finite.equivFinOfCardEq rfl
  let T : Subgroup (Equiv.Perm (Fin (Nat.card Y))) := L.map e.permCongrHom.toMonoidHom
  let f : L ≃* T := e.permCongrHom.subgroupMap L
  have hc : Nat.card (ConjClasses L) ≤ Nat.card (ConjClasses T) :=
    Nat.card_le_card_of_surjective (ConjClasses.map f.symm.toMonoidHom)
      (ConjClasses.map_surjective f.symm.surjective)
  exact (Nat.pow_le_pow_left hc 3).trans (hbound T)

theorem exact_exponent_large_block_cube_step
    {A Ω X : Type} [Group A] [Finite A] [Finite Ω] [Finite X]
    [MulAction A Ω] [MulAction A X] [FaithfulSMul A Ω]
    (b : Ω → X) (hb : ∀ (g : A) (ω : Ω), b (g • ω) = g • b ω)
    (a : ℕ) (ha : 4 ≤ a) (hblocks : 4 ≤ Nat.card X)
    (hsize : ∀ x, Nat.card (originalBlockFibre b x) = a)
    (hSmaller : ∀ m : ℕ, m < Nat.card Ω → 4 ≤ m →
      ∀ L : Subgroup (Equiv.Perm (Fin m)),
        Nat.card (ConjClasses L) ^ 3 ≤ 5 ^ (m - 1)) :
    Nat.card (ConjClasses A) ^ 3 ≤ 5 ^ (Nat.card Ω - 1) := by
  letI : Fintype X := Fintype.ofFinite _
  have hd := GaronziMarotiLargeBlockReduction.card_eq_blocks_mul_fibre b a hsize
  have halt : a < Nat.card Ω := by rw [hd]; nlinarith
  have hblt : Nat.card X < Nat.card Ω := by rw [hd]; nlinarith
  have hc : ∀ x (L : Subgroup (originalBlockComponent b hb x)), L.IsSubnormal →
      Nat.card (ConjClasses L) ^ 3 ≤ 5 ^ (a - 1) := by
    intro x L _
    have hlocal := cube_le_of_finite_permutation_bound (originalBlockFibre b x)
      (5 ^ (Nat.card (originalBlockFibre b x) - 1))
      (hSmaller _ (by rwa [hsize]) (by rwa [hsize]))
      (L.map (originalBlockComponent b hb x).subtype)
    let e := L.equivMapOfInjective (originalBlockComponent b hb x).subtype
      Subtype.val_injective
    have he : Nat.card (ConjClasses L) ≤
        Nat.card (ConjClasses (L.map (originalBlockComponent b hb x).subtype)) :=
      Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
        (ConjClasses.map_surjective e.symm.surjective)
    exact (Nat.pow_le_pow_left he 3).trans (by simpa only [hsize] using hlocal)
  have hker := class_power_le_finite_subnormal_coordinate_bounds 3
    (fun x => originalBlockComponent b hb x) (fun _ => 5 ^ (a - 1))
    (Kernel (A := A) (X := X)) (componentCoordinate b hb)
    (fun x => (componentCoordinate_range_normal b hb x).isSubnormal) hc
    (componentCoordinates_injective b hb)
  have hker' : Nat.card (ConjClasses (Kernel (A := A) (X := X))) ^ 3 ≤
      5 ^ ((a - 1) * Nat.card X) := by
    simpa only [Finset.prod_const,Finset.card_univ,Nat.card_eq_fintype_card,← pow_mul] using hker
  have htop := cube_le_of_finite_permutation_bound X (5 ^ (Nat.card X - 1))
    (hSmaller _ hblt hblocks) (Top (A := A) (X := X))
  have hrec := Nat.pow_le_pow_left
    (conjugacyClass_card_le_kernel_mul_range (topMap (A := A) (X := X))) 3
  rw [mul_pow] at hrec
  have hsum : (a - 1) * Nat.card X + Nat.card X = a * Nat.card X := by
    have h := congrArg (fun t : ℕ => t * Nat.card X)
      (Nat.sub_add_cancel (show 1 ≤ a by omega))
    simpa only [Nat.add_mul,one_mul] using h
  calc
    _ ≤ 5 ^ ((a - 1) * Nat.card X) * 5 ^ (Nat.card X - 1) :=
      hrec.trans (Nat.mul_le_mul hker' htop)
    _ = _ := by
      rw [← pow_add,hd]
      congr 1
      rw [Nat.mul_comm (Nat.card X) a]
      omega

end SymmetricSubgroupAsymptotics.GaronziMarotiLargeBlockCubeReduction
