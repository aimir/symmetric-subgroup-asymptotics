import SymmetricSubgroupAsymptotics.BinaryPlaneWreathActualOddKernelConsequences

/-! The actual sign-projection kernel is abelian of odd order, independently
of correlations among its local coordinates. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryPlaneWreathActualOddKernel
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathIrreducible
open BinaryPlaneWreathNormalGenerators

variable {R I : Type} [Group R] [Finite R] [MulAction R I]
  [Fintype I] [DecidableEq I]
  (C : Subgroup (W (R := R) (I := I)))

theorem localLinear_joint (g h : oddKernel C)
    (heq : ∀ i : I, localLinear C i g=localLinear C i h) : g=h := by
  apply Subtype.ext
  apply Subtype.ext
  apply PermutationalWreathProduct.ext
  · funext i
    exact heq i
  · rw [top_one C g,top_one C h]

theorem cube_eq_one (g : oddKernel C) : g^3=1 := by
  apply localLinear_joint C
  intro i
  rw [map_pow,map_one,local_cubic C i g]

theorem isPGroup_three : IsPGroup 3 (oddKernel C) := by
  intro g
  exact ⟨1,by simpa using cube_eq_one C g⟩

private theorem cubic_permutations_commute :
    ∀ g h : Equiv.Perm (Fin 3), g^3=1 → h^3=1 → g*h=h*g := by
  decide +kernel

theorem commutative : IsMulCommutative (oddKernel C) :=
  IsMulCommutative.of_comm fun g h ↦ by
    apply localLinear_joint C
    intro i
    rw [map_mul,map_mul]
    apply toThree_injective
    rw [map_mul,map_mul]
    apply cubic_permutations_commute
    · rw [← map_pow,local_cubic C i g,map_one]
    · rw [← map_pow,local_cubic C i h,map_one]

theorem card_cast_eq_one : (Nat.card (oddKernel C) : ZMod 2)=1 := by
  obtain ⟨n,hn⟩ := (isPGroup_three C).exists_card_eq
  rw [hn,Nat.cast_pow]
  rw [show ((3 : ℕ) : ZMod 2)=1 by decide +kernel,one_pow]

theorem card_cast_ne_zero : (Nat.card (oddKernel C) : ZMod 2)≠0 := by
  rw [card_cast_eq_one C]
  exact one_ne_zero

/-- Nonbinary actual cyclic-block images have fixed-free odd restriction;
only actual block transporters are used. -/
theorem fixedFree_of_nonbinary
    (hR : IsPGroup 2 R) (hC : ¬ IsPGroup 2 C)
    (htrans : ∀ i j : I, ∃ h : C,
      (h : W (R := R) (I := I)).right • i=j)
    (v : I → Plane)
    (hv : ∀ g : oddKernel C,
      BinaryPlaneCyclicWreathUniform.representation C (g : C) v=v) : v=0 :=
  fixedFree C (all_local_nontrivial C (oddKernel_ne_bot C hR hC) htrans) v hv

end SymmetricSubgroupAsymptotics.BinaryPlaneWreathActualOddKernel
