import SymmetricSubgroupAsymptotics.C2WreathGeneration
import SymmetricSubgroupAsymptotics.BinaryDiagonalSwapAffineGeneration

/-! Shared generation for a three-bit affine local group containing the
retained Singer. It applies to each literal local-affine wreath chart. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace BinarySingerAffineWreathGeneration

open SemidirectProduct
open PrimitiveAffineDegreeTwoPairedEightAffineTops

variable (R : Subgroup LinearGroup) (hsinger : singer ∈ R)

include hsinger

theorem local_mem_of_generators {G : Type} [Group G]
    (f : AffineModel.Aff R →* G) (K : Subgroup G)
    (hlinear : ∀ r : R, f (inr r) ∈ K)
    (ht : f (inl (Multiplicative.ofAdd firstVector)) ∈ K)
    (g : AffineModel.Aff R) : f g ∈ K := by
  let s : R := ⟨singer, hsinger⟩
  have htranslations (v : Multiplicative Vector) : f (inl v) ∈ K := by
    by_cases hv : v.toAdd = 0
    · have heq : v = 1 := Multiplicative.toAdd.injective hv
      rw [heq, map_one, map_one]
      exact K.one_mem
    obtain ⟨i, hi⟩ := singer_nonzero_orbit firstVector v.toAdd firstVector_ne_zero hv
    have h := K.mul_mem (K.mul_mem (hlinear (s ^ i.val)) ht)
      (K.inv_mem (hlinear (s ^ i.val)))
    rw [← map_inv, ← map_mul, ← map_mul, ← map_inv, ← inl_aut] at h
    have heq : AffineModel.linAut R (s ^ i.val) (Multiplicative.ofAdd firstVector) = v := by
      apply Multiplicative.toAdd.injective
      exact hi
    exact heq ▸ h
  rw [← inl_left_mul_inr_right g, map_mul]
  exact K.mul_mem (htranslations g.left) (hlinear g.right)

theorem mem_of_generators (K : Subgroup (C2Wreath.W (AffineModel.Aff R)))
    (hlinear : ∀ r : R, C2Wreath.firstFactor (inr r) ∈ K)
    (ht : C2Wreath.firstFactor (inl (Multiplicative.ofAdd firstVector)) ∈ K)
    (hswap : (inr C2Wreath.gen : C2Wreath.W (AffineModel.Aff R)) ∈ K)
    (g : C2Wreath.W (AffineModel.Aff R)) : g ∈ K :=
  C2Wreath.mem_of_first_and_swap K
    (local_mem_of_generators R hsinger C2Wreath.firstFactor K hlinear ht) hswap g

end BinarySingerAffineWreathGeneration
end SymmetricSubgroupAsymptotics

end
