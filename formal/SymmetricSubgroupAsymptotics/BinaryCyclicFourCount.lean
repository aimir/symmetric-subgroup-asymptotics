import SymmetricSubgroupAsymptotics.BinaryCyclicFourSquareObstruction
import SymmetricSubgroupAsymptotics.BinaryRankSums

/-! Exact two-column counting for the original group C4^a × C2^r.
The first partition is by its actual mod-two image. Only after the
square obstruction and every fibre count are proved are images grouped
by dimension. No Hall formula or subgroup-count estimate is assumed.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.BinaryCyclicFourCount

open BinaryCyclicFourSquareObstruction

local instance subgroupFinite {G : Type*} [Group G] [Finite G] : Finite (Subgroup G) :=
  Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective

attribute [local instance] Fintype.ofFinite

/-- All original subgroups appear once, at their actual mod-two image. -/
theorem card_eq_sum_image (r a : ℕ) :
    (Nat.card (Subgroup (Original r a)) : ℝ) =
      ∑ U : Submodule (ZMod 2) (ImageSpace a),
        (Nat.card {H : Subgroup (Original r a) //
          H.map (projection r a) = U.toAddSubgroup.toSubgroup} : ℝ) := by
  let f : Subgroup (Original r a) → Subgroup (Multiplicative (ImageSpace a)) :=
    fun H => H.map (projection r a)
  have hcard : Nat.card (Subgroup (Original r a)) =
      ∑ L : Subgroup (Multiplicative (ImageSpace a)),
        Nat.card {H : Subgroup (Original r a) // H.map (projection r a) = L} := by
    rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f),Nat.card_sigma]
  calc
    _ = ∑ L : Subgroup (Multiplicative (ImageSpace a)),
        (Nat.card {H : Subgroup (Original r a) // H.map (projection r a) = L} : ℝ) := by
      exact_mod_cast hcard
    _ = _ := (Fintype.sum_equiv
      (terminalKernelSubmoduleOrderIso (K := ImageSpace a)).toEquiv _ _ (fun _ => rfl)).symm

def imagePolynomial (r a j : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (r+a-j+1),
    (binaryGaussianCoefficient (r+a-j) k : ℝ) * (2 : ℝ)^(j*k)

theorem image_card_real (r a : ℕ) (U : Submodule (ZMod 2) (ImageSpace a)) :
    (Nat.card {H : Subgroup (Original r a) //
      H.map (projection r a) = U.toAddSubgroup.toSubgroup} : ℝ) =
      imagePolynomial r a (Module.finrank (ZMod 2) U) := by
  unfold imagePolynomial
  exact_mod_cast image_card_gaussian r a U

/-- The exact dimension grouping keeps the actual multiplicity of every image. -/
theorem card_eq_sum_rank (r a : ℕ) :
    (Nat.card (Subgroup (Original r a)) : ℝ) =
      ∑ j ∈ Finset.range (a+1),
        (binaryGaussianCoefficient a j : ℝ) * imagePolynomial r a j := by
  rw [card_eq_sum_image]
  calc
    _ = ∑ U : Submodule (ZMod 2) (ImageSpace a),
        imagePolynomial r a (Module.finrank (ZMod 2) U) :=
      Finset.sum_congr rfl (fun U _ => image_card_real r a U)
    _ = ∑ j ∈ Finset.range (a+1),
        ∑ U : {U : Submodule (ZMod 2) (ImageSpace a) // Module.finrank (ZMod 2) U = j},
          imagePolynomial r a (Module.finrank (ZMod 2) U.1) := by
      simpa only [ImageSpace,Module.finrank_pi,Fintype.card_fin] using
        binary_subspace_sum_by_rank
          (fun U : Submodule (ZMod 2) (ImageSpace a) =>
            imagePolynomial r a (Module.finrank (ZMod 2) U))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      have hja : j ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      calc
        _ = ∑ _U : {U : Submodule (ZMod 2) (ImageSpace a) //
              Module.finrank (ZMod 2) U = j}, imagePolynomial r a j :=
          Finset.sum_congr rfl (fun U _ => congrArg (imagePolynomial r a) U.2)
        _ = (Nat.card {U : Submodule (ZMod 2) (ImageSpace a) //
              Module.finrank (ZMod 2) U = j} : ℝ) * imagePolynomial r a j := by
          simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
        _ = _ := by
          have h := binary_subspace_rank_card (V := ImageSpace a) j
            (by simpa only [ImageSpace,Module.finrank_pi,Fintype.card_fin] using hja)
          simpa only [ImageSpace,Module.finrank_pi,Fintype.card_fin] using
            congrArg (fun t : ℝ => t * imagePolynomial r a j) h

/-- The literal two-column formula, using the retained-annihilator index k.
It matches the scalar Gaussian estimate without reindexing kernel intersections. -/
theorem card_eq_two_column_sum (r a : ℕ) :
    (Nat.card (Subgroup (Original r a)) : ℝ) =
      ∑ j ∈ Finset.range (a+1), (binaryGaussianCoefficient a j : ℝ) *
        ∑ k ∈ Finset.range (r+a-j+1),
          (binaryGaussianCoefficient (r+a-j) k : ℝ) * (2 : ℝ)^(j*k) := by
  exact card_eq_sum_rank r a

end SymmetricSubgroupAsymptotics.BinaryCyclicFourCount
