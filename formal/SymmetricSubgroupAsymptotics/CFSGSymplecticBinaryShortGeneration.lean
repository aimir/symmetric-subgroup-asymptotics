import SymmetricSubgroupAsymptotics.CFSGSymplecticUpperTransvectionSubgroup
import SymmetricSubgroupAsymptotics.CFSGSymplecticSimpleWeyl

/-! Positive simple roots and short Weyl words suffice for the isotropic
transvections used by the binary dual-orbit bound. This proves containment
inside the displayed subgroup, rather than assuming its full symplectic image. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryShortGeneration
open CFSGSymplecticSerreMatrices CFSGTypeAElementaryMatrices

variable (K : Type) [Field K]

theorem sl_double_mem_of_short_roots (m : ℕ)
    (J : Subgroup (elementaryRootGroup K m))
    (hshort : ∀ (neg : Bool) (i : Fin m), i.val+1<m → ∀ a : K,
      elementaryRoot K m neg i a ∈ J)
    (A : Matrix.SpecialLinearGroup (Fin m) K) :
    CFSGSymplecticSLDoubleEmbedding.doubleIntoElementary K m A ∈ J := by
  let H := J.comap (CFSGSymplecticSLDoubleEmbedding.doubleIntoElementary K m)
  have ht : H = ⊤ := by
    apply CFSGOrthogonalDGenerationAdjacentSL.eq_top_of_adjacent m H
    intro i j hij hadj a
    change CFSGSymplecticSLDoubleEmbedding.doubleIntoElementary K m (elementary hij a) ∈ J
    rcases hadj with hpos | hneg
    · have hi : i.val+1<m := by rw [hpos]; exact j.isLt
      have hn : (⟨i.val+1,hi⟩ : Fin m)=j := Fin.ext hpos
      have he : CFSGSymplecticSLDoubleEmbedding.doubleIntoElementary K m
          (elementary hij a) = elementaryRoot K m false i a := by
        apply Subtype.ext
        apply Units.ext
        change ((CFSGOrthogonalDGenerationSLDouble.doubleHom K m
          (elementary hij a)) : Mat K m) = 1+a • positive K m i
        rw [CFSGOrthogonalDGenerationSLDouble.doubleHom_elementary_val]
        change 1+a • CFSGOrthogonalDGenerationSLDouble.chainMatrix K m i j =
          1+a • positive K m i
        rw [positive,dif_pos hi,hn]
        rfl
      rw [he]
      exact hshort false i hi a
    · have hj : j.val+1<m := by rw [hneg]; exact i.isLt
      have hn : (⟨j.val+1,hj⟩ : Fin m)=i := Fin.ext hneg
      have he : CFSGSymplecticSLDoubleEmbedding.doubleIntoElementary K m
          (elementary hij a) = elementaryRoot K m true j a := by
        apply Subtype.ext
        apply Units.ext
        change ((CFSGOrthogonalDGenerationSLDouble.doubleHom K m
          (elementary hij a)) : Mat K m) = 1+a • negative K m j
        rw [CFSGOrthogonalDGenerationSLDouble.doubleHom_elementary_val]
        change 1+a • CFSGOrthogonalDGenerationSLDouble.chainMatrix K m i j =
          1+a • negative K m j
        simp only [negative,positive,dif_pos hj,hn,Matrix.transpose_sub,
          Matrix.transpose_single,CFSGOrthogonalDGenerationSLDouble.chainMatrix]
      rw [he]
      exact hshort true j hj a
  change A ∈ H
  rw [ht]
  trivial

private theorem binary_zero_or_one [Finite K] (hK : Nat.card K=2) (a : K) :
    a=0 ∨ a=1 := by
  letI : Fintype K := Fintype.ofFinite K
  have hs : a^2=a := by
    simpa only [← Nat.card_eq_fintype_card,hK] using FiniteField.pow_card a
  have hz : a*(a-1)=0 := by rw [mul_sub,mul_one,←pow_two,hs,sub_self]
  rcases mul_eq_zero.mp hz with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

theorem exists_paired_Y_transvection [Finite K] [CharP K 2]
    (hK : Nat.card K=2) (r : ℕ) (hr : 0<r)
    (J : Subgroup (elementaryRootGroup K (r+1)))
    (hpositive : ∀ (i : Fin (r+1)) (a : K), elementaryRoot K (r+1) false i a ∈ J)
    (hweyl : ∀ i : Fin (r+1), i.val+1<r+1 → simpleWeyl K (r+1) i ∈ J)
    (v : Fin (r+1) → K) :
    ∃ g : J, ∀ x : (Fin (r+1) → K) × (Fin (r+1) → K),
      CFSGSymplecticBinaryPointTailAction.vectorLinearHom K (r+1) g.val x =
        BinaryQuadraticRefinementTransvections.transvectionMap (0,v) x := by
  have hshort : ∀ (neg : Bool) (i : Fin (r+1)), i.val+1<r+1 → ∀ a : K,
      elementaryRoot K (r+1) neg i a ∈ J := by
    intro neg i hi a
    cases neg
    · exact hpositive i a
    · rcases binary_zero_or_one K hK a with rfl | rfl
      · rw [elementaryRoot_zero]
        exact J.one_mem
      · have he : elementaryRoot K (r+1) true i 1 =
            (elementaryRoot K (r+1) false i (-1))⁻¹ * simpleWeyl K (r+1) i *
              (elementaryRoot K (r+1) false i (-1))⁻¹ := by
          rw [simpleWeyl]
          simp only [mul_assoc,inv_mul_cancel_left,mul_inv_cancel,mul_one]
        rw [he]
        exact J.mul_mem (J.mul_mem (J.inv_mem (hpositive i (-1))) (hweyl i hi))
          (J.inv_mem (hpositive i (-1)))
  exact CFSGSymplecticUpperTransvectionSubgroup.exists_paired_Y_transvection
    K r hr J (sl_double_mem_of_short_roots K (r+1) J hshort)
    (hpositive (Fin.last r) 1) v

end SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryShortGeneration
