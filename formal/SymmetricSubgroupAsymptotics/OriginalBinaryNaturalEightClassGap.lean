import SymmetricSubgroupAsymptotics.BinarySubnormalSymmetricTopEightClassGap
import SymmetricSubgroupAsymptotics.OriginalBinaryBlockSubnormalClassGap
import SymmetricSubgroupAsymptotics.PrimitiveAlternatingNaturalDegreeRecognition

/-! Native binary fibres with an actual subnormal symmetric-coordinate
range pay the extra exponent from eight blocks onward. The descriptor
consumer first proves that the ORIGINAL permutation top is natural
alternating or symmetric; no abstract A8 action is silently relabelled. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics.OriginalBinaryNaturalEightClassGap
open OriginalBlockClassBound PrimitiveSocleRawStructure WreathHomProjectionRange

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω] [MulAction.IsPretransitive A X]

theorem subnormal_class_cube_gap_at_original_degree
    (b : Ω → X) (hb : ∀ (g : A) (ω : Ω), b (g • ω)=g • b ω)
    (x₀ : X) (htwo : Nat.card (originalBlockFibre b x₀)=2)
    (hn : 8 ≤ Nat.card X) (hTop : (Top (A := A) (X := X)).IsSubnormal)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-2) := by
  letI : IsMulCommutative (Equiv.Perm (originalBlockFibre b x₀)) :=
    Equiv.Perm.isMulCommutative_iff_card_le_two.mpr htwo.le
  letI : CommGroup (Equiv.Perm (originalBlockFibre b x₀)) := inferInstance
  have hC : Nat.card (Equiv.Perm (originalBlockFibre b x₀))=2 := by
    rw [Nat.card_perm,htwo]
    rfl
  let f := (OriginalBinaryBlockSubnormalClassGap.ambientEmbedding b hb x₀).comp H.subtype
  have hf : Function.Injective f :=
    (OriginalBinaryBlockSubnormalClassGap.ambientEmbedding_injective b hb x₀).comp
      Subtype.val_injective
  have hrange : (topProjection f).range.IsSubnormal := by
    have h := SubnormalImageOfSubnormalRange.restricted_range_isSubnormal
      (topMap (A := A) (X := X)) hTop H hH
    have he : topProjection f=(topMap (A := A) (X := X)).comp H.subtype := by
      ext a
      rfl
    rw [he]
    exact h
  have h := BinarySubnormalSymmetricTopEightClassGap.class_cube_gap_of_subnormal_permutation_top_range
    hC hn f hf hrange
  have hd : 2*Nat.card X=Nat.card Ω := by
    have hh := Nat.card_congr (ActualBlockWreathEmbedding.productEquiv b hb x₀)
    rw [Nat.card_prod,htwo] at hh
    exact hh
  simpa only [hd] using h

theorem subnormal_class_cube_gap_of_single_factor_natural_degree
    (b : Ω → X) (hb : ∀ (g : A) (ω : Ω), b (g • ω)=g • b ω)
    (x₀ : X) (htwo : Nat.card (originalBlockFibre b x₀)=2)
    (D : NonaffineData (Top (A := A) (X := X)) X)
    (m : ℕ) (hm : 8 ≤ m) (e : D.Simple ≃* alternatingGroup (Fin m))
    (hk : D.factorCount=1) (hdegree : Nat.card X=m)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-2) := by
  letI := Fintype.ofFinite X
  letI := Classical.decEq X
  have hnatural := PrimitiveAlternatingNaturalDegreeRecognition.alternating_or_top_of_single_factor_natural_degree
    (Top (A := A) (X := X)) D m (by omega) e hk hdegree
  have htop : (Top (A := A) (X := X)).IsSubnormal := by
    rcases hnatural with h | h
    · rw [h]
      exact Subgroup.Normal.isSubnormal inferInstance
    · rw [h]
      exact Subgroup.IsSubnormal.top
  exact subnormal_class_cube_gap_at_original_degree b hb x₀ htwo (by omega) htop H hH

end SymmetricSubgroupAsymptotics.OriginalBinaryNaturalEightClassGap
