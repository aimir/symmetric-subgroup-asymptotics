import SymmetricSubgroupAsymptotics.TernarySubnormalPermutationTopClassGap
import SymmetricSubgroupAsymptotics.OriginalBinaryBlockSubnormalClassGap
import SymmetricSubgroupAsymptotics.PrimitiveAlternatingNaturalDegreeRecognition

/-! Actual ternary block/H transport. The existing original wreath
embedding is coefficient-generic; here its actual three-point fibre
has order six and class capacity three, with no commutativity instance.
The actual subnormal source subgroup need not be transitive. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.OriginalTernaryBlockSubnormalClassGap
open OriginalBlockClassBound WreathHomProjectionRange

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω] [MulAction.IsPretransitive A X]
    (b : Ω → X) (hb : ∀ (g : A) (ω : Ω), b (g • ω)=g • b ω) (x₀ : X)

include hb in
theorem subnormal_class_cube_gap_at_original_degree
    (hthree : Nat.card (originalBlockFibre b x₀)=3) (hn : 28 ≤ Nat.card X)
    (hTop : (Top (A := A) (X := X)).IsSubnormal)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-2) := by
  let C := Equiv.Perm (originalBlockFibre b x₀)
  have horder : Nat.card C ≤ 6 := by
    change Nat.card (Equiv.Perm (originalBlockFibre b x₀)) ≤ 6
    rw [Nat.card_perm,hthree]
    decide
  have hclass : Nat.card (ConjClasses C) ≤ 3 := by
    have htop : Nat.card (ConjClasses (⊤ : Subgroup C)) ≤ 3 :=
      SmallPermutationClassBudgets.subgroup_class_card_le_three hthree.le ⊤
    have hle : Nat.card (ConjClasses C) ≤ Nat.card (ConjClasses (⊤ : Subgroup C)) :=
      Nat.card_le_card_of_surjective
        (ConjClasses.map (Subgroup.topEquiv : (⊤ : Subgroup C) ≃* C).toMonoidHom)
        (ConjClasses.map_surjective Subgroup.topEquiv.surjective)
    exact hle.trans htop
  let f := (OriginalBinaryBlockSubnormalClassGap.ambientEmbedding b hb x₀).comp H.subtype
  have hf : Function.Injective f :=
    (OriginalBinaryBlockSubnormalClassGap.ambientEmbedding_injective b hb x₀).comp Subtype.val_injective
  have hrange : (topProjection f).range.IsSubnormal := by
    have h := SubnormalImageOfSubnormalRange.restricted_range_isSubnormal
      (topMap (A := A) (X := X)) hTop H hH
    have he : topProjection f = (topMap (A := A) (X := X)).comp H.subtype := by ext a; rfl
    rw [he]
    exact h
  have h := TernarySubnormalPermutationTopClassGap.class_cube_gap_of_subnormal_top_range
    horder hclass hn f hf hrange
  have hd : 3*Nat.card X=Nat.card Ω := by
    have hc := Nat.card_congr (ActualBlockWreathEmbedding.productEquiv b hb x₀)
    rw [Nat.card_prod,hthree] at hc
    exact hc
  simpa only [hd] using h

include hb in
theorem subnormal_class_cube_gap_of_symmetric_or_alternating_top [Fintype X] [DecidableEq X]
    (hthree : Nat.card (originalBlockFibre b x₀)=3) (hn : 28 ≤ Nat.card X)
    (hTop : Top (A := A) (X := X)=⊤ ∨ Top (A := A) (X := X)=alternatingGroup X)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-2) := by
  apply subnormal_class_cube_gap_at_original_degree b hb x₀ hthree hn _ H hH
  rcases hTop with h | h
  · rw [h]; exact Subgroup.IsSubnormal.top
  · rw [h]; exact Subgroup.Normal.isSubnormal inferInstance

include hb in
theorem subnormal_class_cube_gap_of_single_natural_factor
    (hthree : Nat.card (originalBlockFibre b x₀)=3)
    (D : PrimitiveSocleRawStructure.NonaffineData (Top (A := A) (X := X)) X)
    (m : ℕ) (hm : 28 ≤ m) (e : D.Simple ≃* alternatingGroup (Fin m))
    (hk : D.factorCount=1) (hdegree : Nat.card X=m)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-2) := by
  letI := Fintype.ofFinite X
  letI := Classical.decEq X
  have hnatural := PrimitiveAlternatingNaturalDegreeRecognition.alternating_or_top_of_single_factor_natural_degree
    (Top (A := A) (X := X)) D m (by omega) e hk hdegree
  apply subnormal_class_cube_gap_at_original_degree b hb x₀ hthree (by omega) _ H hH
  rcases hnatural with h | h
  · rw [h]; exact Subgroup.Normal.isSubnormal inferInstance
  · rw [h]; exact Subgroup.IsSubnormal.top

end SymmetricSubgroupAsymptotics.OriginalTernaryBlockSubnormalClassGap
