import SymmetricSubgroupAsymptotics.BinarySubnormalPermutationTopClassGap
import SymmetricSubgroupAsymptotics.SubnormalImageOfSubnormalRange
import SymmetricSubgroupAsymptotics.BinaryBlockWreathCodimension

/-! The actual original binary block embedding, restricted to each
subnormal source subgroup. Only the original action is transitive on
blocks; the subnormal subgroup need not be. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics.OriginalBinaryBlockSubnormalClassGap
open OriginalBlockClassBound WreathHomProjectionRange

private def includeTop {C Q I : Type} [Group C] [Group Q] [MulAction Q I]
    (R : Subgroup Q) : PermutationalWreathProduct C R I →*
        PermutationalWreathProduct C Q I where
  toFun w := ⟨w.left,w.right.val⟩
  map_one' := by apply PermutationalWreathProduct.ext <;> rfl
  map_mul' _ _ := by apply PermutationalWreathProduct.ext <;> rfl

private theorem includeTop_injective {C Q I : Type} [Group C] [Group Q] [MulAction Q I]
    (R : Subgroup Q) : Function.Injective (includeTop (C := C) (I := I) R) := by
  intro a b he
  apply PermutationalWreathProduct.ext
  · exact congrArg (fun w : PermutationalWreathProduct C Q I => w.left) he
  · apply Subtype.ext
    exact congrArg (fun w : PermutationalWreathProduct C Q I => w.right) he

variable {A Ω X : Type} [Group A] [MulAction A Ω] [FaithfulSMul A Ω]
    [Finite A] [Finite Ω] [Finite X] [MulAction A X] [MulAction.IsPretransitive A X]
    (b : Ω → X) (hb : ∀ (a : A) (ω : Ω), b (a • ω)=a • b ω) (x₀ : X)

def ambientEmbedding : A →* PermutationalWreathProduct
    (Equiv.Perm (originalBlockFibre b x₀)) (Equiv.Perm X) X :=
  (includeTop (Top (A := A) (X := X))).comp
    (BinaryBlockWreathCodimension.fullEmbedding b hb x₀)

theorem ambientEmbedding_injective : Function.Injective (ambientEmbedding b hb x₀) :=
  (includeTop_injective _).comp
    (BinaryBlockWreathCodimension.fullEmbedding_injective b hb x₀)

theorem ambientProjection : topProjection (ambientEmbedding b hb x₀) =
    topMap (A := A) (X := X) := by
  ext a
  rfl

include hb in
theorem subnormal_class_cube_gap
    (htwo : Nat.card (originalBlockFibre b x₀)=2) (hn : 10 ≤ Nat.card X)
    (hTop : (Top (A := A) (X := X)).IsSubnormal)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(2*Nat.card X-2) := by
  letI : IsMulCommutative (Equiv.Perm (originalBlockFibre b x₀)) :=
    Equiv.Perm.isMulCommutative_iff_card_le_two.mpr htwo.le
  letI : CommGroup (Equiv.Perm (originalBlockFibre b x₀)) := inferInstance
  have hC : Nat.card (Equiv.Perm (originalBlockFibre b x₀))=2 := by
    rw [Nat.card_perm,htwo]
    rfl
  let f := (ambientEmbedding b hb x₀).comp H.subtype
  have hf : Function.Injective f :=
    (ambientEmbedding_injective b hb x₀).comp Subtype.val_injective
  have hrange : (topProjection f).range.IsSubnormal := by
    have h := SubnormalImageOfSubnormalRange.restricted_range_isSubnormal
      (topMap (A := A) (X := X)) hTop H hH
    have he : topProjection f = (topMap (A := A) (X := X)).comp H.subtype := by
      ext a
      rfl
    rw [he]
    exact h
  exact BinarySubnormalPermutationTopClassGap.class_cube_gap_of_subnormal_top_range
    hC hn f hf hrange

include hb in
theorem subnormal_class_cube_gap_of_symmetric_or_alternating_top [Fintype X] [DecidableEq X]
    (htwo : Nat.card (originalBlockFibre b x₀)=2) (hn : 10 ≤ Nat.card X)
    (hTop : Top (A := A) (X := X) = ⊤ ∨
      Top (A := A) (X := X) = alternatingGroup X)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(2*Nat.card X-2) := by
  apply subnormal_class_cube_gap b hb x₀ htwo hn _ H hH
  rcases hTop with ht | ht
  · rw [ht]
    exact Subgroup.IsSubnormal.top
  · rw [ht]
    exact Subgroup.Normal.isSubnormal inferInstance

include hb in
theorem subnormal_class_cube_gap_at_original_degree
    (htwo : Nat.card (originalBlockFibre b x₀)=2) (hn : 10 ≤ Nat.card X)
    (hTop : (Top (A := A) (X := X)).IsSubnormal)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-2) := by
  have hd : 2*Nat.card X = Nat.card Ω := by
    have h := Nat.card_congr (ActualBlockWreathEmbedding.productEquiv b hb x₀)
    rw [Nat.card_prod,htwo] at h
    exact h
  simpa only [hd] using subnormal_class_cube_gap b hb x₀ htwo hn hTop H hH

end SymmetricSubgroupAsymptotics.OriginalBinaryBlockSubnormalClassGap
