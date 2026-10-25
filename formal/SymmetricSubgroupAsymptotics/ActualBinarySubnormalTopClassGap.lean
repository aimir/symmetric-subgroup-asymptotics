import SymmetricSubgroupAsymptotics.BinarySubnormalSymmetricTopClassGap
import SymmetricSubgroupAsymptotics.SubnormalImageOfSubnormalRange
import SymmetricSubgroupAsymptotics.BinaryBlockWreathCodimension

/-! The actual original binary block embedding, restricted to each
subnormal source subgroup. Only the original action is transitive on
blocks; the subnormal subgroup need not be. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics.ActualBinarySubnormalTopClassGap
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

variable {A Ω : Type} [Group A] [MulAction A Ω] [FaithfulSMul A Ω]
    [Finite A] [Finite Ω] (n : ℕ) [MulAction A (Fin n)] [MulAction.IsPretransitive A (Fin n)]
    (b : Ω → Fin n) (hb : ∀ (a : A) (ω : Ω), b (a • ω)=a • b ω) (x₀ : Fin n)

def ambientEmbedding : A →* PermutationalWreathProduct
    (Equiv.Perm (originalBlockFibre b x₀)) (Equiv.Perm (Fin n)) (Fin n) :=
  (includeTop (Top (A := A) (X := Fin n))).comp
    (BinaryBlockWreathCodimension.fullEmbedding b hb x₀)

theorem ambientEmbedding_injective : Function.Injective (ambientEmbedding n b hb x₀) :=
  (includeTop_injective _).comp
    (BinaryBlockWreathCodimension.fullEmbedding_injective b hb x₀)

theorem ambientProjection : topProjection (ambientEmbedding n b hb x₀) =
    topMap (A := A) (X := Fin n) := by
  ext a
  rfl

include hb in
theorem subnormal_class_cube_gap
    (htwo : Nat.card (originalBlockFibre b x₀)=2) (hn : 10 ≤ n)
    (hTop : (Top (A := A) (X := Fin n)).IsSubnormal)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(2*n-2) := by
  letI : IsMulCommutative (Equiv.Perm (originalBlockFibre b x₀)) :=
    Equiv.Perm.isMulCommutative_iff_card_le_two.mpr htwo.le
  letI : CommGroup (Equiv.Perm (originalBlockFibre b x₀)) := inferInstance
  have hC : Nat.card (Equiv.Perm (originalBlockFibre b x₀))=2 := by
    rw [Nat.card_perm,htwo]
    rfl
  let f := (ambientEmbedding n b hb x₀).comp H.subtype
  have hf : Function.Injective f :=
    (ambientEmbedding_injective n b hb x₀).comp Subtype.val_injective
  have hrange : (topProjection f).range.IsSubnormal := by
    have h := SubnormalImageOfSubnormalRange.restricted_range_isSubnormal
      (topMap (A := A) (X := Fin n)) hTop H hH
    have he : topProjection f = (topMap (A := A) (X := Fin n)).comp H.subtype := by
      ext a
      rfl
    rw [he]
    exact h
  exact BinarySubnormalSymmetricTopClassGap.class_cube_gap_of_subnormal_top_range
    n hC hn f hf hrange

include hb in
theorem subnormal_class_cube_gap_of_symmetric_or_alternating_top
    (htwo : Nat.card (originalBlockFibre b x₀)=2) (hn : 10 ≤ n)
    (hTop : Top (A := A) (X := Fin n) = ⊤ ∨
      Top (A := A) (X := Fin n) = alternatingGroup (Fin n))
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(2*n-2) := by
  apply subnormal_class_cube_gap n b hb x₀ htwo hn _ H hH
  rcases hTop with ht | ht
  · rw [ht]
    exact Subgroup.IsSubnormal.top
  · rw [ht]
    exact Subgroup.Normal.isSubnormal inferInstance

end SymmetricSubgroupAsymptotics.ActualBinarySubnormalTopClassGap
