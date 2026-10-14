import SymmetricSubgroupAsymptotics.PermutationBinaryFourWeightedHead
import SymmetricSubgroupAsymptotics.RepresentationHeadExact

/-!
# Equality for three four-point binary coordinates

A head of dimension at least six forces every actual coordinate image
to be its augmentation hyperplane. The weighted filtration then forces
the source dimension to be nine. Joint injectivity makes its map onto
the product of the three augmentation hyperplanes surjective, so the
correlated source is identified only after equality has been proved.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics
namespace PermutationBinaryThreeFourAugmentation

open RepresentationHeadExact

variable {G V : Type} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (X : Fin 3 → Type) [∀ i, Finite (X i)] [∀ i, MulAction G (X i)]
  [∀ i, MulAction.IsPretransitive G (X i)]
  (rho : Representation (ZMod 2) G V)
  (f : ∀ i, rho.IntertwiningMap
    (permutationFunctionRepresentation (ZMod 2) G (X i)))

/-- The kernel of any one coordinate is separated by the other two,
and therefore has head at most four. -/
theorem coordinateKernel_head_le_four
    (hG : IsPGroup 2 G) (x : ∀ i, X i) (hcard : ∀ i, Nat.card (X i) = 4)
    (hf : Function.Injective (fun v i ↦ f i v)) (i : Fin 3) :
    Module.finrank (ZMod 2)
      ((f i).ker.toRepresentation.IntertwiningMap
        (Representation.trivial (ZMod 2) G (ZMod 2))) ≤ 4 := by
  let tail : ∀ j : Fin 2, (f i).ker.toRepresentation.IntertwiningMap
      (permutationFunctionRepresentation (ZMod 2) G (X (i.succAbove j))) :=
    fun j ↦ (f (i.succAbove j)).comp (kernelInclusion (f i))
  have hi : Function.Injective (fun v j ↦ tail j v) := by
    intro v w hvw
    apply Subtype.ext
    apply hf
    funext j
    by_cases hj : j = i
    · subst j
      exact v.property.trans w.property.symm
    · obtain ⟨a, rfl⟩ := Fin.exists_succAbove_eq hj
      exact congrFun hvw a
  have hlocal : ∀ (j : Fin 2)
      (S : Subrepresentation
        (permutationFunctionRepresentation (ZMod 2) G (X (i.succAbove j)))),
      Module.finrank (ZMod 2)
        (S.toRepresentation.IntertwiningMap
          (Representation.trivial (ZMod 2) G (ZMod 2))) ≤ 2 := by
    intro j S
    have hb := twoGroup_permutationSubrepresentationHead_le_width hG 2
      (by simpa using hcard (i.succAbove j)) (x (i.succAbove j)) S
    norm_num at hb
    exact hb
  have h := representationHom_finrank_le_coordinates
    (fun j : Fin 2 ↦ X (i.succAbove j) → ZMod 2)
    (f i).ker.toRepresentation
    (fun j ↦ permutationFunctionRepresentation (ZMod 2) G (X (i.succAbove j)))
    (Representation.trivial (ZMod 2) G (ZMod 2)) (fun _ ↦ 2) hlocal tail hi
  simpa using h

/-- The extremal head identifies all three original coordinate images,
and also fixes the dimension of the original correlated source. -/
theorem range_eq_augmentation_and_finrank_eq_nine
    (hG : IsPGroup 2 G) (x : ∀ i, X i) (hcard : ∀ i, Nat.card (X i) = 4)
    (hf : Function.Injective (fun v i ↦ f i v))
    (hhead : 6 ≤ Module.finrank (ZMod 2)
      (rho.IntertwiningMap (Representation.trivial (ZMod 2) G (ZMod 2)))) :
    (∀ i, (f i).range.toSubmodule = PermutationAugmentation.space (ZMod 2) (X i)) ∧
      Module.finrank (ZMod 2) V = 9 := by
  have hrange : ∀ i, (f i).range.toSubmodule =
      PermutationAugmentation.space (ZMod 2) (X i) := by
    intro i
    have hker := coordinateKernel_head_le_four X rho f hG x hcard hf i
    have hsplit := head_finrank_le_kernel_add_range (f i)
    have htwo : 2 ≤ Module.finrank (ZMod 2)
        ((f i).range.toRepresentation.IntertwiningMap
          (Representation.trivial (ZMod 2) G (ZMod 2))) := by omega
    exact (PermutationBinaryFourAugmentation.eq_augmentation_of_head_ge_two_unconditional
      (f i).range (x i) (hcard i) htwo).2
  let F : V →ₗ[ZMod 2]
      (∀ i, PermutationAugmentation.space (ZMod 2) (X i)) :=
    { toFun := fun v i ↦ ⟨f i v, by
        rw [← hrange i]
        exact ⟨v, rfl⟩⟩
      map_add' := by
        intro v w
        funext i
        apply Subtype.ext
        exact (f i).map_add v w
      map_smul' := by
        intro c v
        funext i
        apply Subtype.ext
        exact (f i).map_smul c v }
  have hF : Function.Injective F := by
    intro v w h
    apply hf
    funext i
    exact congrArg Subtype.val (congrFun h i)
  have hdcoord : ∀ i, Module.finrank (ZMod 2)
      (PermutationAugmentation.space (ZMod 2) (X i)) = 3 := by
    intro i
    have h := PermutationAugmentation.space_finrank_add_one (k := ZMod 2) (x i)
    rw [hcard i] at h
    omega
  have hupper := F.finrank_le_finrank_of_injective hF
  have hprod : Module.finrank (ZMod 2)
      (∀ i, PermutationAugmentation.space (ZMod 2) (X i)) = 9 := by
    rw [Module.finrank_pi_fintype]
    simp only [hdcoord, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Nat.nsmul_eq_mul]
  rw [hprod] at hupper
  have hlower : 9 ≤ Module.finrank (ZMod 2) V := by
    by_contra h
    have hsmall : Module.finrank (ZMod 2) V ≤ 8 := by omega
    have hfive := twoGroup_threeFourPoint_head_le_five_of_dimension_le_eight
      hG X x hcard rho f hf hsmall
    omega
  exact ⟨hrange, Nat.le_antisymm hupper hlower⟩

/-- Every augmentation tuple has an original preimage. This is the
product conclusion justified by extremal head equality, rather than a
splitting assumption about the source. -/
theorem extremal_head_original_augmentation_cover
    (hG : IsPGroup 2 G) (x : ∀ i, X i) (hcard : ∀ i, Nat.card (X i) = 4)
    (hf : Function.Injective (fun v i ↦ f i v))
    (hhead : 6 ≤ Module.finrank (ZMod 2)
      (rho.IntertwiningMap (Representation.trivial (ZMod 2) G (ZMod 2))))
    (w : ∀ i, X i → ZMod 2)
    (hw : ∀ i, w i ∈ PermutationAugmentation.space (ZMod 2) (X i)) :
    ∃ v : V, ∀ i, f i v = w i := by
  obtain ⟨hrange, hdim⟩ := range_eq_augmentation_and_finrank_eq_nine
    X rho f hG x hcard hf hhead
  let F : V →ₗ[ZMod 2]
      (∀ i, PermutationAugmentation.space (ZMod 2) (X i)) :=
    { toFun := fun v i ↦ ⟨f i v, by
        rw [← hrange i]
        exact ⟨v, rfl⟩⟩
      map_add' := by
        intro v w
        funext i
        apply Subtype.ext
        exact (f i).map_add v w
      map_smul' := by
        intro c v
        funext i
        apply Subtype.ext
        exact (f i).map_smul c v }
  have hF : Function.Injective F := by
    intro v z h
    apply hf
    funext i
    exact congrArg Subtype.val (congrFun h i)
  have hdcoord : ∀ i, Module.finrank (ZMod 2)
      (PermutationAugmentation.space (ZMod 2) (X i)) = 3 := by
    intro i
    have h := PermutationAugmentation.space_finrank_add_one (k := ZMod 2) (x i)
    rw [hcard i] at h
    omega
  have hprod : Module.finrank (ZMod 2)
      (∀ i, PermutationAugmentation.space (ZMod 2) (X i)) = 9 := by
    rw [Module.finrank_pi_fintype]
    simp only [hdcoord, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Nat.nsmul_eq_mul]
  have honto : Function.Surjective F :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (hdim.trans hprod.symm)).mp hF
  obtain ⟨v, hv⟩ := honto (fun i ↦ ⟨w i, hw i⟩)
  exact ⟨v, fun i ↦ congrArg Subtype.val (congrFun hv i)⟩

end PermutationBinaryThreeFourAugmentation
end SymmetricSubgroupAsymptotics

end
