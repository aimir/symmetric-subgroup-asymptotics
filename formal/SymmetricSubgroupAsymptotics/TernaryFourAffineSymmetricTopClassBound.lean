import SymmetricSubgroupAsymptotics.TernaryFourAffineProperKernelClassBound
import SymmetricSubgroupAsymptotics.TernaryFourSaturatedSemidirectClassBound

/-! Every actual affine subgroup whose signed permutation projection
is S4 has at most 330 classes. Trivial, proper nontrivial, and full
translation intersections are proved separately inside the same group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.TernaryFourAffineSymmetricTopClassBound
open TernaryWreathAffineSemidirectEquiv TernarySignedWreathLinearEquiv
open TernaryFourAffineKernelCoordinates TernaryFourAffineProperKernelClassBound
open TernaryFourProperModuleSignKernel SemidirectSubgroupOverKernel

local instance : Finite (Affine (Fin 4)) :=
  Finite.of_equiv (Translation × Model (Fin 4)) SemidirectProduct.equivProd.symm

theorem class_card_le_threeThirty (L : Subgroup (Affine (Fin 4)))
    (ht : Function.Surjective (originalTopHom L)) :
    Nat.card (ConjClasses L)≤330 := by
  by_cases hfull : translationSubmodule L=⊤
  · have hN : ∀ n : Translation,
        (SemidirectProduct.inl n : Affine (Fin 4))∈L := by
      intro n
      change n.toAdd∈translationSubmodule L
      rw [hfull]
      trivial
    let R := Projected (translationAction (Fin 4)) L
    have htR : Function.Surjective (topHom R) := by
      intro s
      obtain ⟨x,hx⟩ := ht s
      exact ⟨⟨x.val.right,⟨x.val,x.property,rfl⟩⟩,hx⟩
    let e := overKernelEquiv (translationAction (Fin 4)) L hN
    letI : Finite (Translation ⋊[(translationAction (Fin 4)).comp R.subtype] R) :=
      Finite.of_equiv L e.toEquiv
    rw [conjugacyClass_card_congr e]
    exact TernaryFourSaturatedSemidirectClassBound.class_card_le_threeThirty R htR
  · by_cases hzero : translationSubmodule L=⊥
    · have hK : L.comap (SemidirectProduct.inl : Translation →* Affine (Fin 4))=⊥ := by
        ext n
        change n.toAdd∈translationSubmodule L ↔ n=1
        rw [hzero,Submodule.mem_bot]
        exact Multiplicative.toAdd.injective.eq_iff
      have hinj : Function.Injective (projection L) :=
        rightHom_injective_of_comap_bot (translationAction (Fin 4)) L hK
      let e : L ≃* (projection L).range :=
        MulEquiv.ofBijective (projection L).rangeRestrict
          ⟨fun _ _ h => hinj (congrArg Subtype.val h),
            (projection L).rangeRestrict_surjective⟩
      have htR : Function.Surjective (topHom (projection L).range) := by
        intro s
        obtain ⟨x,hx⟩ := ht s
        exact ⟨⟨projection L x,⟨x,rfl⟩⟩,hx⟩
      rw [conjugacyClass_card_congr e]
      exact (TernaryFourSignedStabilizerCapacity.subgroup_class_card_le_fortyTwo
        (projection L).range htR).trans (by decide)
    · exact (class_card_le_twoSeventy_of_nonzero_proper L ht hzero hfull).trans (by decide)

end SymmetricSubgroupAsymptotics.TernaryFourAffineSymmetricTopClassBound
