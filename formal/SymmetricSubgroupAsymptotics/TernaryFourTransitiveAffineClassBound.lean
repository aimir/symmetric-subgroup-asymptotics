import SymmetricSubgroupAsymptotics.TernaryFourAffineProperKernelClassBound
import SymmetricSubgroupAsymptotics.TernaryFourTransitiveProperKernelCapacity
import SymmetricSubgroupAsymptotics.TernaryFourTransitiveSemidirectClassBound

/-! All translation intersections are retained for a transitive signed
four-coordinate action. The proper case uses the coupled |W|*|E|≤54,
not independent maxima; the full case keeps the same projected subgroup
and its checked 360-class semidirect extension. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.TernaryFourTransitiveAffineClassBound
open TernaryWreathAffineSemidirectEquiv TernarySignedWreathLinearEquiv
open TernaryFourAffineKernelCoordinates TernaryFourAffineProperKernelClassBound
open TernaryFourProperModuleSignKernel SemidirectSubgroupOverKernel

local instance : Finite (Affine (Fin 4)) :=
  Finite.of_equiv (Translation × Model (Fin 4)) SemidirectProduct.equivProd.symm

theorem class_card_le_twoSeventy_of_nonzero_proper
    (L : Subgroup (Affine (Fin 4)))
    (htrans : ∀ i j : Fin 4,∃g : L,originalTopHom L g i=j)
    (hne : translationSubmodule L≠⊥) (hproper : translationSubmodule L≠⊤) :
    Nat.card (ConjClasses L)≤270 := by
  let π := projection L
  let R := π.range
  let ψ := originalTopHom L
  let T := ψ.ker
  let f : T →* R := π.rangeRestrict.comp T.subtype
  have htR : ∀ i j : Fin 4,∃g : R,topHom R g i=j := by
    intro i j
    obtain ⟨x,hx⟩ := htrans i j
    exact ⟨⟨π x,⟨x,rfl⟩⟩,hx⟩
  have hproduct : Nat.card (translationSubmodule L)*Nat.card (topHom R).ker≤54 :=
    TernaryFourTransitiveProperKernelCapacity.module_card_mul_sign_kernel_card_le_fiftyFour
      R htR (translationSubmodule L) hne hproper (projected_preserves_submodule L)
  let e : f.ker → π.ker := fun x => ⟨x.val.val,
    congrArg (fun r : R => r.val) x.property⟩
  have he : Function.Injective e := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : π.ker => z.val) hxy
  have hfker : Nat.card f.ker≤Nat.card (translationSubmodule L) := by
    calc
      _≤Nat.card π.ker := Nat.card_le_card_of_injective e he
      _≤Nat.card (L.comap (SemidirectProduct.inl : Translation →* Affine (Fin 4))) :=
        AbelianSemidirectSubgroupCentralizerBound.kernel_card_le_intersection
          (translationAction (Fin 4)) L
      _=Nat.card (translationSubmodule L) :=
        Nat.card_congr (TernaryFourAffineKernelCoordinates.translationEquiv L)
  let a : f.range → (topHom R).ker := fun r => ⟨r.val,by
    obtain ⟨x,hx⟩ := r.property
    change topHom R r.val=1
    rw [←hx]
    exact x.property⟩
  have ha : Function.Injective a := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : (topHom R).ker => z.val) hxy
  have hfrange : Nat.card f.range≤Nat.card (topHom R).ker :=
    Nat.card_le_card_of_injective a ha
  have hT : Nat.card (ConjClasses T)≤54 := by
    have hk : Nat.card (ConjClasses f.ker)≤Nat.card (translationSubmodule L) :=
      (Nat.card_le_card_of_surjective (@ConjClasses.mk f.ker _)
        ConjClasses.mk_surjective).trans hfker
    have hr : Nat.card (ConjClasses f.range)≤Nat.card (topHom R).ker :=
      (Nat.card_le_card_of_surjective (@ConjClasses.mk f.range _)
        ConjClasses.mk_surjective).trans hfrange
    exact (conjugacyClass_card_le_kernel_mul_range f).trans
      ((Nat.mul_le_mul hk hr).trans hproduct)
  have htop : Nat.card (ConjClasses ψ.range)≤5 :=
    FourPointPermutationClassBound.subgroup_class_card_le_five ψ.range
  exact (conjugacyClass_card_le_kernel_mul_range ψ).trans
    (by simpa using Nat.mul_le_mul hT htop)

theorem class_card_le_threeSixty (L : Subgroup (Affine (Fin 4)))
    (htrans : ∀ i j : Fin 4,∃g : L,originalTopHom L g i=j)
    (hQ : Nat.card (originalTopHom L).range≤8) :
    Nat.card (ConjClasses L)≤360 := by
  by_cases hfull : translationSubmodule L=⊤
  · have hN : ∀ n : Translation,
        (SemidirectProduct.inl n : Affine (Fin 4))∈L := by
      intro n
      change n.toAdd∈translationSubmodule L
      rw [hfull]
      trivial
    let R := Projected (translationAction (Fin 4)) L
    have htR : ∀ i j : Fin 4,∃g : R,topHom R g i=j := by
      intro i j
      obtain ⟨x,hx⟩ := htrans i j
      exact ⟨⟨x.val.right,⟨x.val,x.property,rfl⟩⟩,hx⟩
    have heq : (topHom R).range=(originalTopHom L).range := by
      ext s
      constructor
      · rintro ⟨r,hr⟩
        obtain ⟨u,hu,hur⟩ := r.property
        refine ⟨⟨u,hu⟩,?_⟩
        change permutationHom (Fin 4) u.right=s
        have he : u.right=r.val := hur
        rw [he]
        exact hr
      · rintro ⟨u,hu⟩
        exact ⟨⟨u.val.right,⟨u.val,u.property,rfl⟩⟩,hu⟩
    have hQR : Nat.card (topHom R).range≤8 := by rw [heq]; exact hQ
    let e := overKernelEquiv (translationAction (Fin 4)) L hN
    letI : Finite (Translation ⋊[(translationAction (Fin 4)).comp R.subtype] R) :=
      Finite.of_equiv L e.toEquiv
    rw [conjugacyClass_card_congr e]
    exact TernaryFourTransitiveSemidirectClassBound.class_card_le_threeSixty R htR hQR
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
          ⟨fun _ _ h => hinj (congrArg Subtype.val h),(projection L).rangeRestrict_surjective⟩
      have htR : ∀ i j : Fin 4,∃g : (projection L).range,topHom (projection L).range g i=j := by
        intro i j
        obtain ⟨x,hx⟩ := htrans i j
        exact ⟨⟨projection L x,⟨x,rfl⟩⟩,hx⟩
      rw [conjugacyClass_card_congr e]
      exact (TernaryFourTransitiveSignedClassBound.class_card_le_fortyTwo
        (projection L).range htR).trans (by decide)
    · exact (class_card_le_twoSeventy_of_nonzero_proper L htrans hzero hfull).trans (by decide)

end SymmetricSubgroupAsymptotics.TernaryFourTransitiveAffineClassBound
