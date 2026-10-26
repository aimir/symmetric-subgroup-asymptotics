import SymmetricSubgroupAsymptotics.TernaryFourAffineKernelCoordinates
import SymmetricSubgroupAsymptotics.TernaryFourProperModuleSignKernel
import SymmetricSubgroupAsymptotics.FourPointPermutationClassBound

/-! A nonzero proper translation intersection gives at most 270 classes
in the ORIGINAL affine subgroup. The proof factors its actual top kernel
through its own signed projection: translation capacity 27, sign-kernel
capacity 2, and four-point top class capacity 5. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.TernaryFourAffineProperKernelClassBound
open TernaryWreathAffineSemidirectEquiv TernarySignedWreathLinearEquiv
open TernaryFourAffineKernelCoordinates TernaryFourProperModuleSignKernel

local instance : Finite (Affine (Fin 4)) :=
  Finite.of_equiv (Translation × Model (Fin 4)) SemidirectProduct.equivProd.symm

def originalTopHom (L : Subgroup (Affine (Fin 4))) : L →* Equiv.Perm (Fin 4) :=
  (permutationHom (Fin 4)).comp (projection L)

theorem class_card_le_twoSeventy_of_nonzero_proper
    (L : Subgroup (Affine (Fin 4)))
    (ht : Function.Surjective (originalTopHom L))
    (hne : translationSubmodule L≠⊥) (hproper : translationSubmodule L≠⊤) :
    Nat.card (ConjClasses L)≤270 := by
  let π := projection L
  let R := π.range
  let ψ := originalTopHom L
  let T := ψ.ker
  let f : T →* R := π.rangeRestrict.comp T.subtype
  have htR : Function.Surjective (topHom R) := by
    intro s
    obtain ⟨x,hx⟩ := ht s
    exact ⟨⟨π x,⟨x,rfl⟩⟩,hx⟩
  have hJ : Nat.card (topHom R).ker≤2 :=
    kernel_card_le_two R htR (translationSubmodule L) hne hproper
      (projected_preserves_submodule L)
  let e : f.ker → π.ker := fun x => ⟨x.val.val,
    congrArg (fun r : R => r.val) x.property⟩
  have he : Function.Injective e := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : π.ker => z.val) hxy
  have hfker : Nat.card f.ker≤27 := by
    calc
      _≤Nat.card π.ker := Nat.card_le_card_of_injective e he
      _≤Nat.card (L.comap (SemidirectProduct.inl : Translation →* Affine (Fin 4))) :=
        AbelianSemidirectSubgroupCentralizerBound.kernel_card_le_intersection
          (translationAction (Fin 4)) L
      _≤27 := translation_card_le_twentySeven L hproper
  let a : f.range → (topHom R).ker := fun r => ⟨r.val,by
    obtain ⟨x,hx⟩ := r.property
    change topHom R r.val=1
    rw [←hx]
    exact x.property⟩
  have ha : Function.Injective a := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : (topHom R).ker => z.val) hxy
  have hfrange : Nat.card f.range≤2 :=
    (Nat.card_le_card_of_injective a ha).trans hJ
  have hT : Nat.card (ConjClasses T)≤54 := by
    have hk : Nat.card (ConjClasses f.ker)≤27 :=
      (Nat.card_le_card_of_surjective (@ConjClasses.mk f.ker _)
        ConjClasses.mk_surjective).trans hfker
    have hr : Nat.card (ConjClasses f.range)≤2 :=
      (Nat.card_le_card_of_surjective (@ConjClasses.mk f.range _)
        ConjClasses.mk_surjective).trans hfrange
    exact (conjugacyClass_card_le_kernel_mul_range f).trans
      (by simpa using Nat.mul_le_mul hk hr)
  have htop : Nat.card (ConjClasses ψ.range)≤5 :=
    FourPointPermutationClassBound.subgroup_class_card_le_five ψ.range
  exact (conjugacyClass_card_le_kernel_mul_range ψ).trans
    (by simpa using Nat.mul_le_mul hT htop)

end SymmetricSubgroupAsymptotics.TernaryFourAffineProperKernelClassBound
