import SymmetricSubgroupAsymptotics.BinaryFourTrivialSectionBottom

/-! Factor an actual Klein-trivial target map through the original
submodule's literal middle-coordinate quotient. No complement is chosen
in E, its target, or the original group extension. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryFourBlockAugmentation

def encodeLinear : Module →ₗ[Scalar] Coordinates where
  toFun := encode
  map_add' := by intro x y; ext i; fin_cases i <;> simp [encode] <;> ring
  map_smul' := by intro a x; ext i; fin_cases i <;> simp [encode] <;> ring

def submoduleMiddleMap (E : Submodule Scalar Module) : E →ₗ[Scalar] Middle :=
  middleProjection.comp (encodeLinear.comp E.subtype)

theorem middle_kernel_diagonal (w : Module)
    (hw : ambientAugmentation w = 0)
    (hm : middleProjection (encode w) = 0) :
    ∃ a : Local, w = diagonal a := by
  have exactIdentity : ∀ w : Module, ambientAugmentation w = 0 →
      middleProjection (encode w) = 0 → w = diagonal (w 0) := by
    decide +kernel
  exact ⟨w 0, exactIdentity w hw hm⟩

/-- This quotient is taken from E itself. Its exact middle-coordinate
map embeds it into Middle by the first isomorphism theorem. -/
theorem klein_trivial_map_factors_middle
    (E : Submodule Scalar Module) (hproper : E ≠ ⊤)
    (hU : ∀ w ∈ E, ambientDifferenceU w ∈ E)
    (hV : ∀ w ∈ E, ambientDifferenceV w ∈ E)
    (hC : ∀ w ∈ E, ambientCycle w ∈ E)
    (w : Module) (hw : w ∈ E) (hnotbottom : ¬ ∃ a : Local, w = diagonal a)
    {W : Type} [AddCommGroup W] [_root_.Module Scalar W]
    (f : E →ₗ[Scalar] W) (T : W →ₗ[Scalar] W)
    (hfU : ∀ x : E, f ⟨ambientDifferenceU x, hU x x.2⟩ = 0)
    (hfV : ∀ x : E, f ⟨ambientDifferenceV x, hV x x.2⟩ = 0)
    (hfC : ∀ x : E, f ⟨ambientCycle x, hC x x.2⟩ = T (f x)) :
    ∃ g : (E ⧸ LinearMap.ker (submoduleMiddleMap E)) →ₗ[Scalar] W,
      g.comp (LinearMap.ker (submoduleMiddleMap E)).mkQ = f := by
  have hrad := proper_submodule_le_augmentation_kernel E hproper hU hV hC
  have hker : LinearMap.ker (submoduleMiddleMap E) ≤ LinearMap.ker f := by
    intro x hx
    obtain ⟨a, ha⟩ := middle_kernel_diagonal x (hrad x.2) hx
    obtain ⟨hdiag, hfdiag⟩ := klein_trivial_map_kills_diagonal
      E hU hV hC w hw hnotbottom f T hfU hfV hfC a
    have hxeq : x = (⟨diagonal a, hdiag⟩ : E) := Subtype.ext ha
    change f x = 0
    rw [hxeq]
    exact hfdiag
  refine ⟨(LinearMap.ker (submoduleMiddleMap E)).liftQ f hker, ?_⟩
  ext x
  rfl

end SymmetricSubgroupAsymptotics.BinaryFourBlockAugmentation

end
