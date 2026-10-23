import SymmetricSubgroupAsymptotics.CFSGTrialityGeckSectionParameterRanges
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateExactHeightLayer

/-! All actual positive D4 roots indexed by the literal word parameters
of the fixed sections. The only reindexing is the proved cycle in the
top short triple. Exact-height restriction is an actual equivalence. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckWordRootIndex
open CFSGTrialityD4PositiveRootOrbits CFSGTrialityD4PositiveRootIndex
open CFSGTrialityGeckSectionRootLabels CFSGTrialityGeckSectionParameterRanges
open CFSGTrialityGeckSectionHeightMembership CFSGNormTwoCoordinateExactHeightLayer
open CFSGIntegerHeightSign

def cycleEquiv : Equiv.Perm (Fin 3) := Equiv.ofBijective cycle (by decide)

def wordIndexPermutation : Equiv.Perm OrbitIndex where
  toFun
    | Sum.inl s => Sum.inl s
    | Sum.inr (s,k) => Sum.inr (s, if s = 2 then cycleEquiv k else k)
  invFun
    | Sum.inl s => Sum.inl s
    | Sum.inr (s,k) => Sum.inr (s, if s = 2 then cycleEquiv.symm k else k)
  left_inv := by
    rintro (s | ⟨s,k⟩)
    · rfl
    · by_cases hs : s = 2 <;> simp [hs]
  right_inv := by
    rintro (s | ⟨s,k⟩)
    · rfl
    · by_cases hs : s = 2 <;> simp [hs]

def wordPositiveRoot : OrbitIndex → CFSGTrialityD4PositiveRootIndex.Positive
  | Sum.inl s => ⟨longRoot s, long_positive s⟩
  | Sum.inr (s,k) => ⟨shortLabel s k, short_label_positive s k⟩

theorem wordPositiveRoot_reindex (a : OrbitIndex) :
    wordPositiveRoot a = positiveRoot (wordIndexPermutation a) := by
  rcases a with s | ⟨s,k⟩
  · rfl
  · fin_cases s <;> rfl

theorem wordPositiveRoot_bijective : Function.Bijective wordPositiveRoot := by
  have he : wordPositiveRoot = positiveRoot ∘ wordIndexPermutation :=
    funext wordPositiveRoot_reindex
  rw [he]
  have hp : Function.Bijective positiveRoot := ⟨positiveRoot_injective, positiveRoot_surjective⟩
  exact hp.comp wordIndexPermutation.bijective

def wordPositiveRootEquiv : OrbitIndex ≃ CFSGTrialityD4PositiveRootIndex.Positive :=
  Equiv.ofBijective wordPositiveRoot wordPositiveRoot_bijective

abbrev WordHeightIndex (h : ℤ) :=
  {a : OrbitIndex // height (wordPositiveRoot a).val.val = h}

def wordHeightEquiv (h : ℤ) : WordHeightIndex h ≃ ExactHeightRoot (CartanMatrix.D 4) h where
  toFun a := ⟨wordPositiveRoot a.val, a.property⟩
  invFun k := ⟨wordPositiveRootEquiv.symm k.val, by
    change height (wordPositiveRoot (wordPositiveRootEquiv.symm k.val)).val.val = h
    rw [show wordPositiveRoot (wordPositiveRootEquiv.symm k.val) = k.val from
      wordPositiveRootEquiv.apply_symm_apply k.val]
    exact k.property⟩
  left_inv a := Subtype.ext (wordPositiveRootEquiv.symm_apply_apply a.val)
  right_inv k := Subtype.ext (wordPositiveRootEquiv.apply_symm_apply k.val)

def wordParameterEquiv (K : Type) [Field K] [Finite K] :
    (a : OrbitIndex) → K ≃ RootLine K (wordPositiveRoot a).val
  | Sum.inl s => longParameterEquiv K s
  | Sum.inr (s,k) => shortParameterEquiv K s k

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckWordRootIndex
