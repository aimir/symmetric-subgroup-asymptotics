import SymmetricSubgroupAsymptotics.CFSGCliffordIsotypicTransport

/-! The actual ambient group permutes the canonical isotypic components
of its normal restriction. Its literal kernel fixes every original
component; no block action is supplied as a hypothesis. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics.CFSGCliffordIsotypicPermutation
open CFSGCliffordIsotypicTransport

variable {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
  (rho : Representation k G V) (H : Subgroup G) [H.Normal]

abbrev Components := isotypicComponents k[H] (restricted rho H).asModule

def componentMap (g : G) (C : Components rho H) : Components rho H :=
  ⟨latticeConjugation rho H g C.1, by
    obtain ⟨S, hs, he⟩ := C.2
    refine ⟨latticeConjugation rho H g S, ?_, ?_⟩
    · apply isSimpleModule_iff_isAtom.mpr
      exact ((latticeConjugation rho H g).isAtom_iff S).mpr
        (isSimpleModule_iff_isAtom.mp hs)
    · rw [he, latticeConjugation_isotypicComponent]⟩

theorem componentMap_one (C : Components rho H) : componentMap rho H 1 C = C := by
  apply Subtype.ext
  exact latticeConjugation_one rho H C.1

theorem componentMap_mul (g h : G) (C : Components rho H) :
    componentMap rho H (g * h) C = componentMap rho H g (componentMap rho H h C) := by
  apply Subtype.ext
  exact latticeConjugation_mul rho H g h C.1

def componentPermutation (g : G) : Equiv.Perm (Components rho H) where
  toFun := componentMap rho H g
  invFun := componentMap rho H g⁻¹
  left_inv C := by
    rw [← componentMap_mul, inv_mul_cancel, componentMap_one]
  right_inv C := by
    rw [← componentMap_mul, mul_inv_cancel, componentMap_one]

def componentPermutationHom : G →* Equiv.Perm (Components rho H) where
  toFun := componentPermutation rho H
  map_one' := by
    apply Equiv.ext
    exact componentMap_one rho H
  map_mul' g h := by
    apply Equiv.ext
    exact componentMap_mul rho H g h

theorem kernel_fixes_component (g : G) (hg : g ∈ (componentPermutationHom rho H).ker)
    (C : Components rho H) : latticeConjugation rho H g C.1 = C.1 := by
  have he := congrArg (fun f : Equiv.Perm (Components rho H) => f C)
    (MonoidHom.mem_ker.mp hg)
  exact congrArg Subtype.val he

end SymmetricSubgroupAsymptotics.CFSGCliffordIsotypicPermutation
