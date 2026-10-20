import SymmetricSubgroupAsymptotics.TernaryLocalWreathNormalGenerators
import SymmetricSubgroupAsymptotics.C2WreathGeneration
import SymmetricSubgroupAsymptotics.SixPairCyclicSymmetricSocles
import SymmetricSubgroupAsymptotics.BinarySixPointSymmetricMatrixBlocks

/-! The full two-block ternary local wreath image on six physical pairs.
The explicit image cover carries the all-normal bound two. Its pair
permutation module contains the operators of the regular S3 matrix-block
argument and has uniform bound one. The original correlated pair kernel
therefore gives quotient-socle bound three. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.SixPairLocalWreathSocles

open SemidirectProduct

abbrev Local := TernaryLocalWreathNormalGenerators.Local
abbrev Model := TernaryLocalWreathNormalGenerators.Model
abbrev translation := TernaryLocalWreathNormalGenerators.localTranslation
abbrev reflection := TernaryLocalWreathNormalGenerators.localReflection

def localAction : Local →* Equiv.Perm (ZMod 3) where
  toFun g :=
    { toFun := fun x => g.left.toAdd + if g.right = 1 then x else -x
      invFun := fun x => if g.right = 1 then x - g.left.toAdd else g.left.toAdd - x
      left_inv := by
        intro x
        rcases g with ⟨v,b⟩
        revert v b x
        decide +kernel
      right_inv := by
        intro x
        rcases g with ⟨v,b⟩
        revert v b x
        decide +kernel }
  map_one' := by apply Equiv.ext; intro x; revert x; decide +kernel
  map_mul' := by
    rintro ⟨v,b⟩ ⟨w,c⟩
    apply Equiv.ext
    intro x
    revert v b w c x
    decide +kernel

def pairChart : ZMod 3 ⊕ ZMod 3 ≃ Fin 6 where
  toFun
    | .inl x => (#[1,3,5] : Array (Fin 6))[x.val]!
    | .inr x => (#[0,2,4] : Array (Fin 6))[x.val]!
  invFun := ![.inr 0, .inl 0, .inr 1, .inl 1, .inr 2, .inl 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def literalAction : Model →* Equiv.Perm (Fin 6) :=
  pairChart.permCongrHom.toMonoidHom.comp (C2Wreath.action localAction)

def firstTranslation : Model := C2Wreath.firstFactor translation
def firstReflection : Model := C2Wreath.firstFactor reflection
def blockSwap : Model := inr C2Wreath.gen

theorem local_decomposition (g : Local) :
    g = translation ^ g.left.toAdd.val * reflection ^ g.right.toAdd.val := by
  rcases g with ⟨v,b⟩
  revert v b
  decide +kernel

theorem range_le (K : Subgroup (Equiv.Perm (Fin 6)))
    (ht : literalAction firstTranslation ∈ K)
    (hr : literalAction firstReflection ∈ K)
    (hs : literalAction blockSwap ∈ K) : literalAction.range ≤ K := by
  have hfirst (a : Local) : C2Wreath.firstFactor a ∈ K.comap literalAction := by
    rw [local_decomposition a, map_mul, map_pow, map_pow]
    exact (K.comap literalAction).mul_mem
      ((K.comap literalAction).pow_mem ht a.left.toAdd.val)
      ((K.comap literalAction).pow_mem hr a.right.toAdd.val)
  rintro _ ⟨g,rfl⟩
  exact C2Wreath.mem_of_first_and_swap (K.comap literalAction) hfirst hs g

theorem generated_range {ι : Type*} (codes : ι → Model)
    (ht : literalAction firstTranslation ∈
      Subgroup.closure (Set.range (fun i => literalAction (codes i))))
    (hr : literalAction firstReflection ∈
      Subgroup.closure (Set.range (fun i => literalAction (codes i))))
    (hs : literalAction blockSwap ∈
      Subgroup.closure (Set.range (fun i => literalAction (codes i)))) :
    Subgroup.closure (Set.range (fun i => literalAction (codes i))) = literalAction.range := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    exact ⟨codes i,rfl⟩
  · exact range_le _ ht hr hs

def regularRotation : Model := inl (translation,translation)
def regularReflection : Model :=
  inl (translation ^ 2 * reflection,translation ^ 2 * reflection) * blockSwap

theorem regularRotation_action : literalAction regularRotation =
    BinarySixPointSymmetricMatrixBlocks.rotation := by decide +kernel

theorem regularReflection_action : literalAction regularReflection =
    BinarySixPointSymmetricMatrixBlocks.reflection := by decide +kernel

theorem image_normalGen (L : Subgroup literalAction.range) (hL : L.Normal) :
    MarkedC4.normalGen L ≤ 2 := by
  letI := hL
  obtain ⟨x,hx⟩ := normal_generating_tuples_of_surjective literalAction.rangeRestrict
    literalAction.rangeRestrict_surjective TernaryLocalWreathNormalGenerators.normal_generating_pairs L hL
  exact normalGen_le_of_fin_tuple x hx

theorem quotientSocle {U : Subgroup (Equiv.Perm (Fin 12))}
    (F : BinaryPairFrame U (Fin 6)) (himage : F.top.range = literalAction.range)
    (N : Subgroup U) [N.Normal] : SocleNormalGeneratorBound (U ⧸ N) 3 := by
  let c : F.top.range := ⟨literalAction regularRotation, by rw [himage]; exact ⟨_,rfl⟩⟩
  let b : F.top.range := ⟨literalAction regularReflection, by rw [himage]; exact ⟨_,rfl⟩⟩
  apply F.quotientSocle_of_uniform_pair_action 1 2
    (BinarySixPointSymmetricMatrixBlocks.uniform_subgroup F.top.range c b
      regularRotation_action regularReflection_action) ?_ N
  intro L hL
  letI := hL
  let e : F.top.range ≃* literalAction.range := MulEquiv.subgroupCongr himage
  exact CoprimeKernelQuotientSocles.normalGen_image_bound
    e.symm.toMonoidHom e.symm.surjective 2 image_normalGen L

end SymmetricSubgroupAsymptotics.SixPairLocalWreathSocles

end
