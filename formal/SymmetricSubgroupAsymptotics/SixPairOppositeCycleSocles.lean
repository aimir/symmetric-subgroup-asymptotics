import SymmetricSubgroupAsymptotics.QuaternaryTripleTernaryWreathModel
import SymmetricSubgroupAsymptotics.SixPairCyclicSymmetricSocles
import SymmetricSubgroupAsymptotics.DerivedGeneratorWords

/-! A six-cycle and an opposite transposition generate C2 wreath C3.
This actual pair image is covered by the established C4 wreath C3 model,
using scalar reduction modulo two. Its all-normal bound one passes through
that surjection. The original pair-kernel bound contributes one more.
Only fixed displayed point identities are checked by finite reduction. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.SixPairOppositeCycleSocles

open SemidirectProduct

abbrev Block := QuaternaryTripleTernaryWreathModel.Block
abbrev Scalar := QuaternaryTernaryInvariantPlane.Scalar
abbrev Vector := QuaternaryTripleTernaryWreathModel.Vector
abbrev Model := QuaternaryTripleTernaryWreathModel.Model
abbrev Points := Block × ZMod 2

def reduce : Scalar →+* ZMod 2 := ZMod.castHom (show 2 ∣ 4 by decide) (ZMod 2)

def translations : Multiplicative Vector →* Equiv.Perm Points where
  toFun v :=
    { toFun := fun p => (p.1, reduce (v.toAdd p.1) + p.2)
      invFun := fun p => (p.1, -reduce (v.toAdd p.1) + p.2)
      left_inv := by intro p; apply Prod.ext <;> simp
      right_inv := by intro p; apply Prod.ext <;> simp }
  map_one' := by apply Equiv.ext; intro p; apply Prod.ext <;> simp
  map_mul' v w := by
    apply Equiv.ext
    intro p
    apply Prod.ext
    · rfl
    · change reduce (v.toAdd p.1 + w.toAdd p.1) + p.2 =
        reduce (v.toAdd p.1) + (reduce (w.toAdd p.1) + p.2)
      rw [map_add,add_assoc]

def blockShifts : Block →* Equiv.Perm Points where
  toFun c :=
    { toFun := fun p => (c * p.1,p.2)
      invFun := fun p => (c⁻¹ * p.1,p.2)
      left_inv := by intro p; apply Prod.ext <;> simp
      right_inv := by intro p; apply Prod.ext <;> simp }
  map_one' := by apply Equiv.ext; intro p; apply Prod.ext <;> simp
  map_mul' c d := by
    apply Equiv.ext
    intro p
    apply Prod.ext
    · exact mul_assoc c d p.1
    · rfl

def action : Model →* Equiv.Perm Points :=
  SemidirectProduct.lift translations blockShifts (by
    intro c
    apply MonoidHom.ext
    intro v
    apply Equiv.ext
    intro p
    apply Prod.ext <;>
      simp [translations,blockShifts,QuaternaryTripleTernaryWreathModel.rotation,
        QuaternaryTripleTernaryWreathModel.linearAction,mul_assoc])

def pairChart : Points ≃ Fin 6 where
  toFun p := if p.2 = 0 then (#[0,1,2] : Array (Fin 6))[p.1.toAdd.val]!
    else (#[3,4,5] : Array (Fin 6))[p.1.toAdd.val]!
  invFun := ![(Multiplicative.ofAdd 0,0),(Multiplicative.ofAdd 1,0),
    (Multiplicative.ofAdd 2,0),(Multiplicative.ofAdd 0,1),
    (Multiplicative.ofAdd 1,1),(Multiplicative.ofAdd 2,1)]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def literalAction : Model →* Equiv.Perm (Fin 6) :=
  pairChart.permCongrHom.toMonoidHom.comp action

def cycleModel : Model :=
  inl (Multiplicative.ofAdd (Pi.single (1 : Block) (1 : Scalar))) *
    inr (Multiplicative.ofAdd 1)

def oppositeModel : Model :=
  inl (Multiplicative.ofAdd (Pi.single (Multiplicative.ofAdd 2 : Block) (1 : Scalar)))

abbrev cycle := SixPairCyclicSymmetricSocles.cycle
def opposite : Equiv.Perm (Fin 6) := Equiv.swap 2 5

theorem cycleModel_action : literalAction cycleModel = cycle := by decide +kernel
theorem oppositeModel_action : literalAction oppositeModel = opposite := by decide +kernel

theorem modelGenerator_zero :
    literalAction (QuaternaryTripleTernaryWreathModel.modelGenerators 0) =
      cycle * opposite * cycle⁻¹ := by decide +kernel

theorem modelGenerator_one :
    literalAction (QuaternaryTripleTernaryWreathModel.modelGenerators 1) =
      cycle * opposite := by decide +kernel

theorem range_le (K : Subgroup (Equiv.Perm (Fin 6)))
    (hc : cycle ∈ K) (hs : opposite ∈ K) : literalAction.range ≤ K := by
  have hgen : Subgroup.closure (Set.range QuaternaryTripleTernaryWreathModel.modelGenerators) ≤
      K.comap literalAction := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    change literalAction (QuaternaryTripleTernaryWreathModel.modelGenerators i) ∈ K
    fin_cases i
    · change literalAction (QuaternaryTripleTernaryWreathModel.modelGenerators 0) ∈ K
      rw [modelGenerator_zero]
      exact K.mul_mem (K.mul_mem hc hs) (K.inv_mem hc)
    · change literalAction (QuaternaryTripleTernaryWreathModel.modelGenerators 1) ∈ K
      rw [modelGenerator_one]
      exact K.mul_mem hc hs
  rw [QuaternaryTripleTernaryWreathModel.model_generated] at hgen
  rintro _ ⟨g,rfl⟩
  exact hgen (Subgroup.mem_top g)

theorem generated_range {ι : Type*} (codes : ι → Model) (ci si : ι)
    (hc : literalAction (codes ci) = cycle)
    (hs : literalAction (codes si) = opposite) :
    Subgroup.closure (Set.range (fun i => literalAction (codes i))) = literalAction.range := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    exact ⟨codes i,rfl⟩
  · apply range_le
    · rw [← hc]
      exact Subgroup.subset_closure ⟨ci,rfl⟩
    · rw [← hs]
      exact Subgroup.subset_closure ⟨si,rfl⟩

theorem image_normalGen (L : Subgroup literalAction.range) (hL : L.Normal) :
    MarkedC4.normalGen L ≤ 1 := by
  letI := hL
  obtain ⟨x,hx⟩ := normal_generating_tuples_of_surjective
    (literalAction.rangeRestrict.comp QuaternaryTripleTernaryWreathModel.sourceMap)
    (literalAction.rangeRestrict_surjective.comp QuaternaryTripleTernaryWreathModel.sourceMap_surjective)
    QuaternaryTripleTernaryNormalGenerators.normal_generating_singletons L hL
  exact normalGen_le_of_fin_tuple x hx

theorem quotientSocle {U : Subgroup (Equiv.Perm (Fin 12))}
    (F : BinaryPairFrame U (Fin 6)) (g : U) (hg : F.top g = cycle)
    (himage : F.top.range = literalAction.range)
    (N : Subgroup U) [N.Normal] : SocleNormalGeneratorBound (U ⧸ N) 2 := by
  apply F.quotientSocle_of_uniform_pair_action 1 1
    (SixPairCyclicSymmetricSocles.uniform F g hg) ?_ N
  intro L hL
  letI := hL
  let e : F.top.range ≃* literalAction.range := MulEquiv.subgroupCongr himage
  exact CoprimeKernelQuotientSocles.normalGen_image_bound
    e.symm.toMonoidHom e.symm.surjective 1 image_normalGen L

theorem quotientSocle_of_generators {ι : Type*} (frame : Fin 6 × ZMod 2 ≃ Fin 12)
    (generators : ι → Equiv.Perm (Fin 12)) (codes : ι → Model) (ci si : ι)
    (hc : literalAction (codes ci) = cycle)
    (hs : literalAction (codes si) = opposite)
    (hp : ∀ i, BinaryPairFrame.Preserves frame (generators i) (literalAction (codes i)))
    (N : Subgroup (Subgroup.closure (Set.range generators))) [N.Normal] :
    SocleNormalGeneratorBound ((Subgroup.closure (Set.range generators)) ⧸ N) 2 := by
  let F := BinaryPairFrame.ofGenerators frame generators (fun i => literalAction (codes i)) hp
  apply quotientSocle F (closureGenerators generators ci)
    ((BinaryPairFrame.ofGenerators_top_generator _ _ _ hp ci).trans hc) ?_ N
  exact (BinaryPairFrame.ofGenerators_top_range _ _ _ hp).trans (generated_range codes ci si hc hs)

end SymmetricSubgroupAsymptotics.SixPairOppositeCycleSocles

end
