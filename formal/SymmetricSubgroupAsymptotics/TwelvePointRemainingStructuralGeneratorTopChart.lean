import SymmetricSubgroupAsymptotics.DerivedGeneratorWords
import SymmetricSubgroupAsymptotics.GeneratedLiteralImage
import SymmetricSubgroupAsymptotics.BinaryPairFrameGenerators
import SymmetricSubgroupAsymptotics.NaturalFourNormalChains

/-! One actual-generator template constructs every remaining six-pair
S4 top chart. Finite descriptors give the physical labels, a faithful
six-point S4 action, generator codes, and two source words. The original
subgroup and its exact kernel are retained throughout. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TwelvePointRemainingStructural

private theorem symmetric_codes_generate {n : ℕ} (codes : Fin n → Equiv.Perm (Fin 4))
    (cycleWord swapWord : List (Fin n))
    (hcycle : (cycleWord.map codes).prod=finRotate 4)
    (hswap : (swapWord.map codes).prod=Equiv.swap (0 : Fin 4) 1) :
    Subgroup.closure (Set.range codes)=⊤ := by
  let K := Subgroup.closure (Set.range codes)
  have word_mem (w : List (Fin n)) : (w.map codes).prod ∈ K := by
    apply K.list_prod_mem
    intro g hg
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hg
    exact Subgroup.subset_closure ⟨i,rfl⟩
  have hc : finRotate 4 ∈ K := hcycle ▸ word_mem cycleWord
  have hs : Equiv.swap (0 : Fin 4) 1 ∈ K := hswap ▸ word_mem swapWord
  have hgen : Subgroup.closure
      ({finRotate 4,Equiv.swap (0 : Fin 4) 1} : Set (Equiv.Perm (Fin 4)))=⊤ := by
    simpa only [show finRotate 4 (0 : Fin 4)=1 from rfl] using
      Equiv.Perm.closure_cycle_adjacent_swap
        (isCycle_finRotate_of_le (by decide : 2 ≤ 4))
        (support_finRotate_of_le (by decide : 2 ≤ 4)) (0 : Fin 4)
  apply top_unique
  rw [← hgen]
  apply (Subgroup.closure_le K).mpr
  intro g hg
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl
  · exact hc
  · exact hs

structure SymmetricPairGeneratorData {n : ℕ}
    (generators : Fin n → Equiv.Perm (Fin 12)) where
  points : Fin 6 × ZMod 2 ≃ Fin 12
  topEmbedding : Equiv.Perm (Fin 4) →* Equiv.Perm (Fin 6)
  top_injective : Function.Injective topEmbedding
  codes : Fin n → Equiv.Perm (Fin 4)
  cycleWord : List (Fin n)
  swapWord : List (Fin n)
  cycle_bind : (cycleWord.map codes).prod=finRotate 4
  swap_bind : (swapWord.map codes).prod=Equiv.swap (0 : Fin 4) 1
  preserves : ∀ i, BinaryPairFrame.Preserves points (generators i) (topEmbedding (codes i))

namespace SymmetricPairGeneratorData
variable {n : ℕ} {generators : Fin n → Equiv.Perm (Fin 12)}
  (D : SymmetricPairGeneratorData generators)

abbrev OriginalTop := Subgroup.closure (Set.range generators)

def frame : BinaryPairFrame (OriginalTop (generators := generators)) (Fin 6) :=
  BinaryPairFrame.ofGenerators D.points generators (fun i => D.topEmbedding (D.codes i)) D.preserves

theorem codes_generate : Subgroup.closure (Set.range D.codes)=⊤ :=
  symmetric_codes_generate D.codes D.cycleWord D.swapWord D.cycle_bind D.swap_bind

theorem top_range : D.frame.top.range=D.topEmbedding.range := by
  exact (BinaryPairFrame.ofGenerators_top_range _ _ _ D.preserves).trans
    (GeneratedLiteralImage.range_eq D.topEmbedding D.codes
      (fun i => D.topEmbedding (D.codes i)) (Equiv.refl _) D.codes_generate (fun _ => rfl)).symm

private def sourceEquiv := MonoidHom.ofInjective D.top_injective
private def rangeEquiv : D.frame.top.range ≃* D.topEmbedding.range :=
  MulEquiv.subgroupCongr D.top_range

def beta : OriginalTop (generators := generators) →* Equiv.Perm (Fin 4) :=
  (sourceEquiv D).symm.toMonoidHom.comp
    ((rangeEquiv D).toMonoidHom.comp D.frame.top.rangeRestrict)

theorem beta_surjective : Function.Surjective D.beta :=
  (sourceEquiv D).symm.surjective.comp
    ((rangeEquiv D).surjective.comp D.frame.top.rangeRestrict_surjective)

theorem beta_action (u : OriginalTop (generators := generators)) :
    D.topEmbedding (D.beta u)=D.frame.top u := by
  have h := (sourceEquiv D).apply_symm_apply ((rangeEquiv D) (D.frame.top.rangeRestrict u))
  exact congrArg Subtype.val h

theorem beta_kernel : D.beta.ker=D.frame.top.ker := by
  ext u
  change D.beta u=1 ↔ D.frame.top u=1
  constructor
  · intro h
    rw [← D.beta_action u,h,map_one]
  · intro h
    apply D.top_injective
    rw [D.beta_action,h,map_one]

theorem beta_generator (i : Fin n) : D.beta (closureGenerators generators i)=D.codes i := by
  apply D.top_injective
  rw [D.beta_action]
  exact BinaryPairFrame.ofGenerators_top_generator _ _ _ D.preserves i

end SymmetricPairGeneratorData
end SymmetricSubgroupAsymptotics.TwelvePointRemainingStructural
