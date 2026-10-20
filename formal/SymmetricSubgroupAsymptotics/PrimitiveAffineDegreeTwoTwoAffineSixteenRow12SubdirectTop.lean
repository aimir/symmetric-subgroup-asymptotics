import SymmetricSubgroupAsymptotics.BinaryDiagonalSwapSubdirect
import SymmetricSubgroupAsymptotics.BinaryDiagonalSwapAffine
import SymmetricSubgroupAsymptotics.BinarySingerAffineWreathGeneration
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwoAffineSixteenRow13SwapTop

/-!
# The literal row12 inside the common-linear two-block model

The generated subgroup is retained exactly. Its first block-stabilizer
projection is onto the actual local affine group, and it contains the
pure swap and all diagonal translations. These facts suffice for the
subdirect dichotomy, without deciding which fiber alternative occurs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwoAffineSixteenRow12SubdirectTop

open SemidirectProduct
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open PrimitiveAffineDegreeTwoPairedEightAffineTops

abbrev R := Row20.linearGroup
abbrev V := Multiplicative Vector
abbrev φ := AffineModel.linAut R
abbrev FullModel := BinaryDiagonalSwap.Model φ
abbrev Local := AffineModel.Aff R
abbrev Top := DegreeTwoTwoAffineSixteenInterfaces.row12.top

abbrev vector := PrimitiveAffineDegreeTwoTwoAffineSixteenRow13SwapTop.vector
abbrev transvection := PrimitiveAffineDegreeTwoTwoAffineSixteenRow13SwapTop.transvection
abbrev coordinateRotation := PrimitiveAffineDegreeTwoTwoAffineSixteenRow13SwapTop.coordinateRotation
abbrev singerElement := PrimitiveAffineDegreeTwoTwoAffineSixteenRow13SwapTop.singerElement
abbrev swapElement := PrimitiveAffineDegreeTwoTwoAffineSixteenRow13SwapTop.swapElement
abbrev fullAction := PrimitiveAffineDegreeTwoTwoAffineSixteenRow13SwapTop.literalAction

def modelGenerators : Fin 6 → FullModel :=
  ![inl (vector 1, vector 1), inl (vector 2, vector 2), inl (vector 4, vector 4),
    ⟨(1, vector 3), (transvection, 1)⟩,
    ⟨(1, vector 6), (coordinateRotation, 1)⟩,
    inr (1, C2Wreath.gen)]

def modelGroup : Subgroup FullModel := Subgroup.closure (Set.range modelGenerators)
abbrev Model := modelGroup

theorem generator_mem (i : Fin 6) : modelGenerators i ∈ modelGroup :=
  Subgroup.subset_closure (Set.mem_range_self i)

def literalAction : Model →* Equiv.Perm (Fin 16) := fullAction.comp modelGroup.subtype

theorem literalAction_injective : Function.Injective literalAction :=
  PrimitiveAffineDegreeTwoTwoAffineSixteenRow13SwapTop.literalAction_injective.comp
    Subtype.val_injective

theorem generators_binding (i : Fin 6) :
    fullAction (modelGenerators i) = DegreeTwoTwoAffineSixteenInterfaces.row12Generators i := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

theorem action_range : literalAction.range = Top := by
  have hle : modelGroup ≤ Top.comap fullAction := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    change fullAction (modelGenerators i) ∈ Top
    rw [generators_binding]
    exact Subgroup.subset_closure (Set.mem_range_self i)
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    exact hle g.property
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨⟨modelGenerators i, generator_mem i⟩, generators_binding i⟩

def modelEquiv : Model ≃* Top :=
  (MonoidHom.ofInjective (f := literalAction) literalAction_injective).trans
    (MulEquiv.subgroupCongr action_range)

abbrev Even := BinaryDiagonalSwapSubdirect.Even φ modelGroup
abbrev first := BinaryDiagonalSwapSubdirect.first φ modelGroup

/-- The first five original generators preserve the two blocks. -/
def evenGenerator (i : Fin 5) : Even :=
  ⟨⟨modelGenerators i.castSucc, generator_mem i.castSucc⟩, by
    fin_cases i <;> rfl⟩

theorem first_even_translation :
    first (evenGenerator 0) = inl (Multiplicative.ofAdd firstVector) := rfl

theorem first_even_transvection : first (evenGenerator 3) = inr transvection := rfl

theorem first_even_rotation : first (evenGenerator 4) = inr coordinateRotation := rfl

theorem singer_word : transvection * coordinateRotation ^ 2 = singerElement := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  revert v
  decide +kernel

theorem swap_word : (singerElement ^ 4)⁻¹ * transvection * singerElement ^ 4 = swapElement := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  revert v
  decide +kernel

theorem first_surjective : Function.Surjective first := by
  let K : Subgroup Local := first.range
  have ht : (inl (Multiplicative.ofAdd firstVector) : Local) ∈ K :=
    ⟨evenGenerator 0, first_even_translation⟩
  have hT : (inr transvection : Local) ∈ K :=
    ⟨evenGenerator 3, first_even_transvection⟩
  have hR : (inr coordinateRotation : Local) ∈ K :=
    ⟨evenGenerator 4, first_even_rotation⟩
  have hs : (inr singerElement : Local) ∈ K := by
    rw [← singer_word, map_mul, map_pow]
    exact K.mul_mem hT (K.pow_mem hR 2)
  have hb : (inr swapElement : Local) ∈ K := by
    rw [← swap_word]
    simp only [map_mul, map_inv, map_pow]
    exact K.mul_mem (K.mul_mem (K.inv_mem (K.pow_mem hs 4)) hT) (K.pow_mem hs 4)
  have hlinear (r : R) : (inr r : Local) ∈ K := by
    apply BinaryDiagonalSwap.hom_mem_of_closure_generators Row20.linearGenerators
      (inr : R →* Local) K _ r
    intro i
    fin_cases i
    · exact hs
    · exact hb
  intro g
  exact BinarySingerAffineWreathGeneration.local_mem_of_generators R Row20.singer_mem
    (MonoidHom.id Local) K hlinear ht g

theorem pure_swap_mem : (inr (1, C2Wreath.gen) : FullModel) ∈ modelGroup :=
  generator_mem 5

/-- One actual nonzero diagonal translation and the onto local projection
force the entire diagonal translation subgroup. -/
theorem diagonal_mem (v : V) : (inl (v, v) : FullModel) ∈ modelGroup := by
  let D : Subgroup V := modelGroup.comap (BinaryDiagonalSwap.diagonal φ)
  have hinv : ∀ r w, w ∈ D → φ r w ∈ D := by
    intro r w hw
    obtain ⟨g, hg⟩ := first_surjective (inr r)
    have hr : (BinaryDiagonalSwapSubdirect.underlying φ modelGroup g).right.1 = r :=
      congrArg (fun x : Local ↦ x.right) hg
    have hc := modelGroup.mul_mem
      (modelGroup.mul_mem (BinaryDiagonalSwapSubdirect.underlying_mem φ modelGroup g) hw)
      (modelGroup.inv_mem (BinaryDiagonalSwapSubdirect.underlying_mem φ modelGroup g))
    change BinaryDiagonalSwapSubdirect.underlying φ modelGroup g * inl (w, w) *
      (BinaryDiagonalSwapSubdirect.underlying φ modelGroup g)⁻¹ ∈ modelGroup at hc
    rw [BinaryDiagonalSwap.conj_inl,
      BinaryDiagonalSwapSubdirect.even_right_pair φ modelGroup g, hr,
      BinaryDiagonalSwap.action_one] at hc
    exact hc
  have hne : D ≠ ⊥ := by
    intro hb
    have hm : Multiplicative.ofAdd firstVector ∈ D := generator_mem 0
    have he : Multiplicative.ofAdd firstVector = (1 : V) :=
      Subgroup.mem_bot.mp (hb ▸ hm)
    exact firstVector_ne_zero (congrArg Multiplicative.toAdd he)
  have htop : D = ⊤ :=
    (BinaryDiagonalSwap.affine_irreducible R Row20.irreducible D hinv).resolve_left hne
  change v ∈ D
  rw [htop]
  trivial

end PrimitiveAffineDegreeTwoTwoAffineSixteenRow12SubdirectTop
end SymmetricSubgroupAsymptotics

end
