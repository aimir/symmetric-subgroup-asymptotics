import SymmetricSubgroupAsymptotics.PairedSixSmallQuotientAlternatives
import SymmetricSubgroupAsymptotics.PairedSixLiteralModels
import SymmetricSubgroupAsymptotics.S3WreathTernaryCore
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeSixS3ProductAlgebra

/-!
# Quotient alternatives for the exact paired-six literal tops

Every quotient has either a normally cyclic socle or an actual injection
into the binary plane. The product's two minimal ternary factors share one
normal generator, and its nontrivial quotients factor through S3 × C2.
The wreath product's unique minimal ternary core reduces nontrivial
quotients to D8. All maps preserve the retained literal permutation tops.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
noncomputable section
open scoped Classical commutatorElement

namespace SymmetricSubgroupAsymptotics
namespace PairedSixQuotientAlternatives

open CyclicSocleQuotientTools
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoTwelvePairFiniteCatalogue
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPairTowerCyclicPrefix

namespace Product

abbrev G := DegreeSixS3Product.G
abbrev S3 := Equiv.Perm (Fin 3)
abbrev rotation := PairedSixSmallQuotientAlternatives.rotation

def axis (i : Bool) : Subgroup G := (DegreeSixS3Product.projection i).ker
def axisGenerator : Bool → G
  | false => (1, rotation)
  | true => (rotation, 1)

instance axis_normal (i : Bool) : (axis i).Normal := MonoidHom.normal_ker _

private theorem axis_generator_mem (i j : Bool) :
    axisGenerator i ∈ axis j ↔ i = j := by
  change DegreeSixS3Product.projection j (axisGenerator i) = 1 ↔ i = j
  revert i j
  decide +kernel

private theorem axis_generator_ne_one (i : Bool) : axisGenerator i ≠ 1 := by
  revert i
  decide +kernel

theorem axis_ne_bot (i : Bool) : axis i ≠ ⊥ := by
  intro h
  have hg := (axis_generator_mem i i).mpr rfl
  exact axis_generator_ne_one i (Subgroup.mem_bot.mp (h ▸ hg))

theorem axis_minimal (i : Bool) : IsMinimalNormalSubgroup (axis i) := by
  refine ⟨inferInstance, axis_ne_bot i, ?_⟩
  intro N hN hNb hNi
  obtain ⟨j, hj⟩ := DegreeSixS3Product.normal_cover N hN hNb
  have hji : j = i :=
    (axis_generator_mem j i).mp (hNi (hj ((axis_generator_mem j j).mpr rfl)))
  subst j
  exact le_antisymm hNi hj

private theorem axis_le_derivedBase (i : Bool) : axis i ≤ DegreeSixS3Product.derivedBase := by
  have hcheck : ∀ (j : Bool) (x : G),
      x ∈ axis j → x ∈ DegreeSixS3Product.derivedBase := by
    simp only [axis, DegreeSixS3Product.derivedBase, MonoidHom.mem_ker]
    decide +kernel
  exact hcheck i

def generator : G := (rotation, rotation)

theorem socle : SocleNormalGeneratorBound G 1 := by
  have hsocle : finiteGroupSocle G ≤ DegreeSixS3Product.derivedBase := by
    apply Subgroup.normalClosure_le_normal
    rintro x ⟨N, hN, hx⟩
    obtain ⟨i, hi⟩ := DegreeSixS3Product.normal_cover N hN.1 hN.2.1
    have heq : axis i = N := hN.2.2 _ inferInstance (axis_ne_bot i) hi
    exact axis_le_derivedBase i (heq.symm ▸ hx)
  have haxis (i : Bool) : axisGenerator i ∈ finiteGroupSocle G :=
    Subgroup.subset_normalClosure
      ⟨axis i, axis_minimal i, (axis_generator_mem i i).mpr rfl⟩
  have hgenerator : generator ∈ finiteGroupSocle G := by
    have heq : axisGenerator true * axisGenerator false = generator := by decide +kernel
    exact heq ▸ (finiteGroupSocle G).mul_mem (haxis true) (haxis false)
  let W := Subgroup.normalClosure (Set.range (fun _ : Fin 1 ↦ generator))
  letI : W.Normal := by dsimp [W]; infer_instance
  have hgW : generator ∈ W :=
    Subgroup.subset_normalClosure (Set.mem_range_self (0 : Fin 1))
  have haW : axisGenerator true ∈ W := by
    have hw : ⁅(Equiv.swap (1 : Fin 3) 2, (1 : S3)), generator⁆ =
        axisGenerator true := by decide +kernel
    exact hw ▸ PairedSixSmallQuotientAlternatives.comm_mem_normal W inferInstance hgW
      (Equiv.swap (1 : Fin 3) 2, 1)
  have hbW : axisGenerator false ∈ W := by
    have hw : (axisGenerator true)⁻¹ * generator = axisGenerator false := by decide +kernel
    exact hw ▸ W.mul_mem (W.inv_mem haW) hgW
  have hVW : DegreeSixS3Product.derivedBase ≤ W := by
    have hform : ∀ x : G, x ∈ DegreeSixS3Product.derivedBase →
        ∃ i j : Fin 3,
          x = axisGenerator true ^ i.val * axisGenerator false ^ j.val := by
      simp only [DegreeSixS3Product.derivedBase, MonoidHom.mem_ker]
      decide +kernel
    intro x hx
    obtain ⟨i, j, hij⟩ := hform x hx
    rw [hij]
    exact W.mul_mem (W.pow_mem haW _) (W.pow_mem hbW _)
  refine ⟨fun _ ↦ generator, le_antisymm ?_ (hsocle.trans hVW)⟩
  apply Subgroup.normalClosure_le_normal
  rintro _ ⟨i, rfl⟩
  exact hgenerator

theorem image_alternative {Q : Type} [Group Q]
    (q : G →* Q) (hq : Function.Surjective q) : TopAlternative Q := by
  by_cases hbot : q.ker = ⊥
  · exact Or.inl (socleBound_equiv (MulEquiv.ofBijective q
      ⟨(MonoidHom.ker_eq_bot_iff q).mp hbot, hq⟩) socle)
  · obtain ⟨i, hi⟩ := DegreeSixS3Product.normal_cover q.ker inferInstance hbot
    obtain ⟨f, hf, _⟩ := exists_surjective_factor (DegreeSixS3Product.projection i)
      (DegreeSixS3Product.projection_surjective i) q hq hi
    exact PairedSixSmallQuotientAlternatives.S3Binary.image_alternative f hf

end Product

namespace Wreath

abbrev G := DegreeSixS3Wreath.G

theorem socle : SocleNormalGeneratorBound G 1 := by
  apply socleBound_of_normal_cover DegreeSixS3Wreath.projection.ker _
    S3WreathTernaryCore.normal_cover
  intro hbot
  exact S3WreathTernaryCore.firstRotation_ne_one
    (Subgroup.mem_bot.mp (hbot ▸ S3WreathTernaryCore.firstRotation_mem))

theorem image_alternative {Q : Type} [Group Q]
    (q : G →* Q) (hq : Function.Surjective q) : TopAlternative Q := by
  by_cases hbot : q.ker = ⊥
  · exact Or.inl (socleBound_equiv (MulEquiv.ofBijective q
      ⟨(MonoidHom.ker_eq_bot_iff q).mp hbot, hq⟩) socle)
  · obtain ⟨f, hf, _⟩ := exists_surjective_factor DegreeSixS3Wreath.projection
      DegreeSixS3Wreath.projection_surjective q hq
      (S3WreathTernaryCore.normal_cover q.ker inferInstance hbot)
    exact PairedSixSmallQuotientAlternatives.DihedralEight.image_alternative f hf

end Wreath

/-- The exact first retained top, for every actual normal quotient. -/
theorem first (N : Subgroup PairedSix1Top) [N.Normal] :
    TopAlternative (PairedSix1Top ⧸ N) :=
  Product.image_alternative
    ((QuotientGroup.mk' N).comp PairedSixLiteralModels.Product.modelEquiv.toMonoidHom)
    ((QuotientGroup.mk'_surjective N).comp PairedSixLiteralModels.Product.modelEquiv.surjective)

/-- The exact second retained top, for every actual normal quotient. -/
theorem second (N : Subgroup PairedSix2Top) [N.Normal] :
    TopAlternative (PairedSix2Top ⧸ N) :=
  Wreath.image_alternative
    ((QuotientGroup.mk' N).comp PairedSixLiteralModels.FullWreath.modelEquiv.toMonoidHom)
    ((QuotientGroup.mk'_surjective N).comp PairedSixLiteralModels.FullWreath.modelEquiv.surjective)

theorem first_family (N : {N : Subgroup PairedSix1Top // N.Normal}) :
    TopAlternative (PairedSix1Top ⧸ N.1) := by
  letI := N.2
  exact first N.1

theorem second_family (N : {N : Subgroup PairedSix2Top // N.Normal}) :
    TopAlternative (PairedSix2Top ⧸ N.1) := by
  letI := N.2
  exact second N.1

end PairedSixQuotientAlternatives
end SymmetricSubgroupAsymptotics

end
