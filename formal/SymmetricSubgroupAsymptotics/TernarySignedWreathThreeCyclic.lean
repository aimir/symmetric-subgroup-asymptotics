import SymmetricSubgroupAsymptotics.BinaryPairFrameTernarySignedRepresentation
import SymmetricSubgroupAsymptotics.PermutationalWreathFinite
import SymmetricSubgroupAsymptotics.SurjectiveRepresentationGeneratorTransport
import SymmetricSubgroupAsymptotics.TernaryC3CyclicModule

/-!
# Cyclic submodules for the signed wreath action on three coordinates

Every subgroup of order three in `C2 wr S3` is Sylow, hence conjugate to
the canonical copy of `A3` in the top.  The natural signed coordinate
representation on that canonical copy is the regular ternary permutation
module certified in `TernaryC3CyclicModule`.  Conjugation transports the
uniform one-generator theorem to every order-three signed subgroup.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics

open BinaryPairFrame OddMarkerTernaryChart

/-- The full signed permutation group on three ternary coordinates. -/
abbrev TernarySignedWreathThree :=
  PermutationalWreathProduct (Multiplicative (ZMod 2))
    (Equiv.Perm (Fin 3)) (Fin 3)

/-- Its faithful monomial coordinate representation over `F3`. -/
abbrev ternarySignedWreathThreeRepresentation :
    Representation (ZMod 3) TernarySignedWreathThree
      (Fin 3 → ZMod 3) :=
  PermutationalWreathProduct.functionRepresentation
    (Q := Equiv.Perm (Fin 3)) (I := Fin 3)
    ternarySignRepresentation

/-- The canonical order-three subgroup, embedded with trivial base sign. -/
def ternaryTopC3Hom : TernaryNaturalC3 →* TernarySignedWreathThree :=
  (PermutationalWreathProduct.topHom
    (D := Multiplicative (ZMod 2))
    (Q := Equiv.Perm (Fin 3)) (I := Fin 3)).comp
      TernaryNaturalC3.subtype

/-- The canonical order-three top as a literal subgroup of the signed
wreath product. -/
abbrev TernarySignedTopC3 : Subgroup TernarySignedWreathThree :=
  ternaryTopC3Hom.range

theorem ternaryTopC3Hom_injective :
    Function.Injective ternaryTopC3Hom :=
  PermutationalWreathProduct.topHom_injective.comp
    TernaryNaturalC3.subtype_injective

/-- The source `A3` is exactly the canonical top subgroup. -/
def ternaryTopC3Equiv : TernaryNaturalC3 ≃* TernarySignedTopC3 :=
  MulEquiv.ofBijective ternaryTopC3Hom.rangeRestrict
    ⟨MonoidHom.rangeRestrict_injective_iff.mpr
        ternaryTopC3Hom_injective,
      ternaryTopC3Hom.rangeRestrict_surjective⟩

/-- On the canonical top, the signed action has no base signs and is the
standard regular permutation module. -/
theorem ternarySignedWreathThree_comp_topC3 :
    ternarySignedWreathThreeRepresentation.comp ternaryTopC3Hom =
      ternaryNaturalC3Representation := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro v
  funext i
  change signScalar 1 * v (g.1⁻¹ i) = v (g.1⁻¹ i)
  rw [signScalar_one, one_mul]

/-- Every invariant submodule on the canonical signed top is cyclic. -/
theorem ternarySignedTopC3_uniformSubrepresentationGeneratorBound_one :
    UniformSubrepresentationGeneratorBound
      (ternarySignedWreathThreeRepresentation.comp
        TernarySignedTopC3.subtype) 1 := by
  let e := ternaryTopC3Equiv
  have hsource : UniformSubrepresentationGeneratorBound
      (ternarySignedWreathThreeRepresentation.comp ternaryTopC3Hom) 1 := by
    rw [ternarySignedWreathThree_comp_topC3]
    exact naturalC3Ternary_uniformSubrepresentationGeneratorBound_one
  have hback := hsource.comp_mulEquiv
    (ternarySignedWreathThreeRepresentation.comp ternaryTopC3Hom) e.symm
  have hrepresentation :
      (ternarySignedWreathThreeRepresentation.comp ternaryTopC3Hom).comp
          e.symm.toMonoidHom =
        ternarySignedWreathThreeRepresentation.comp
          TernarySignedTopC3.subtype := by
    apply MonoidHom.ext
    intro t
    apply LinearMap.ext
    intro v
    obtain ⟨g, rfl⟩ := e.surjective t
    rfl
  rwa [hrepresentation] at hback

/-- The signed three-coordinate wreath product has order `48`. -/
theorem ternarySignedWreathThree_card :
    Nat.card TernarySignedWreathThree = 48 := by
  rw [PermutationalWreathProduct.natCard_eq,
    Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, Nat.card_fin,
    Nat.card_perm]
  norm_num

/-- The canonical signed top has order three. -/
theorem ternarySignedTopC3_card : Nat.card TernarySignedTopC3 = 3 := by
  rw [← Nat.card_congr ternaryTopC3Equiv.toEquiv,
    nat_card_alternatingGroup, Nat.card_fin]
  norm_num

/-- Every order-three subgroup of the three-coordinate signed wreath action
has cyclic invariant submodules.  This is the literal ternary-fibre input,
independent of a transitive-group catalogue. -/
theorem ternarySignedWreathThree_orderThree_uniformSubrepresentationGeneratorBound_one
    (H : Subgroup TernarySignedWreathThree)
    (hH : Nat.card H = 3) :
    UniformSubrepresentationGeneratorBound
      (ternarySignedWreathThreeRepresentation.comp H.subtype) 1 := by
  letI : Fact (3 : ℕ).Prime := ⟨Nat.prime_three⟩
  let HSylow : Sylow 3 TernarySignedWreathThree :=
    Sylow.ofCard H (by
      rw [hH, ternarySignedWreathThree_card]
      norm_num)
  let TSylow : Sylow 3 TernarySignedWreathThree :=
    Sylow.ofCard TernarySignedTopC3 (by
      rw [ternarySignedTopC3_card, ternarySignedWreathThree_card]
      norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq
    TernarySignedWreathThree HSylow TSylow
  have hgsub : g • H = TernarySignedTopC3 := by
    exact congrArg Sylow.toSubgroup hg
  have hconj : UniformSubrepresentationGeneratorBound
      (ternarySignedWreathThreeRepresentation.comp
        (g • H : Subgroup TernarySignedWreathThree).subtype) 1 := by
    rw [hgsub]
    exact ternarySignedTopC3_uniformSubrepresentationGeneratorBound_one
  exact uniformSubrepresentationGeneratorBound_conjugate_restriction
    ternarySignedWreathThreeRepresentation H g hconj

end SymmetricSubgroupAsymptotics

end
