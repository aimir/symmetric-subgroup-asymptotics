import SymmetricSubgroupAsymptotics.BinaryFourAugmentationNormalCover
import SymmetricSubgroupAsymptotics.BinaryFourAugmentationQuotientCoordinates

/-! The exact epimorphism removes only the diagonal translations.
Its elementary-by-cyclic target has quotient-socle bound two, and the
proved diagonal normal cover transfers that bound to the original model. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace BinaryFourBlockAugmentation

open SemidirectProduct

def projection (full : Bool) : Model full →* QuotientModel full where
  toFun g :=
    ⟨Multiplicative.ofAdd (tailMap full g.left.toAdd, g.right.left.toAdd), g.right.right⟩
  map_one' := by
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      apply Prod.ext
      · exact (tailMap full).map_zero
      · rfl
    · rfl
  map_mul' g h := by
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      change
        (tailMap full (g.left.toAdd + restrictedLinear full g.right h.left.toAdd),
          g.right.left.toAdd + (kleinCyclicAction g.right.right h.right.left).toAdd) =
        (tailMap full g.left.toAdd, g.right.left.toAdd) +
          quotientLinear full g.right.right (tailMap full h.left.toAdd, h.right.left.toAdd)
      rw [map_add, tailMap_action, quotientLinear_apply]
      rfl
    · rfl

theorem projection_surjective (full : Bool) : Function.Surjective (projection full) := by
  intro q
  refine ⟨⟨Multiplicative.ofAdd (tailSection full q.left.toAdd.1),
    ⟨Multiplicative.ofAdd q.left.toAdd.2, q.right⟩⟩, ?_⟩
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    apply Prod.ext
    · exact tailMap_section full _
    · rfl
  · rfl

theorem projection_ker (full : Bool) :
    (projection full).ker = diagonalSubgroup full := by
  apply le_antisymm
  · intro g hg
    have hp := MonoidHom.mem_ker.mp hg
    have hz : g.right.right = 1 := congrArg SemidirectProduct.right hp
    have hv : (tailMap full g.left.toAdd, g.right.left.toAdd) = 0 :=
      congrArg (fun q : QuotientModel full => q.left.toAdd) hp
    have ht : tailMap full g.left.toAdd = 0 := congrArg Prod.fst hv
    have hk : g.right.left = 1 :=
      Multiplicative.toAdd.injective (congrArg Prod.snd hv)
    have hr : g.right = 1 := SemidirectProduct.ext hk hz
    refine ⟨Multiplicative.ofAdd ![(g.left.toAdd : Coordinates) 0,
      (g.left.toAdd : Coordinates) 1], ?_⟩
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      apply Subtype.ext
      have hi (i : Fin 4) := congrArg (fun w : tailSpace full => (w : TailCoordinates) i) ht
      ext i
      fin_cases i
      · rfl
      · rfl
      · exact (hi 0).symm
      · exact (hi 1).symm
      · exact (hi 2).symm
      · exact (hi 3).symm
    · exact hr.symm
  · rintro g ⟨d, rfl⟩
    apply MonoidHom.mem_ker.mpr
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      apply Prod.ext
      · apply Subtype.ext
        ext i
        fin_cases i <;> rfl
      · rfl
    · rfl

theorem quotientModel_quotientSocle (full : Bool)
    (N : Subgroup (QuotientModel full)) [N.Normal] :
    SocleNormalGeneratorBound (QuotientModel full ⧸ N) 2 := by
  have hcop : Nat.Coprime 2 (Nat.card Ternary) := by
    rw [Nat.card_congr (Multiplicative.toAdd : Ternary ≃ ZMod 3), Nat.card_zmod]
    decide
  exact LinearSemidirectCoprimeSocleBounds.quotient (quotientLinear full)
    hcop 2 (by decide) (quotientRepresentation_generated full) N

/-- Every epimorphism has the same quotient-socle bound; its source and
kernel remain the original displayed homomorphism. -/
theorem model_socle_of_surjective (full : Bool) {Q : Type} [Group Q]
    (pi : Model full →* Q) (hpi : Function.Surjective pi) :
    SocleNormalGeneratorBound Q 2 := by
  apply quotientSocle_of_surjective_normal_cover (projection full)
    (projection_surjective full)
    (by rw [projection_ker]; exact diagonalSubgroup_ne_bot full)
    (fun N hN hNb => by rw [projection_ker]; exact normal_cover full N hN hNb)
    (by decide) ?_ pi hpi
  intro N hN
  letI := hN
  exact quotientModel_quotientSocle full N

theorem model_quotientSocle (full : Bool) (N : Subgroup (Model full)) [N.Normal] :
    SocleNormalGeneratorBound (Model full ⧸ N) 2 :=
  model_socle_of_surjective full (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

end BinaryFourBlockAugmentation
end SymmetricSubgroupAsymptotics

end
