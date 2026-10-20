import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows1To50
import SymmetricSubgroupAsymptotics.BinaryCommutativePrefixOrbits

/-!
# One actual binary quotient of the smallest exceptional twelve-point top

The literal row-10 action has coordinates `C2^2 × Fin 3`: its last two
generators are translations and its first two generate the symmetric
action on the three-point factor. This identifies its original generated
top with `C2^2 × S3`. The parity quotient is an actual elementary abelian
quotient of order eight, with original normal kernel of order three.

For this selected quotient, central binary rank is three, derived-central
rank is zero, and every conjugation type is fixed. The designated-prefix
bridge therefore constructs one binary-primary linear prefix and two
relative orbit slots. This is a selected top-quotient pilot, not a
certificate for arbitrary normal quotients of pair lifts of row 10.

All finite reductions below range over twelve points, twenty-four model
elements, or eight quotient elements; none enumerates permutations of
twelve points or normal subgroups of pair lifts.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwelveRow10BinaryQuotientPilot

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

abbrev Binary := Multiplicative (ZMod 2)
abbrev Translation := Binary × Binary
abbrev Points := Translation × Fin 3
abbrev Model := Translation × Equiv.Perm (Fin 3)
abbrev BinaryQuotient := Translation × Binary
abbrev Top := DegreeTwoTwelvePairFiniteCatalogue.Row10Top

def bit : Binary := Multiplicative.ofAdd 1

/-- The fibre phase depends on the original binary coordinate. -/
def pointEquiv : Fin 12 ≃ Points where
  toFun x := (#[((1, 1), 0), ((bit, 1), 1), ((1, bit), 2), ((bit, bit), 0),
    ((1, 1), 1), ((bit, 1), 2), ((1, bit), 0), ((bit, bit), 1),
    ((1, 1), 2), ((bit, 1), 0), ((1, bit), 1), ((bit, bit), 2)] :
      Array Points)[x.val]!
  invFun p := if p.1.1 = 1 then
      if p.1.2 = 1 then (#[0, 4, 8] : Array (Fin 12))[p.2.val]!
      else (#[6, 10, 2] : Array (Fin 12))[p.2.val]!
    else if p.1.2 = 1 then (#[9, 1, 5] : Array (Fin 12))[p.2.val]!
      else (#[3, 7, 11] : Array (Fin 12))[p.2.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def modelAction : Model →* Equiv.Perm Points where
  toFun g :=
    { toFun := fun p ↦ (g.1 * p.1, g.2 p.2)
      invFun := fun p ↦ (g.1⁻¹ * p.1, g.2.symm p.2)
      left_inv := by intro p; simp
      right_inv := by intro p; simp }
  map_one' := by ext p <;> simp
  map_mul' g h := by ext p <;> simp [mul_assoc]

def literalAction : Model →* Equiv.Perm (Fin 12) :=
  pointEquiv.symm.permCongrHom.toMonoidHom.comp modelAction

theorem modelAction_injective : Function.Injective modelAction := by
  intro g h he
  apply Prod.ext
  · have hv := congrArg (fun p : Equiv.Perm Points ↦ (p (1, 0)).1) he
    change g.1 * 1 = h.1 * 1 at hv
    simpa only [mul_one] using hv
  · apply Equiv.ext
    intro i
    exact congrArg (fun p : Equiv.Perm Points ↦ (p (1, i)).2) he

theorem literalAction_injective : Function.Injective literalAction :=
  pointEquiv.symm.permCongrHom.injective.comp modelAction_injective

def rotation : Equiv.Perm (Fin 3) where
  toFun x := (#[1, 2, 0] : Array (Fin 3))[x.val]!
  invFun x := (#[2, 0, 1] : Array (Fin 3))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def modelGenerators : Fin 4 → Model :=
  ![(1, rotation), (1, Equiv.swap 0 1), ((bit, 1), 1), ((1, bit), 1)]

/-- The point chart binds all four original catalogue generators. -/
theorem generators_binding (i : Fin 4) :
    literalAction (modelGenerators i) =
      DegreeTwoTwelvePairFiniteCatalogue.row10Generators i := by
  ext x
  revert i x
  decide +kernel

theorem model_word_cover (g : Model) :
    ∃ a : Fin 3, ∃ b c d : Fin 2,
      g = (modelGenerators 0) ^ a.val * (modelGenerators 1) ^ b.val *
        (modelGenerators 2) ^ c.val * (modelGenerators 3) ^ d.val := by
  decide +kernel +revert

theorem literalAction_range : literalAction.range = Top := by
  apply le_antisymm
  · have hgen (i : Fin 4) : literalAction (modelGenerators i) ∈ Top := by
      rw [generators_binding]
      exact Subgroup.subset_closure (Set.mem_range_self i)
    rintro _ ⟨g, rfl⟩
    obtain ⟨a, b, c, d, hg⟩ := model_word_cover g
    rw [hg, map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow]
    exact Top.mul_mem
      (Top.mul_mem (Top.mul_mem (Top.pow_mem (hgen 0) a.val)
        (Top.pow_mem (hgen 1) b.val)) (Top.pow_mem (hgen 2) c.val))
      (Top.pow_mem (hgen 3) d.val)
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨modelGenerators i, generators_binding i⟩

def modelEquiv : Model ≃* Top :=
  (MonoidHom.ofInjective literalAction_injective).trans
    (MulEquiv.subgroupCongr literalAction_range)

theorem top_card : Nat.card Top = 24 := by
  rw [← Nat.card_congr modelEquiv.toEquiv, Nat.card_eq_fintype_card]
  decide +kernel

/-- Parity in the six-element symmetric factor, retained as a binary
homomorphism with finite multiplication checked on that factor alone. -/
def parity : Equiv.Perm (Fin 3) →* Binary where
  toFun g := if g = 1 ∨ g = rotation ∨ g = rotation ^ 2 then 1 else bit
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

def modelProjection : Model →* BinaryQuotient where
  toFun g := (g.1, parity g.2)
  map_one' := by simp
  map_mul' g h := by simp

theorem modelProjection_surjective : Function.Surjective modelProjection := by
  decide +kernel

/-- The homomorphism is on the literal original row-10 generated top. -/
def projection : Top →* BinaryQuotient :=
  modelProjection.comp modelEquiv.symm.toMonoidHom

theorem projection_surjective : Function.Surjective projection :=
  modelProjection_surjective.comp modelEquiv.symm.surjective

abbrev ActualQuotient := Top ⧸ projection.ker

def quotientEquiv : ActualQuotient ≃* BinaryQuotient :=
  QuotientGroup.quotientKerEquivOfSurjective projection projection_surjective

theorem binaryQuotient_card : Nat.card BinaryQuotient = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem actualQuotient_card : Nat.card ActualQuotient = 8 :=
  (Nat.card_congr quotientEquiv.toEquiv).trans binaryQuotient_card

theorem original_kernel_card : Nat.card projection.ker = 3 := by
  have h := projection.ker.card_mul_index
  rw [Subgroup.index_eq_card, actualQuotient_card, top_card] at h
  omega

theorem binaryQuotient_square (g : BinaryQuotient) : g ^ 2 = 1 := by
  decide +kernel +revert

instance actualQuotient_commutative : IsMulCommutative ActualQuotient := by
  apply isMulCommutative_iff.mpr
  intro g h
  apply quotientEquiv.injective
  rw [map_mul, map_mul, mul_comm]

theorem actualQuotient_isPGroup : IsPGroup 2 ActualQuotient :=
  IsPGroup.of_card (n := 3) actualQuotient_card

def binaryQuotientOmegaEquiv : binaryCentralOmega BinaryQuotient ≃* BinaryQuotient :=
  MulEquiv.ofBijective binaryCentralOmegaEmbedding
    ⟨binaryCentralOmegaEmbedding_injective, by
      intro g
      refine ⟨⟨⟨g, Subgroup.mem_center_iff.mpr (fun _ ↦ mul_comm _ _)⟩,
        Subtype.ext (binaryQuotient_square g)⟩, rfl⟩⟩

theorem actualQuotient_central_rank :
    Module.finrank (ZMod 2) (Additive (binaryCentralOmega ActualQuotient)) = 3 := by
  apply binaryCentralOmega_finrank ActualQuotient 3
  rw [binaryCentralOmega_card_congr ActualQuotient quotientEquiv,
    Nat.card_congr binaryQuotientOmegaEquiv.toEquiv, binaryQuotient_card]
  norm_num

theorem actualQuotient_derived_central_rank :
    Module.finrank (ZMod 2)
      (binaryCentralOmegaSubmodule (commutator ActualQuotient)) = 0 := by
  rw [commutator_eq_bot, binaryCentralOmegaSubmodule_bot, finrank_bot]

/-- The selected pilot statement on the actual original quotient: one
binary-primary prefix leaves central rank and Schur demand
at most two, and gives two actual separating normal-orbit slots. -/
theorem actualQuotient_prefix_two :
    ∃ χ : ActualQuotient →* ℂˣ, IsPGroup 2 χ.range ∧ IsPGroup 2 χ.ker ∧
      Module.finrank (ZMod 2) (binaryCentralOmegaSubmodule χ.ker) ≤ 2 ∧
      representationSchurCapacity
        (finiteRepresentationSocle
          (binaryKernelOmegaConjugationRepresentation χ)).toRepresentation ≤ 2 ∧
      Nonempty (BinaryKernelOmegaLinearOrbits χ 2) := by
  apply exists_binaryPrimaryPrefix_orbits_of_commutative actualQuotient_isPGroup 2
  simpa only [actualQuotient_central_rank] using (show 3 ≤ 2 + 1 by decide)

end PrimitiveAffineDegreeTwoTwelveRow10BinaryQuotientPilot
end SymmetricSubgroupAsymptotics
