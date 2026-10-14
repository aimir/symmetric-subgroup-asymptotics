import SymmetricSubgroupAsymptotics.CyclicByCyclicNormalGenerators
import SymmetricSubgroupAsymptotics.TernaryMonomialSemidirect
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow131AffineModel

/-!
# One four-block model with dihedral or commuting involution

The two Boolean parameters record whether the extra involution reverses
the four blocks and whether it negates all ternary coordinates. Its
complement is the actual split extension C4 by C2, so all complement
normal subgroups have two normal generators. The ternary translation
module is cyclic because its restriction contains the regular C4 action.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace TernaryFourBlockMetacyclicModel

open SemidirectProduct
open PrimitiveAffineDegreeTwoTwelveRow131AffineModel (Block Vector Translation Points)

abbrev Bit := Multiplicative (ZMod 2)

def bitAction (reverse : Bool) : Bit →* MulAut Block where
  toFun b :=
    { toFun := fun c ↦ if reverse = true ∧ b ≠ 1 then c⁻¹ else c
      invFun := fun c ↦ if reverse = true ∧ b ≠ 1 then c⁻¹ else c
      left_inv := by intro c; split_ifs <;> simp
      right_inv := by intro c; split_ifs <;> simp
      map_mul' := by intro c d; split_ifs <;> simp [mul_comm] }
  map_one' := by apply MulEquiv.ext; intro c; simp
  map_mul' := by
    intro b d
    apply MulEquiv.ext
    intro c
    revert b d c
    cases reverse <;> decide +kernel

abbrev Complement (reverse : Bool) := Block ⋊[bitAction reverse] Bit

instance (reverse : Bool) : Fintype (Complement reverse) :=
  Fintype.ofEquiv (Block × Bit) SemidirectProduct.equivProd.symm

def blockAction (reverse : Bool) : Complement reverse →* Equiv.Perm Block where
  toFun g := Equiv.mulLeft g.left * (bitAction reverse g.right).toEquiv
  map_one' := by
    apply Equiv.ext
    intro i
    simp [bitAction]
  map_mul' := by
    intro g h
    apply Equiv.ext
    intro i
    revert g h i
    cases reverse <;> decide +kernel

def bitScalar (negate : Bool) : Bit →* (ZMod 3)ˣ where
  toFun b := if negate = true ∧ b ≠ 1 then -1 else 1
  map_one' := by simp
  map_mul' := by cases negate <;> decide +kernel

def scalar (reverse negate : Bool) : Complement reverse →* (ZMod 3)ˣ :=
  (bitScalar negate).comp rightHom

def linearAction (reverse negate : Bool) : Complement reverse →* (Vector ≃ₗ[ZMod 3] Vector) :=
  TernaryMonomialSemidirect.linearAction (blockAction reverse) (scalar reverse negate)

abbrev Model (reverse negate : Bool) :=
  LinearSemidirectCoprimeSocleBounds.Model (linearAction reverse negate)

theorem linearAction_inl (reverse negate : Bool) (c : Block) (v : Vector) :
    linearAction reverse negate (inl c) v =
      PrimitiveAffineDegreeTwoTwelveRow131AffineModel.linearAction c v := by
  funext i
  change TernaryMonomialSemidirect.coefficient (scalar reverse negate) (inl c) *
      v (blockAction reverse ((inl c : Complement reverse)⁻¹) i) = v (c⁻¹ * i)
  have hs : scalar reverse negate (inl c) = 1 := by
    change bitScalar negate 1 = 1
    exact (bitScalar negate).map_one
  have hc : TernaryMonomialSemidirect.coefficient (scalar reverse negate) (inl c) = 1 :=
    congrArg (fun u : (ZMod 3)ˣ ↦ (u : ZMod 3)) hs
  have hi : blockAction reverse ((inl c : Complement reverse)⁻¹) i = c⁻¹ * i := by
    rw [← (inl : Block →* Complement reverse).map_inv]
    change c⁻¹ * bitAction reverse 1 i = c⁻¹ * i
    exact congrArg (fun u : MulAut Block ↦ c⁻¹ * u i) (bitAction reverse).map_one
  rw [hc, hi, one_mul]

theorem representation_comp (reverse negate : Bool) :
    (LinearSemidirectCoprimeSocleBounds.linearRepresentation (linearAction reverse negate)).comp
      (inl : Block →* Complement reverse) =
        permutationFunctionRepresentation (ZMod 3) Block Block := by
  apply MonoidHom.ext
  intro c
  apply LinearMap.ext
  intro v
  exact linearAction_inl reverse negate c v

theorem representation_generated (reverse negate : Bool) :
    RepresentationGeneratedBy
      (LinearSemidirectCoprimeSocleBounds.linearRepresentation (linearAction reverse negate)) 1 := by
  apply RepresentationGeneratedBy.of_comp _ (inl : Block →* Complement reverse)
  rw [representation_comp]
  apply permutationFunctionRepresentation_generatedBy_orbitCover (fun _ : Fin 1 ↦ 1)
  intro c
  exact ⟨0, c, mul_one c⟩

theorem complement_coprime (reverse : Bool) : Nat.Coprime 3 (Nat.card (Complement reverse)) := by
  rw [Nat.card_eq_fintype_card]
  cases reverse <;> decide +kernel

theorem complement_normalGen (reverse : Bool) (H : Subgroup (Complement reverse))
    (hH : H.Normal) : MarkedC4.normalGen H ≤ 2 := by
  letI := hH
  exact CyclicByCyclicNormalGenerators.semidirect_normalGen_le_two (bitAction reverse) H

theorem socle_of_surjective (reverse negate : Bool) {Q : Type} [Group Q]
    (pi : Model reverse negate →* Q) (hpi : Function.Surjective pi) :
    SocleNormalGeneratorBound Q 2 := by
  exact LinearSemidirectCoprimeQuotientSocles.socle_of_surjective
    (linearAction reverse negate) (complement_coprime reverse) 1 2
    (representation_generated reverse negate) (complement_normalGen reverse) pi hpi

/-- The checked four-block C4 model sits in either metacyclic model. -/
def baseMap (reverse negate : Bool) :
    PrimitiveAffineDegreeTwoTwelveRow131AffineModel.Model →* Model reverse negate :=
  SemidirectProduct.map (MonoidHom.id Translation) (inl : Block →* Complement reverse) (by
    intro c
    apply MonoidHom.ext
    intro v
    apply Multiplicative.toAdd.injective
    exact (linearAction_inl reverse negate c v.toAdd).symm)

def generators (reverse negate : Bool) : Fin 3 → Model reverse negate :=
  ![baseMap reverse negate (PrimitiveAffineDegreeTwoTwelveRow131AffineModel.modelGenerators 0),
    baseMap reverse negate (PrimitiveAffineDegreeTwoTwelveRow131AffineModel.modelGenerators 1),
    inr (inr (Multiplicative.ofAdd 1 : Bit))]

theorem model_generated (reverse negate : Bool) :
    Subgroup.closure (Set.range (generators reverse negate)) = ⊤ := by
  let D : Subgroup (Model reverse negate) :=
    Subgroup.closure (Set.range (generators reverse negate))
  have hbase (g : PrimitiveAffineDegreeTwoTwelveRow131AffineModel.Model) :
      baseMap reverse negate g ∈ D := by
    have hle : Subgroup.closure
        (Set.range PrimitiveAffineDegreeTwoTwelveRow131AffineModel.modelGenerators) ≤
        D.comap (baseMap reverse negate) := by
      apply (Subgroup.closure_le _).mpr
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact Subgroup.subset_closure (Set.mem_range_self (0 : Fin 3))
      · exact Subgroup.subset_closure (Set.mem_range_self (1 : Fin 3))
    apply hle
    rw [PrimitiveAffineDegreeTwoTwelveRow131AffineModel.model_generated]
    exact Subgroup.mem_top g
  have hbit (b : Bit) : (inr (inr b) : Model reverse negate) ∈ D := by
    have hb : (Multiplicative.ofAdd (1 : ZMod 2)) ^ b.toAdd.val = b := by
      apply Multiplicative.toAdd.injective
      simp [toAdd_pow, nsmul_eq_mul]
    rw [← hb, map_pow, map_pow]
    exact D.pow_mem (Subgroup.subset_closure (Set.mem_range_self (2 : Fin 3))) _
  apply top_unique
  intro g _
  rw [← inl_left_mul_inr_right g, ← inl_left_mul_inr_right g.right, map_mul]
  apply D.mul_mem
  · exact hbase (inl g.left)
  · exact D.mul_mem (hbase (inr g.right.left)) (hbit g.right.right)

end TernaryFourBlockMetacyclicModel
end SymmetricSubgroupAsymptotics

end
