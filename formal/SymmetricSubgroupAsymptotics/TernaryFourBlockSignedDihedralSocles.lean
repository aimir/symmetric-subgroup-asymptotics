import SymmetricSubgroupAsymptotics.TernaryMonomialOrbitGenerators
import SymmetricSubgroupAsymptotics.SplitAffineLiteralSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveMetacyclicImages

/-! The dihedral four-block complement with a sign on odd rotations and
either sign on reflection. Two short complement words expose the pure
rotation and reflection in each of the two retained tuple shapes. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace TernaryFourBlockSignedDihedralSocles

open SemidirectProduct
open PrimitiveAffineDegreeTwoTwelveRow131AffineModel (Block Vector)

abbrev Bit := TernaryFourBlockMetacyclicModel.Bit
abbrev Complement := TernaryFourBlockMetacyclicModel.Complement true

def scalar (negate : Bool) : Complement →* (ZMod 3)ˣ where
  toFun h := (-1) ^ h.left.toAdd.val *
    TernaryFourBlockMetacyclicModel.bitScalar negate h.right
  map_one' := by cases negate <;> decide +kernel
  map_mul' := by cases negate <;> decide +kernel

def linearAction (negate : Bool) : Complement →* (Vector ≃ₗ[ZMod 3] Vector) :=
  TernaryMonomialSemidirect.linearAction
    (TernaryFourBlockMetacyclicModel.blockAction true) (scalar negate)

abbrev Model (negate : Bool) := LinearSemidirectCoprimeSocleBounds.Model (linearAction negate)

theorem representation_generated (negate : Bool) : RepresentationGeneratedBy
    (LinearSemidirectCoprimeSocleBounds.linearRepresentation (linearAction negate)) 1 := by
  apply TernaryMonomialOrbitGenerators.generatedBy_orbitCover
    (TernaryFourBlockMetacyclicModel.blockAction true) (scalar negate)
    (fun _ : Fin 1 ↦ 1)
  intro c
  refine ⟨0, inl c, ?_⟩
  change c * TernaryFourBlockMetacyclicModel.bitAction true 1 1 = c
  simp

def rotation : Complement := inl (Multiplicative.ofAdd (1 : ZMod 4))
def reflection : Complement := inr (Multiplicative.ofAdd (1 : ZMod 2))

def lifted (negate : Bool) (v : Vector) : Fin 4 → Model negate :=
  if negate then
    ![inl (Multiplicative.ofAdd v), inr (rotation * reflection),
      inr (rotation ^ 2), inr reflection]
  else
    ![inl (Multiplicative.ofAdd v), inr (rotation ^ 2 * reflection),
      inr reflection, inr (rotation * reflection)]

theorem complement_mem (negate : Bool) (v : Vector) (h : Complement) :
    (inr h : Model negate) ∈ Subgroup.closure (Set.range (lifted negate v)) := by
  let K := Subgroup.closure (Set.range (lifted negate v))
  have hrs : (inr (rotation * reflection) : Model negate) ∈ K := by
    cases negate
    · exact Subgroup.subset_closure (Set.mem_range_self (3 : Fin 4))
    · exact Subgroup.subset_closure (Set.mem_range_self (1 : Fin 4))
  have hs : (inr reflection : Model negate) ∈ K := by
    cases negate
    · exact Subgroup.subset_closure (Set.mem_range_self (2 : Fin 4))
    · exact Subgroup.subset_closure (Set.mem_range_self (3 : Fin 4))
  have hr : (inr rotation : Model negate) ∈ K := by
    have hm := K.mul_mem hrs (K.inv_mem hs)
    simpa only [← map_inv, ← map_mul, mul_inv_cancel_right] using hm
  have hblock (c : Block) : (inr (inl c) : Model negate) ∈ K := by
    have hc : (Multiplicative.ofAdd (1 : ZMod 4)) ^ c.toAdd.val = c := by
      apply Multiplicative.toAdd.injective
      simp [toAdd_pow, nsmul_eq_mul]
    rw [← hc, map_pow, map_pow]
    exact K.pow_mem hr _
  have hbit (b : Bit) : (inr (inr b) : Model negate) ∈ K := by
    have hb : (Multiplicative.ofAdd (1 : ZMod 2)) ^ b.toAdd.val = b := by
      apply Multiplicative.toAdd.injective
      simp [toAdd_pow, nsmul_eq_mul]
    rw [← hb, map_pow, map_pow]
    exact K.pow_mem hs _
  rw [← inl_left_mul_inr_right h, map_mul]
  exact K.mul_mem (hblock h.left) (hbit h.right)

def literalAction (negate : Bool) : Model negate →* Equiv.Perm (Fin 12) :=
  PrimitiveAffineDegreeTwoTwelveMetacyclicImages.centeredPointEquiv.symm.permCongrHom.toMonoidHom.comp
    (TernaryMonomialSemidirect.action
      (TernaryFourBlockMetacyclicModel.blockAction true) (scalar negate))

theorem quotientSocle (negate : Bool) (v : Vector)
    (target : Fin 4 → Equiv.Perm (Fin 12))
    (hbinding : ∀ i, literalAction negate (lifted negate v i) = target i)
    (N : Subgroup (Subgroup.closure (Set.range target))) [N.Normal] :
    SocleNormalGeneratorBound (Subgroup.closure (Set.range target) ⧸ N) 2 :=
  SplitAffineLiteralSocles.quotientSocle (linearAction negate) (literalAction negate)
    (lifted negate v) target (Equiv.refl _) hbinding (complement_mem negate v)
    (TernaryFourBlockMetacyclicModel.complement_coprime true) 1 2
    (representation_generated negate)
    (TernaryFourBlockMetacyclicModel.complement_normalGen true) N

end TernaryFourBlockSignedDihedralSocles
end SymmetricSubgroupAsymptotics

end
