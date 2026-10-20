import SymmetricSubgroupAsymptotics.InducedOrbitDecomposition
import SymmetricSubgroupAsymptotics.PermutationSubrepresentationHead
import SymmetricSubgroupAsymptotics.RepresentationDualSubquotientGenerators
import SymmetricSubgroupAsymptotics.RepresentationScalarBasisGenerators
import Mathlib.GroupTheory.Index

/-! The literal transitive permutation-function module embeds in induction
of the trivial line from its actual point stabilizer. Evaluation after the
inverse action gives the map into coinduction; finite-index duality then
gives the induced-module map. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PermutationStabilizerInduced

variable {k G X : Type} [Field k] [Group G] [MulAction G X]

def toCoinduced (x : X) :
    (permutationFunctionRepresentation k G X).IntertwiningMap
      (Representation.coind (MulAction.stabilizer G x).subtype
        (Representation.trivial k (MulAction.stabilizer G x) k)) where
  toLinearMap := {
    toFun f := ⟨fun g => f (g⁻¹ • x), by
      intro h g
      change f (((h : G) * g)⁻¹ • x) = f (g⁻¹ • x)
      rw [mul_inv_rev, mul_smul]
      have hh : (h : G)⁻¹ • x = x := (h⁻¹).property
      rw [hh]⟩
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  isIntertwining' a := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext g
    change f (a⁻¹ • (g⁻¹ • x)) = f ((g * a)⁻¹ • x)
    rw [mul_inv_rev, mul_smul]

theorem toCoinduced_injective [MulAction.IsPretransitive G X] (x : X) :
    Function.Injective (toCoinduced (k := k) (G := G) x) := by
  intro f f' h
  funext y
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G y x
  have hy : g⁻¹ • x = y := by rw [← hg, inv_smul_smul]
  have he := congrArg (fun z => z.1 g) h
  change f (g⁻¹ • x) = f' (g⁻¹ • x) at he
  simpa only [hy] using he

def toInduced [Finite G] (x : X) :
    (permutationFunctionRepresentation k G X).IntertwiningMap
      (Representation.ind (MulAction.stabilizer G x).subtype
        (Representation.trivial k (MulAction.stabilizer G x) k)) :=
  (inducedToCoinducedEquiv (MulAction.stabilizer G x)
    (Representation.trivial k (MulAction.stabilizer G x) k)).symm.toIntertwiningMap.comp
      (toCoinduced x)

theorem toInduced_injective [Finite G] [MulAction.IsPretransitive G X] (x : X) :
    Function.Injective (toInduced (k := k) (G := G) x) :=
  (inducedToCoinducedEquiv (MulAction.stabilizer G x)
    (Representation.trivial k (MulAction.stabilizer G x) k)).symm.injective.comp
      (toCoinduced_injective x)

/-- Scalar dimension supplies the elementary uniform bound, including
empty and singleton point sets. -/
theorem uniform_card [Finite X] :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation k G X) (Nat.card X) := by
  letI : Fintype X := Fintype.ofFinite X
  intro M
  apply representationGeneratedBy_of_scalar_finrank_le M.toRepresentation
  simpa only [Module.finrank_fintype_fun_eq_card, ← Nat.card_eq_fintype_card] using
    M.toSubmodule.finrank_le

end SymmetricSubgroupAsymptotics.PermutationStabilizerInduced
