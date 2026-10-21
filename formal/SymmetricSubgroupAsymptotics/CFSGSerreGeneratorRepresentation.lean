import SymmetricSubgroupAsymptotics.CFSGSerreGeneratorRelations
import Mathlib.Algebra.Lie.Ideal
import Mathlib.LinearAlgebra.Quotient.Basic

/-! Universal representation of the literal rational Serre quotient from
genuine target generator identities. The six defining relator families are
evaluated explicitly; no quotient representation is included as input. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGSerreGeneratorRepresentation
open CFSG.Models.Chevalley CFSGSerreLocalNilpotence
variable {n : ℕ} {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    (H E F : Fin n → L)

def assignment : CartanMatrix.Generators (Fin n) → L
  | .H i => H i
  | .E i => E i
  | .F i => F i

def freeRepresentation : Free (n := n) →ₗ⁅ℚ⁆ L :=
  FreeLieAlgebra.lift ℚ (assignment H E F)

@[simp] theorem freeRepresentation_of (g : CartanMatrix.Generators (Fin n)) :
    freeRepresentation H E F (FreeLieAlgebra.of ℚ g) = assignment H E F g :=
  FreeLieAlgebra.lift_of_apply _ _

variable (A : Matrix (Fin n) (Fin n) ℤ)
    (hHH : ∀ i j, ⁅H i, H j⁆ = 0)
    (hEF : ∀ i j, ⁅E i, F j⁆ = if i = j then H i else 0)
    (hHE : ∀ i j, ⁅H i, E j⁆ = A i j • E j)
    (hHF : ∀ i j, ⁅H i, F j⁆ = -(A i j • F j))
    (hEE : ∀ i j, (LieAlgebra.ad ℚ L (E i) ^ (-A i j).toNat) ⁅E i, E j⁆ = 0)
    (hFF : ∀ i j, (LieAlgebra.ad ℚ L (F i) ^ (-A i j).toNat) ⁅F i, F j⁆ = 0)
include hHH hEF hHE hHF hEE hFF

theorem relations_map_zero (r : Free (n := n)) (hr : r ∈ CartanMatrix.Relations.toSet ℚ A) :
    freeRepresentation H E F r = 0 := by
  rcases hr with (((((hr | hr) | hr) | hr) | hr) | hr)
  · obtain ⟨⟨i, j⟩, rfl⟩ := hr
    simpa only [CartanMatrix.Relations.HH, Function.uncurry, Function.comp_apply,
      LieHom.map_lie, freeRepresentation_of, assignment] using hHH i j
  · obtain ⟨⟨i, j⟩, rfl⟩ := hr
    by_cases hij : i = j
    · subst j
      simp only [CartanMatrix.Relations.EF, Function.uncurry, Function.comp_apply,
        if_pos rfl, if_true, map_sub, LieHom.map_lie, freeRepresentation_of, assignment,
        hEF, sub_self]
    · simp only [CartanMatrix.Relations.EF, Function.uncurry, Function.comp_apply,
        if_neg hij, LieHom.map_lie, freeRepresentation_of, assignment, hEF]
  · obtain ⟨⟨i, j⟩, rfl⟩ := hr
    simp only [CartanMatrix.Relations.HE, Function.uncurry, Function.comp_apply,
      map_sub, LieHom.map_lie, map_zsmul, freeRepresentation_of, assignment, hHE, sub_self]
  · obtain ⟨⟨i, j⟩, rfl⟩ := hr
    simp only [CartanMatrix.Relations.HF, Function.uncurry, Function.comp_apply,
      map_add, LieHom.map_lie, map_zsmul, freeRepresentation_of, assignment, hHF, neg_add_cancel]
  · obtain ⟨⟨i, j⟩, rfl⟩ := hr
    simpa only [CartanMatrix.Relations.adE, Function.uncurry, Function.comp_apply,
      lieHom_ad_pow_apply, LieHom.map_lie, freeRepresentation_of, assignment] using hEE i j
  · obtain ⟨⟨i, j⟩, rfl⟩ := hr
    simpa only [CartanMatrix.Relations.adF, Function.uncurry, Function.comp_apply,
      lieHom_ad_pow_apply, LieHom.map_lie, freeRepresentation_of, assignment] using hFF i j

theorem ideal_le_kernel : CartanMatrix.Relations.toIdeal ℚ A ≤ (freeRepresentation H E F).ker := by
  apply LieSubmodule.lieSpan_le.mpr
  intro r hr
  exact (LieHom.mem_ker).mpr (relations_map_zero H E F A hHH hEF hHE hHF hEE hFF r hr)

def rationalRepresentation : RationalLie A →ₗ⁅ℚ⁆ L where
  __ := (CartanMatrix.Relations.toIdeal ℚ A).toSubmodule.liftQ
    (freeRepresentation H E F).toLinearMap (ideal_le_kernel H E F A hHH hEF hHE hHF hEE hFF)
  map_lie' := by
    intro x y
    obtain ⟨u, rfl⟩ := quotientMap_surjective A x
    obtain ⟨v, rfl⟩ := quotientMap_surjective A y
    change freeRepresentation H E F ⁅u, v⁆ =
      ⁅freeRepresentation H E F u, freeRepresentation H E F v⁆
    exact LieHom.map_lie _ _ _

@[simp] theorem rationalRepresentation_generator (g : CartanMatrix.Generators (Fin n)) :
    rationalRepresentation H E F A hHH hEF hHE hHF hEE hFF (generator A g) = assignment H E F g :=
  freeRepresentation_of H E F g

end SymmetricSubgroupAsymptotics.CFSGSerreGeneratorRepresentation
