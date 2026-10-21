import SymmetricSubgroupAsymptotics.BinaryCommonEightShearCoordinates
import SymmetricSubgroupAsymptotics.BinaryPairPolynomialCoordinates

/-! One genuine extra top shear for both critical inner models.
The literal kernel vector120 is135 plus the constant255, so it is present
in both models. In Boolean labels it shears the physical variable by
variable3. Its leading behavior uses pointwise, not convolution, product. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryCommonEightExtraShearLeading

open BinaryBooleanFourPolynomialCoordinates BinaryElementaryPairMonomialWidth
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

def originalPermutation : Equiv.Perm (Fin 16) :=
  binaryEightCanonicalPairFrame.affinePermutation 1 (binaryVectorOfMask 8 120)

def booleanPermutation : Equiv.Perm (Fin 16) :=
  BinaryCommonEightShearCoordinates.pointLabels.trans
    (originalPermutation.trans BinaryCommonEightShearCoordinates.pointLabels.symm)

def actualDifference : V →ₗ[ZMod 2] V :=
  evaluate.comp ((BinaryBooleanFourPolynomialCoordinates.reindex booleanPermutation).toLinearMap.comp evaluate) -
    LinearMap.id

def operator : V →ₗ[ZMod 2] V := (monomialMultiplier 8).comp (derivative 0)

private theorem actual_basis : ∀ a : Fin 16,
    actualDifference (Pi.single a 1) = operator (Pi.single a 1) := by
  simp only [actualDifference, operator, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.id_apply, evaluate_basis, derivative_basis, apply_ite,
    monomialMultiplier_basis, map_zero]
  decide +kernel

theorem actualDifference_eq_operator : actualDifference = operator := by
  apply LinearMap.pi_ext
  intro a c
  have hs : Pi.single a c = c • Pi.single a (1 : ZMod 2) := by
    ext j
    simp [Pi.single_apply, mul_ite]
  simp only [hs, map_smul, actual_basis]

def target (a : Fin 16) : Fin 16 := ⟨(a.val + 7) % 16, Nat.mod_lt _ (by decide)⟩

private theorem extra_parts : ∀ a : Fin 16, a.val % 2 = 1 → a.val < 8 →
    (0 : Fin 4) ∈ support a ∧ Disjoint (support 8) (support (removeIndex 0 a)) ∧
      unionIndex 8 (removeIndex 0 a) = target a := by decide

theorem operator_hasLeading (v : V) (a : Fin 16)
    (hv : FiniteRowLeadingWeight.HasLeading v a)
    (hodd : a.val % 2 = 1) (hsmall : a.val < 8) :
    FiniteRowLeadingWeight.HasLeading (operator v) (target a) := by
  obtain ⟨hzero, hdisj, heq⟩ := extra_parts a hodd hsmall
  have h := monomialMultiplier_hasLeading 8 (removeIndex 0 a) (derivative 0 v)
    (derivative_hasLeading 0 a v hv hzero) hdisj
  rw [heq] at h
  exact h

end SymmetricSubgroupAsymptotics.BinaryCommonEightExtraShearLeading
