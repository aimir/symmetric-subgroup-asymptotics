import SymmetricSubgroupAsymptotics.BinaryBooleanFourLeadingDerivatives

/-! Leading terms under actual pointwise multiplication. This is not
the convolution multiplication of the translation group algebra. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryBooleanFourPolynomialCoordinates

open BinaryElementaryPairMonomialWidth
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

def unionIndex (a b : Fin 16) : Fin 16 :=
  ⟨(a.val ||| b.val) % 16, Nat.mod_lt _ (by decide)⟩

theorem support_unionIndex : ∀ a b : Fin 16,
    support (unionIndex a b) = support a ∪ support b := by decide

def multiplyMonomial (b : Fin 16) : V →ₗ[ZMod 2] V where
  toFun v := monomial (support b) * v
  map_add' v z := by
    funext x
    exact mul_add _ _ _
  map_smul' c v := by
    funext x
    change monomial (support b) x * (c * v x) = c * (monomial (support b) x * v x)
    exact mul_left_comm _ _ _

def monomialMultiplier (b : Fin 16) : V →ₗ[ZMod 2] V :=
  evaluate.comp ((multiplyMonomial b).comp evaluate)

theorem monomialMultiplier_basis (b a : Fin 16) :
    monomialMultiplier b (Pi.single a 1) = Pi.single (unionIndex b a) 1 := by
  change evaluate (multiplyMonomial b (evaluate (Pi.single a 1))) = _
  rw [evaluate_basis]
  change evaluate (monomial (support b) * monomial (support a)) = _
  rw [monomial_mul, ← support_unionIndex, evaluate_monomial]

private theorem unionIndex_strict : ∀ b a j : Fin 16,
    Disjoint (support b) (support a) → j < a → unionIndex b j < unionIndex b a := by decide

private theorem unionIndex_mono : ∀ b a j : Fin 16,
    Disjoint (support b) (support a) → j ≤ a → unionIndex b j ≤ unionIndex b a := by decide

theorem monomialMultiplier_hasLeading (b a : Fin 16) (v : V)
    (hv : FiniteRowLeadingWeight.HasLeading v a)
    (hdisj : Disjoint (support b) (support a)) :
    FiniteRowLeadingWeight.HasLeading (monomialMultiplier b v) (unionIndex b a) := by
  apply LeadingOperatorColumns.hasLeading_apply_of_columns (monomialMultiplier b) v a
    (unionIndex b a) hv
  · rw [monomialMultiplier_basis]
    simpa only [Pi.single_eq_same] using (one_ne_zero : (1 : ZMod 2) ≠ 0)
  · intro j hj
    rw [monomialMultiplier_basis]
    have hne : unionIndex b j ≠ unionIndex b a := ne_of_lt (unionIndex_strict b a j hdisj hj)
    simp [Pi.single_apply, hne, Ne.symm hne]
  · intro c hc j hj
    rw [monomialMultiplier_basis]
    have hne : unionIndex b j ≠ c :=
      ne_of_lt (lt_of_le_of_lt (unionIndex_mono b a j hdisj hj) hc)
    simp [Pi.single_apply, hne, Ne.symm hne]

end SymmetricSubgroupAsymptotics.BinaryBooleanFourPolynomialCoordinates
