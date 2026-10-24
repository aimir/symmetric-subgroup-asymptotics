import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! Sparse integral entries for finite source-action certificates.
A row is a target label and an integer coefficient. Integral mixed
identities cast to the rational coefficient equations used by source
height induction; linear combinations evaluate without a dense sum.
No vector family is assumed to be a basis. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGIntegralRootActionEntries
variable {I:Type*} [DecidableEq I]

def integerRow (u:I×ℤ) : I→ℤ := Pi.single u.1 u.2
def rationalRow (u:I×ℤ) : I→ℚ := Pi.single u.1 (u.2:ℚ)

def coefficientCast : (I→ℤ)→+(I→ℚ) where
  toFun z i:=(z i:ℚ)
  map_zero':=by funext i;exact Int.cast_zero
  map_add' z w:=by funext i;exact Int.cast_add (z i) (w i)

theorem coefficientCast_smul (c:ℤ) (z:I→ℤ) :
    coefficientCast (c • z)=(c:ℚ) • coefficientCast z := by
  funext i
  change ((c*z i:ℤ):ℚ)=(c:ℚ)*(z i:ℚ)
  exact Int.cast_mul c (z i)

theorem coefficientCast_single (j:I) (c:ℤ) :
    coefficientCast (Pi.single j c)=Pi.single j (c:ℚ) := by
  funext i
  by_cases h:j=i <;> simp [coefficientCast,Pi.single_apply,h]

theorem coefficientCast_integerRow (u:I×ℤ) :
    coefficientCast (integerRow u)=rationalRow u := coefficientCast_single u.1 u.2

theorem rationalRow_support (u:I×ℤ) (k:I) (hk:rationalRow u k≠0) : k=u.1 := by
  by_contra h
  exact hk (by simp [rationalRow,Pi.single_apply,Ne.symm h])

theorem rationalRow_eq_zero (u:I×ℤ) (hu:u.2=0) : rationalRow u=0 := by
  simp [rationalRow,hu]

theorem combination_rationalRow [Fintype I] {V:Type*} [AddCommGroup V] [Module ℚ V]
    (v:I→V) (u:I×ℤ) :
    Fintype.linearCombination ℚ v (rationalRow u)=(u.2:ℚ) • v u.1 :=
  Fintype.linearCombination_apply_single ℚ v u.1 (u.2:ℚ)

theorem mixed_identity_cast {r:ℕ} (a i:Fin r) (j:I) (mu:ℤ)
    (u v:I×ℤ) (E F:I→I×ℤ)
    (h:(if a=i then (-mu) • Pi.single j 1 else 0)+u.2 • integerRow (E u.1)=
      v.2 • integerRow (F v.1)) :
    (if a=i then (-(mu:ℚ)) • Pi.single j 1 else 0)+(u.2:ℚ) • rationalRow (E u.1)=
      (v.2:ℚ) • rationalRow (F v.1) := by
  have hc:=congrArg (coefficientCast (I:=I)) h
  by_cases hai:a=i
  · simpa only [if_pos hai,map_add,coefficientCast_smul,coefficientCast_single,
      coefficientCast_integerRow,Int.cast_neg,Int.cast_one] using hc
  · simpa only [if_neg hai,map_add,map_zero,coefficientCast_smul,
      coefficientCast_integerRow] using hc

end SymmetricSubgroupAsymptotics.CFSGIntegralRootActionEntries
