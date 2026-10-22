import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationSignedPermutation
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationTerminalWeyl
import Mathlib.Logic.Equiv.Fin.Rotate

/-! A genuine B Coxeter lift: an actual SL-chain signed rotation,
followed by the original terminal B Weyl word. Both the actual coordinate
permutation and all scalar column weights are retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationCoxeter
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBGenerationSignedPermutation
open CFSGOrthogonalBGenerationTerminalWeyl CFSGTypeAMonomialMatrices
variable (K : Type) [Field K]

def prefixRowPermutation (r : ℕ) : Equiv.Perm (Index (r + 1)) :=
  naturalPermutation (r + 1) (finRotate (r + 1)).symm

def prefixWeight (r : ℕ) : Index (r + 1) → K :=
  naturalWeight K (r + 1) 0 (finRotate (r + 1)).symm

def terminalPermutation (r : ℕ) : Equiv.Perm (Index (r + 1)) :=
  Equiv.swap (pos (r + 1) (Fin.last r)) (CFSGOrthogonalBSerreMatrices.neg (r + 1) (Fin.last r))

def terminalSign (r : ℕ) (x : Index (r + 1)) : K :=
  if x = pos (r + 1) (Fin.last r) ∨
      x = CFSGOrthogonalBSerreMatrices.neg (r + 1) (Fin.last r) ∨ x = middle (r + 1)
    then -1 else 1

def coxeterCycle (r : ℕ) : Equiv.Perm (Index (r + 1)) :=
  (terminalPermutation r).trans (prefixRowPermutation r).symm

def coxeterSign (r : ℕ) (x : Index (r + 1)) : K :=
  terminalSign K r x * prefixWeight K r ((prefixRowPermutation r).symm (terminalPermutation r x))

def coxeterWeyl (r : ℕ) : elementaryRootGroup K (r + 1) :=
  signedPermutationElement K (r + 1) 0 (finRotate (r + 1)).symm * terminalWeyl K r

private theorem monomial_basis {I : Type*} [Fintype I] [DecidableEq I]
    (σ : Equiv.Perm I) (d : I → K) (x : I) :
    monomial σ d *ᵥ Pi.single x 1 = d (σ.symm x) • Pi.single (σ.symm x) 1 := by
  rw [Matrix.mulVec_single_one]
  funext j
  simp only [Matrix.col_apply, monomial_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  by_cases hj : j = σ.symm x
  · subst j
    simp
  · have hs : σ j ≠ x := by
      intro he
      apply hj
      simpa only [Equiv.symm_apply_apply] using congrArg σ.symm he
    simp [hj, hs]

theorem terminal_basis (r : ℕ) (x : Index (r + 1)) :
    ((terminalWeyl K r).val : Mat K (r + 1)) *ᵥ Pi.single x 1 =
      terminalSign K r x • Pi.single (terminalPermutation r x) 1 := by
  rw [terminalWeyl_val, Matrix.mulVec_single_one]
  funext j
  by_cases hp : x = pos (r + 1) (Fin.last r)
  · subst x
    simp [terminalArray, terminalSign, terminalPermutation, Matrix.col_apply,
      Matrix.single_apply, Matrix.one_apply, Pi.single_apply, pos,
      CFSGOrthogonalBSerreMatrices.neg, middle, eq_comm]
    all_goals try split_ifs
    all_goals ring
  · by_cases hn : x = CFSGOrthogonalBSerreMatrices.neg (r + 1) (Fin.last r)
    · subst x
      simp [terminalArray, terminalSign, terminalPermutation, Matrix.col_apply,
        Matrix.single_apply, Matrix.one_apply, Pi.single_apply, pos,
        CFSGOrthogonalBSerreMatrices.neg, middle, eq_comm]
      all_goals try split_ifs
      all_goals ring
    · by_cases hm : x = middle (r + 1)
      · subst x
        have hs : terminalPermutation r (middle (r + 1)) = middle (r + 1) :=
          Equiv.swap_apply_of_ne_of_ne hp hn
        rw [hs]
        simp [terminalArray, terminalSign, terminalPermutation, Matrix.col_apply,
          Matrix.single_apply, Matrix.one_apply, Pi.single_apply, pos,
          CFSGOrthogonalBSerreMatrices.neg, middle, eq_comm]
        all_goals try split_ifs
        all_goals ring
      · have hs : terminalPermutation r x = x := Equiv.swap_apply_of_ne_of_ne hp hn
        rw [hs]
        simp [terminalArray, terminalSign, terminalPermutation, Matrix.col_apply,
          Matrix.one_apply, Pi.single_apply, hp, hn, hm,
          Ne.symm hp, Ne.symm hn, Ne.symm hm, eq_comm]

theorem coxeter_basis (r : ℕ) (x : Index (r + 1)) :
    ((coxeterWeyl K r).val : Mat K (r + 1)) *ᵥ Pi.single x 1 =
      coxeterSign K r x • Pi.single (coxeterCycle r x) 1 := by
  change (((signedPermutationElement K (r + 1) 0 (finRotate (r + 1)).symm).val :
      Mat K (r + 1)) * ((terminalWeyl K r).val : Mat K (r + 1))) *ᵥ Pi.single x 1 = _
  rw [← Matrix.mulVec_mulVec, terminal_basis, Matrix.mulVec_smul,
    signedPermutationElement_val, monomial_basis, smul_smul]
  rfl

theorem coxeterSign_ne_zero (r : ℕ) (x : Index (r + 1)) : coxeterSign K r x ≠ 0 := by
  apply mul_ne_zero
  · unfold terminalSign
    split_ifs <;> simp
  · exact naturalWeight_ne_zero K (r + 1) 0 (finRotate (r + 1)).symm _

theorem coxeter_monomial (r : ℕ) :
    ((coxeterWeyl K r).val : Mat K (r + 1)) =
      monomial (coxeterCycle r).symm (coxeterSign K r ∘ (coxeterCycle r).symm) := by
  apply Matrix.ext_of_mulVec_single
  intro i
  rw [coxeter_basis]
  funext j
  simp only [Matrix.mulVec_single_one, Matrix.col_apply, monomial_apply,
    Function.comp_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  by_cases h : j = coxeterCycle r i
  · subst j
    simp
  · have hh : (coxeterCycle r).symm j ≠ i := by
      intro he
      apply h
      simpa only [Equiv.apply_symm_apply] using congrArg (coxeterCycle r) he
    simp [h, hh]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationCoxeter
