import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationInitialElements

/-! The initial negative chain root commutes with the terminal short
root and the required negative-coordinate orbit. Four actual sparse
products vanish; the quadratic coefficient is included explicitly. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationInitialCommutation
open Matrix CFSGOrthogonalBSerreMatrices CFSGOrthogonalBGenerationShortArrays
open CFSGOrthogonalBGenerationInitialElements
variable (K : Type) [Field K]

private theorem sparse_products (s : ℕ) (b : Fin (s + 3) ⊕ Fin (s + 3))
    (hp : b ≠ Sum.inl (penIndex s)) (hn : b ≠ Sum.inr (lastIndex s)) :
    alphaArray K s * shortArray K (s + 3) b = 0 ∧
      shortArray K (s + 3) b * alphaArray K s = 0 ∧
      alphaArray K s * shortSecond K (s + 3) b = 0 ∧
      shortSecond K (s + 3) b * alphaArray K s = 0 := by
  rcases b with (i | i)
  · have hi : i ≠ penIndex s := fun he => hp (congrArg Sum.inl he)
    simp [alphaArray, shortArray, shortSecond, paired, pos,
      CFSGOrthogonalBSerreMatrices.neg, middle, mul_sub, sub_mul, hi, hi.symm]
  · have hi : i ≠ lastIndex s := fun he => hn (congrArg Sum.inr he)
    simp [alphaArray, shortArray, shortSecond, paired, pos,
      CFSGOrthogonalBSerreMatrices.neg, middle, mul_sub, sub_mul, hi, hi.symm]

theorem alpha_short_commute (s : ℕ) (b : Fin (s + 3) ⊕ Fin (s + 3))
    (hp : b ≠ Sum.inl (penIndex s)) (hn : b ≠ Sum.inr (lastIndex s)) (a d : K) :
    Commute (alphaUnit K s a) (shortUnit K (s + 3) b d) := by
  obtain ⟨hAX, hXA, hAD, hDA⟩ := sparse_products K s b hp hn
  change alphaUnit K s a * shortUnit K (s + 3) b d =
    shortUnit K (s + 3) b d * alphaUnit K s a
  apply Units.ext
  simp only [Units.val_mul, alphaUnit_val, shortUnit_val, mul_add, add_mul,
    mul_one, one_mul, smul_mul_assoc, mul_smul_comm, smul_smul,
    hAX, hXA, hAD, hDA, smul_zero, add_zero, zero_add]
  abel

theorem alpha_beta_commute (s : ℕ) (a d : K) :
    Commute (alphaUnit K s a) (betaUnit K s d) :=
  alpha_short_commute K s (Sum.inl (lastIndex s))
    (fun he => (pen_ne_last s).symm (Sum.inl.inj he)) (by intro he; cases he) a d

theorem alpha_negative_short_commute (s : ℕ) (i : Fin (s + 3)) (hi : i ≠ lastIndex s)
    (a d : K) : Commute (alphaUnit K s a) (shortUnit K (s + 3) (Sum.inr i) d) :=
  alpha_short_commute K s (Sum.inr i) (by intro he; cases he)
    (fun he => hi (Sum.inr.inj he)) a d

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationInitialCommutation
