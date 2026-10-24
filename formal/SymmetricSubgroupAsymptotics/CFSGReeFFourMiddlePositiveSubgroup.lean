import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleWordMultiplication

/-! The ordinary four-parameter middle cell is a genuine subgroup of
the ambient positive E6 group. This is before imposing the Ree fixed
condition. Its closure uses the checked SAME-source multiplication and
inverse; membership retains an actual original middle-word witness. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourMiddlePositiveSubgroup
open CFSGReeFFourFieldParameters CFSGFFourOriginalMiddleWords
open CFSGReeFFourMiddleFixedWords CFSGReeFFourMiddleWordInjective
open CFSGReeFFourMiddleWordMultiplication CFSGTwistedE6GeckPositiveTwist

theorem matrixMiddleWord_mul (m : ℕ) (a b c d e f s t : Field m) :
    matrixMiddleWord (Field m) a b c d * matrixMiddleWord (Field m) e f s t =
      matrixMiddleWord (Field m) (a+e) (b+f) (c+s+e*b) (d+t+e^2*b) := by
  apply Subtype.ext
  have h := congrArg (rawHom (Field m)) (middleWord_mul m a b c d e f s t)
  simpa only [map_mul, rawHom_middleWord, Subgroup.coe_mul] using h

theorem matrixMiddleWord_zero (m : ℕ) : matrixMiddleWord (Field m) 0 0 0 0 = 1 := by
  apply Subtype.ext
  have h := congrArg (rawHom (Field m)) (middleWord_zero m)
  simpa only [rawHom_middleWord, map_one, Subgroup.coe_one] using h

theorem matrixMiddleWord_inv (m : ℕ) (a b c d : Field m) :
    (matrixMiddleWord (Field m) a b c d)⁻¹ =
      matrixMiddleWord (Field m) a b (c+a*b) (d+a^2*b) := by
  apply Subtype.ext
  have h := congrArg (rawHom (Field m)) (middleWord_inv m a b c d)
  simpa only [map_inv, rawHom_middleWord, Subgroup.coe_inv] using h

def middlePositiveSubgroup (m : ℕ) : Subgroup (Positive (Field m)) where
  carrier := {u | ∃ a b c d : Field m, matrixMiddleWord (Field m) a b c d = u}
  one_mem' := ⟨0,0,0,0,matrixMiddleWord_zero m⟩
  mul_mem' := by
    rintro u v ⟨a,b,c,d,rfl⟩ ⟨e,f,s,t,rfl⟩
    exact ⟨a+e,b+f,c+s+e*b,d+t+e^2*b,(matrixMiddleWord_mul m a b c d e f s t).symm⟩
  inv_mem' := by
    rintro u ⟨a,b,c,d,rfl⟩
    exact ⟨a,b,c+a*b,d+a^2*b,(matrixMiddleWord_inv m a b c d).symm⟩

theorem matrixMiddleWord_mem (m : ℕ) (a b c d : Field m) :
    matrixMiddleWord (Field m) a b c d ∈ middlePositiveSubgroup m := ⟨a,b,c,d,rfl⟩

theorem exists_source_middle_parameters (m : ℕ) (u : Positive (Field m))
    (hu : u ∈ middlePositiveSubgroup m) :
    ∃ a b c d : Field m, rawHom (Field m) (middleWord m a b c d) = u.val := by
  obtain ⟨a,b,c,d,rfl⟩ := hu
  exact ⟨a,b,c,d,rawHom_middleWord m a b c d⟩

end SymmetricSubgroupAsymptotics.CFSGReeFFourMiddlePositiveSubgroup
