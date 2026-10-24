import SymmetricSubgroupAsymptotics.CFSGReeFFourRootTorusCharacters
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedTorus
import SymmetricSubgroupAsymptotics.CFSGE6GeckProductTorusRootAction
import SymmetricSubgroupAsymptotics.CFSGFFourE6ProductTorus

/-! The arithmetic two-unit characters are exactly the characters of
the actual raw E6 torus tuple of the same original fixed F4 torus.
Rectangular exponent composition uses the proved Cartan embedding;
there is no replacement of the original torus by an abstract one. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourRawRootCharacter
open CFSGNormTwoRootPairing CFSGIntegerMatrixPairing CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGRectangularMatrixPowerHom
open CFSGFFourE6ScalarTuple CFSGFFourRelativeScalarIndex CFSGReeFFourRootTorusExponentPilot
open CFSGReeFFourFieldParameters CFSGReeFFourFixedTorus CFSGReeFFourParameterizedTorusCovariance
open CFSGReeFFourRootTorusExponents
local notation "A" => CartanMatrix.E₆
local instance : DecidableEq (Roots A) := Classical.decEq _

private def rootRow (v : Fin 6→ℤ) : Matrix (Fin 1) (Fin 6) ℤ := fun _ i=>v i
private def foldedRow (v : Fin 6→ℤ) : Matrix (Fin 1) (Fin 4) ℤ :=
  fun _=>![firstBase v,secondBase v,secondAlpha v,firstAlpha v]

private theorem rootRow_embedding (v : Fin 6→ℤ) :
    (rootRow v*embedding)*relativeCartan=foldedRow v := by
  ext i j
  fin_cases i
  fin_cases j <;>
    simp [Matrix.mul_apply,Fin.sum_univ_six,Fin.sum_univ_four,rootRow,foldedRow,
      embedding,coordinateEmbedding,foldedCoordinate,relativeCartan,CartanMatrix.F₄,
      firstBase,firstAlpha,secondBase,secondAlpha] <;> ring

private theorem pairing_rootRow (v : Fin 6→ℤ) (j : Fin 6) :
    integerPairing A (E6Index j : Roots A).val v=(rootRow v*A) 0 j := by
  change integerPairing A (Pi.single j (1:ℤ)) v=_
  rw [integer_symmetric A CartanMatrix.E₆_transpose]
  simp [integerPairing,Matrix.toBilin'_apply,Matrix.mul_apply,rootRow,Pi.single_apply]

private theorem rootCharacter_row (K : Type) [_root_.Field K]
    (x : Fin 6→Kˣ) (k : Roots A) :
    CFSGE6GeckProductTorusRootAction.rootCharacter K x k=
      matrixPowerHom (rootRow k.val*A) x 0 := by
  change (∏j,x j^integerPairing A (E6Index j : Roots A).val k.val)=
    ∏j,x j^(rootRow k.val*A) 0 j
  apply Finset.prod_congr rfl
  intro j _
  rw [pairing_rootRow]

private theorem folded_character {G : Type*} [CommGroup G]
    (x : Fin 4→G) (v : Fin 6→ℤ) :
    matrixPowerHom (rootRow v*A) (scalarTupleHom x) 0=matrixPowerHom (foldedRow v) x 0 := by
  rw [←embedding_value,←matrixPowerHom_mul]
  have he : (rootRow v*A)*embedding=(rootRow v*embedding)*relativeCartan := by
    rw [Matrix.mul_assoc,cartan_embedding,←Matrix.mul_assoc]
  rw [he,rootRow_embedding]

private theorem unitPower_first (m : ℕ) (i : Fin 4) (hi : i=0∨i=1) (a : (Field m)ˣ) :
    unitPower m i a=a^(2^(m+1)) := by
  apply Units.ext
  rw [unitPower_val,Units.val_pow_eq_pow_val]
  rcases hi with rfl|rfl <;> rfl

private theorem monomial_combine {G : Type*} [CommGroup G]
    (a b : G) (p q r s e : ℤ) :
    a^p*b^r*(b^e)^s*(a^e)^q=a^(p+e*q)*b^(r+e*s) := by
  calc
    a^p*b^r*(b^e)^s*(a^e)^q =
        (a^p*b^r)*((a^e)^q*(b^e)^s) := by
      rw [mul_assoc, mul_comm ((b^e)^s) ((a^e)^q)]
    _ = (a^p*(a^e)^q)*(b^r*(b^e)^s) :=
      mul_mul_mul_comm _ _ _ _
    _ = (a^p*a^(e*q))*(b^r*b^(e*s)) := by
      rw [zpow_mul, zpow_mul]
    _ = a^(p+e*q)*b^(r+e*s) := by
      rw [←zpow_add, ←zpow_add]

theorem raw_root_character_eq (m : ℕ) (a b : (Field m)ˣ) (k : Roots A) :
    CFSGE6GeckProductTorusRootAction.rootCharacter (Field m)
      (CFSGFFourE6ProductTorus.torusTuple (Field m) (fixedTorusTuple m a b)) k=
        CFSGReeFFourRootTorusCharacters.rootCharacter m k (a,b) := by
  have ht : CFSGFFourE6ProductTorus.torusTuple (Field m) (fixedTorusTuple m a b)=
      scalarTupleHom (fixedTorusTuple m a b) := by
    funext i
    fin_cases i <;> rfl
  rw [ht,rootCharacter_row,folded_character]
  change (∏i : Fin 4,fixedTorusTuple m a b i^foldedRow k.val 0 i)=_
  rw [Fin.prod_univ_four]
  change a^firstBase k.val*b^secondBase k.val*
    (unitPower m 1 b)^secondAlpha k.val*(unitPower m 0 a)^firstAlpha k.val=_
  rw [unitPower_first m 1 (Or.inr rfl),unitPower_first m 0 (Or.inl rfl)]
  have he : ((2^(m+1) : ℕ) : ℤ)=(2 : ℤ)^(m+1) := by norm_cast
  have hpow (u : (Field m)ˣ) : u^(2^(m+1) : ℕ)=u^((2 : ℤ)^(m+1)) := by
    rw [←zpow_natCast,he]
  rw [hpow a,hpow b]
  change a^firstBase k.val*b^secondBase k.val*
    (b^((2 : ℤ)^(m+1)))^secondAlpha k.val*(a^((2 : ℤ)^(m+1)))^firstAlpha k.val=
      a^(firstBase k.val+(2 : ℤ)^(m+1)*firstAlpha k.val)*
        b^(secondBase k.val+(2 : ℤ)^(m+1)*secondAlpha k.val)
  exact monomial_combine a b _ _ _ _ _

end SymmetricSubgroupAsymptotics.CFSGReeFFourRawRootCharacter
