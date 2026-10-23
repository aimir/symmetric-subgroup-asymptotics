import SymmetricSubgroupAsymptotics.CFSGCartanDiagramLinearAction
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateBase
import Mathlib.LinearAlgebra.BilinearForm.Hom

/-! A literal Cartan-preserving coordinate permutation acts on the
actual norm-two integral root type. Pairing preservation is proved on
the coordinate basis and extended bilinearly. No finite-root census or
abstract root-system identification is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCartanDiagramRoots
open CFSGCartanDiagramLinearAction CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
variable {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℤ) (p : Equiv.Perm I) (hA : ∀ i j, A (p i) (p j)=A i j)

include hA

theorem pairing_permutation (x y : I→ℤ) :
    integerPairing A (permutationLinear p x) (permutationLinear p y)=integerPairing A x y := by
  have he : (integerPairing A).compl₁₂ (permutationLinear p).toLinearMap
      (permutationLinear p).toLinearMap=integerPairing A := by
    apply (Pi.basisFun ℤ I).ext
    intro i
    apply (Pi.basisFun ℤ I).ext
    intro j
    simp only [Pi.basisFun_apply,LinearMap.compl₁₂_apply]
    change integerPairing A (permutationLinear p (Pi.single i (1:ℤ) : I→ℤ))
      (permutationLinear p (Pi.single j (1:ℤ) : I→ℤ))=
        integerPairing A (Pi.single i (1:ℤ)) (Pi.single j (1:ℤ))
    rw [permutationLinear_single,permutationLinear_single]
    simpa only [integerPairing,Matrix.toBilin'_single] using hA i j
  exact LinearMap.congr_fun (LinearMap.congr_fun he x) y

theorem preserves_symm (i j : I) : A (p.symm i) (p.symm j)=A i j := by
  simpa only [p.apply_symm_apply] using (hA (p.symm i) (p.symm j)).symm

def rootPermutation : Equiv.Perm (Roots A) where
  toFun x:=⟨permutationLinear p x.val,by rw [pairing_permutation A p hA,x.property]⟩
  invFun x:=⟨permutationLinear p.symm x.val,by
    rw [pairing_permutation A p.symm (preserves_symm A p hA),x.property]⟩
  left_inv x:=by
    apply Subtype.ext
    funext i
    change x.val (p.symm (p i))=x.val i
    rw [p.symm_apply_apply]
  right_inv x:=by
    apply Subtype.ext
    funext i
    change x.val (p (p.symm i))=x.val i
    rw [p.apply_symm_apply]

theorem rootPermutation_val (x : Roots A) :
    (rootPermutation A p hA x).val=permutationLinear p x.val := rfl

theorem rootPermutation_pairing (x y : Roots A) :
    integerPairing A (rootPermutation A p hA x).val (rootPermutation A p hA y).val=
      integerPairing A x.val y.val := pairing_permutation A p hA x.val y.val

theorem rootPermutation_simple (hd : ∀ i,A i i=2) (i : I) :
    rootPermutation A p hA (coordinateRoot A hd i)=coordinateRoot A hd (p i) :=
  Subtype.ext (permutationLinear_single p i)

theorem rootPermutation_add_iff (x y z : Roots A) :
    (rootPermutation A p hA x).val=
      (rootPermutation A p hA y).val+(rootPermutation A p hA z).val ↔ x.val=y.val+z.val := by
  change permutationLinear p x.val=permutationLinear p y.val+permutationLinear p z.val ↔ _
  rw [←map_add,(permutationLinear p).injective.eq_iff]

end SymmetricSubgroupAsymptotics.CFSGNormTwoCartanDiagramRoots
