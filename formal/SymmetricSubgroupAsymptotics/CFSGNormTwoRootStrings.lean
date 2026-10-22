import SymmetricSubgroupAsymptotics.CFSGNormTwoPairingBounds
import SymmetricSubgroupAsymptotics.CFSGNormTwoRootPairingReduced
import Mathlib.LinearAlgebra.RootSystem.Chain

/-! Genuine simply-laced root-string coefficients for the same norm-two
lattice: whenever adding a root is possible, the opposite coefficient is
zero. These are actual string computations, not supplied nilpotence data. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoRootStrings
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoPairingBounds
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)

theorem pairing_of_root_add {i j k : Roots A}
    (hk : (rootPairing A hs hp).root k=
      (rootPairing A hs hp).root i+(rootPairing A hs hp).root j) :
    integerPairing A i.val j.val= -1 := by
  have hv : k.val=i.val+j.val := by
    ext t
    have ht := congrFun hk t
    change (k.val t:ℚ)=(i.val t:ℚ)+(j.val t:ℚ) at ht
    exact_mod_cast ht
  have hn := k.property
  rw [hv,norm_add A hs,i.property,j.property] at hn
  omega

theorem pairing_of_root_sub {i j k : Roots A}
    (hk : (rootPairing A hs hp).root k=
      (rootPairing A hs hp).root j-(rootPairing A hs hp).root i) :
    integerPairing A i.val j.val=1 := by
  have hv : k.val=j.val-i.val := by
    ext t
    have ht := congrFun hk t
    change (k.val t:ℚ)=(j.val t:ℚ)-(i.val t:ℚ) at ht
    exact_mod_cast ht
  have hn := k.property
  rw [hv,norm_sub A hs,j.property,i.property,integer_symmetric A hs j.val i.val] at hn
  omega

variable [Finite (Roots A)]

theorem chainBotCoeff_of_root_add {i j k : Roots A}
    (hk : (rootPairing A hs hp).root k=
      (rootPairing A hs hp).root i+(rootPairing A hs hp).root j) :
    (rootPairing A hs hp).chainBotCoeff i j=0 := by
  apply (rootPairing A hs hp).chainBotCoeff_eq_zero_iff.mpr
  right
  rintro ⟨l,hl⟩
  have hadd := pairing_of_root_add A hs hp hk
  have hsub := pairing_of_root_sub A hs hp hl
  omega

theorem chainTopCoeff_of_root_sub {i j k : Roots A}
    (hk : (rootPairing A hs hp).root k=
      (rootPairing A hs hp).root j-(rootPairing A hs hp).root i) :
    (rootPairing A hs hp).chainTopCoeff i j=0 := by
  apply (rootPairing A hs hp).chainTopCoeff_eq_zero_iff.mpr
  right
  rintro ⟨l,hl⟩
  have hsub := pairing_of_root_sub A hs hp hk
  have hadd : integerPairing A i.val j.val= -1 :=
    pairing_of_root_add A hs hp (by simpa only [add_comm] using hl)
  omega

end SymmetricSubgroupAsymptotics.CFSGNormTwoRootStrings
