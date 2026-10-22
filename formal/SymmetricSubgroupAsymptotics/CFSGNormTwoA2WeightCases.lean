import SymmetricSubgroupAsymptotics.CFSGNormTwoRootStepCoordinates

/-! The complete outside-A2 weight list follows from positive definiteness
and the actual root alpha+beta. There is no named root-system census. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoA2WeightCases
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoPairingBounds
open CFSGNormTwoRootStepCoordinates
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)

theorem outside_weights (i j gamma k : Roots A)
    (hg : (rootPairing A hs hp).root gamma=
      (rootPairing A hs hp).root i+(rootPairing A hs hp).root j)
    (hi : k≠i) (hj : k≠j) (hgamma : k≠gamma)
    (hni : k.val≠ -i.val) (hnj : k.val≠ -j.val) (hngamma : k.val≠ -gamma.val) :
    (integerPairing A i.val k.val=0 ∧ integerPairing A j.val k.val=0) ∨
    (integerPairing A i.val k.val= -1 ∧ integerPairing A j.val k.val=0) ∨
    (integerPairing A i.val k.val=1 ∧ integerPairing A j.val k.val= -1) ∨
    (integerPairing A i.val k.val=0 ∧ integerPairing A j.val k.val=1) ∨
    (integerPairing A i.val k.val= -1 ∧ integerPairing A j.val k.val=1) ∨
    (integerPairing A i.val k.val=0 ∧ integerPairing A j.val k.val= -1) ∨
    (integerPairing A i.val k.val=1 ∧ integerPairing A j.val k.val=0) := by
  have ha := root_pairing_interior A hs hp k i hi hni
  have hb := root_pairing_interior A hs hp k j hj hnj
  have hc := root_pairing_interior A hs hp k gamma hgamma hngamma
  rw [integer_symmetric A hs k.val i.val] at ha
  rw [integer_symmetric A hs k.val j.val] at hb
  rw [integer_symmetric A hs k.val gamma.val,root_add_val A hs hp hg,map_add,
    LinearMap.add_apply] at hc
  omega

end SymmetricSubgroupAsymptotics.CFSGNormTwoA2WeightCases
