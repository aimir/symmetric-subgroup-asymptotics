import SymmetricSubgroupAsymptotics.CFSGNormTwoRootStrings

/-! Exact root-neighbor existence in the same integer norm-two lattice.
The short strings follow by constructing the actual sum/difference root,
not by enumerating a named finite root system. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoRootNeighbors
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoPairingBounds
open CFSGNormTwoRootStrings
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)

theorem root_add_mem_iff (i j : Roots A) :
    (rootPairing A hs hp).root i+(rootPairing A hs hp).root j∈
      Set.range (rootPairing A hs hp).root ↔ integerPairing A i.val j.val= -1 := by
  constructor
  · rintro ⟨k,hk⟩
    exact pairing_of_root_add A hs hp hk
  · intro h
    let k : Roots A := ⟨i.val+j.val,by
      rw [norm_add A hs,i.property,j.property,h]
      norm_num⟩
    refine ⟨k,?_⟩
    ext t
    change ((i.val+j.val) t:ℚ)=(i.val t:ℚ)+(j.val t:ℚ)
    simp

theorem root_sub_mem_iff (i j : Roots A) :
    (rootPairing A hs hp).root j-(rootPairing A hs hp).root i∈
      Set.range (rootPairing A hs hp).root ↔ integerPairing A i.val j.val=1 := by
  constructor
  · rintro ⟨k,hk⟩
    exact pairing_of_root_sub A hs hp hk
  · intro h
    let k : Roots A := ⟨j.val-i.val,by
      rw [norm_sub A hs,j.property,i.property,integer_symmetric A hs j.val i.val,h]
      norm_num⟩
    refine ⟨k,?_⟩
    ext t
    change ((j.val-i.val) t:ℚ)=(j.val t:ℚ)-(i.val t:ℚ)
    simp

end SymmetricSubgroupAsymptotics.CFSGNormTwoRootNeighbors
