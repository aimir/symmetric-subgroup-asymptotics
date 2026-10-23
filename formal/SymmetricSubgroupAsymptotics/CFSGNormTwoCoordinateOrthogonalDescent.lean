import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateInversionCount

/-! Actual orthogonal coordinate reflections commute and preserve each
other's simple root. Consequently a pair of negative orthogonal simple
images gives a two-step decrease of the finite inversion count. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOrthogonalDescent
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckSignedRootColumns
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylWordAlgebra
open CFSGNormTwoCoordinateInversionCount
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

theorem simple_reflection_fixes (i j : Fin r) (hji : A j i=0) :
    (rootPairing A hs hp).reflectionPerm (s₀ i) (s₀ j)=(s₀ j : Roots A) := by
  apply Subtype.ext
  rw [reflection_val]
  change (Pi.single j (1:ℤ) : Fin r→ℤ)-
    integerPairing A (Pi.single j 1) (Pi.single i 1) • Pi.single i 1=Pi.single j 1
  rw [show integerPairing A (Pi.single j 1) (Pi.single i 1)=A j i from
    Matrix.toBilin'_single A j i,hji,zero_smul,sub_zero]

theorem orthogonal_reflections_commute (i j : Fin r) (hij : A i j=0) (hji : A j i=0) :
    Commute ((rootPairing A hs hp).reflectionPerm (s₀ i))
      ((rootPairing A hs hp).reflectionPerm (s₀ j)) := by
  let P := rootPairing A hs hp
  have hpij : P.pairing (s₀ i) (s₀ j)=0 := by
    rw [pairing_cast]
    change (integerPairing A (Pi.single i 1) (Pi.single j 1):ℚ)=0
    rw [show integerPairing A (Pi.single i 1) (Pi.single j 1)=A i j from
      Matrix.toBilin'_single A i j,hij,Int.cast_zero]
  have hpji : P.pairing (s₀ j) (s₀ i)=0 := by
    rw [pairing_cast]
    change (integerPairing A (Pi.single j 1) (Pi.single i 1):ℚ)=0
    rw [show integerPairing A (Pi.single j 1) (Pi.single i 1)=A j i from
      Matrix.toBilin'_single A j i,hji,Int.cast_zero]
  have hc := P.isOrthogonal_comm (i:=s₀ i) (j:=s₀ j) ⟨hpij,hpji⟩
  change P.reflectionPerm (s₀ i)*P.reflectionPerm (s₀ j)=
    P.reflectionPerm (s₀ j)*P.reflectionPerm (s₀ i)
  apply Equiv.ext
  intro k
  apply P.root.injective
  simpa only [Equiv.Perm.mul_apply,RootPairing.root_reflectionPerm,LinearEquiv.mul_apply]
    using LinearEquiv.congr_fun hc.eq (P.root k)

theorem inversionCount_append_pair (w : List (Fin r)) (i j : Fin r) (hji : A j i=0)
    (hi : ∀k,(wordRoot A hs hp b₀ s₀ w (s₀ i)).val k≤0)
    (hj : ∀k,(wordRoot A hs hp b₀ s₀ w (s₀ j)).val k≤0) :
    inversionCount A hd hs hp ho (w++[i,j])+2=inversionCount A hd hs hp ho w := by
  have hfirst := inversionCount_append_simple A hd hs hp ho w i hi
  have hj' : ∀k,(wordRoot A hs hp b₀ s₀ (w++[i]) (s₀ j)).val k≤0 := by
    rw [wordRoot_append]
    change ∀k,(wordRoot A hs hp b₀ s₀ w
      ((rootPairing A hs hp).reflectionPerm (s₀ i) (s₀ j))).val k≤0
    rw [simple_reflection_fixes A hd hs hp ho i j hji]
    exact hj
  have hsecond := inversionCount_append_simple A hd hs hp ho (w++[i]) j hj'
  have he : (w++[i])++[j]=w++[i,j] := by simp only [List.append_assoc,List.cons_append,List.nil_append]
  rw [he] at hsecond
  omega

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOrthogonalDescent
