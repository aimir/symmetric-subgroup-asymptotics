import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOrthogonalDescent
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylLatticeLinear
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateReflectionSigns
import SymmetricSubgroupAsymptotics.CFSGIntegerPairingReflectionDescent

/-! Positive-root descent through a commuting pair of actual coordinate
reflections. Positivity and height loss are proved directly on the
original norm-two lattice, without folded-root recognition assumptions. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOrthogonalPositiveStep
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoCoordinateOrthogonalDescent CFSGNormTwoCoordinateReflectionSigns
open CFSGNormTwoGeckSignedRootColumns CFSGNormTwoGeckWeylWordDegree
open CFSGNormTwoGeckWeylLatticeLinear
open CFSGIntegerHeightSign CFSGIntegerPairingReflectionDescent
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

theorem simple_reflection_height (i : Fin r) (k : Roots A) :
    height ((rootPairing A hs hp).reflectionPerm (s₀ i) k).val=
      height k.val-integerPairing A k.val (s₀ i:Roots A).val := by
  rw [reflection_val]
  exact height_coordinate_step k.val i _

theorem orthogonal_pairing_preserved (i j : Fin r) (hij : A i j=0) (k : Roots A) :
    integerPairing A ((rootPairing A hs hp).reflectionPerm (s₀ j) k).val (s₀ i:Roots A).val=
      integerPairing A k.val (s₀ i:Roots A).val := by
  have he := wordRoot_integer_pairing A hs hp b₀ s₀ [j] k (s₀ i)
  change integerPairing A ((rootPairing A hs hp).reflectionPerm (s₀ j) k).val
    ((rootPairing A hs hp).reflectionPerm (s₀ j) (s₀ i)).val=_ at he
  rw [simple_reflection_fixes A hd hs hp ho j i hij] at he
  exact he

theorem orthogonal_pair_height (i j : Fin r) (hij : A i j=0) (k : Roots A) :
    height (wordRoot A hs hp b₀ s₀ [i,j] k).val=
      height k.val-(integerPairing A k.val (s₀ i:Roots A).val+
        integerPairing A k.val (s₀ j:Roots A).val) := by
  change height ((rootPairing A hs hp).reflectionPerm (s₀ i)
    ((rootPairing A hs hp).reflectionPerm (s₀ j) k)).val=_
  rw [simple_reflection_height A hd hs hp ho,simple_reflection_height A hd hs hp ho,
    orthogonal_pairing_preserved A hd hs hp ho i j hij]
  ring

theorem orthogonal_pair_nonnegative (i j : Fin r) (hij : A i j=0) (k : Roots A)
    (hk : ∀a,0≤k.val a) (hki : k≠(s₀ i:Roots A)) (hkj : k≠(s₀ j:Roots A)) :
    ∀a,0≤(wordRoot A hs hp b₀ s₀ [i,j] k).val a := by
  have hj := reflection_nonnegative A hd hs hp ho j k hk hkj
  have hne : (rootPairing A hs hp).reflectionPerm (s₀ j) k≠(s₀ i:Roots A) := by
    intro he
    apply hki
    apply ((rootPairing A hs hp).reflectionPerm (s₀ j)).injective
    rw [simple_reflection_fixes A hd hs hp ho j i hij]
    exact he
  exact reflection_nonnegative A hd hs hp ho i _ hj hne

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOrthogonalPositiveStep
