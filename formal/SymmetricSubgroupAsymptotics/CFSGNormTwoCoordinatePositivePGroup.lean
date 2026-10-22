import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateHeight
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckPositivePGroup

/-! The coordinate-height premise is discharged on the literal original
coordinate base. This is the shared E6/E7/E8 positive/negative p-group
installer; no Sylow or normalizer property is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositivePGroup
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoCoordinateHeight
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    {r : ℕ} (s : Fin r≃(coordinateBase A hd hs hp ho).support)

theorem rootGroup_isPGroup (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (neg : Bool) : IsPGroup p
      (CFSGNormTwoGeckPositivePGroup.rootGroup A hs hp (coordinateBase A hd hs hp ho) s K neg) := by
  cases neg
  · exact CFSGNormTwoGeckPositivePGroup.positive_isPGroup A hs hp
      (coordinateBase A hd hs hp ho) s coordinateHeight (simple_height A hd hs hp ho) K p
  · exact CFSGNormTwoGeckPositivePGroup.negative_isPGroup A hs hp
      (coordinateBase A hd hs hp ho) s coordinateHeight (simple_height A hd hs hp ho) K p

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositivePGroup
