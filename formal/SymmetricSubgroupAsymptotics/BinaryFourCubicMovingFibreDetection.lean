import SymmetricSubgroupAsymptotics.BinaryFourCubicFibreTransportGauge

/-! A nonidentity element commuting with the original cubic transport
and fixing the fixed fibre must move the chosen moving fibre. Faithfulness
is used on all original physical points, not on an enlarged product group. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryFourCubicMovingFibreDetection
open BinaryFourBlockAugmentation BinaryFourCubicNormalizerPointShapes
open BinaryFourCubicFibreTransportGauge

theorem exists_moving {G X : Type} [Group G] [MulAction G X] [Finite X]
    [FaithfulSMul G X] (block : X → Fin 4) (s : G)
    (fixed : Local ≃ {x : X // block x = 0})
    (moving : Local ≃ {x : X // block x = 1})
    (hs : ∀ x : X, block (s • x) = blockCycle (block x))
    (hcard : Nat.card X = 16) (e : G) (hne : e ≠ 1)
    (hcommute : ∀ x : X, e • (s • x) = s • (e • x))
    (hfixed : ∀ v : Local, e • (fixed v).1 = (fixed v).1) :
    ∃ v : Local, e • (moving v).1 ≠ (moving v).1 := by
  classical
  by_contra hnot
  push_neg at hnot
  apply hne
  apply eq_of_smul_eq_smul (α := X)
  intro x
  obtain ⟨⟨v,b⟩,rfl⟩ := (pointEquiv block s fixed moving hs hcard).surjective x
  change e • pointMap block s fixed moving (v,b) =
    1 • pointMap block s fixed moving (v,b)
  fin_cases b <;>
    simp [pointMap,pow_two,mul_smul,hcommute,hfixed,hnot]

end SymmetricSubgroupAsymptotics.BinaryFourCubicMovingFibreDetection
