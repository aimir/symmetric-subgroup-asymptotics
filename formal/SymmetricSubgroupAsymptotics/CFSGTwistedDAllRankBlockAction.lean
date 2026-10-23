import SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankBlockMembership

/-! The actual all-rank retained block action is scalar extension on
its literal smaller split-D coordinates, fixing the last pair. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankBlockAction
open CFSGOrthogonalDSerreMatrices CFSGTwistedDAllRankBlockMembership
open CFSGTwistedA2FixedField CFSGTwistedDHyperbolicBlockMatrices
open CFSGTwistedDHyperbolicBlockCoordinates

theorem scalarBlockHom_val (n : ℕ) (q : CFSG.PrimePower)
    (g : (Mat (fixedField q) (n + 2))ˣ) :
    (scalarBlockHom n q g : Mat (q.Extension 2) (n + 3)) =
      blockMatrixHom (q.Extension 2) (n + 2)
        ((g : Mat (fixedField q) (n + 2)).map (fixedField q).subtype) := rfl

theorem scalarBlockHom_action (n : ℕ) (q : CFSG.PrimePower)
    (g : (Mat (fixedField q) (n + 2))ˣ)
    (v : Index (n + 3) → q.Extension 2) (x : Index (n + 2) → fixedField q)
    (hx : ∀ i, v (blockIndex (n + 2) i) = (x i : q.Extension 2))
    (i : Index (n + 2)) :
    ((scalarBlockHom n q g : Mat (q.Extension 2) (n + 3)) *ᵥ v)
      (blockIndex (n + 2) i) =
        (((g : Mat (fixedField q) (n + 2)) *ᵥ x) i : q.Extension 2) := by
  rw [scalarBlockHom_val]
  have h := congrFun (blockMatrixHom_action (q.Extension 2) (n + 2)
    ((g : Mat (fixedField q) (n + 2)).map (fixedField q).subtype) v) i
  have he : v ∘ blockIndex (n + 2) = (fixedField q).subtype ∘ x := funext hx
  dsimp only [Function.comp_apply] at h
  rw [he, ← RingHom.map_mulVec] at h
  exact h

end SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankBlockAction
