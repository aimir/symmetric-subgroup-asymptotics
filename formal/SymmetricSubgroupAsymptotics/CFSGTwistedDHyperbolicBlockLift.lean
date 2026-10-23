import SymmetricSubgroupAsymptotics.CFSGTwistedDHyperbolicBlockMembership

/-! Whole smaller split-D words, not merely root generators, have actual
lifts above the original Derived action image. Their natural block
action is the scalar extension of the original smaller matrix action. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDHyperbolicBlockLift
open CFSGOrthogonalDSerreMatrices CFSGTwistedDHyperbolicBlockMembership
open CFSGTwistedDDerivedPairedRoots CFSGTwistedA2FixedField
open CFSGTwistedDHyperbolicBlockMatrices CFSGTwistedDHyperbolicBlockCoordinates

theorem exists_derived_lift (s : ℕ) (q : CFSG.PrimePower)
    (g : elementaryRootGroup (fixedField q) (s + 3)) :
    ∃ u : naturalDerivedPreimage s q, u.val.val = scalarBlockHom s q g.val := by
  obtain ⟨u, hu, he⟩ := scalarBlockHom_maps_elementary s q g.property
  exact ⟨⟨u, hu⟩, he⟩

theorem scalarBlockHom_val (s : ℕ) (q : CFSG.PrimePower)
    (g : (Mat (fixedField q) (s + 3))ˣ) :
    (scalarBlockHom s q g : Mat (q.Extension 2) (s + 4)) =
      blockMatrixHom (q.Extension 2) (s + 3)
        ((g : Mat (fixedField q) (s + 3)).map (fixedField q).subtype) := rfl

theorem scalarBlockHom_action (s : ℕ) (q : CFSG.PrimePower)
    (g : (Mat (fixedField q) (s + 3))ˣ)
    (v : Index (s + 4) → q.Extension 2) (x : Index (s + 3) → fixedField q)
    (hx : ∀ i, v (blockIndex (s + 3) i) = (x i : q.Extension 2))
    (i : Index (s + 3)) :
    ((scalarBlockHom s q g : Mat (q.Extension 2) (s + 4)) *ᵥ v)
      (blockIndex (s + 3) i) =
        (((g : Mat (fixedField q) (s + 3)) *ᵥ x) i : q.Extension 2) := by
  rw [scalarBlockHom_val]
  have h := congrFun (blockMatrixHom_action (q.Extension 2) (s + 3)
    ((g : Mat (fixedField q) (s + 3)).map (fixedField q).subtype) v) i
  have he : v ∘ blockIndex (s + 3) = (fixedField q).subtype ∘ x := funext hx
  dsimp only [Function.comp_apply] at h
  rw [he, ← RingHom.map_mulVec] at h
  exact h

end SymmetricSubgroupAsymptotics.CFSGTwistedDHyperbolicBlockLift
