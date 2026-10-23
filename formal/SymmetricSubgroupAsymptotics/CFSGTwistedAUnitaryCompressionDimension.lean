import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitarySubspaceCompression
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Literal middle compression removes exactly the first axis from
an isotropic space containing it. In particular a two-plane compresses
to a one-dimensional singular residue, with no residue classification
or group-order premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGHermitianHyperbolicCompression

theorem unitaryCompressedSpace_split_eq (q : CFSG.PrimePower) (s : ℕ)
    (S : Submodule (q.Extension 2) (Fin (s + 3) → q.Extension 2)) :
    compressedSpace (S.map (unitarySplitLinearEquiv q s).toLinearMap) =
      unitaryCompressedSpace q s S := by
  ext v
  change middleVector v ∈ S.map (unitarySplitLinearEquiv q s).toLinearMap ↔
    unitaryMiddleVector q s v ∈ S
  constructor
  · rintro ⟨x, hx, he⟩
    have hh := congrArg (unitarySplitLinearEquiv q s).symm he
    change (unitarySplitLinearEquiv q s).symm (unitarySplitLinearEquiv q s x) =
      unitaryMiddleVector q s v at hh
    rw [LinearEquiv.symm_apply_apply] at hh
    exact hh ▸ hx
  · intro hv
    refine ⟨unitaryMiddleVector q s v, hv, ?_⟩
    change unitarySplitLinearEquiv q s ((unitarySplitLinearEquiv q s).symm (middleVector v)) = _
    exact (unitarySplitLinearEquiv q s).apply_symm_apply _

theorem unitaryCompressedSpace_finrank_add_one (q : CFSG.PrimePower) (s : ℕ)
    (S : Submodule (q.Extension 2) (Fin (s + 3) → q.Extension 2))
    (he : Pi.single (0 : Fin (s + 3)) 1 ∈ S)
    (hS : ∀ x ∈ S, ∀ y ∈ S, unitaryNaturalPair q (s + 2) x y = 0) :
    Module.finrank (q.Extension 2) S =
      1 + Module.finrank (q.Extension 2) (unitaryCompressedSpace q s S) := by
  let T := S.map (unitarySplitLinearEquiv q s).toLinearMap
  have heT : (headVector : CFSGTwistedAUnitaryUpperArrays.Index (Fin (s + 1)) → q.Extension 2) ∈ T :=
    ⟨Pi.single 0 1, he, unitarySplit_head q s⟩
  have hzT : ∀ x ∈ T, x (.inr (.inr ())) = 0 := by
    rintro x ⟨y, hy, rfl⟩
    change y (Fin.last (s + 2)) = 0
    simpa only [unitaryNaturalPair_first] using hS _ he y hy
  let e := ((unitarySplitLinearEquiv q s).submoduleMap S).trans (compressionEquiv T heT hzT)
  have hd := e.finrank_eq
  rw [Module.finrank_prod, Module.finrank_self] at hd
  have hc : Module.finrank (q.Extension 2) (compressedSpace T) =
      Module.finrank (q.Extension 2) (unitaryCompressedSpace q s S) :=
    (LinearEquiv.ofEq _ _ (unitaryCompressedSpace_split_eq q s S)).finrank_eq
  exact hd.trans (congrArg (fun n : ℕ => 1 + n) hc)

theorem unitaryCompressedPlane_finrank_one (q : CFSG.PrimePower) (s : ℕ)
    (S : Submodule (q.Extension 2) (Fin (s + 3) → q.Extension 2))
    (he : Pi.single (0 : Fin (s + 3)) 1 ∈ S)
    (hS : ∀ x ∈ S, ∀ y ∈ S, unitaryNaturalPair q (s + 2) x y = 0)
    (hd : Module.finrank (q.Extension 2) S = 2) :
    Module.finrank (q.Extension 2) (unitaryCompressedSpace q s S) = 1 := by
  have hh := unitaryCompressedSpace_finrank_add_one q s S he hS
  omega

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
