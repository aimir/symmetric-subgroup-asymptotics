import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeUnipotentCenterShape
import SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankBlockMembership
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexAllRankRootLines
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexUnipotentCenter

/-! The actual highest-root words over the fixed field belong to the
literal relative group via its retained split block. Together with the
necessary centre shape this gives the exact relative Sylow centre. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeHighestRoot
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationRootArrays
open CFSGTwistedDRelativeElementaryGroup CFSGTwistedDRelativeUnipotentSylow
open CFSGTwistedDAllRankBlockMembership CFSGTwistedDHyperbolicBlockMatrices
open CFSGTwistedDHyperbolicBlockOperators CFSGTwistedDHyperbolicBlockCoordinates
open CFSGOrthogonalDMatrixScalarExtension CFSGOrthogonalDIndexHighestRoot
open CFSGOrthogonalDIndexFlagVectors CFSGTwistedA2FixedField

theorem block_plus_array (K : Type) [Field K] (r : ℕ)
    (i j : Fin r) (a : K) :
    blockMatrixHom K r (plusArray i j a) = plusArray i.castSucc j.castSucc a := by
  rw [blockMatrixHom_eq_one_add]
  have he : plusArray i j a - 1 =
      Matrix.single (Sum.inl i) (Sum.inr j) a -
        Matrix.single (Sum.inl j) (Sum.inr i) a := by
    unfold plusArray
    abel
  rw [he, map_sub, zeroBlockLinear_single, zeroBlockLinear_single]
  simp only [blockIndex, plusArray]
  abel

theorem highest_mem_relative (s : ℕ) (q : CFSG.PrimePower) (a : fixedField q) :
    (highestInU (q.Extension 2) s (a : q.Extension 2)).val.val ∈
      relativeRootGroup (s + 2) q := by
  let i : Fin (s + 3) := 0
  let j : Fin (s + 3) := ⟨1, by omega⟩
  have hij : i ≠ j := by
    intro h
    have hv := congrArg Fin.val h
    change 0 = 1 at hv
    omega
  obtain ⟨g, hg, he⟩ :=
    CFSGOrthogonalDIndexAllRankRootLines.plus_line_all_ranks (fixedField q)
      (s + 3) (by omega) i j hij a
  have hm : (scalarBlockHom (s + 1) q g : Mat (q.Extension 2) (s + 4)) =
      plusArray (0 : Fin (s + 4)) (secondIndex s) (a : q.Extension 2) := by
    change blockMatrixHom (q.Extension 2) (s + 3)
      ((g : Mat (fixedField q) (s + 3)).map (fixedField q).subtype) = _
    have hs : (g : Mat (fixedField q) (s + 3)).map (fixedField q).subtype =
        plusArray i j (a : q.Extension 2) := by
      rw [he]
      ext x y
      simp only [plusArray, Matrix.map_apply, Matrix.add_apply, Matrix.sub_apply,
        Matrix.single_apply, Matrix.one_apply, map_add, map_sub]
      split_ifs <;> simp
    rw [hs, block_plus_array]
    rfl
  have hu : scalarBlockHom (s + 1) q g =
      (highestInU (q.Extension 2) s (a : q.Extension 2)).val.val := by
    apply Units.ext
    rw [hm, highestInU_val_plus]
  exact hu ▸ scalarBlockHom_maps_relative (s + 1) q hg

def highestInRelativeU (s : ℕ) (q : CFSG.PrimePower) (a : fixedField q) : unipotent s q :=
  ⟨⟨(highestInU (q.Extension 2) s (a : q.Extension 2)).val.val,
    highest_mem_relative s q a⟩, (highestInU (q.Extension 2) s (a : q.Extension 2)).property⟩

theorem highestInRelativeU_val (s : ℕ) (q : CFSG.PrimePower) (a : fixedField q) :
    ((highestInRelativeU s q a).val.val : Mat (q.Extension 2) (s + 4)) =
      plusArray (0 : Fin (s + 4)) (secondIndex s) (a : q.Extension 2) :=
  highestInU_val_plus (q.Extension 2) s (a : q.Extension 2)

theorem highestInRelativeU_mem_center (s : ℕ) (q : CFSG.PrimePower) (a : fixedField q) :
    highestInRelativeU s q a ∈ Subgroup.center (unipotent s q) := by
  apply Subgroup.mem_center_iff.mpr
  intro g
  let ga : CFSGOrthogonalDIndexUnipotent.unipotent (q.Extension 2) (s + 4) :=
    ⟨relativeInclusion s q g.val, g.property⟩
  have h := Subgroup.mem_center_iff.mp
    (highestInU_mem_center (q.Extension 2) s (a : q.Extension 2)) ga
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun u : CFSGOrthogonalDIndexUnipotent.unipotent (q.Extension 2) (s + 4) =>
    u.val.val) h

theorem center_eq_highest (s : ℕ) (q : CFSG.PrimePower)
    (z : unipotent s q) (hz : z ∈ Subgroup.center (unipotent s q)) :
    ∃ a : fixedField q, z = highestInRelativeU s q a := by
  obtain ⟨a, ha⟩ :=
    CFSGTwistedDRelativeUnipotentCenterShape.central_highest_fixed_shape s q z hz
  refine ⟨a, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  rw [highestInRelativeU_val]
  exact ha

end SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeHighestRoot
