import SymmetricSubgroupAsymptotics.CFSGTwistedDPlaneFamilyAction
import SymmetricSubgroupAsymptotics.CFSGInnerActionFaithfulness
import SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankChainLift

/-! The intrinsic two-plane action is faithful under simplicity of
the SAME relative central quotient. A literal retained chain root
moves the standard fixed-field two-plane, so the inner action is
nontrivial. Original-model simplicity is transported by the proved
actual model equivalence; no ambient-D simplicity is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDPlaneActionFaithful
open CFSGOrthogonalDSerreMatrices CFSGTwistedDRelativeElementaryGroup
open CFSGTwistedDProjectiveUnipotent CFSGTwistedDProjectiveRootFamily
open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDFixedQuadraticAction
open CFSGTwistedDHighestPairOperator CFSGTwistedDSingularPlaneOrbit
open CFSGTwistedDPlaneFamilyAction CFSGTwistedA2FixedField CFSGTwistedDA2MatrixWitness
open CFSGOrthogonalDIndexFlagVectors CFSGTwistedDRelativeProjectiveModel

theorem singularLabel_inner_plane (s : ℕ) (q : CFSG.PrimePower)
    (g h : relativeRootGroup (s + 2) q) :
    singularLabel s q (singularPlane s q (g * h)) =
      (singularLabel s q (singularPlane s q h)).map
        (MulAut.conj (projection s q g)).toMonoidHom := by
  rw [singularLabel_plane, singularLabel_plane]
  change (projectiveHighestRootLine s q).map (MulAut.conj (projection s q (g * h))).toMonoidHom =
    ((projectiveHighestRootLine s q).map (MulAut.conj (projection s q h)).toMonoidHom).map
      (MulAut.conj (projection s q g)).toMonoidHom
  rw [Subgroup.map_map]
  congr 1
  apply MonoidHom.ext
  intro x
  simp [MulAut.conj_apply, map_mul, mul_assoc]

theorem singularAction_inner_plane (s : ℕ) (q : CFSG.PrimePower)
    (g h : relativeRootGroup (s + 2) q) :
    singularActionHom s q (MulAut.conj (projection s q g)) (singularPlane s q h) =
      singularPlane s q (g * h) := by
  apply singularLabel_injective s q
  rw [singularLabel_action]
  exact (singularLabel_inner_plane s q g h).symm

theorem exists_moved_original_plane (s : ℕ) (q : CFSG.PrimePower) :
    ∃ g : relativeRootGroup (s + 2) q, singularPlane s q g ≠ singularPlane s q 1 := by
  let i : Fin (s + 3) := ⟨2, by omega⟩
  have hi : i ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    change 2 = 0 at hv
    omega
  let g : relativeRootGroup (s + 2) q :=
    ⟨(chain (q.Extension 2) (s + 4) i.castSucc (0 : Fin (s + 3)).castSucc
      ((Fin.castSucc_injective (s + 3)).ne hi) 1).val,
      CFSGTwistedDAllRankChainLift.chain_mem (s + 2) q i 0 hi 1⟩
  have hcoord :
      (fixedLinearHom (s + 2) q g (CFSGTwistedDHighestPairOperator.firstVector s q)).val
        (Sum.inl i.castSucc) = 1 := by
    rw [fixedLinearHom_apply, firstVector_val]
    change (((chain (q.Extension 2) (s + 4) i.castSucc (0 : Fin (s + 3)).castSucc
      ((Fin.castSucc_injective (s + 3)).ne hi) 1).val : Mat (q.Extension 2) (s + 4)) *ᵥ
        Pi.single (Sum.inl 0) 1) (Sum.inl i.castSucc) = 1
    rw [CFSGTwistedDRetainedForkRoots.chain_val, Matrix.mulVec_single_one]
    simp [Matrix.col_apply, Matrix.one_apply, Matrix.single_apply, i, Fin.ext_iff]
  have hstandard : ∀ x ∈ standardRootPlane s q, x.val (Sum.inl i.castSucc) = 0 := by
    intro x hx
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hx
    simp [CFSGTwistedDHighestPairOperator.firstVector,
      CFSGTwistedDHighestPairOperator.secondVector, positiveBasis,
      Pi.single_apply, secondIndex, i, Fin.ext_iff]
  have hbase : conjugateRootPlane s q (1 : relativeRootGroup (s + 2) q) = standardRootPlane s q := by
    rw [conjugateRootPlane, map_one]
    change (standardRootPlane s q).map LinearMap.id = _
    exact Submodule.map_id _
  refine ⟨g, ?_⟩
  intro he
  have hp := congrArg Subtype.val he
  change conjugateRootPlane s q g = conjugateRootPlane s q (1 : relativeRootGroup (s + 2) q) at hp
  have hm : fixedLinearHom (s + 2) q g (CFSGTwistedDHighestPairOperator.firstVector s q) ∈
      conjugateRootPlane s q g := by
    rw [CFSGTwistedDPlaneRootLine.conjugateRootPlane_eq_span]
    exact Submodule.subset_span (Or.inl rfl)
  rw [hp, hbase] at hm
  have hz := hstandard _ hm
  rw [hcoord] at hz
  exact one_ne_zero hz

theorem singularActionHom_injective (s : ℕ) (q : CFSG.PrimePower)
    [IsSimpleGroup (Projective s q)] : Function.Injective (singularActionHom s q) := by
  apply CFSGInnerActionFaithfulness.injective_of_inner_nontrivial
  obtain ⟨g, hg⟩ := exists_moved_original_plane s q
  refine ⟨projection s q g, ?_⟩
  intro he
  have hm := singularAction_inner_plane s q g 1
  rw [he] at hm
  have hp : singularPlane s q 1 = singularPlane s q g := by
    simpa only [Equiv.Perm.one_apply, mul_one] using hm
  exact hg hp.symm

def originalSingularActionHom (s : ℕ) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedD (s + 4) q)] :
    MulAut (CFSG.Models.TwistedD (s + 4) q) →* Equiv.Perm (SingularPlanes s q) :=
  (singularActionHom s q).comp (MulAut.congr (originalRelativeProjectiveEquiv s q)).toMonoidHom

theorem originalSingularActionHom_injective (s : ℕ) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedD (s + 4) q)] :
    Function.Injective (originalSingularActionHom s q) := by
  let e := originalRelativeProjectiveEquiv s q
  letI : IsSimpleGroup (Projective s q) := e.symm.isSimpleGroup
  exact (singularActionHom_injective s q).comp (MulAut.congr e).injective

end SymmetricSubgroupAsymptotics.CFSGTwistedDPlaneActionFaithful
