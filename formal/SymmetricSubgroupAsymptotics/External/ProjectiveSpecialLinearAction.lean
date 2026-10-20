/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE-2.0.txt.
Authors: David Loeffler, Antoine Chambert-Loir
Selected PSL action lemmas ported from mathlib, revision
29c53517cf8e316f02ecadf525b142c15f8eb386.
-/
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Mathlib.LinearAlgebra.Center

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped LinearAlgebra.Projectivization Matrix
namespace Projectivization
open MulAction LinearEquiv SpecialLinearGroup
variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma SL_mulAction_ker :
    (MulAction.toPermHom (Matrix.SpecialLinearGroup ι K) (ℙ K (ι → K))).ker =
      Subgroup.center (Matrix.SpecialLinearGroup ι K) := by
  ext m
  simp only [MonoidHom.mem_ker, toPermHom_apply, Equiv.Perm.one_def, DFunLike.ext_iff, toPerm_apply,
    Equiv.refl_apply, Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨fun hm ↦ ?_, fun ⟨r, hr1, hr2⟩ l ↦ ?_⟩
  · set f : (ι → K) →ₗ[K] ι → K := (Matrix.SpecialLinearGroup.toLin' m).toLinearMap with hf
    obtain ⟨a, ha⟩ := f.exists_eq_smul_id_of_forall_notLinearIndependent fun (v : ι → K) ↦ by
      by_cases hv : v = 0
      · simp [hv, linearIndependent_fin2]
      · simpa [LinearIndependent.pair_iff' hv, mk_eq_mk_iff'] using hm (.mk K v hv)
    have hscalar : m.1 = Matrix.scalar ι a := calc
      m.1 = LinearMap.toMatrix' f := by
        rw [hf, Matrix.SpecialLinearGroup.toLin'_to_linearMap, LinearMap.toMatrix'_toLin']
      _ = (algebraMap K (Module.End K (ι → K)) a).toMatrix' := congrArg LinearMap.toMatrix' ha
      _ = Matrix.scalar ι a := LinearMap.toMatrix'_algebraMap a
    exact ⟨a, by simpa [hscalar] using m.2, hscalar.symm⟩
  · induction l using Projectivization.ind with | _ v hv =>
    simp only [smul_mk, mk_eq_mk_iff']
    use r
    change _ = m.1 • v
    simp [← hr2]

/-- The action of the special linear group on `ℙ F (ι → F)` factors through the
projective special linear group `PSL = SL ⧸ Z(SL)`. -/
def PSLAction.toPermHom :
    Matrix.ProjectiveSpecialLinearGroup ι K →* Equiv.Perm (ℙ K (ι → K)) :=
  QuotientGroup.lift _ (MulAction.toPermHom _ _) (le_of_eq SL_mulAction_ker.symm)

instance : MulAction (Matrix.ProjectiveSpecialLinearGroup ι K) (ℙ K (ι → K)) :=
  MulAction.compHom _ PSLAction.toPermHom

lemma _root_.Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk (g : Matrix.SpecialLinearGroup ι K)
    (p : ℙ K (ι → K)) : (g : Matrix.ProjectiveSpecialLinearGroup ι K) • p = g • p := rfl

theorem _root_.Matrix.ProjectiveSpecialLinearGroup.toPermHom_injective :
    Function.Injective (PSLAction.toPermHom (K := K) (ι := ι)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  rwa [← MonoidHom.mem_ker, PSLAction.toPermHom,
    QuotientGroup.ker_lift, SL_mulAction_ker, QuotientGroup.map_mk'_self,
    Subgroup.mem_bot] at hg

instance : FaithfulSMul (Matrix.ProjectiveSpecialLinearGroup ι K) (ℙ K (ι → K)) :=
  faithfulSMul_iff.2 fun g hg ↦
    Matrix.ProjectiveSpecialLinearGroup.toPermHom_injective <| Equiv.ext fun x ↦ by
      simpa using hg x

instance : IsPreprimitive (Matrix.ProjectiveSpecialLinearGroup ι K) (ℙ K (ι → K)) :=
  @MulAction.IsPreprimitive.of_surjective _ _ _ _ _ _ _ _ (QuotientGroup.mk' _)
    {toFun := id, map_smul' := by intros; simp; rfl} (prePrimitive_SL (ι := ι) (K := K))
    Function.surjective_id


end Projectivization
