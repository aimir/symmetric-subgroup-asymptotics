import SymmetricSubgroupAsymptotics.CFSGTypeARootGeometryAction
import SymmetricSubgroupAsymptotics.CFSGTypeATransvectionHighestRoot
import SymmetricSubgroupAsymptotics.CFSGInnerActionFaithfulness

/-! One literal elementary matrix moves an original point-root group.
For a simple original PSL this proves that the complete automorphism
representation on its root geometry is faithful. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGTypeARootActionFaithfulness
open Matrix Module LinearMap Submodule CFSGTypeAProjectivePointRoots
open CFSGTypeARootLabels CFSGTypeARootIncidence CFSGTypeARootGeometryAction
open CFSGTypeAElementaryMatrices CFSGTypeATransvectionHighestRoot
variable {F : Type*} [Field F] [Finite F] {n : ℕ}

theorem exists_inner_moving_root (p : ℕ) [Fact p.Prime] [CharP F p] (hn : 3≤n) :
    ∃g : PSL (F:=F) (n:=Fin n),rootPermutationHom p hn (MulAut.conj g)≠1 := by
  let i : Fin n := ⟨0,by omega⟩
  let j : Fin n := ⟨1,by omega⟩
  have hij : i≠j := by intro he;have hh := congrArg Fin.val he;dsimp [i,j] at hh;omega
  let v : Fin n→F := Pi.single j 1
  have hv : v≠0 := by
    intro he
    have hh := congrArg (fun w : Fin n→F => w j) he
    exact (one_ne_zero : (1 : F)≠0) (by simpa only [v,Pi.single_eq_same,Pi.zero_apply] using hh)
  let A : Matrix.SpecialLinearGroup (Fin n) F := elementary hij (1 : F)
  have hAv : A.toLin' v≠0 := by
    intro he
    apply hv
    exact A.toLin'.injective (he.trans (map_zero A.toLin').symm)
  have hdiff : pointRoot (A.toLin' v)≠pointRoot v := by
    intro he
    have hc := (pointRoot_eq_iff_centre (by simpa using hn) hAv hv).mp he
    have hm : A.toLin' v∈F ∙ v := by
      rw [←hc]
      exact Submodule.mem_span_singleton_self _
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hm
    have hh := congrArg (fun w : Fin n→F => w i) hc
    dsimp only at hh
    rw [show A.toLin' v=v+(1*v j) • Pi.single i 1 from elementary_apply hij 1 v] at hh
    have hz : (0 : F)=1 := by simpa [v,hij,Ne.symm hij] using hh
    exact zero_ne_one hz
  refine ⟨CFSGTypeAProjectivePointRoots.projection A,?_⟩
  intro he
  let q := Projectivization.mk F v hv
  have hh := rootLabel_rootPermutation p hn (MulAut.conj (CFSGTypeAProjectivePointRoots.projection A)) (Sum.inl q)
  rw [he] at hh
  change pointLabel q=(pointLabel q).map (MulAut.conj (CFSGTypeAProjectivePointRoots.projection A)).toMonoidHom at hh
  rw [pointLabel_mk (by simpa using hn),pointRoot_map_conjugate] at hh
  exact hdiff hh.symm

theorem rootPermutationHom_injective (p : ℕ) [Fact p.Prime] [CharP F p] (hn : 3≤n)
    [IsSimpleGroup (PSL (F:=F) (n:=Fin n))] :
    Function.Injective (rootPermutationHom (F:=F) p hn) :=
  CFSGInnerActionFaithfulness.injective_of_inner_nontrivial _ (exists_inner_moving_root p hn)

end SymmetricSubgroupAsymptotics.CFSGTypeARootActionFaithfulness
