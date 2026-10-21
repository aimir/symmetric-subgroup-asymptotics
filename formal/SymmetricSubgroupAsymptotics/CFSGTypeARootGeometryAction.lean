import SymmetricSubgroupAsymptotics.CFSGTypeARootIncidence
import SymmetricSubgroupAsymptotics.CFSGTypeARootPermutation
import SymmetricSubgroupAsymptotics.CFSGSubgroupFamilyPermutation

/-! Every actual PSL automorphism acts on the original projective point
and dual-point labels. The definition retains their actual subgroup maps;
there is no prior choice of point-versus-hyperplane orientation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGTypeARootGeometryAction
open Matrix Module CFSGTypeAProjectivePointRoots CFSGTypeAHyperplaneRoots
open CFSGTypeARootLabels CFSGTypeARootIncidence CFSGTypeARootPermutation
variable {F : Type*} [Field F] [Finite F] {n : ℕ}

theorem rootLabel_map_exists (p : ℕ) [Fact p.Prime] [CharP F p] (hn : 3≤n)
    (a : MulAut (PSL (F:=F) (n:=Fin n))) (x : Vertex (F:=F) (n:=Fin n)) :
    ∃y,rootLabel y=(rootLabel x).map a.toMonoidHom := by
  have hdim : 3≤Fintype.card (Fin n) := by simpa using hn
  cases x with
  | inl q =>
    rcases automorphism_pointRoot_eq_point_or_hyperplane p hn a q.rep q.rep_nonzero with
      ⟨v,hv,he⟩|⟨f,hf,he⟩
    · refine ⟨Sum.inl (Projectivization.mk F v hv),?_⟩
      change pointLabel _=(pointRoot q.rep).map a.toMonoidHom
      rw [pointLabel_mk hdim]
      exact he.symm
    · refine ⟨Sum.inr (Projectivization.mk F f hf),?_⟩
      change hyperplaneLabel _=(pointRoot q.rep).map a.toMonoidHom
      rw [hyperplaneLabel_mk hdim]
      exact he.symm
  | inr q =>
    rcases automorphism_hyperplaneRoot_eq_point_or_hyperplane p hn a q.rep q.rep_nonzero with
      ⟨v,hv,he⟩|⟨f,hf,he⟩
    · refine ⟨Sum.inl (Projectivization.mk F v hv),?_⟩
      change pointLabel _=(hyperplaneRoot q.rep).map a.toMonoidHom
      rw [pointLabel_mk hdim]
      exact he.symm
    · refine ⟨Sum.inr (Projectivization.mk F f hf),?_⟩
      change hyperplaneLabel _=(hyperplaneRoot q.rep).map a.toMonoidHom
      rw [hyperplaneLabel_mk hdim]
      exact he.symm

def rootPermutationHom (p : ℕ) [Fact p.Prime] [CharP F p] (hn : 3≤n) :
    MulAut (PSL (F:=F) (n:=Fin n))→*Equiv.Perm (Vertex (F:=F) (n:=Fin n)) :=
  CFSGSubgroupFamilyPermutation.permutationHom rootLabel
    (rootLabel_injective (by simpa using hn)) (rootLabel_map_exists p hn)

theorem rootLabel_rootPermutation (p : ℕ) [Fact p.Prime] [CharP F p] (hn : 3≤n)
    (a : MulAut (PSL (F:=F) (n:=Fin n))) (x : Vertex (F:=F) (n:=Fin n)) :
    rootLabel (rootPermutationHom p hn a x)=(rootLabel x).map a.toMonoidHom :=
  CFSGSubgroupFamilyPermutation.label_permutation _ _ _ a x

end SymmetricSubgroupAsymptotics.CFSGTypeARootGeometryAction
