import SymmetricSubgroupAsymptotics.CFSGTypeATransvectionSubgroups
import Mathlib.Algebra.Group.Subgroup.Finite

/-! Actual PSL automorphisms permute the full original point-root and
hyperplane-root groups. Containment follows from original rank-one product
geometry; equality follows from their independently proved equal finite
parameter cardinalities. No orientation is chosen in this statement. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTypeARootPermutation
open Matrix Module LinearMap Submodule CFSGTypeAProjectivePointRoots CFSGTypeAHyperplaneRoots
open CFSGTypeATransvectionSubgroups CFSGTypeAProjectiveTransvectionRecognition
variable {F : Type*} [Field F] [Finite F] {n : ℕ}

omit [Finite F] in
private theorem pointRoot_all_transvections (v : Fin n→F)
    (x : Matrix.ProjectiveSpecialLinearGroup (Fin n) F) (hx : x∈pointRoot v) :
    IsProjectiveTransvection x := by
  obtain ⟨f,rfl⟩ := hx
  exact ⟨f.toAdd.val,v,f.toAdd.property,rfl⟩

omit [Finite F] in
private theorem hyperplaneRoot_all_transvections (f : Dual F (Fin n→F))
    (x : Matrix.ProjectiveSpecialLinearGroup (Fin n) F) (hx : x∈hyperplaneRoot f) :
    IsProjectiveTransvection x := by
  obtain ⟨v,rfl⟩ := hx
  exact ⟨f,v.toAdd.val,v.toAdd.property,rfl⟩

theorem transvection_subgroup_eq_root_of_card (hn : 3≤n)
    (H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin n) F))
    (hcard : Nat.card H=Nat.card F^(n-1))
    (hAll : ∀x,x∈H→IsProjectiveTransvection x) :
    (∃v : Fin n→F,v≠0 ∧ H=pointRoot v) ∨
      (∃f : Dual F (Fin n→F),f≠0 ∧ H=hyperplaneRoot f) := by
  have hpow : 1<Nat.card F^(n-1) :=
    one_lt_pow' (Finite.one_lt_card : 1<Nat.card F) (by omega : n-1≠0)
  have hH : H≠⊥ := by
    intro hbot
    have hc : Nat.card H=1 := by rw [hbot];exact Nat.card_unique
    omega
  rcases subgroup_le_point_or_hyperplane hn H hH hAll with ⟨v,hv,hle⟩|⟨f,hf,hle⟩
  · left
    refine ⟨v,hv,Subgroup.eq_of_le_of_card_ge hle ?_⟩
    rw [pointRoot_card hv,Fintype.card_fin,hcard]
  · right
    refine ⟨f,hf,Subgroup.eq_of_le_of_card_ge hle ?_⟩
    rw [hyperplaneRoot_card hf,Fintype.card_fin,hcard]

omit [Finite F] in
private theorem card_map_aut (H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin n) F))
    (a : MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin n) F)) :
    Nat.card (H.map a.toMonoidHom)=Nat.card H :=
  (Nat.card_congr (a.subgroupMap H).toEquiv).symm

theorem automorphism_pointRoot_eq_point_or_hyperplane
    (p : ℕ) [Fact p.Prime] [CharP F p] (hn : 3≤n)
    (a : MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin n) F))
    (v : Fin n→F) (hv : v≠0) :
    (∃w : Fin n→F,w≠0 ∧ (pointRoot v).map a.toMonoidHom=pointRoot w) ∨
      (∃f : Dual F (Fin n→F),f≠0 ∧ (pointRoot v).map a.toMonoidHom=hyperplaneRoot f) := by
  apply transvection_subgroup_eq_root_of_card hn
  · rw [card_map_aut,pointRoot_card hv,Fintype.card_fin]
  · rintro x ⟨y,hy,rfl⟩
    exact (automorphism_isProjectiveTransvection_iff p (by omega) a y).mpr
      (pointRoot_all_transvections v y hy)

theorem automorphism_hyperplaneRoot_eq_point_or_hyperplane
    (p : ℕ) [Fact p.Prime] [CharP F p] (hn : 3≤n)
    (a : MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin n) F))
    (f : Dual F (Fin n→F)) (hf : f≠0) :
    (∃v : Fin n→F,v≠0 ∧ (hyperplaneRoot f).map a.toMonoidHom=pointRoot v) ∨
      (∃g : Dual F (Fin n→F),g≠0 ∧ (hyperplaneRoot f).map a.toMonoidHom=hyperplaneRoot g) := by
  apply transvection_subgroup_eq_root_of_card hn
  · rw [card_map_aut,hyperplaneRoot_card hf,Fintype.card_fin]
  · rintro x ⟨y,hy,rfl⟩
    exact (automorphism_isProjectiveTransvection_iff p (by omega) a y).mpr
      (hyperplaneRoot_all_transvections f y hy)

end SymmetricSubgroupAsymptotics.CFSGTypeARootPermutation
