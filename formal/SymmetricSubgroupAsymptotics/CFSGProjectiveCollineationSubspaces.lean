import SymmetricSubgroupAsymptotics.CFSGProjectiveFrameCoordinates

/-! A literal collineation transports actual projective subspaces. This
is proved from its ternary line incidence, without semilinear recognition. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGProjectiveFrameCoordinates
open Submodule
variable {F n : Type*} [Field F]

private theorem mem_subspace_iff_le (S : Projectivization.Subspace F (n→F))
    (p : Points (F:=F) (n:=n)) : p∈S↔p.submodule≤Projectivization.Subspace.submodule S := by
  have hh := Submodule.mem_projectivization_iff_submodule_le
    (Projectivization.Subspace.submodule S) p
  simpa only [Submodule.projectivization,OrderIso.symm_apply_apply] using hh

private theorem mem_of_onLine (S : Projectivization.Subspace F (n→F))
    {p q r : Points (F:=F) (n:=n)} (hq : q∈S) (hr : r∈S) (hp : OnLine p q r) : p∈S := by
  apply (mem_subspace_iff_le S p).mpr
  exact hp.trans (sup_le ((mem_subspace_iff_le S q).mp hq) ((mem_subspace_iff_le S r).mp hr))

private theorem add_onLine (v w : n→F) (hv : v≠0) (hw : w≠0) (hs : v+w≠0) :
    OnLine (Projectivization.mk F (v+w) hs) (Projectivization.mk F v hv)
      (Projectivization.mk F w hw) := by
  unfold OnLine
  rw [Projectivization.submodule_mk,Projectivization.submodule_mk,
    Projectivization.submodule_mk,Submodule.span_singleton_le_iff_mem]
  exact ((F ∙ v) ⊔ (F ∙ w)).add_mem
    ((show F ∙ v≤(F ∙ v) ⊔ (F ∙ w) from le_sup_left) (Submodule.mem_span_singleton_self v))
    ((show F ∙ w≤(F ∙ v) ⊔ (F ∙ w) from le_sup_right) (Submodule.mem_span_singleton_self w))

def mapSubspace (f : collineationGroup (F:=F) (n:=n))
    (S : Projectivization.Subspace F (n→F)) : Projectivization.Subspace F (n→F) where
  carrier := (f : Equiv.Perm (Points (F:=F) (n:=n))) '' S
  mem_add' := by
    intro v w hv hw hs hvm hwm
    obtain ⟨p,hp,hfp⟩ := hvm
    obtain ⟨q,hq,hfq⟩ := hwm
    let z : Points (F:=F) (n:=n) := Projectivization.mk F (v+w) hs
    have hline : OnLine z (f.val p) (f.val q) := by
      rw [hfp,hfq]
      exact add_onLine v w hv hw hs
    have hpre : OnLine ((f : Equiv.Perm (Points (F:=F) (n:=n))).symm z) p q := by
      apply (f.property _ _ _).mp
      simpa only [Equiv.apply_symm_apply] using hline
    exact ⟨(f : Equiv.Perm (Points (F:=F) (n:=n))).symm z,
      mem_of_onLine S hp hq hpre,Equiv.apply_symm_apply _ _⟩

theorem mem_mapSubspace (f : collineationGroup (F:=F) (n:=n))
    (S : Projectivization.Subspace F (n→F)) (p : Points (F:=F) (n:=n)) :
    p∈mapSubspace f S↔(f : Equiv.Perm (Points (F:=F) (n:=n))).symm p∈S := by
  constructor
  · rintro ⟨q,hq,rfl⟩
    simpa only [Equiv.symm_apply_apply] using hq
  · intro hp
    exact ⟨_,hp,Equiv.apply_symm_apply _ _⟩

def subspaceOrderIso (f : collineationGroup (F:=F) (n:=n)) :
    Projectivization.Subspace F (n→F)≃oProjectivization.Subspace F (n→F) where
  toFun := mapSubspace f
  invFun := mapSubspace f⁻¹
  left_inv S := by
    ext p
    change p∈mapSubspace f⁻¹ (mapSubspace f S)↔p∈S
    rw [mem_mapSubspace,mem_mapSubspace]
    change ((f : Equiv.Perm (Points (F:=F) (n:=n))).symm
      ((f : Equiv.Perm (Points (F:=F) (n:=n))) p)∈S)↔p∈S
    rw [Equiv.symm_apply_apply]
  right_inv S := by
    ext p
    change p∈mapSubspace f (mapSubspace f⁻¹ S)↔p∈S
    rw [mem_mapSubspace,mem_mapSubspace]
    change (((f : Equiv.Perm (Points (F:=F) (n:=n))))
      ((f : Equiv.Perm (Points (F:=F) (n:=n))).symm p)∈S)↔p∈S
    rw [Equiv.apply_symm_apply]
  map_rel_iff' := by
    intro S T
    constructor
    · intro h p hp
      have hh := h (show f.val p∈mapSubspace f S from ⟨p,hp,rfl⟩)
      change f.val p∈mapSubspace f T at hh
      simpa only [mem_mapSubspace,Equiv.symm_apply_apply] using hh
    · intro h p hp
      apply (mem_mapSubspace f T p).mpr
      exact h ((mem_mapSubspace f S p).mp hp)

end SymmetricSubgroupAsymptotics.CFSGProjectiveFrameCoordinates
