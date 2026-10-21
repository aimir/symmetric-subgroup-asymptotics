import Mathlib.LinearAlgebra.Projectivization.Subspace
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.GroupTheory.GroupAction.FixingSubgroup

/-! Canonical projective collineations and the actual coordinate-frame
stabilizer. No semilinear classification is built into these definitions. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGProjectiveFrameCoordinates
variable {F n : Type*} [Field F] [Fintype n] [DecidableEq n]

abbrev Points := Projectivization F (n→F)

def OnLine (p q r : Points (F:=F) (n:=n)) : Prop :=
  p.submodule≤q.submodule ⊔ r.submodule

def collineationGroup : Subgroup (Equiv.Perm (Points (F:=F) (n:=n))) where
  carrier := {f | ∀ p q r, OnLine (f p) (f q) (f r)↔OnLine p q r}
  one_mem' := by intro p q r;rfl
  mul_mem' := by
    intro f g hf hg p q r
    exact (hf (g p) (g q) (g r)).trans (hg p q r)
  inv_mem' := by
    intro f hf p q r
    have hh := (hf (f.symm p) (f.symm q) (f.symm r)).symm
    simpa only [Equiv.apply_symm_apply] using hh

omit [Fintype n] [DecidableEq n] in
@[simp] theorem mem_collineationGroup_iff (f : Equiv.Perm (Points (F:=F) (n:=n))) :
    f∈collineationGroup (F:=F) (n:=n)↔
      ∀ p q r, OnLine (f p) (f q) (f r)↔OnLine p q r := Iff.rfl

def basisPoint (i : n) : Points (F:=F) (n:=n) :=
  Projectivization.mk F (Pi.single i 1) (by
    intro he
    have hh := congrArg (fun v : n→F => v i) he
    simp only [Pi.single_eq_same,Pi.zero_apply,one_ne_zero] at hh)

def sumPoint (b : n) : Points (F:=F) (n:=n) :=
  Projectivization.mk F (fun _ => 1) (by
    intro he
    have hh := congrArg (fun v : n→F => v b) he
    exact one_ne_zero hh)

def standardFrame (b : n) : Set (Points (F:=F) (n:=n)) :=
  Set.range (basisPoint (F:=F)) ∪ {sumPoint (F:=F) b}

def frameStabilizer (b : n) : Subgroup (collineationGroup (F:=F) (n:=n)) :=
  fixingSubgroup _ (standardFrame (F:=F) b)

theorem mem_frameStabilizer_iff (b : n) (g : collineationGroup (F:=F) (n:=n)) :
    g∈frameStabilizer (F:=F) (n:=n) b↔
      (∀ i : n,g • basisPoint (F:=F) i=basisPoint (F:=F) i) ∧
        g • sumPoint (F:=F) b=sumPoint (F:=F) b := by
  rw [frameStabilizer,mem_fixingSubgroup_iff]
  constructor
  · intro h
    exact ⟨fun i => h (basisPoint i) (Or.inl ⟨i,rfl⟩),
      h (sumPoint b) (Or.inr rfl)⟩
  · rintro ⟨hB,hS⟩ y (hy | hy)
    · obtain ⟨i,rfl⟩ := hy
      exact hB i
    · have he : y=sumPoint (F:=F) b := hy
      rw [he]
      exact hS

end SymmetricSubgroupAsymptotics.CFSGProjectiveFrameCoordinates
