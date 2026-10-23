import SymmetricSubgroupAsymptotics.CFSGHermitianTotallyIsotropic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Orthogonality extends through literal linear spans. Consequently
maximal orthogonal cliques of singular point lines correspond exactly to
maximal totally isotropic subspaces. No dimension, Witt decomposition,
or geometric extension theorem is an input to this correspondence. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
open CFSGTwistedAUnitaryParameters
variable {K I : Type*} [Field K] [Fintype I]

theorem pair_zero_left (sigma : K ≃+* K) (H : Matrix I I K) (y : I → K) :
    hermitianPair sigma H 0 y = 0 := by
  have hh := hermitianPair_smul sigma H 0 1 (0 : I → K) y
  simpa only [zero_smul, one_smul, map_zero, zero_mul] using hh

theorem pair_zero_right (sigma : K ≃+* K) (H : Matrix I I K) (x : I → K) :
    hermitianPair sigma H x 0 = 0 := by
  have hh := hermitianPair_smul sigma H 1 0 x (0 : I → K)
  simpa only [zero_smul, one_smul, map_one, mul_zero, one_mul, zero_mul] using hh

def leftPerp (sigma : K ≃+* K) (H : Matrix I I K) (T : Submodule K (I → K)) :
    Submodule K (I → K) where
  carrier := {x | ∀ y ∈ T, hermitianPair sigma H x y = 0}
  zero_mem' := fun y _ => pair_zero_left sigma H y
  add_mem' := by
    intro x y hx hy z hz
    rw [hermitianPair_add_left, hx z hz, hy z hz, zero_add]
  smul_mem' := by
    intro a x hx y hy
    have hh := hermitianPair_smul sigma H a 1 x y
    simpa only [one_smul, mul_one, hx y hy, mul_zero] using hh

def rightPerp (sigma : K ≃+* K) (H : Matrix I I K) (S : Submodule K (I → K)) :
    Submodule K (I → K) where
  carrier := {y | ∀ x ∈ S, hermitianPair sigma H x y = 0}
  zero_mem' := fun x _ => pair_zero_right sigma H x
  add_mem' := by
    intro x y hx hy z hz
    rw [hermitianPair_add_right, hx z hz, hy z hz, zero_add]
  smul_mem' := by
    intro a y hy x hx
    have hh := hermitianPair_smul sigma H 1 a x y
    simpa only [one_smul, map_one, one_mul, hy x hx, mul_zero] using hh

def Orthogonal (sigma : K ≃+* K) (H : Matrix I I K)
    (S T : Submodule K (I → K)) : Prop :=
  ∀ x ∈ S, ∀ y ∈ T, hermitianPair sigma H x y = 0

theorem orthogonal_iff_le_leftPerp (sigma : K ≃+* K) (H : Matrix I I K)
    (S T : Submodule K (I → K)) :
    Orthogonal sigma H S T ↔ S ≤ leftPerp sigma H T := Iff.rfl

theorem orthogonal_iff_le_rightPerp (sigma : K ≃+* K) (H : Matrix I I K)
    (S T : Submodule K (I → K)) :
    Orthogonal sigma H S T ↔ T ≤ rightPerp sigma H S := by
  constructor
  · intro h y hy x hx
    exact h x hx y hy
  · intro h x hx y hy
    exact h hy x hx

theorem orthogonal_iSup_iff (sigma : K ≃+* K) (H : Matrix I I K)
    {A B : Type*} (S : A → Submodule K (I → K)) (T : B → Submodule K (I → K)) :
    Orthogonal sigma H (⨆ a, S a) (⨆ b, T b) ↔
      ∀ a b, Orthogonal sigma H (S a) (T b) := by
  constructor
  · intro h a b x hx y hy
    exact h x ((le_iSup S a) hx) y ((le_iSup T b) hy)
  · intro h
    apply (orthogonal_iff_le_leftPerp sigma H _ _).mpr
    apply iSup_le
    intro a
    apply (orthogonal_iff_le_leftPerp sigma H _ _).mp
    apply (orthogonal_iff_le_rightPerp sigma H _ _).mpr
    apply iSup_le
    intro b
    exact (orthogonal_iff_le_rightPerp sigma H _ _).mp (h a b)

def SingularPoint (sigma : K ≃+* K) (H : Matrix I I K) :=
  {P : Submodule K (I → K) // Module.finrank K P = 1 ∧
    ∀ x ∈ P, hermitianPair sigma H x x = 0}

def pointSpan (sigma : K ≃+* K) (H : Matrix I I K)
    (C : Set (SingularPoint sigma H)) : Submodule K (I → K) :=
  ⨆ P : C, P.val.val

def pointSet (sigma : K ≃+* K) (H : Matrix I I K)
    (S : Submodule K (I → K)) : Set (SingularPoint sigma H) := {P | P.val ≤ S}

def IsClique (sigma : K ≃+* K) (H : Matrix I I K)
    (C : Set (SingularPoint sigma H)) : Prop :=
  ∀ P ∈ C, ∀ Q ∈ C, Orthogonal sigma H P.val Q.val

theorem pointSpan_orthogonal_iff (sigma : K ≃+* K) (H : Matrix I I K)
    (C : Set (SingularPoint sigma H)) :
    Orthogonal sigma H (pointSpan sigma H C) (pointSpan sigma H C) ↔
      IsClique sigma H C := by
  rw [pointSpan, orthogonal_iSup_iff]
  constructor
  · intro h P hP Q hQ
    exact h ⟨P, hP⟩ ⟨Q, hQ⟩
  · intro h P Q
    exact h P.val P.property Q.val Q.property

theorem pointSpan_pointSet_eq (sigma : K ≃+* K) (H : Matrix I I K)
    (S : Submodule K (I → K)) (hS : Orthogonal sigma H S S) :
    pointSpan sigma H (pointSet sigma H S) = S := by
  apply le_antisymm
  · exact iSup_le (fun P => P.property)
  · intro x hx
    by_cases hx0 : x = 0
    · subst x
      exact Submodule.zero_mem _
    let P : SingularPoint sigma H :=
      ⟨K ∙ x, finrank_span_singleton hx0, by
        intro v hv
        have hle : K ∙ x ≤ S := (Submodule.span_singleton_le_iff_mem _ _).mpr hx
        exact hS v (hle hv) v (hle hv)⟩
    have hP : P ∈ pointSet sigma H S := (Submodule.span_singleton_le_iff_mem _ _).mpr hx
    exact (le_iSup (fun Q : pointSet sigma H S => Q.val.val) ⟨P, hP⟩)
      (Submodule.mem_span_singleton_self x)

theorem pointSet_isClique (sigma : K ≃+* K) (H : Matrix I I K)
    (S : Submodule K (I → K)) (hS : Orthogonal sigma H S S) :
    IsClique sigma H (pointSet sigma H S) := by
  intro P hP Q hQ x hx y hy
  exact hS x (hP hx) y (hQ hy)

theorem clique_subset_pointSet_pointSpan (sigma : K ≃+* K) (H : Matrix I I K)
    (C : Set (SingularPoint sigma H)) : C ⊆ pointSet sigma H (pointSpan sigma H C) := by
  intro P hP
  exact le_iSup (fun Q : C => Q.val.val) ⟨P, hP⟩

theorem pointSet_mono (sigma : K ≃+* K) (H : Matrix I I K)
    {S T : Submodule K (I → K)} (h : S ≤ T) :
    pointSet sigma H S ⊆ pointSet sigma H T := fun _ hP => hP.trans h

theorem pointSpan_mono (sigma : K ≃+* K) (H : Matrix I I K)
    {C D : Set (SingularPoint sigma H)} (h : C ⊆ D) :
    pointSpan sigma H C ≤ pointSpan sigma H D := by
  apply iSup_le
  intro P
  exact le_iSup (fun Q : D => Q.val.val) ⟨P.val, h P.property⟩

def MaximalIsotropic (sigma : K ≃+* K) (H : Matrix I I K)
    (S : Submodule K (I → K)) : Prop :=
  Orthogonal sigma H S S ∧ ∀ T, Orthogonal sigma H T T → S ≤ T → T = S

def MaximalClique (sigma : K ≃+* K) (H : Matrix I I K)
    (C : Set (SingularPoint sigma H)) : Prop :=
  IsClique sigma H C ∧ ∀ D, IsClique sigma H D → C ⊆ D → D = C

theorem maximalClique_pointSpan (sigma : K ≃+* K) (H : Matrix I I K)
    {C : Set (SingularPoint sigma H)} (hC : MaximalClique sigma H C) :
    MaximalIsotropic sigma H (pointSpan sigma H C) ∧
      pointSet sigma H (pointSpan sigma H C) = C := by
  have hi := (pointSpan_orthogonal_iff sigma H C).mpr hC.1
  have he := hC.2 _ (pointSet_isClique sigma H _ hi)
    (clique_subset_pointSet_pointSpan sigma H C)
  refine ⟨⟨hi, ?_⟩, he⟩
  intro T hT hCT
  have hD : pointSet sigma H T = C := hC.2 _ (pointSet_isClique sigma H T hT)
    ((clique_subset_pointSet_pointSpan sigma H C).trans (pointSet_mono sigma H hCT))
  rw [← pointSpan_pointSet_eq sigma H T hT, hD]

theorem maximalIsotropic_pointSet (sigma : K ≃+* K) (H : Matrix I I K)
    {S : Submodule K (I → K)} (hS : MaximalIsotropic sigma H S) :
    MaximalClique sigma H (pointSet sigma H S) := by
  refine ⟨pointSet_isClique sigma H S hS.1, ?_⟩
  intro D hD hSD
  apply Set.Subset.antisymm
  · have he : pointSpan sigma H D = S := hS.2 _
      ((pointSpan_orthogonal_iff sigma H D).mpr hD) (by
        rw [← pointSpan_pointSet_eq sigma H S hS.1]
        exact pointSpan_mono sigma H hSD)
    simpa only [he] using clique_subset_pointSet_pointSpan sigma H D
  · exact hSD

end SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
