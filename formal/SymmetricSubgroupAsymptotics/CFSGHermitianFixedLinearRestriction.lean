import SymmetricSubgroupAsymptotics.CFSGHermitianGlobalFieldCoherence
import SymmetricSubgroupAsymptotics.CFSGEmbeddedLinearRayScalar

/-! Pointwise fixed singular domains force the genuine semilinear field
component to be trivial, and linear representatives are one scalar on
their fixed subspaces. These are vector statements on the original
embedding, rather than a projective or abstract character surrogate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
variable {K I : Type*} [Field K] [Fintype I]
variable (sigma : K ≃+* K) (H : Matrix I I K)

def identitySemilinearPiece (f : Equiv.Perm (SingularPoint sigma H))
    (S : IsotropicSpace sigma H)
    (hfix : ∀ P : SingularPoint sigma H, P.val ≤ S.val → f P = P) :
    SemilinearPiece sigma H f S (RingEquiv.refl K) where
  map := S.val.subtype
  injective := S.val.subtype_injective
  ray x hx := by
    rw [hfix _ (projectiveInside sigma H S (Projectivization.mk K x hx)).property,
      projectiveInside_mk_submodule]
    rfl

theorem semilinearPiece_field_eq_id_of_fixed_subspace
    (f : Equiv.Perm (SingularPoint sigma H)) (S : IsotropicSpace sigma H)
    (tau : K ≃+* K) (F : SemilinearPiece sigma H f S tau)
    (hS : 2 ≤ Module.finrank K S.val)
    (hfix : ∀ P : SingularPoint sigma H, P.val ≤ S.val → f P = P) :
    tau = RingEquiv.refl K := by
  apply semilinearPiece_fields_eq_of_two_le_intersection sigma H f S S tau (RingEquiv.refl K)
    F (identitySemilinearPiece sigma H f S hfix)
  change 2 ≤ Module.finrank K ↥(S.val ⊓ S.val)
  rw [inf_idem]
  exact hS

theorem hermitian_fixed_restriction_scalar
    (f : Equiv.Perm (SingularPoint sigma H)) (S : IsotropicSpace sigma H)
    (F : SemilinearPiece sigma H f S (RingEquiv.refl K))
    (T : Submodule K (I → K)) (hTS : T ≤ S.val)
    (hfix : ∀ P : SingularPoint sigma H, P.val ≤ T → f P = P) :
    ∃ a : K, ∀ x : T, F.map ⟨x.val, hTS x.property⟩ = a • x.val := by
  let L : T →ₗ[K] (I → K) := F.map.comp (Submodule.inclusion hTS)
  apply CFSGEmbeddedLinearRayScalar.exists_scalar T.subtype L T.subtype_injective
  intro x
  by_cases hx : x = 0
  · refine ⟨0, ?_⟩
    simp [hx, L]
  have hxS : (⟨x.val, hTS x.property⟩ : S.val) ≠ 0 := by
    intro h
    have hv : x.val = 0 := congrArg (fun z : S.val => z.val) h
    exact hx (Subtype.ext hv)
  let P := (projectiveInside sigma H S (Projectivization.mk K ⟨x.val, hTS x.property⟩ hxS)).val
  have hp : P.val = Submodule.span K {x.val} := projectiveInside_mk_submodule sigma H S _ _
  have hPT : P.val ≤ T := by
    rw [hp]
    exact (Submodule.span_singleton_le_iff_mem _ _).mpr x.property
  have he := F.ray ⟨x.val, hTS x.property⟩ hxS
  change Submodule.span K {L x} = (f P).val at he
  rw [hfix P hPT, hp] at he
  have hm : L x ∈ Submodule.span K {x.val} := he ▸ Submodule.mem_span_singleton_self (L x)
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hm
  exact ⟨a, ha.symm⟩

theorem hermitian_fixed_restriction_scalar_nonzero
    (f : Equiv.Perm (SingularPoint sigma H)) (S : IsotropicSpace sigma H)
    (F : SemilinearPiece sigma H f S (RingEquiv.refl K))
    (T : Submodule K (I → K)) (hTS : T ≤ S.val) (hT : T ≠ ⊥)
    (hfix : ∀ P : SingularPoint sigma H, P.val ≤ T → f P = P) :
    ∃ a : K, a ≠ 0 ∧ ∀ x : T, F.map ⟨x.val, hTS x.property⟩ = a • x.val := by
  obtain ⟨a, ha⟩ := hermitian_fixed_restriction_scalar sigma H f S F T hTS hfix
  refine ⟨a, ?_, ha⟩
  intro hz
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hT
  have he := ha ⟨x, hx⟩
  rw [hz, zero_smul] at he
  have hh := F.injective (he.trans F.map.map_zero.symm)
  exact hx0 (congrArg Subtype.val hh)

end SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
