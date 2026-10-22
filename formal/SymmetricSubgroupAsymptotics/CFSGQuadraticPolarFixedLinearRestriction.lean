import SymmetricSubgroupAsymptotics.CFSGQuadraticPolarFieldCoherence
import SymmetricSubgroupAsymptotics.CFSGEmbeddedLinearRayScalar

/-! A genuine linear representative of a polar point map is a single
scalar on every subspace whose actual points are fixed. This retains the
literal embedding into the original ambient vector space. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticSubspacePoints
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem fixed_restriction_scalar (q : QuadraticForm K V) (f : Points q≃Points q)
    (W : Subspaces q) (F : SemilinearPiece q f W (RingEquiv.refl K))
    (T : Submodule K V) (hTW : T≤W.val)
    (hfix : ∀P : Points q,P.val≤T → f P=P) :
    ∃a : K,∀x : T,F.map ⟨x.val,hTW x.property⟩=a•x.val := by
  let L : T→ₗ[K]V := F.map.comp (Submodule.inclusion hTW)
  apply CFSGEmbeddedLinearRayScalar.exists_scalar T.subtype L T.subtype_injective
  intro x
  by_cases hx : x=0
  · refine ⟨0,?_⟩
    simp [hx,L]
  have hx0 : x.val≠0 := fun h=>hx (Subtype.ext h)
  let P := ray q x.val hx0 (W.property x.val (hTW x.property))
  have hP : P.val≤T := (Submodule.span_singleton_le_iff_mem _ _).mpr x.property
  have hxW : (⟨x.val,hTW x.property⟩ : W.val)≠0 := fun h=>hx0 (congrArg Subtype.val h)
  have he := F.point ⟨x.val,hTW x.property⟩ hxW
  change Submodule.span K {L x}=(f P).val at he
  rw [hfix P hP] at he
  have hm : L x∈P.val := he ▸ Submodule.mem_span_singleton_self (L x)
  obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp hm
  exact ⟨a,ha.symm⟩

theorem fixed_restriction_scalar_nonzero (q : QuadraticForm K V)
    (f : Points q≃Points q) (W : Subspaces q)
    (F : SemilinearPiece q f W (RingEquiv.refl K))
    (T : Submodule K V) (hTW : T≤W.val) (hT : T≠⊥)
    (hfix : ∀P : Points q,P.val≤T → f P=P) :
    ∃a : K,a≠0 ∧ ∀x : T,F.map ⟨x.val,hTW x.property⟩=a•x.val := by
  obtain ⟨a,ha⟩ := fixed_restriction_scalar q f W F T hTW hfix
  refine ⟨a,?_,ha⟩
  intro hz
  obtain ⟨x,hx,hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hT
  have he := ha ⟨x,hx⟩
  rw [hz,zero_smul] at he
  have hh := F.injective (he.trans F.map.map_zero.symm)
  exact hx0 (congrArg Subtype.val hh)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticSubspacePoints
