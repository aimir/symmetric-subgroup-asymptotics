import SymmetricSubgroupAsymptotics.CFSGPolarLocalFieldCoherence

/-! A linear piece's actual range is determined by its point images
and dimension. This supplies the literal range equality required by
paired-block normalization, with no extra representative hypothesis. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGPolarSubspacePoints
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
local instance (s : K≃+*K) : RingHomInvPair s.toRingHom s.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv s
local instance (s : K≃+*K) : RingHomInvPair s.symm.toRingHom s.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm s

theorem linearPiece_range_eq (B : LinearMap.BilinForm K V) (f : Points B≃Points B)
    (W : Subspaces B) (F : SemilinearPiece B f W (RingEquiv.refl K))
    (T : Submodule K V) (hd : Module.finrank K T=Module.finrank K W.val)
    (hpoint : ∀P : Points B,P.val≤W.val → (f P).val≤T) : F.map.range=T := by
  have hle : F.map.range≤T := by
    rintro v ⟨x,rfl⟩
    by_cases hx : x=0
    · simp only [hx,map_zero]
      exact T.zero_mem
    have hx0 : x.val≠0 := fun h=>hx (Subtype.ext h)
    let P := ray B x.val hx0 (W.property x.val x.property x.val x.property)
    have hp : P.val≤W.val := (Submodule.span_singleton_le_iff_mem _ _).mpr x.property
    have he := F.point x hx
    have hm : F.map x∈(f P).val := he ▸ Submodule.mem_span_singleton_self _
    exact hpoint P hp hm
  let e := LinearEquiv.ofInjective F.map F.injective
  have hr : Module.finrank K F.map.range=Module.finrank K W.val := e.finrank_eq.symm
  exact Submodule.eq_of_le_of_finrank_le hle (by rw [hd,hr])

end SymmetricSubgroupAsymptotics.CFSGPolarSubspacePoints
