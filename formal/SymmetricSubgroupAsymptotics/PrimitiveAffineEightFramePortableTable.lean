import SymmetricSubgroupAsymptotics.BinaryPlaneKernelClassification
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFramePortableHead
import SymmetricSubgroupAsymptotics.CoinducedGroupLocalTransport

/-!
The retained local-map completeness of an eight-point table applies outside
the original eight-block affine profile. In particular it applies to the
actual eight-pair image in the sixteen-block branch. The local quotient
map, its kernel, and its faithful binary plane are preserved. No additional
module-head premise is required after an exact table has been selected.

This module does not select a permutation top or assert that the concrete
tables use only standard axioms. Those are separate finite obligations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
namespace GeneratedTopTable

variable (T : GeneratedTopData) (C : GeneratedTopTable T)

/-- Completeness on the literal point stabilizer also covers the identical
map on the retained source stabilizer. -/
theorem source_complete
    {L : Type} [Group L] [Finite L]
    (f : T.sourceStabilizer →* L) (hf : Function.Surjective f)
    (hL : Nat.card L = 3 ∨ (Nat.card L = 6 ∧ ¬ IsMulCommutative L)) :
    ∃ r : C.Row, ∃ e : L ≃* (C.data r).LocalTarget,
      e.toMonoidHom.comp f = (C.data r).sourceLocalMap := by
  obtain ⟨r, e, he⟩ := C.complete L
    (f.comp T.sourceStabilizerEquivLiteral.symm.toMonoidHom)
    (hf.comp T.sourceStabilizerEquivLiteral.symm.surjective) hL
  refine ⟨r, e, ?_⟩
  apply MonoidHom.ext
  intro h
  have hh := DFunLike.congr_fun he (T.sourceStabilizerEquivLiteral h)
  simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    GeneratedRowData.literalLocalMap,
    T.sourceStabilizerEquivLiteral.symm_apply_apply] using hh

include C in
/-- Every eligible actual local map and faithful plane on the source
stabilizer inherits the selected row's head bound. -/
theorem source_coind_head_le_two
    {L V : Type} [Group L] [Finite L]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (f : T.sourceStabilizer →* L) (hf : Function.Surjective f)
    (hL : Nat.card L = 3 ∨ (Nat.card L = 6 ∧ ¬ IsMulCommutative L))
    (tau : Representation (ZMod 2) L V)
    (htau : Function.Injective tau) (hV : Module.finrank (ZMod 2) V = 2)
    (B : Subrepresentation
      (Representation.coind T.sourceStabilizer.subtype (tau.comp f))) :
    Module.finrank (ZMod 2)
      (B.toRepresentation.IntertwiningMap
        (Representation.trivial (ZMod 2) T.ModelGroup (ZMod 2))) ≤ 2 := by
  obtain ⟨r, e, he⟩ := C.source_complete T f hf hL
  let R := C.data r
  let eV := BinaryPlaneKernelClassification.representationEquiv_of_card_three_or_six_at rfl
    tau (R.localRepresentation.comp e.toMonoidHom)
    (hL.imp_right And.left) hV (by simp)
    htau (R.localRepresentation_injective.comp e.injective)
  have hmap (h : T.sourceStabilizer) : e (f h) = R.sourceLocalMap h :=
    DFunLike.congr_fun he h
  let eLocal : Representation.Equiv (tau.comp f) (R.sourceLocalRepresentation T) :=
    Representation.Equiv.mk eV.toLinearEquiv (fun h => by
      have hh := eV.isIntertwining' (f h)
      have hmap' : e.toMonoidHom (f h) = R.sourceLocalMap h := hmap h
      simp only [MonoidHom.comp_apply] at hh
      rw [hmap'] at hh
      simpa only [GeneratedRowData.sourceLocalRepresentation,
        MonoidHom.comp_apply] using hh)
  exact R.coind_head_le_two_of_local_equiv T (tau.comp f) eLocal B

include C in
/-- Transport an actual stabilizer map to the table only through an exact
ambient equivalence and a commuting equivalence of stabilizers. -/
theorem coind_head_le_two_of_equiv
    {G L V : Type} [Group G] [Finite G] [Group L] [Finite L]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (H : Subgroup G) (eG : G ≃* T.ModelGroup)
    (eH : H ≃* T.sourceStabilizer)
    (commutes : ∀ h : H, eG (h : G) = (eH h : T.ModelGroup))
    (f : H →* L) (hf : Function.Surjective f)
    (hL : Nat.card L = 3 ∨ (Nat.card L = 6 ∧ ¬ IsMulCommutative L))
    (tau : Representation (ZMod 2) L V)
    (htau : Function.Injective tau) (hV : Module.finrank (ZMod 2) V = 2)
    (B : Subrepresentation (Representation.coind H.subtype (tau.comp f))) :
    Module.finrank (ZMod 2)
      (B.toRepresentation.IntertwiningMap
        (Representation.trivial (ZMod 2) G (ZMod 2))) ≤ 2 := by
  let fModel : T.sourceStabilizer →* L := f.comp eH.symm.toMonoidHom
  let sigma := tau.comp fModel
  let eLocal : Representation.Equiv (tau.comp f) (sigma.comp eH.toMonoidHom) :=
    Representation.Equiv.mk (LinearEquiv.refl (ZMod 2) V) (fun h => by
      apply LinearMap.ext
      intro v
      change tau (f h) v = tau (f (eH.symm (eH h))) v
      rw [eH.symm_apply_apply])
  exact CoinducedGroupLocalTransport.uniform_head_le
    H T.sourceStabilizer eG eH commutes (tau.comp f) sigma eLocal 2
    (C.source_coind_head_le_two T fModel (hf.comp eH.symm.surjective)
      hL tau htau hV) B

/-- The same selected table supplies the normal-axis bound on the actual
ambient group, independently of the choice of local quotient map. -/
theorem top_relativeHead_le_two_of_equiv
    {G : Type} [Group G] [Finite G] (eG : G ≃* T.ModelGroup)
    (N : Subgroup G) [N.Normal] :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) ≤ 2 :=
  T.topRegistry.bound_equiv eG.symm N

end GeneratedTopTable
end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics

end
