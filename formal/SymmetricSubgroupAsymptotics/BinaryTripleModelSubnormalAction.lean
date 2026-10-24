import SymmetricSubgroupAsymptotics.GeneralThreeTwoSurvivingSubnormal
import SymmetricSubgroupAsymptotics.BinaryTripleSingerIrreducible

/-! The actual three-model image recognition controls both ordinary
image rank and the inherited action on the same three-bit translation
chart. The whole action's irreducibility is retained in the two cases
where the actual nontrivial subnormal image is the whole model. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.BinaryTripleModelSubnormalAction
open PrimitiveAffineDegreeEightThreeImages GeneralThreeTwoSurvivingSubnormal

theorem subnormal_image_genRank_le_two
    {H : Type} [Group H] [Finite H] (i : Fin 3) (e : H ≃* models i)
    (E : Subgroup H) (hE : E.IsSubnormal) : MarkedC4.genRank E ≤ 2 := by
  let q := E.equivMapOfInjective e.toMonoidHom e.injective
  rw [CoprimeNilpotentProductGenerators.genRank_mulEquiv q]
  exact model_subnormal_genRank_le_two i _ (hE.map e.surjective)

private theorem model_zero_subnormal_eq_top
    (M : Subgroup (models 0)) (hM : M.IsSubnormal) (hne : M ≠ ⊥) : M = ⊤ := by
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  exact (hM.eq_bot_or_top_of_isSimpleGroup
    (isSimpleGroup_of_prime_card model_zero_card)).resolve_left hne

private theorem eq_top_of_map_eq_top {H K : Type} [Group H] [Group K]
    (e : H ≃* K) (E : Subgroup H) (he : E.map e.toMonoidHom = ⊤) : E = ⊤ := by
  apply top_le_iff.mp
  intro h _
  have hm : e h ∈ E.map e.toMonoidHom := by rw [he]; exact Subgroup.mem_top _
  obtain ⟨h',hh',heq⟩ := hm
  have hh : h' = h := e.injective heq
  simpa only [hh] using hh'

private theorem model_one_irreducible
    {V H : Type} [CommGroup V] [Group H]
    (φ : H →* MulAut V) (b : V ≃* Multiplicative (Fin 3 → ZMod 2))
    (e : H ≃* models 1)
    (hact : ∀ h v, (e h).val.val *ᵥ (b v).toAdd = (b (φ h v)).toAdd)
    (E : Subgroup H) (hE : E.IsSubnormal) (hne : E ≠ ⊥) :
    IrreducibleAbelianSemidirect.Irreducible (φ.comp E.subtype) := by
  let M := E.map e.toMonoidHom
  have hM : M.IsSubnormal := hE.map e.surjective
  have hMne : M ≠ ⊥ := by
    intro hzero
    exact hne ((E.map_eq_bot_iff_of_injective e.injective).mp hzero)
  obtain ⟨h,hh,he⟩ := model_one_subnormal_contains_singer M hM hMne
  let f := (models 1).subtype.comp e.toMonoidHom
  have hs : f h = GeneralThreeTwoTwentyOneSinger.singer :=
    congrArg (fun z : models 1 => z.val) he
  exact BinaryTripleSingerIrreducible.irreducible_of_actual_singer φ b f hact
    E ⟨h,hh⟩ hs

theorem subnormal_image_irreducible
    {V H : Type} [CommGroup V] [Group H]
    (φ : H →* MulAut V) (b : V ≃* Multiplicative (Fin 3 → ZMod 2))
    (i : Fin 3) (e : H ≃* models i)
    (hact : ∀ h v, (e h).val.val *ᵥ (b v).toAdd = (b (φ h v)).toAdd)
    (hwhole : IrreducibleAbelianSemidirect.Irreducible φ)
    (E : Subgroup H) (hE : E.IsSubnormal) (hne : E ≠ ⊥) :
    IrreducibleAbelianSemidirect.Irreducible (φ.comp E.subtype) := by
  let M := E.map e.toMonoidHom
  have hM : M.IsSubnormal := hE.map e.surjective
  have hMne : M ≠ ⊥ := by
    intro hzero
    exact hne ((E.map_eq_bot_iff_of_injective e.injective).mp hzero)
  have hfull : M = ⊤ → IrreducibleAbelianSemidirect.Irreducible (φ.comp E.subtype) := by
    intro htop
    have hEtop : E = ⊤ := eq_top_of_map_eq_top e E htop
    intro S hS
    apply hwhole S
    intro h v hv
    have hh : h ∈ E := by rw [hEtop]; exact Subgroup.mem_top h
    exact hS ⟨h,hh⟩ v hv
  fin_cases i
  · exact hfull (model_zero_subnormal_eq_top M hM hMne)
  · exact model_one_irreducible φ b e hact E hE hne
  · exact hfull ((hM.eq_bot_or_top_of_isSimpleGroup model_two_simple).resolve_left hMne)

end SymmetricSubgroupAsymptotics.BinaryTripleModelSubnormalAction
