import SymmetricSubgroupAsymptotics.SemisimpleNormalChart
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.SetTheory.Cardinal.Finite

/-! A selected internal simple factor is detected injectively by an
ACTUAL original coordinate of any jointly faithful family. The chart may
be heterogeneous and the original coordinates may have arbitrary
diagonal correlations. No product independence is inferred. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SemisimpleChartCoordinateFactorEmbedding

theorem simple_has_injective_coordinate
    {T I : Type} [Group T] [IsSimpleGroup T]
    (D : I → Type) [∀ i, Group (D i)] (f : ∀ i, T →* D i)
    (hi : Function.Injective (fun x i => f i x)) :
    ∃ i : I, Function.Injective (f i) := by
  classical
  obtain ⟨x, hx⟩ := exists_ne (1 : T)
  have hdetect : ∃ i : I, f i x ≠ 1 := by
    by_contra hn
    apply hx
    apply hi
    funext i
    have hxi : f i x = 1 := by
      by_contra hne
      exact hn ⟨i, hne⟩
    exact hxi.trans (map_one (f i)).symm
  obtain ⟨i, hxi⟩ := hdetect
  refine ⟨i, (MonoidHom.ker_eq_bot_iff (f i)).mp ?_⟩
  rcases (inferInstance : (f i).ker.Normal).eq_bot_or_eq_top with hbot | htop
  · exact hbot
  · have hxker : x ∈ (f i).ker := by rw [htop]; trivial
    exact (hxi hxker).elim

theorem factor_has_injective_coordinate
    {G I : Type} [Group G] (E : Subgroup G) (C : SemisimpleNormalChart E)
    (D : I → Type) [∀ i, Group (D i)] (f : ∀ i, E →* D i)
    (hi : Function.Injective (fun x i => f i x)) (j : C.ι) [DecidableEq C.ι] :
    ∃ i : I, Function.Injective
      ((f i).comp (C.equiv.symm.toMonoidHom.comp (MonoidHom.mulSingle C.factor j))) := by
  classical
  letI : IsSimpleGroup (C.factor j) := C.simple j
  let a : C.factor j →* E :=
    C.equiv.symm.toMonoidHom.comp (MonoidHom.mulSingle C.factor j)
  have ha : Function.Injective a := by
    intro x y hxy
    have h := congrArg (fun z : E => C.equiv z j) hxy
    simpa only [a, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same] using h
  apply simple_has_injective_coordinate D (fun i => (f i).comp a)
  intro x y hxy
  apply ha
  apply hi
  exact hxy

theorem factor_card_le_coordinate
    {G I D : Type} [Group G] [Group D] [Finite D]
    (E : Subgroup G) (C : SemisimpleNormalChart E)
    (f : I → E →* D) (hi : Function.Injective (fun x i => f i x)) (j : C.ι) :
    Nat.card (C.factor j) ≤ Nat.card D := by
  classical
  obtain ⟨i, hfi⟩ := factor_has_injective_coordinate E C (fun _ => D) f hi j
  exact Nat.card_le_card_of_injective _ hfi

end SymmetricSubgroupAsymptotics.SemisimpleChartCoordinateFactorEmbedding
