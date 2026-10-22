import SymmetricSubgroupAsymptotics.CFSGCliffordUniformBlockChart
import SymmetricSubgroupAsymptotics.CFSGLinearBlockOrderSelected

/-! Exhaustion of actual non-isotypic normal restrictions in binary
dimension six. All proper block counts come from the canonical Clifford
decomposition and spend at most eleven prime-factor units. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics.CFSGCliffordBinarySixBlockExhaustion
open CFSGCliffordIsotypicTransport CFSGCliffordIsotypicPermutation
  CFSGCliffordComponentCoordinates CFSGCliffordComponentDimensions
  CFSGCliffordUniformBlockChart

variable {G V : Type} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [Finite V] [FiniteDimensional (ZMod 2) V]

theorem isotypic_or_trace_le_fourteen
    (rho : Representation (ZMod 2) G V) (hrho : Representation.IsIrreducible rho)
    (hf : Function.Injective rho) (hd : Module.finrank (ZMod 2) V = 6)
    (H : Subgroup G) [H.Normal] (T : FixedTargetCompositionTrace G) :
    IsIsotypic (ZMod 2)[H] (restricted rho H).asModule ∨
      T.envelope.abelianLength ≤ 14 := by
  letI : Representation.IsIrreducible rho := hrho
  letI : Nontrivial V := Subrepresentation.irreducible_module_nontrivial rho
  letI : Finite (Components rho H) := components_finite rho H
  letI : Fintype (Components rho H) := Fintype.ofFinite _
  let rhoH : Representation (ZMod 2) H V := rho.comp H.subtype
  letI : Nontrivial rhoH.asModule := rhoH.asModuleEquiv.toEquiv.nontrivial
  obtain ⟨W, hW⟩ :=
    Subrepresentation.irreducible_subrepresentation_of_finite_dimensional rhoH
  have hs : IsSimpleModule (ZMod 2)[H] W.asSubmodule := by
    apply isSimpleModule_iff_isAtom.mpr
    exact (Subrepresentation.subrepresentationSubmoduleOrderIso.isAtom_iff W).mpr
      ((Subrepresentation.irreducible_iff_isAtom W).mp hW)
  let C : Components rho H :=
    ⟨isotypicComponent (ZMod 2)[H] rhoH.asModule W.asSubmodule, W.asSubmodule, hs, rfl⟩
  let b := Nat.card (Components rho H)
  let d := Module.finrank (ZMod 2) C.val
  let hss := CliffordRawRestriction.proved.semisimple rho hrho H
  have hdim : b * d = 6 := by
    have he := component_count_mul_finrank rho H hrho hss C
    exact he.trans hd
  by_cases hb : b = 1
  · apply Or.inl
    letI : Subsingleton (Components rho H) :=
      Finite.card_le_one_iff_subsingleton.mp hb.le
    have hall (D : Components rho H) : D.val = C.val :=
      congrArg Subtype.val (Subsingleton.elim D C)
    have he : (⨆ D : Components rho H, D.val) = C.val :=
      le_antisymm (iSup_le (fun D => le_of_eq (hall D)))
        (le_iSup (fun D : Components rho H => D.val) C)
    have htop : C.val = ⊤ := he.symm.trans (components_sup_eq_top rho H hss)
    let e := (LinearEquiv.ofEq C.val ⊤ htop).trans Submodule.topEquiv
    exact e.isIsotypic_iff.mp (IsIsotypic.isotypicComponents C.property)
  have hdiv : b ∣ 6 := ⟨d, hdim.symm⟩
  have hcases : ∀ n ∈ Nat.divisors 6, n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 6 := by
    decide +kernel
  have hbs := hcases b (Nat.mem_divisors.mpr ⟨hdiv, by decide⟩)
  have hbd : (b = 2 ∧ d = 3) ∨ (b = 3 ∧ d = 2) ∨ (b = 6 ∧ d = 1) := by
    rcases hbs with hh | hh | hh | hh
    · exact False.elim (hb hh)
    · refine Or.inl ⟨hh, ?_⟩
      rw [hh] at hdim
      omega
    · refine Or.inr (Or.inl ⟨hh, ?_⟩)
      rw [hh] at hdim
      omega
    · refine Or.inr (Or.inr ⟨hh, ?_⟩)
      rw [hh] at hdim
      omega
  obtain ⟨e, pi, hker⟩ := exists_uniform_block_chart rho hrho H C
  exact Or.inr (CFSGLinearBlockOrderSelected.trace_le_fourteen_of_binary_block_chart
    hbd rho hf e pi hker T)

end SymmetricSubgroupAsymptotics.CFSGCliffordBinarySixBlockExhaustion
