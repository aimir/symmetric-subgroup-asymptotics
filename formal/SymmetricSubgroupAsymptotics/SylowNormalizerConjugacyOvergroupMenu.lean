import SymmetricSubgroupAsymptotics.SylowNormalizerFiniteOvergroupMenu
import Mathlib.Order.Atoms.Finite

/-! A menu of proper overgroup classes needs no enumeration of conjugates.
A subgroup containing the Sylow normalizer is the unique conjugate in its
class containing that Sylow subgroup. Literal representatives can therefore
be selected with the same cardinal weights as the class representatives. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise BigOperators
namespace SymmetricSubgroupAsymptotics.SylowNormalizerConjugacyOvergroupMenu

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- There is only one conjugate of an overgroup of `N(P)` containing `P`. -/
theorem conjugate_eq_self (P : Sylow p G) (M : Subgroup G)
    (hNM : Subgroup.normalizer (P : Set G) ≤ M) (g : G)
    (hPM : (P : Subgroup G) ≤ MulAut.conj g • M) :
    MulAut.conj g • M = M := by
  have hPi : ((g⁻¹ • P : Sylow p G) : Subgroup G) ≤ M := by
    rw [Sylow.smul_def, Sylow.pointwise_smul_def]
    simpa only [map_inv] using
      (Subgroup.subset_pointwise_smul_iff.mp hPM)
  have hgi : g⁻¹ ∈ M :=
    SylowNormalizerTwoOvergroups.conjugator_mem P M hNM g⁻¹ hPi
  have hg : g ∈ M := by simpa only [inv_inv] using M.inv_mem hgi
  exact Subgroup.conj_smul_eq_self_of_mem hg

/-- Selecting one actual overgroup from each relevant conjugacy class gives
an ordinary literal cover with exactly the original cardinal weights. -/
theorem literal_menu_of_conjugacy_cover {I : Type*} (P : Sylow p G)
    (K : I → Subgroup G)
    (hclasses : ∀ H : Subgroup G, Subgroup.normalizer (P : Set G) ≤ H →
      H ≠ ⊤ → ∃ (i : I) (g : G), H ≤ MulAut.conj g • K i) :
    ∃ L : I → Subgroup G,
      (∀ i, Nat.card (L i) = Nat.card (K i)) ∧
      ∀ H : Subgroup G, Subgroup.normalizer (P : Set G) ≤ H →
        H ≠ ⊤ → ∃ i : I, H ≤ L i := by
  classical
  let relevant (i : I) : Prop :=
    ∃ g : G, Subgroup.normalizer (P : Set G) ≤ MulAut.conj g • K i
  let L (i : I) : Subgroup G := if hi : relevant i then
    MulAut.conj (Classical.choose hi) • K i else K i
  refine ⟨L, ?_, ?_⟩
  · intro i
    dsimp only [L]
    split_ifs with hi
    · simpa only [Subgroup.pointwise_smul_def] using
        (Subgroup.card_map_of_injective
          (K := K i) (MulAut.conj (Classical.choose hi)).injective)
    · rfl
  · intro H hNH hH
    obtain ⟨i, g, hHg⟩ := hclasses H hNH hH
    have hi : relevant i := ⟨g, hNH.trans hHg⟩
    let f : G := Classical.choose hi
    have hLf : L i = MulAut.conj f • K i := dif_pos hi
    have hNL : Subgroup.normalizer (P : Set G) ≤ L i := by
      rw [hLf]
      exact Classical.choose_spec hi
    have hrel : MulAut.conj (g * f⁻¹) • L i = MulAut.conj g • K i := by
      rw [hLf, map_mul, map_inv, mul_smul, inv_smul_smul]
    have hPL : (P : Subgroup G) ≤ MulAut.conj (g * f⁻¹) • L i := by
      rw [hrel]
      exact Subgroup.le_normalizer.trans (hNH.trans hHg)
    have heq : MulAut.conj g • K i = L i :=
      hrel.symm.trans (conjugate_eq_self P (L i) hNL (g * f⁻¹) hPL)
    exact ⟨i, hHg.trans_eq heq⟩

/-- A finite class menu whose representative orders sum to less than `|G|`
supplies two generating conjugates of the actual Sylow normalizer. -/
theorem conjugates_generate {I : Type*} [Fintype I] (P : Sylow p G)
    (K : I → Subgroup G)
    (hclasses : ∀ H : Subgroup G, Subgroup.normalizer (P : Set G) ≤ H →
      H ≠ ⊤ → ∃ (i : I) (g : G), H ≤ MulAut.conj g • K i)
    (hcard : (∑ i : I, Nat.card (K i)) < Nat.card G) :
    ∃ g : G, Subgroup.closure (((Subgroup.normalizer (P : Set G)) : Set G) ∪
      (Subgroup.normalizer (P : Set G)).map (MulAut.conj g).toMonoidHom) = ⊤ := by
  obtain ⟨L, hLcard, hLcover⟩ := literal_menu_of_conjugacy_cover P K hclasses
  apply SylowNormalizerFiniteOvergroupMenu.conjugates_generate P L hLcover
  simpa only [hLcard] using hcard

/-- It suffices to classify maximal proper overgroups up to conjugacy. -/
theorem conjugates_generate_of_coatom_classes {I : Type*} [Fintype I]
    (P : Sylow p G) (K : I → Subgroup G)
    (hclasses : ∀ M : Subgroup G, IsCoatom M →
      Subgroup.normalizer (P : Set G) ≤ M →
      ∃ (i : I) (g : G), M = MulAut.conj g • K i)
    (hcard : (∑ i : I, Nat.card (K i)) < Nat.card G) :
    ∃ g : G, Subgroup.closure (((Subgroup.normalizer (P : Set G)) : Set G) ∪
      (Subgroup.normalizer (P : Set G)).map (MulAut.conj g).toMonoidHom) = ⊤ := by
  apply conjugates_generate P K ?_ hcard
  intro H hNH hH
  obtain ⟨M, hM, hHM⟩ := (eq_top_or_exists_le_coatom H).resolve_left hH
  obtain ⟨i, g, he⟩ := hclasses M hM (hNH.trans hHM)
  exact ⟨i, g, hHM.trans_eq he⟩

/-- A closed finite menu together with actual normalizer solubility pays
the weaker Sylow-normalizer assembler directly. -/
theorem normalizerPrime_of_coatom_classes {I : Type*} [Fintype I]
    (P : Sylow p G) (hsol : IsSolvable (Subgroup.normalizer (P : Set G)))
    (K : I → Subgroup G)
    (hclasses : ∀ M : Subgroup G, IsCoatom M →
      Subgroup.normalizer (P : Set G) ≤ M →
      ∃ (i : I) (g : G), M = MulAut.conj g • K i)
    (hcard : (∑ i : I, Nat.card (K i)) < Nat.card G) :
    SolubleSylowNormalizerGeneration.SolubleSylowNormalizerPrime G p := by
  obtain ⟨g, hgen⟩ := conjugates_generate_of_coatom_classes P K hclasses hcard
  exact ⟨Fact.out, P, g, hsol, hgen⟩

end SymmetricSubgroupAsymptotics.SylowNormalizerConjugacyOvergroupMenu
