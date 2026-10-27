import SymmetricSubgroupAsymptotics.SylowNormalizerTwoOvergroups
import SymmetricSubgroupAsymptotics.SolubleSylowNormalizerPrime

/-! A finite proper-overgroup cover with total cardinality below the
actual group order yields a generating normalizer conjugate. Overlaps in
the menu are harmless. No generation or maximality conclusion is an input. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Pointwise
namespace SymmetricSubgroupAsymptotics.SylowNormalizerFiniteOvergroupMenu

variable {G : Type*} [Group G] [Finite G] {I : Type*} [Fintype I]

theorem exists_outside_menu (K : I → Subgroup G)
    (hcard : (∑ i : I, Nat.card (K i)) < Nat.card G) :
    ∃ g : G, ∀ i : I, g ∉ K i := by
  by_contra! hcover
  choose label hlabel using hcover
  let f : G → (i : I) × K i := fun g => ⟨label g, ⟨g, hlabel g⟩⟩
  have hinj : Function.Injective f := by
    intro g h he
    exact congrArg (fun z : (i : I) × K i => (z.2 : G)) he
  have hc : Nat.card G ≤ ∑ i : I, Nat.card (K i) := by
    simpa only [Nat.card_sigma] using Nat.card_le_card_of_injective f hinj
  exact (not_le_of_gt hcard) hc

theorem exists_outside_menu_of_uniform_bound (K : I → Subgroup G) (M : ℕ)
    (hM : ∀ i, Nat.card (K i) ≤ M) (hcard : Fintype.card I * M < Nat.card G) :
    ∃ g : G, ∀ i : I, g ∉ K i := by
  apply exists_outside_menu K
  apply lt_of_le_of_lt ?_ hcard
  calc
    (∑ i : I, Nat.card (K i)) ≤ ∑ _i : I, M :=
      Finset.sum_le_sum (fun i _ => hM i)
    _ = Fintype.card I * M := by simp

theorem conjugates_generate {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (K : I → Subgroup G)
    (hcover : ∀ H : Subgroup G, Subgroup.normalizer (P : Set G) ≤ H →
      H ≠ ⊤ → ∃ i : I, H ≤ K i)
    (hcard : (∑ i : I, Nat.card (K i)) < Nat.card G) :
    ∃ g : G, Subgroup.closure (((Subgroup.normalizer (P : Set G)) : Set G) ∪
      (Subgroup.normalizer (P : Set G)).map (MulAut.conj g).toMonoidHom) = ⊤ := by
  obtain ⟨g, hg⟩ := exists_outside_menu K hcard
  let N := Subgroup.normalizer (P : Set G)
  let H := N ⊔ N.map (MulAut.conj g).toMonoidHom
  have hNH : N ≤ H := le_sup_left
  have hmap : (P : Subgroup G).map (MulAut.conj g).toMonoidHom ≤ H :=
    (Subgroup.map_mono Subgroup.le_normalizer).trans le_sup_right
  have hPg : ((g • P : Sylow p G) : Subgroup G) ≤ H := by
    simpa only [Sylow.smul_def, Sylow.pointwise_smul_def,
      Subgroup.pointwise_smul_def] using hmap
  have hgH : g ∈ H := SylowNormalizerTwoOvergroups.conjugator_mem P H hNH g hPg
  have htop : H = ⊤ := by
    by_contra hne
    obtain ⟨i, hi⟩ := hcover H hNH hne
    exact hg i (hi hgH)
  refine ⟨g, ?_⟩
  simpa only [Subgroup.closure_union, Subgroup.closure_eq] using htop

theorem normalizerPrime_of_menu {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hsol : IsSolvable (Subgroup.normalizer (P : Set G))) (K : I → Subgroup G)
    (hcover : ∀ H : Subgroup G, Subgroup.normalizer (P : Set G) ≤ H →
      H ≠ ⊤ → ∃ i : I, H ≤ K i)
    (hcard : (∑ i : I, Nat.card (K i)) < Nat.card G) :
    SolubleSylowNormalizerGeneration.SolubleSylowNormalizerPrime G p := by
  obtain ⟨g, hgen⟩ := conjugates_generate P K hcover hcard
  exact ⟨Fact.out, P, g, hsol, hgen⟩

end SymmetricSubgroupAsymptotics.SylowNormalizerFiniteOvergroupMenu
