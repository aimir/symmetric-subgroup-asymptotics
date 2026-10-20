import SymmetricSubgroupAsymptotics.MarkedC4SolubleContainerOrder
import SymmetricSubgroupAsymptotics.MarkedC4ContainerRelativeEncoding

/-! A complete literal large-orbit marked reduction. Container choices are
charged ONCE, not once per lifted generator. The inputs are the ordinary
published Proposition 6.2 and Theorem 8.6 (Pyber/Dixon). Actual orbit
partitions, maximal soluble containers, original projection kernels,
relative tuples, source recovery, and all C4-character restrictions are
constructed in the preceding modules. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.ConstructedLargeOrbitMoment
open LiteralSolubleOrbitContainers SolubleContainerCount SolubleContainerOrder
open LargeOrbitOrdinaryGeneration ActualLargeOrbitKernel

def menuSize (b : ℕ) : ℕ := b^b * (2^(13*b) * (b+1)^b)

theorem words_bound (h86 : PublishedTheorem86Representatives)
    (hDixon : PublishedDixonOrder) (b l : ℕ) :
    Nat.card (ContainerRelativeEncoding.Words (l := l) (physicalContainer (Fin b))) ≤
      menuSize b * 2^(2*b*l) := by
  letI : Fintype (Index (Fin b)) := Fintype.ofFinite _
  letI (i : Index (Fin b)) : Fintype (physicalContainer (Fin b) i) := Fintype.ofFinite _
  have ho (i : Index (Fin b)) : Nat.card (physicalContainer (Fin b) i) ≤ 2^(2*b) := by
    simpa only [Fintype.card_fin] using physicalContainer_order (Fin b) hDixon i
  change Nat.card (Σ i : Index (Fin b), Fin l → physicalContainer (Fin b) i) ≤ _
  rw [Nat.card_sigma]
  calc
    _ = ∑ i : Index (Fin b), (Nat.card (physicalContainer (Fin b) i))^l := by
      simp only [Nat.card_eq_fintype_card,Fintype.card_fun,Fintype.card_fin]
    _ ≤ ∑ _i : Index (Fin b), (2^(2*b))^l := by
      exact Finset.sum_le_sum (fun i _ => Nat.pow_le_pow_left (ho i) l)
    _ = Nat.card (Index (Fin b)) * 2^(2*b*l) := by
      simp [Nat.card_eq_fintype_card,pow_mul]
    _ ≤ menuSize b * 2^(2*b*l) := by
      apply Nat.mul_le_mul_right
      simpa only [menuSize,Fintype.card_fin] using index_card_bound (Fin b) h86

/-- At the selected cutoff, the global source has a proved one-container
code and the SAME bounded-orbit target moment. The only marked loss is the
restriction cost 4^(r*l) of the actual lifted tuple. -/
theorem moment_le_of_relative_tuples
    (h86 : PublishedTheorem86Representatives) (hDixon : PublishedDixonOrder)
    {C l b : ℕ} (hC : 2 ≤ C)
    (hrelative : ∀ G : SolublePermutationSubgroup b,
      ∃ t : Fin l → G.val,
        Subgroup.closure (Set.range t ∪ (projection G.val C).ker) = ⊤)
    (r : ℕ) :
    solubleMarkedC4Moment b r ≤
      ((menuSize b * 2^(2*b*l) : ℕ) : ℝ) * (2 : ℝ)^(2*r*l) *
        OrbitCutoffFamilies.solubleCount C b r := by
  letI : Fintype (Index (Fin b)) := Fintype.ofFinite _
  let D := physicalContainer (Fin b)
  have hcover (G : SolublePermutationSubgroup b) : ∃ i, G.val ≤ D i := by
    letI : IsSolvable G.val := G.property
    exact cover (Fin b) G.val
  choose container hcontainer using hcover
  choose tuple htuple using hrelative
  let K : ∀ G : SolublePermutationSubgroup b, Subgroup G.val :=
    fun G => (projection G.val C).ker
  let P : Subgroup (PermutationGroup b) → Prop :=
    fun J => IsSolvable J ∧ OrbitCutoffFamilies.OrbitCutoff C J
  letI : Fintype (ContainerRelativeEncoding.Target P) :=
    inferInstanceAs (Fintype (OrbitCutoffFamilies.SolubleFamily C b))
  have hP (G : SolublePermutationSubgroup b) : P ((K G).map G.val.subtype) := by
    letI : IsSolvable G.val := G.property
    exact (solubleTarget G.val C hC).property
  have hs := ContainerRelativeEncoding.moment_le D
    (fun G : SolublePermutationSubgroup b => G.val) Subtype.val_injective
    container hcontainer K tuple htuple P hP r
  have hwords : (∑ i : Index (Fin b), (Fintype.card (D i) : ℝ)^l) ≤
      ((menuSize b * 2^(2*b*l) : ℕ) : ℝ) := by
    have hw := words_bound h86 hDixon b l
    rw [Nat.card_eq_fintype_card,ContainerRelativeEncoding.words_card] at hw
    exact_mod_cast hw
  have ht : 0 ≤ OrbitCutoffFamilies.solubleCount C b r :=
    Finset.sum_nonneg (fun _ _ => by positivity)
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hwords (by positivity : (0 : ℝ) ≤ 2^(2*r*l))) ht
  have hs' : solubleMarkedC4Moment b r ≤
      (∑ i : Index (Fin b), (Fintype.card (D i) : ℝ)^l) *
        (2 : ℝ)^(2*r*l) * OrbitCutoffFamilies.solubleCount C b r := by
    convert hs using 1
    congr 1
    apply Finset.sum_congr
    · ext z
      simp
    · intro z _
      rfl
  exact hs'.trans hm

/-- A single cutoff handles ALL original soluble sources, degrees, and
mark ranks. No project-owned recovery or generation premise remains. -/
theorem exists_cutoff_moment_le
    (h62 : PublishedProposition62) (h86 : PublishedTheorem86Representatives)
    (hDixon : PublishedDixonOrder) (rate : ℝ) (hrate : 0 < rate) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ b r : ℕ,
      solubleMarkedC4Moment b r ≤
        ((menuSize b * 2^(2*b*tupleLength rate b) : ℕ) : ℝ) *
          (2 : ℝ)^(2*r*tupleLength rate b) * OrbitCutoffFamilies.solubleCount C b r := by
  obtain ⟨C,hC,ht⟩ := exists_cutoff_relative_tuples h62 rate hrate
  refine ⟨C,hC,?_⟩
  intro b r
  apply moment_le_of_relative_tuples h86 hDixon hC
  intro G
  letI : IsSolvable G.val := G.property
  exact ht b G.val

end SymmetricSubgroupAsymptotics.MarkedC4.ConstructedLargeOrbitMoment
end
