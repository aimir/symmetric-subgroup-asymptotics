import SymmetricSubgroupAsymptotics.MarkedC4AbelianSectionSize
import SymmetricSubgroupAsymptotics.MarkedC4BoundedOrbitImages
import SymmetricSubgroupAsymptotics.ZmudFaithfulCharacterInput
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Algebra.Group.Subgroup.Finite

/-! Ordinary published inputs for RDT Theorem 7, before any encoding.
`Height n G` means that n successive quotients by the literal socle kill G;
it is exactly the upper bound sl(G) ≤ n, without choosing a numerical sl.
All literature hypotheses concern ordinary finite groups, not counts,
characters, marked objects, chosen nilpotent cores, or recovery data. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.OrdinaryNilpotentGeneration

/-- The literal upper socle series, expressed by successive quotients. -/
def Height : (n : ℕ) → (G : Type) → [Group G] → Prop
  | 0,G,_ => Subsingleton G
  | n+1,G,_ => Height n (G ⧸ finiteGroupSocle G)

theorem height_of_subsingleton (n : ℕ) (G : Type) [Group G] [Subsingleton G] :
    Height n G := by
  induction n generalizing G with
  | zero =>
    change Subsingleton G
    infer_instance
  | succ n ih => exact ih (G ⧸ finiteGroupSocle G)

theorem height_mono {n m : ℕ} (hnm : n ≤ m) (G : Type) [Group G]
    (h : Height n G) : Height m G := by
  induction n generalizing m G with
  | zero =>
    letI : Subsingleton G := h
    exact height_of_subsingleton m G
  | succ n ih =>
    cases m with
    | zero => omega
    | succ m => exact ih (by omega) (G ⧸ finiteGroupSocle G) h

private theorem socle_ne_bot (G : Type) [Group G] [Finite G] [Nontrivial G] :
    finiteGroupSocle G ≠ ⊥ := by
  let good : Subgroup G → Prop := fun M => M.Normal ∧ M ≠ ⊥
  obtain ⟨M,_,hminimal⟩ := Finite.exists_le_minimal (p := good)
    (a := (⊤ : Subgroup G)) (show good ⊤ from ⟨inferInstance,top_ne_bot⟩)
  have hM : IsMinimalNormalSubgroup M := by
    refine ⟨hminimal.1.1,hminimal.1.2,?_⟩
    intro N hN hn hNM
    exact hminimal.eq_of_le ⟨hN,hn⟩ hNM
  have hle : M ≤ finiteGroupSocle G := by
    intro x hx
    exact Subgroup.subset_normalClosure ⟨M,hM,hx⟩
  intro he
  exact hM.2.1 (le_bot_iff.mp (he ▸ hle))

/-- Elementary cardinal induction supplies the coarse height bound; this
is PROVED here and is not an additional literature or project premise. -/
theorem height_card (G : Type) [Group G] [Finite G] : Height (Nat.card G) G := by
  generalize hn : Nat.card G = n
  induction n using Nat.strong_induction_on generalizing G with
  | h n ih =>
    by_cases ht : Subsingleton G
    · letI := ht
      exact height_of_subsingleton n G
    · letI : Nontrivial G := not_subsingleton_iff_nontrivial.mp ht
      have hs : 1 < Nat.card (finiteGroupSocle G) :=
        (Subgroup.one_lt_card_iff_ne_bot (finiteGroupSocle G)).mpr (socle_ne_bot G)
      have hq : 0 < Nat.card (G ⧸ finiteGroupSocle G) := Nat.card_pos
      have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup (finiteGroupSocle G)
      rw [hn] at hmul
      have hlt : Nat.card (G ⧸ finiteGroupSocle G) < n := by nlinarith
      have hh : Height (Nat.card (G ⧸ finiteGroupSocle G))
          (G ⧸ finiteGroupSocle G) :=
        ih _ hlt (G ⧸ finiteGroupSocle G) rfl
      exact height_mono (Nat.succ_le_of_lt hlt) G
        (show Height (Nat.card (G ⧸ finiteGroupSocle G)+1) G from hh)

/-- RDT Lemma 8.5, p.33: the socle length of a soluble subdirect product is
at most the maximum of the factor socle lengths. The equivalent uniform
upper-bound formulation avoids a choice of an index attaining the maximum. -/
def PublishedSolubleSubdirectHeight : Prop :=
  ∀ (I : Type) [Fintype I] [Nonempty I]
    (F : I → Type) [∀ i,Group (F i)] [∀ i,Finite (F i)] [∀ i,IsSolvable (F i)]
    (G : Type) [Group G] [Finite G] [IsSolvable G]
    (f : G →* ∀ i,F i), Function.Injective f →
    (∀ i,Function.Surjective (fun g => f g i)) →
    ∀ L : ℕ,(∀ i,Height L (F i)) → Height L G

/-- RDT Theorem 7, p.3; proof pp.32–33. Here L bounds the literal socle
length and M bounds Ω of EVERY actual abelian section. Monotonicity of
4 L √M gives this upper-bound form of the exact published statement. -/
def PublishedTheoremSeven : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSolvable G] (L M : ℕ),
    Height L G →
    (∀ (H : Subgroup G) (A : Type) [CommGroup A] [Finite A]
      (f : H →* A), Function.Surjective f →
      AbelianSectionSize.omega (Nat.card A) ≤ M) →
    ∃ (K : Subgroup G) (S : Finset G), Group.IsNilpotent K ∧
      (S.card : ℝ) ≤ 4*(L : ℝ)*Real.sqrt (M : ℝ) ∧
      Subgroup.closure ((S : Set G) ∪ K)=⊤

/-- Actual orbit images, not an assumed decomposition, instantiate Lemma8.5. -/
theorem bounded_height (hsub : PublishedSolubleSubdirectHeight)
    {C b : ℕ} (G : Subgroup (PermutationGroup b)) [IsSolvable G]
    (hG : OrbitCutoffFamilies.OrbitCutoff C G) : Height C.factorial G := by
  by_cases hb : b=0
  · subst b
    exact height_of_subsingleton _ G
  · letI : Nonempty (Fin b) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hb)
    letI (x : Fin b) : IsSolvable (BoundedOrbitImages.Image G x) :=
      BoundedOrbitImages.image_solvable G x
    apply hsub (Fin b) (fun x => ↥(BoundedOrbitImages.Image G x)) G
      (BoundedOrbitImages.subdirect G) (BoundedOrbitImages.subdirect_injective G)
      (BoundedOrbitImages.projection_surjective G) C.factorial
    intro x
    exact height_mono (BoundedOrbitImages.image_card_le_factorial G hG x) _
      (height_card (BoundedOrbitImages.Image G x))

/-- Every original subgroup section is mapped to its SAME literal subgroup
of S_b before the existing Kovács--Praeger bound is applied. -/
theorem bounded_section_omega (hKP : KovacsPraegerAbelianizationBound)
    {b : ℕ} (G : Subgroup (PermutationGroup b))
    (H : Subgroup G) (A : Type) [CommGroup A] [Finite A]
    (f : H →* A) (hf : Function.Surjective f) :
    AbelianSectionSize.omega (Nat.card A) ≤ 2*b := by
  let e := H.equivMapOfInjective G.subtype Subtype.val_injective
  exact AbelianSectionSize.section_omega_le_twice_degree hKP (H.map G.subtype)
    (f.comp e.symm.toMonoidHom) (hf.comp e.symm.surjective)

/-- Ordinary Theorem7 now produces the actual nilpotent core and actual
finite generator set in EACH bounded-orbit source. No encoding is assumed. -/
theorem bounded_nilpotent_generation
    (hsub : PublishedSolubleSubdirectHeight)
    (hseven : PublishedTheoremSeven) (hKP : KovacsPraegerAbelianizationBound)
    {C b : ℕ} (G : Subgroup (PermutationGroup b)) [IsSolvable G]
    (hG : OrbitCutoffFamilies.OrbitCutoff C G) :
    ∃ (K : Subgroup G) (S : Finset G), Group.IsNilpotent K ∧
      (S.card : ℝ) ≤ 4*(C.factorial : ℝ)*Real.sqrt (2*b : ℕ) ∧
      Subgroup.closure ((S : Set G) ∪ K)=⊤ :=
  hseven G C.factorial (2*b) (bounded_height hsub G hG)
    (bounded_section_omega hKP G)

end SymmetricSubgroupAsymptotics.MarkedC4.OrdinaryNilpotentGeneration
