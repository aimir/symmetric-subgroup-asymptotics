import SymmetricSubgroupAsymptotics.CFSGHomConjugateOrbitCardinality
import SymmetricSubgroupAsymptotics.CFSGCentralizerFamilySquare

/-! A finite seed menu and literal homomorphism centralizers charge a
whole root family jointly. The source-group cardinal stays symbolic;
no exact unipotent order or action-map injectivity is needed. Combining
this count with strict double-Sylow growth gives the original simple
least-index square without a separate root-by-root numerical argument. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGHomRootFamilyCoverCardinality
open CFSGHomConjugateOrbitCardinality CFSGSimpleConjugateFamilyIndex
open CFSGCentralizerFamilySquare PrimitiveSocleRawStructure
variable {U I : Type*} {G : Type} [Group U] [Group G] [Finite U] [Finite G] [Fintype I]

def conjugateOrbit (f : U →* G) (R : Subgroup G) : Set (Subgroup G) :=
  Set.range (fun u : U => R.map (MulAut.conj (f u)).toMonoidHom)

theorem family_card_le_sum (f : U →* G) (R : I → Subgroup G) (S : Set (Subgroup G))
    (hcover : ∀ x ∈ S, ∃ i : I, ∃ u : U,
      (R i).map (MulAut.conj (f u)).toMonoidHom=x) :
    Nat.card S ≤ ∑ i : I,Nat.card (conjugateOrbit f (R i)) := by
  classical
  letI (i : I) : Finite (conjugateOrbit f (R i)) :=
    Finite.of_surjective
      (fun u : U => (⟨_,⟨u,rfl⟩⟩ : conjugateOrbit f (R i)))
      (by
        rintro ⟨x,⟨u,hu⟩⟩
        exact ⟨u,Subtype.ext hu⟩)
  have hcovered (x : S) : ∃ i : I, ∃ y : conjugateOrbit f (R i), y.val=x.val := by
    obtain ⟨i,u,he⟩ := hcover x.val x.property
    exact ⟨i,⟨_,⟨u,rfl⟩⟩,he⟩
  let idx (x : S) : I := Classical.choose (hcovered x)
  let term (x : S) : conjugateOrbit f (R (idx x)) :=
    Classical.choose (Classical.choose_spec (hcovered x))
  have hterm (x : S) : (term x).val=x.val :=
    Classical.choose_spec (Classical.choose_spec (hcovered x))
  let enc : S → (i : I) × conjugateOrbit f (R i) := fun x=>⟨idx x,term x⟩
  have hinj : Function.Injective enc := by
    intro x y he
    apply Subtype.ext
    have hh := congrArg (fun z : (i : I) × conjugateOrbit f (R i)=>z.2.val) he
    change (term x).val=(term y).val at hh
    rwa [hterm,hterm] at hh
  exact (Nat.card_le_card_of_injective enc hinj).trans_eq Nat.card_sigma

theorem family_card_mul_centralizer_le (f : U →* G) (R : I → Subgroup G)
    (S : Set (Subgroup G)) (c : ℕ)
    (hcover : ∀ x ∈ S, ∃ i : I, ∃ u : U,
      (R i).map (MulAut.conj (f u)).toMonoidHom=x)
    (hcapacity : ∀ i : I,c ≤ Nat.card ((Subgroup.centralizer (R i : Set G)).comap f)) :
    Nat.card S*c ≤ Nat.card I*Nat.card U := by
  classical
  calc
    _ ≤ (∑ i : I,Nat.card (conjugateOrbit f (R i)))*c :=
      Nat.mul_le_mul_right c (family_card_le_sum f R S hcover)
    _ = ∑ i : I,Nat.card (conjugateOrbit f (R i))*c := Finset.sum_mul _ _ _
    _ ≤ ∑ _i : I,Nat.card U := by
      apply Finset.sum_le_sum
      intro i _
      exact (Nat.mul_le_mul_left _ (hcapacity i)).trans
        (image_card_mul_comap_centralizer_le f (R i))
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,Nat.card_eq_fintype_card]

theorem least_index_square_lt [IsSimpleGroup G]
    (f : U →* G) (R : I → Subgroup G) (L : Subgroup G)
    (hL0 : L≠⊥) (hL1 : L≠⊤) (c : ℕ) (hc : 0<c)
    (hmenu : Nat.card I ≤ c)
    (hcover : ∀ g : G, ∃ i : I, ∃ u : U,
      (R i).map (MulAut.conj (f u)).toMonoidHom = L.map (MulAut.conj g).toMonoidHom)
    (hcapacity : ∀ i : I,c ≤ Nat.card ((Subgroup.centralizer (R i : Set G)).comap f))
    (horder : Nat.card U^2 < Nat.card G)
    (ell : ℕ) (hell : LeastProperIndex G ell) : ell^2 < Nat.card G := by
  let S := Set.range (fun g : G=>L.map (MulAut.conj g).toMonoidHom)
  have hweighted : Nat.card S*c ≤ Nat.card I*Nat.card U := by
    apply family_card_mul_centralizer_le f R S c _ hcapacity
    rintro _ ⟨g,rfl⟩
    exact hcover g
  have hS : Nat.card S^2 < Nat.card G :=
    square_lt_of_strict_double_sylow_and_centralizer (Nat.card S) c (Nat.card I)
      (Nat.card U) (Nat.card G) hc hmenu hweighted horder
  exact (Nat.pow_le_pow_left (least_index_le_family L hL0 hL1 ell hell) 2).trans_lt hS

end SymmetricSubgroupAsymptotics.CFSGHomRootFamilyCoverCardinality
