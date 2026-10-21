import SymmetricSubgroupAsymptotics.CFSGRadicalFreeSocle
import SymmetricSubgroupAsymptotics.MinimalNormalCompositionCharts
import SymmetricSubgroupAsymptotics.PrimitiveSocleDirectProduct

/-! A literal semisimple chart of the full socle of every finite group
with trivial soluble radical. The finite join retains the actual ambient
minimal normal subgroups, discards redundant factors, and splits only
disjoint commuting factors. No CFSG hypothesis is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGReduction

def transportSemisimpleChart {A B : Type} [Group A] [Group B]
    (e : A ≃* B) (C : SemisimpleGroupChart A) : SemisimpleGroupChart B where
  ι := C.ι
  factor := C.factor
  simple := C.simple
  centerless := C.centerless
  equiv := e.symm.trans C.equiv

def joinedFactor {A B : Type} [Group A] [Group B]
    (C : SemisimpleGroupChart A) (D : SemisimpleGroupChart B) : C.ι ⊕ D.ι → Type
  | .inl i => C.factor i
  | .inr i => D.factor i

instance joinedFactorGroup {A B : Type} [Group A] [Group B]
    (C : SemisimpleGroupChart A) (D : SemisimpleGroupChart B) :
    ∀ i, Group (joinedFactor C D i)
  | .inl i => C.group i
  | .inr i => D.group i

instance joinedFactorFinite {A B : Type} [Group A] [Group B]
    (C : SemisimpleGroupChart A) (D : SemisimpleGroupChart B) :
    ∀ i, Finite (joinedFactor C D i)
  | .inl i => C.finite i
  | .inr i => D.finite i

def productSemisimpleChart {A B : Type} [Group A] [Group B]
    (C : SemisimpleGroupChart A) (D : SemisimpleGroupChart B) :
    SemisimpleGroupChart (A × B) := by
  let e : (((i : C.ι) → C.factor i) × ((i : D.ι) → D.factor i)) ≃*
      ((i : C.ι ⊕ D.ι) → joinedFactor C D i) :=
    { toFun := fun f i => match i with
        | .inl j => f.1 j
        | .inr j => f.2 j
      invFun := fun f => (fun i => f (.inl i), fun i => f (.inr i))
      left_inv := fun _ => rfl
      right_inv := by intro f; funext i; cases i <;> rfl
      map_mul' := by intro f g; funext i; cases i <;> rfl }
  refine {
    ι := C.ι ⊕ D.ι
    factor := joinedFactor C D
    simple := ?_
    centerless := ?_
    equiv := (C.equiv.prodCongr D.equiv).trans e }
  · intro i
    cases i with
    | inl i => exact C.simple i
    | inr i => exact D.simple i
  · intro i
    cases i with
    | inl i => exact C.centerless i
    | inr i => exact D.centerless i

def botSemisimpleChart (G : Type) [Group G] :
    SemisimpleGroupChart ↥(⊥ : Subgroup G) where
  ι := Empty
  factor := fun _ => PUnit
  simple := fun i => Empty.elim i
  centerless := fun i => Empty.elim i
  equiv :=
    { toFun := fun _ _ => PUnit.unit
      invFun := fun _ => 1
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun _ => Subsingleton.elim _ _
      map_mul' := fun _ _ => Subsingleton.elim _ _ }

private theorem sup_normal_of_finite_normals {G : Type} [Group G]
    (S : Finset (Subgroup G)) (hS : ∀ M ∈ S, M.Normal) :
    (S.sup id : Subgroup G).Normal := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert M S hMS ih =>
    letI : M.Normal := hS M (Finset.mem_insert_self _ _)
    letI : (S.sup id : Subgroup G).Normal :=
      ih (fun K hK => hS K (Finset.mem_insert_of_mem hK))
    simpa only [Finset.sup_insert] using
      (inferInstance : (M ⊔ S.sup id : Subgroup G).Normal)

theorem finite_minimal_join_semisimple {G : Type} [Group G] [Finite G]
    (S : Finset (Subgroup G))
    (hS : ∀ M ∈ S, IsMinimalNormalSubgroup M ∧ ¬ IsMulCommutative M) :
    Nonempty (SemisimpleGroupChart ↥(S.sup id)) := by
  induction S using Finset.induction_on with
  | empty =>
    simpa only [Finset.sup_empty] using Nonempty.intro (botSemisimpleChart G)
  | @insert M S hMS ih =>
    have hM := hS M (Finset.mem_insert_self _ _)
    have hrest := fun K hK => hS K (Finset.mem_insert_of_mem hK)
    obtain ⟨D⟩ := ih hrest
    letI : M.Normal := hM.1.1
    letI : (S.sup id : Subgroup G).Normal :=
      sup_normal_of_finite_normals S (fun K hK => (hrest K hK).1.1)
    by_cases hle : M ≤ S.sup id
    · have he : S.sup id = (insert M S).sup id := by
        rw [Finset.sup_insert, id_eq, sup_eq_right.mpr hle]
      exact ⟨transportSemisimpleChart (MulEquiv.subgroupCongr he) D⟩
    · have hdis : Disjoint M (S.sup id) := by
        rw [disjoint_iff]
        by_contra hne
        have heq : M ⊓ S.sup id = M :=
          hM.1.2.2 _ inferInstance hne inf_le_left
        exact hle (by rw [← heq]; exact inf_le_right)
      let C₀ := semisimpleNormalChart_of_nonabelian_minimal M
        (fun K hK hKM => by
          by_cases hbot : K = ⊥
          · exact Or.inl hbot
          · exact Or.inr (hM.1.2.2 K hK hbot hKM)) hM.2
      let C : SemisimpleGroupChart M :=
        { ι := C₀.ι, factor := C₀.factor, simple := C₀.simple,
          centerless := C₀.centerless, equiv := C₀.equiv }
      let e := PrimitiveSocleONanScottHelpers.commutingDisjointSupEquiv
        M (S.sup id) hdis (fun a b =>
          Subgroup.commute_of_normal_of_disjoint M (S.sup id) inferInstance
            inferInstance hdis a b a.property b.property)
      have he : M ⊔ S.sup id = (insert M S).sup id := by
        rw [Finset.sup_insert, id_eq]
      exact ⟨transportSemisimpleChart
        (e.trans (MulEquiv.subgroupCongr he)) (productSemisimpleChart C D)⟩

theorem radicalFreeSocle_semisimple (G : Type) [Group G] [Finite G]
    (hR : solubleRadical G = ⊥) :
    Nonempty (SemisimpleGroupChart (finiteGroupSocle G)) := by
  let S : Finset (Subgroup G) :=
    Finset.univ.filter (fun M => IsMinimalNormalSubgroup M)
  have hS (M : Subgroup G) (hM : M ∈ S) :
      IsMinimalNormalSubgroup M ∧ ¬ IsMulCommutative M := by
    have h := (Finset.mem_filter.mp hM).2
    exact ⟨h, minimalNormal_noncommutative_of_radical_eq_bot hR M h⟩
  obtain ⟨C⟩ := finite_minimal_join_semisimple S hS
  letI : (S.sup id : Subgroup G).Normal :=
    sup_normal_of_finite_normals S (fun M hM => (hS M hM).1.1)
  have he : S.sup id = finiteGroupSocle G := by
    apply le_antisymm
    · apply Finset.sup_le
      intro M hM x hx
      exact Subgroup.subset_normalClosure ⟨M, (hS M hM).1, hx⟩
    · apply Subgroup.normalClosure_le_normal
      rintro x ⟨M, hM, hx⟩
      have hmS : M ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hM⟩
      exact (Finset.le_sup (f := id) hmS) hx
  exact ⟨transportSemisimpleChart (MulEquiv.subgroupCongr he) C⟩

end SymmetricSubgroupAsymptotics.CFSGReduction
