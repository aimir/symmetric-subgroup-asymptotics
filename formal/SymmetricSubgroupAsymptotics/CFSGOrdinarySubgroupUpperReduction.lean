import SymmetricSubgroupAsymptotics.BoundedOrbitNilpotentCoreGeneration
import SymmetricSubgroupAsymptotics.KovacsPraegerAbelianizationProof
import SymmetricSubgroupAsymptotics.MarkedC4AschbacherGuralnickSolubleGeneration
import SymmetricSubgroupAsymptotics.MarkedC4SolubleContainerOrder

/-! Ordinary finite counting reductions for the CFSG closure project.
These statements do not assume the symmetric subgroup upper bound or T1.
The nilpotent targets are actual subgroups on the original points, and
recovery uses their actual supplement tuples. No asymptotic bound on those
targets is asserted in this file. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGOrdinarySubgroupUpperReduction
open MarkedC4

/-- Aschbacher--Guralnick removes nonsoluble sources at the exact cost of
one original ambient element, for every finite group. -/
theorem subgroup_card_le_card_mul_soluble
    (hAG : PublishedAschbacherGuralnickSolubleGeneration)
    (G : Type) [Group G] [Finite G] :
    Nat.card (Subgroup G) ≤ Nat.card G * Nat.card {K : Subgroup G // IsSolvable K} := by
  choose K x hsol hgen using (fun J : Subgroup G => hAG J)
  have hcore (J : Subgroup G) : IsSolvable ((K J).map J.subtype) := by
    letI := hsol J
    exact solvable_of_solvable_injective
      (f := ((K J).equivMapOfInjective J.subtype Subtype.val_injective).symm.toMonoidHom)
      ((K J).equivMapOfInjective J.subtype Subtype.val_injective).symm.injective
  let code : Subgroup G → {K : Subgroup G // IsSolvable K} × G :=
    fun J => (⟨(K J).map J.subtype,hcore J⟩,(x J : G))
  have hinj : Function.Injective code := by
    intro J L h
    have hc : (K J).map J.subtype=(K L).map L.subtype :=
      congrArg (fun z : {K : Subgroup G // IsSolvable K} × G => z.1.val) h
    have hx : (x J : G)=(x L : G) := congrArg Prod.snd h
    rw [←ambient_recovery_of_soluble_generation J (K J) (x J) (hgen J),
      ←ambient_recovery_of_soluble_generation L (K L) (x L) (hgen L),hc,hx]
  calc
    _ ≤ Nat.card ({K : Subgroup G // IsSolvable K} × G) :=
      Nat.card_le_card_of_injective code hinj
    _ = _ := by rw [Nat.card_prod]; exact Nat.mul_comm _ _

/-- A generic literal family can be counted by its retained cores and
its displayed generators in the SAME finite container. -/
theorem family_card_le_core_mul_power
    {b l : ℕ} {A : Type} [Finite A]
    (D : Subgroup (PermutationGroup b))
    (source : A → Subgroup (PermutationGroup b))
    (hsource : Function.Injective source) (hD : ∀ a,source a≤D)
    (P : Subgroup (PermutationGroup b) → Prop)
    (hordinary : ∀ a,∃ (K : Subgroup (source a)) (S : Finset (source a)),
      P (K.map (source a).subtype) ∧ S.card≤l ∧
        Subgroup.closure ((S : Set (source a))∪K)=⊤) :
    Nat.card A ≤ Nat.card {J : Subgroup (PermutationGroup b) // P J} * Nat.card D^l := by
  letI : Fintype A := Fintype.ofFinite A
  choose K S hP hcard hgen using hordinary
  have ht (a : A) : ∃ t : Fin l → source a,
      Subgroup.closure (Set.range t∪K a)=⊤ :=
    NilpotentGenerationRelative.exists_padded_generating_tuple (K a) (S a) (hcard a) (hgen a)
  choose tuple htuple using ht
  have hinj := RelativeGenerationLiteral.code_injective D source hsource hD K tuple htuple P hP
  calc
    _ ≤ Nat.card ({J : Subgroup (PermutationGroup b) // P J} × (Fin l → D)) :=
      Nat.card_le_card_of_injective _ hinj
    _ = _ := by rw [Nat.card_prod,Nat.card_fun,Nat.card_fin]

abbrev NilpotentSources (b : ℕ) :=
  {J : Subgroup (PermutationGroup b) // Group.IsNilpotent J}
abbrev BoundedSolubleInside (C b : ℕ) (D : Subgroup (PermutationGroup b)) :=
  {J : Subgroup (PermutationGroup b) //
    IsSolvable J ∧ OrbitCutoffFamilies.OrbitCutoff C J ∧ J≤D}

/-- The already proved bounded-chief-section theorem supplies the short
supplement. In particular there is no unrestricted Theorem7 premise. -/
theorem bounded_soluble_inside_card_le (C b : ℕ) (D : Subgroup (PermutationGroup b)) :
    Nat.card (BoundedSolubleInside C b D) ≤
      Nat.card (NilpotentSources b) *
        Nat.card D^(OrdinaryNilpotentGeneration.nilpotentControlCutoff C * Nat.sqrt (2*b)) := by
  apply family_card_le_core_mul_power D
    (fun J : BoundedSolubleInside C b D => J.val) Subtype.val_injective
    (fun J => J.property.2.2) (fun J => Group.IsNilpotent J)
  intro J
  letI : IsSolvable J.val := J.property.1
  obtain ⟨K,S,hK,hS,hgen⟩ := OrdinaryNilpotentGeneration.bounded_orbit_nilpotent_core_generation
    KovacsPraegerAbelianizationProof.kovacsPraegerAbelianizationBound J.val J.property.2.1
  refine ⟨K,S,?_,hS,hgen⟩
  letI := hK
  exact Group.nilpotent_of_mulEquiv
    (K.equivMapOfInjective J.val.subtype Subtype.val_injective)

/-- Finite covers are paid once. This elementary union bound retains
literal membership in every container and tolerates overlaps. -/
theorem family_card_le_sum_inside
    {G I : Type} [Group G] [Finite G] [Fintype I]
    (P : Subgroup G → Prop) (D : I → Subgroup G)
    (hcover : ∀ J : Subgroup G,P J → ∃ i,J≤D i) :
    Nat.card {J : Subgroup G // P J} ≤
      ∑ i : I,Nat.card {J : Subgroup G // P J ∧ J≤D i} := by
  choose index hindex using (fun J : {J : Subgroup G // P J} => hcover J.val J.property)
  let code : {J : Subgroup G // P J} →
      Σ i : I,{J : Subgroup G // P J ∧ J≤D i} :=
    fun J => ⟨index J,⟨J.val,J.property,hindex J⟩⟩
  have hinj : Function.Injective code := by
    intro J L h
    apply Subtype.ext
    exact congrArg (fun z : Σ i : I,{J : Subgroup G // P J ∧ J≤D i} => z.2.val) h
  exact (Nat.card_le_card_of_injective code hinj).trans_eq (by rw [Nat.card_sigma])

/-- A concrete ordinary bounded-orbit soluble count, after removing all
relative generation and core-recovery obligations. The remaining factors
are the actual soluble-container menu and actual nilpotent subgroups. -/
theorem bounded_soluble_card_le_menu_mul_nilpotent
    (hDixon : MarkedC4.SolubleContainerOrder.PublishedDixonOrder) (C b : ℕ) :
    Nat.card (OrbitCutoffFamilies.SolubleFamily C b) ≤
      Nat.card (SolubleContainerCount.Index (Fin b)) * Nat.card (NilpotentSources b) *
        (2^(2*b))^(OrdinaryNilpotentGeneration.nilpotentControlCutoff C * Nat.sqrt (2*b)) := by
  letI : Fintype (SolubleContainerCount.Index (Fin b)) := Fintype.ofFinite _
  have hcover (J : Subgroup (PermutationGroup b))
      (hJ : IsSolvable J ∧ OrbitCutoffFamilies.OrbitCutoff C J) :
      ∃ i : SolubleContainerCount.Index (Fin b),
        J≤SolubleContainerOrder.physicalContainer (Fin b) i := by
    letI : IsSolvable J := hJ.1
    exact SolubleContainerOrder.cover (Fin b) J
  have hu := family_card_le_sum_inside
    (fun J : Subgroup (PermutationGroup b) => IsSolvable J ∧ OrbitCutoffFamilies.OrbitCutoff C J)
    (SolubleContainerOrder.physicalContainer (Fin b)) hcover
  calc
    _ ≤ ∑ i : SolubleContainerCount.Index (Fin b),
        Nat.card (BoundedSolubleInside C b (SolubleContainerOrder.physicalContainer (Fin b) i)) := by
      simpa only [BoundedSolubleInside,and_assoc] using hu
    _ ≤ ∑ _i : SolubleContainerCount.Index (Fin b),
        Nat.card (NilpotentSources b) *
          (2^(2*b))^(OrdinaryNilpotentGeneration.nilpotentControlCutoff C * Nat.sqrt (2*b)) := by
      apply Finset.sum_le_sum
      intro i _
      apply (bounded_soluble_inside_card_le C b _).trans
      apply Nat.mul_le_mul_left
      apply Nat.pow_le_pow_left
      simpa only [Fintype.card_fin] using SolubleContainerOrder.physicalContainer_order (Fin b) hDixon i
    _ = _ := by simp [Nat.card_eq_fintype_card,mul_assoc,mul_left_comm,mul_comm]

end SymmetricSubgroupAsymptotics.CFSGOrdinarySubgroupUpperReduction
