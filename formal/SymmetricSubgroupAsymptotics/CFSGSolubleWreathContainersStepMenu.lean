import SymmetricSubgroupAsymptotics.CFSGSolublePrimitiveContainersMenu
import SymmetricSubgroupAsymptotics.CFSGSolubleWreathContainersInterface
import SymmetricSubgroupAsymptotics.CFSGSolubleWreathContainersAction

/-! One finite wreath-envelope menu at degree n. Proper product factors
have degree less than n and use an already constructed top cover. The
final permutation explicitly records the original whole-point labels. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGSolubleWreathContainers
open CFSGSolublePrimitiveContainers

abbrev FactorPair (n : ℕ) :=
  {p : Fin n × Fin n // 2 ≤ p.1.val ∧ 2 ≤ p.2.val ∧ p.1.val * p.2.val = n}

abbrev StepBaseIndex (n : ℕ) (below : ∀ d : Fin n, TransitiveSolubleContainerCover d.val) :=
  PrimitiveIndex n ⊕
    (Σ p : FactorPair n, PrimitiveIndex p.val.1.val × (below p.val.2).Index)

abbrev StepIndex (n : ℕ) (below : ∀ d : Fin n, TransitiveSolubleContainerCover d.val) :=
  StepBaseIndex n below × Equiv.Perm (Fin n)

instance stepIndex_finite (n : ℕ) (below : ∀ d : Fin n, TransitiveSolubleContainerCover d.val) :
    Finite (StepIndex n below) := inferInstance

def stepBaseGroup (n : ℕ) (below : ∀ d : Fin n, TransitiveSolubleContainerCover d.val) :
    StepBaseIndex n below → Subgroup (Equiv.Perm (Fin n))
  | Sum.inl i => primitiveEnvelope i
  | Sum.inr ⟨p, i, j⟩ =>
    (wreathEnvelope (primitiveEnvelope i) ((below p.val.2).group j)).map
      (finCongr p.property.2.2).permCongrHom.toMonoidHom

def stepGroup (n : ℕ) (below : ∀ d : Fin n, TransitiveSolubleContainerCover d.val)
    (i : StepIndex n below) : Subgroup (Equiv.Perm (Fin n)) :=
  (stepBaseGroup n below i.1).map i.2.permCongrHom.toMonoidHom

theorem subgroup_map_soluble {G H : Type*} [Group G] [Group H]
    (f : G →* H) (K : Subgroup G) [IsSolvable K] : IsSolvable (K.map f) :=
  solvable_of_surjective (f.subgroupMap_surjective K)

theorem stepBaseGroup_soluble (n : ℕ)
    (below : ∀ d : Fin n, TransitiveSolubleContainerCover d.val) (i : StepBaseIndex n below) :
    IsSolvable (stepBaseGroup n below i) := by
  cases i with
  | inl i => exact primitiveEnvelope_soluble i
  | inr i =>
    rcases i with ⟨p, i, j⟩
    letI solubleWreathStep_local : IsSolvable (primitiveEnvelope i) := primitiveEnvelope_soluble i
    letI solubleWreathStep_top : IsSolvable ((below p.val.2).group j) := (below p.val.2).soluble j
    letI solubleWreathStep_product :
        IsSolvable (wreathEnvelope (primitiveEnvelope i) ((below p.val.2).group j)) :=
      wreathEnvelope_soluble _ _
    exact subgroup_map_soluble _ _

theorem stepGroup_soluble (n : ℕ)
    (below : ∀ d : Fin n, TransitiveSolubleContainerCover d.val) (i : StepIndex n below) :
    IsSolvable (stepGroup n below i) := by
  letI solubleWreathStep_base : IsSolvable (stepBaseGroup n below i.1) := stepBaseGroup_soluble n below i.1
  exact subgroup_map_soluble _ _

theorem stepIndex_card_eq (n : ℕ)
    (below : ∀ d : Fin n, TransitiveSolubleContainerCover d.val) :
    Nat.card (StepIndex n below) =
      (Nat.card (PrimitiveIndex n) + ∑ p : FactorPair n,
        Nat.card (PrimitiveIndex p.val.1.val) * Nat.card (below p.val.2).Index) * n.factorial := by
  have hsigma : Nat.card (Σ p : FactorPair n,
      PrimitiveIndex p.val.1.val × (below p.val.2).Index) =
      ∑ p : FactorPair n, Nat.card (PrimitiveIndex p.val.1.val) *
        Nat.card (below p.val.2).Index := by
    rw [Nat.card_sigma]
    simp only [Nat.card_prod]
  rw [Nat.card_prod]
  change Nat.card (StepBaseIndex n below) * Nat.card (Equiv.Perm (Fin n)) = _
  rw [Nat.card_sum, hsigma]
  rw [Nat.card_eq_fintype_card (α := Equiv.Perm (Fin n)), Fintype.card_perm, Fintype.card_fin]

end SymmetricSubgroupAsymptotics.CFSGSolubleWreathContainers
