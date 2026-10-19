import SymmetricSubgroupAsymptotics.MarkedC4ActualWordCharacterGraphs
import SymmetricSubgroupAsymptotics.MarkedC4BinaryWordFamilyEncoding

/-! Group the literal target family by shape and original letters BEFORE
counting subgroups and characters. An image is consumed inside its joint
graph fibre; it is not an additional external menu coordinate. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualBinaryWordSkeletons
open FiniteOrbitWordShapes FiniteBinaryWordTargets

abbrev Skeleton (C b : ℕ) := {p : Σ S : Shape C b,LocalGroups S //
  (∀ i,IsPGroup 2 (p.2 i)) ∧
    ∀ i (x y : Fin (p.1.degrees i).val),∃ g : p.2 i,g.val x=y}
instance skeletonFinite (C b : ℕ) : Finite (Skeleton C b) := by
  unfold Skeleton
  infer_instance
instance skeletonFintype (C b : ℕ) : Fintype (Skeleton C b) := Fintype.ofFinite _
abbrev Factors {C b : ℕ} (p : Skeleton C b) := fun i => ↥(p.val.2 i)
local instance sourceFintype {C b : ℕ} (p : Skeleton C b) :
    Fintype (ActualWordCharacterGraphs.Source (Factors p)) := Fintype.ofFinite _

def targetEquiv (C b : ℕ) : Target C b ≃
    Σ p : Skeleton C b,ActualWordCharacterGraphs.Source (Factors p) where
  toFun T := ⟨⟨⟨T.shape,T.letters⟩,T.binary,T.transitive⟩,T.image,T.subdirect⟩
  invFun z :=
    { shape := z.1.val.1
      letters := z.1.val.2
      binary := z.1.property.1
      transitive := z.1.property.2
      image := z.2.val
      subdirect := z.2.property }
  left_inv T := by cases T; rfl
  right_inv z := by rcases z with ⟨⟨⟨S,L⟩,hb,ht⟩,H,hH⟩; rfl

theorem wordCount_eq (C b r : ℕ) : BinaryWordFamilyEncoding.wordCount C b r=
    ∑ p : Skeleton C b,∑ H : ActualWordCharacterGraphs.Source (Factors p),
      (Nat.card (H.val →* Multiplicative (ZMod 4)) : ℝ)^r := by
  unfold BinaryWordFamilyEncoding.wordCount
  calc
    _ = ∑ z : (Σ p : Skeleton C b,ActualWordCharacterGraphs.Source (Factors p)),
        (Nat.card (z.2.val →* Multiplicative (ZMod 4)) : ℝ)^r :=
      Fintype.sum_equiv (targetEquiv C b) _ _ (fun _ => rfl)
    _ = _ := Fintype.sum_sigma _

/-- Each fixed shape/letter term is exactly one marked physical family. -/
theorem wordCount_le (C b r : ℕ) : BinaryWordFamilyEncoding.wordCount C b r ≤
    ∑ p : Skeleton C b,
      (Nat.card (ActualFullPhysicalWordPeel.Family (Factors p)
        (ActualGlobalMarkGeneratorRank.Marks r)) : ℝ) := by
  rw [wordCount_eq]
  exact Finset.sum_le_sum (fun p _ => ActualWordCharacterGraphs.moment_le (Factors p) r)

end SymmetricSubgroupAsymptotics.MarkedC4.ActualBinaryWordSkeletons
