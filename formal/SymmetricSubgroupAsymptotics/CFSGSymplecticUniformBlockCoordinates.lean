import SymmetricSubgroupAsymptotics.CFSGSymplecticUniformRootCoordinates

/-! Literal entry coordinates determine every symplectic block matrix.
This is a structural ALL-rank statement, not a finite matrix census. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticUniformBlockCoordinates
open CFSGSymplecticSerreMatrices CFSGSymplecticOriginalRootCandidates
open CFSGSymplecticUniformRootCoordinates
variable (R : Type*) [CommRing R] (r : ℕ)

def Block (M : Mat R r) : Prop :=
  (∀ i j,M (.inr i) (.inr j)= -M (.inl j) (.inl i)) ∧
  (∀ i j,M (.inl i) (.inr j)=M (.inl j) (.inr i)) ∧
  (∀ i j,M (.inr i) (.inl j)=M (.inr j) (.inl i))

theorem coordinates_injective (M N : Mat R r) (hM : Block R r M) (hN : Block R r N)
    (hc : coordinates R r M=coordinates R r N) : M=N := by
  have hPP : ∀ i j : Fin r,M (.inl i) (.inl j)=N (.inl i) (.inl j) := by
    intro i j
    rcases lt_trichotomy i.val j.val with hij | he | hji
    · exact congrFun hc (.inr (false,.inl ⟨(i,j),hij⟩))
    · have he' : i=j:=Fin.ext he
      subst j
      exact congrFun hc (.inl i)
    · exact congrFun hc (.inr (true,.inl ⟨(j,i),hji⟩))
  have hPQ : ∀ i j : Fin r,M (.inl i) (.inr j)=N (.inl i) (.inr j) := by
    intro i j
    rcases lt_trichotomy i.val j.val with hij | he | hji
    · exact congrFun hc (.inr (false,.inr (.inr ⟨(i,j),hij⟩)))
    · have he' : i=j:=Fin.ext he
      subst j
      exact congrFun hc (.inr (false,.inr (.inl i)))
    · rw [hM.2.1 i j,hN.2.1 i j]
      exact congrFun hc (.inr (false,.inr (.inr ⟨(j,i),hji⟩)))
  have hQP : ∀ i j : Fin r,M (.inr i) (.inl j)=N (.inr i) (.inl j) := by
    intro i j
    rcases lt_trichotomy i.val j.val with hij | he | hji
    · rw [hM.2.2 i j,hN.2.2 i j]
      exact congrFun hc (.inr (true,.inr (.inr ⟨(i,j),hij⟩)))
    · have he' : i=j:=Fin.ext he
      subst j
      exact congrFun hc (.inr (true,.inr (.inl i)))
    · exact congrFun hc (.inr (true,.inr (.inr ⟨(j,i),hji⟩)))
  apply Matrix.ext
  intro i j
  cases i with
  | inl i => cases j with
    | inl j => exact hPP i j
    | inr j => exact hPQ i j
  | inr i => cases j with
    | inl j => exact hQP i j
    | inr j => rw [hM.1 i j,hN.1 i j,hPP]

end SymmetricSubgroupAsymptotics.CFSGSymplecticUniformBlockCoordinates
