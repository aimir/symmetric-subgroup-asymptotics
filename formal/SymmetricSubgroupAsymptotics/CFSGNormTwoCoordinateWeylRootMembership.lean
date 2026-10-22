import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylWordDegree
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckRootSignSteps
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateReflectionSigns

/-! Simultaneous positive/negative membership for EVERY actual finite
Weyl-word conjugate of an original simple root unit. The sign is the
literal sign of its reflected norm-two integer vector. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWeylRootMembership
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckColumns
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckPositivePGroup
open CFSGNormTwoGeckLatticeDegree CFSGNormTwoGeckWeylWordDegree
open CFSGNormTwoGeckQuadraticMembership CFSGNormTwoGeckRootSignSteps
open CFSGNormTwoCoordinateExcludedHeight CFSGNormTwoPositiveRootExcludedHeight
open CFSGNormTwoCoordinateReflectionSigns CFSGSerreQuadraticMatrix CFSGGradedQuadraticUnit
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀j,A j j=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]

local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

def rootWord (K : Type) [Field K] (w : List (Fin r)) (j : Fin r) (t : K) :
    (Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K)ˣ :=
  wordUnit A hs hp b₀ s₀ K w*canonicalRoot (realizationData A hs hp b₀ s₀) K false j t*
    (wordUnit A hs hp b₀ s₀ K w)⁻¹

theorem rootWord_cons (K : Type) [Field K] (i : Fin r) (w : List (Fin r))
    (j : Fin r) (t : K) :
    rootWord A hd hs hp ho K (i::w) j t=
      canonicalWeyl (realizationData A hs hp b₀ s₀) K i*rootWord A hd hs hp ho K w j t*
        (canonicalWeyl (realizationData A hs hp b₀ s₀) K i)⁻¹ := by
  dsimp only [rootWord,wordUnit]
  group

theorem word_sign_membership (K : Type) [Field K] (w : List (Fin r)) (j : Fin r) (t : K) :
    ((∀l,0≤(wordRoot A hs hp b₀ s₀ w (s₀ j)).val l) ∧
      rootWord A hd hs hp ho K w j t∈rootGroup A hs hp b₀ s₀ K false) ∨
    ((∀l,(wordRoot A hs hp b₀ s₀ w (s₀ j)).val l≤0) ∧
      rootWord A hd hs hp ho K w j t∈rootGroup A hs hp b₀ s₀ K true) := by
  induction w with
  | nil=>
    left
    constructor
    · intro l
      change 0≤(Pi.single j (1:ℤ) : Fin r→ℤ) l
      by_cases hjl : j=l <;> simp [Pi.single_apply,hjl]
    · change 1*canonicalRoot (realizationData A hs hp b₀ s₀) K false j t*1⁻¹∈_
      rw [one_mul,inv_one,mul_one]
      exact Subgroup.subset_closure ⟨(j,t),rfl⟩
  | cons i w ih=>
    let k : Roots A := wordRoot A hs hp b₀ s₀ w (s₀ j)
    let g := rootWord A hd hs hp ho K w j t
    have hgrade : QuadraticGrade (latticeWeight A hs hp b₀) k.val g :=
      word_conjugate_quadraticGrade A hs hp b₀ s₀ K w j t
    have hi : excludedHeight i (s₀ i:Roots A).val=0 := excluded_simple_zero A hd hs hp ho i
    have hother : ∀l : Fin r,i≠l→0<excludedHeight i (s₀ l:Roots A).val :=
      fun l hil=>excluded_other_positive A hd hs hp ho i l hil
    rcases ih with ⟨hkpos,hgpos⟩|⟨hkneg,hgneg⟩
    · by_cases hk : k=coordinateRoot A hd i
      · right
        have hroot : wordRoot A hs hp b₀ s₀ (i::w) (s₀ j)=
            negativeIndex A hs hp (coordinateRoot A hd i) := by
          change (rootPairing A hs hp).reflectionPerm (s₀ i) k=_
          rw [hk]
          rfl
        constructor
        · intro l
          rw [hroot,negative_val]
          change -((Pi.single i (1:ℤ) : Fin r→ℤ) l)≤0
          by_cases hil : i=l <;> simp [Pi.single_apply,hil]
        · have hz : excludedHeight i k.val=0 := by
            rw [hk]
            change excludedHeight i (Pi.single i 1)=0
            simp [excludedHeight_single]
          rw [rootWord_cons]
          exact positive_flip A hs hp b₀ s₀ (excludedHeight i) i hi hother K k.val g hgpos hgrade hz
      · left
        constructor
        · exact reflection_nonnegative A hd hs hp ho i k hkpos hk
        · have hgt := excludedHeight_positive A hd i k hkpos hk
          rw [rootWord_cons]
          exact weyl_conjugate_positive A hs hp b₀ s₀ (excludedHeight i) i hi hother K k.val g
            hgpos hgrade hgt
    · by_cases hk : negativeIndex A hs hp k=coordinateRoot A hd i
      · left
        have hkv : k.val= -(coordinateRoot A hd i).val := by
          have he := congrArg Subtype.val hk
          rw [negative_val] at he
          have hh := congrArg (fun x : Fin r→ℤ=> -x) he
          simpa only [neg_neg] using hh
        have hkn : k=negativeIndex A hs hp (coordinateRoot A hd i) := by
          apply Subtype.ext
          rw [negative_val]
          exact hkv
        have hroot : wordRoot A hs hp b₀ s₀ (i::w) (s₀ j)=coordinateRoot A hd i := by
          change (rootPairing A hs hp).reflectionPerm (coordinateRoot A hd i) k=_
          rw [hkn,negativeIndex,RootPairing.reflectionPerm_self]
        constructor
        · intro l
          rw [hroot]
          change 0≤(Pi.single i (1:ℤ) : Fin r→ℤ) l
          by_cases hil : i=l <;> simp [Pi.single_apply,hil]
        · have hz : excludedHeight i k.val=0 := by
            rw [hkv,map_neg]
            change -(excludedHeight i (Pi.single i 1))=0
            simp [excludedHeight_single]
          rw [rootWord_cons]
          exact negative_flip A hs hp b₀ s₀ (excludedHeight i) i hi hother K k.val g hgneg hgrade hz
      · right
        constructor
        · exact reflection_nonpositive A hd hs hp ho i k hkneg hk
        · have hpos : ∀l,0≤(negativeIndex A hs hp k).val l := by
            intro l
            rw [negative_val]
            change 0≤ -k.val l
            exact neg_nonneg.mpr (hkneg l)
          have hgt := excludedHeight_positive A hd i (negativeIndex A hs hp k) hpos hk
          rw [negative_val,map_neg] at hgt
          have hlt : excludedHeight i k.val<0 := by omega
          rw [rootWord_cons]
          exact negative_stays_negative A hs hp b₀ s₀ (excludedHeight i) i hi hother K k.val g
            hgneg hgrade hlt

theorem positive_word_mem (K : Type) [Field K] (w : List (Fin r)) (j : Fin r) (t : K)
    (hpos : ∀l,0≤(wordRoot A hs hp b₀ s₀ w (s₀ j)).val l) :
    rootWord A hd hs hp ho K w j t∈rootGroup A hs hp b₀ s₀ K false := by
  rcases word_sign_membership A hd hs hp ho K w j t with ⟨_,h⟩|⟨hneg,_⟩
  · exact h
  · exact False.elim (root_signs_incompatible A _ hpos hneg)

theorem negative_word_mem (K : Type) [Field K] (w : List (Fin r)) (j : Fin r) (t : K)
    (hneg : ∀l,(wordRoot A hs hp b₀ s₀ w (s₀ j)).val l≤0) :
    rootWord A hd hs hp ho K w j t∈rootGroup A hs hp b₀ s₀ K true := by
  rcases word_sign_membership A hd hs hp ho K w j t with ⟨hpos,_⟩|⟨_,h⟩
  · exact False.elim (root_signs_incompatible A _ hpos hneg)
  · exact h

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWeylRootMembership
