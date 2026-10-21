import SymmetricSubgroupAsymptotics.MarkedC4BinaryWordOriginalRecovery
import SymmetricSubgroupAsymptotics.MarkedC4ActualWordMenuPartition
import SymmetricSubgroupAsymptotics.CFSGNilpotentBinaryOddConvolution

/-! Actual bounded ODD NILPOTENT orbit words. The source, all transitive
letters, the full correlated subdirect image and original labels are
retained. This is the odd-nilpotent analogue of the checked prime encoding. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGOddNilpotentBoundedWordEncoding
open MarkedC4 FiniteOrbitWordShapes FiniteBinaryWordTargets

abbrev Skeleton (C b : ℕ) := {q : Σ S : Shape C b,LocalGroups S //
  (∀ i,Group.IsNilpotent (q.2 i) ∧ ¬2 ∣ Nat.card (q.2 i)) ∧
    ∀ i (x y : Fin (q.1.degrees i).val),∃ g : q.2 i,g.val x=y}

instance skeletonFinite (C b : ℕ) : Finite (Skeleton C b) := by
  unfold Skeleton
  infer_instance

abbrev Factors {C b : ℕ} (q : Skeleton C b) := fun i => ↥(q.val.2 i)
abbrev Target (C b : ℕ) := Σ q : Skeleton C b,ActualWordMenuPartition.Family (Factors q)

instance targetFinite (C b : ℕ) : Finite (Target C b) := by
  unfold Target
  infer_instance

variable {C b : ℕ}
    (G : Subgroup (PermutationGroup b))
    [Group.IsNilpotent G]
    (hcut : OrbitCutoffFamilies.OrbitCutoff C G) (hodd : ¬2 ∣ Nat.card G)

def actualSkeleton : Skeleton C b := by
  refine ⟨⟨actualShape G hcut,actualLetters G hcut⟩,?_,
    fun i => ActualBinaryOrbitWord.letter_transitive G ((number G).symm i)⟩
  intro i
  let q := ActualBinaryOrbitWord.projection G ((number G).symm i)
  have hq := ActualBinaryOrbitWord.projection_surjective G ((number G).symm i)
  have hn : Group.IsNilpotent (ActualBinaryOrbitWord.Letter G ((number G).symm i)) :=
    Group.nilpotent_of_surjective q hq
  have hd : Nat.card (ActualBinaryOrbitWord.Letter G ((number G).symm i)) ∣ Nat.card G := by
    have h := Subgroup.card_range_dvd (ActualBinaryOrbitWord.letterMap G ((number G).symm i))
    exact h
  exact ⟨hn,fun h => hodd (h.trans hd)⟩

/-- The target retains exactly the original correlated subdirect image. -/
def actualTarget : Target C b := by
  let e : G ≃* (actualMap G hcut).range := MonoidHom.ofInjective (actualMap_injective G hcut)
  refine ⟨actualSkeleton G hcut hodd,⟨(actualMap G hcut).range,?_,?_⟩⟩
  · intro i x
    obtain ⟨g,hg⟩ := ActualBinaryOrbitWord.projection_surjective G ((number G).symm i) x
    exact ⟨(actualMap G hcut).rangeRestrict g,hg⟩
  · exact Group.nilpotent_of_mulEquiv e

def representation (T : Target C b) : T.2.val →* PermutationGroup b :=
  (canonicalPoints T.1.val.1).permCongrHom.toMonoidHom.comp
    ((BinaryWordOriginalRecovery.sigmaAction T.1.val.2).comp T.2.val.subtype)

/-- Original point labels intertwine the SAME original action. -/
theorem conjugate_eq (g : G) :
    (labelCode G hcut).permCongrHom g.val=
      representation (actualTarget G hcut hodd) ((actualMap G hcut).rangeRestrict g) := by
  have happly (y : Fin b) :
      representation (actualTarget G hcut hodd) ((actualMap G hcut).rangeRestrict g) y=
        canonicalPoints (actualShape G hcut)
          (BinaryWordOriginalRecovery.sigmaAction (actualLetters G hcut) (actualMap G hcut g)
            ((canonicalPoints (actualShape G hcut)).symm y)) := rfl
  apply Equiv.ext
  intro y
  rw [happly]
  change labelCode G hcut (g.val ((labelCode G hcut).symm y))=_
  let x : Fin b := (labelCode G hcut).symm y
  have hp : canonicalPoints (actualShape G hcut) (labels G hcut x)=y :=
    (labelCode G hcut).apply_symm_apply y
  have he : (canonicalPoints (actualShape G hcut)).symm y=labels G hcut x := by
    rw [←hp,Equiv.symm_apply_apply]
  rw [he]
  exact congrArg (canonicalPoints (actualShape G hcut))
    (BinaryWordOriginalRecovery.labels_equivariant G hcut g x)

theorem original_image :
    G.map (labelCode G hcut).permCongrHom.toMonoidHom=
      (representation (actualTarget G hcut hodd)).range := by
  apply le_antisymm
  · rintro z ⟨g,hg,rfl⟩
    exact ⟨(actualMap G hcut).rangeRestrict ⟨g,hg⟩,(conjugate_eq G hcut hodd ⟨g,hg⟩).symm⟩
  · rintro z ⟨w,rfl⟩
    have hw : ∃ g : G,actualMap G hcut g=w.val := w.property
    obtain ⟨g,hg⟩ := hw
    have he : (actualMap G hcut).rangeRestrict g=w := Subtype.ext hg
    rw [←he]
    exact ⟨g.val,g.property,conjugate_eq G hcut hodd g⟩

theorem source_eq (H : Subgroup (PermutationGroup b))
    [Group.IsNilpotent H]
    (hHcut : OrbitCutoffFamilies.OrbitCutoff C H) (hHodd : ¬2 ∣ Nat.card H)
    (ht : actualTarget G hcut hodd=actualTarget H hHcut hHodd)
    (hl : labelCode G hcut=labelCode H hHcut) : G=H := by
  apply Subgroup.map_injective
    (f := (labelCode G hcut).permCongrHom.toMonoidHom)
    (labelCode G hcut).permCongrHom.injective
  calc
    G.map (labelCode G hcut).permCongrHom.toMonoidHom=
        (representation (actualTarget G hcut hodd)).range := original_image G hcut hodd
    _ = (representation (actualTarget H hHcut hHodd)).range :=
      congrArg (fun T : Target C b => (representation T).range) ht
    _ = H.map (labelCode H hHcut).permCongrHom.toMonoidHom := (original_image H hHcut hHodd).symm
    _ = H.map (labelCode G hcut).permCongrHom.toMonoidHom := by rw [hl]

/-- The only label overhead is exactly b!, shared across the entire word. -/
theorem bounded_odd_nilpotent_card_le (C b : ℕ) :
    Nat.card (CFSGNilpotentBinaryOddConvolution.OddFamily C b) ≤ b.factorial*Nat.card (Target C b) := by
  let A := CFSGNilpotentBinaryOddConvolution.OddFamily C b
  let code : A → Target C b × Equiv.Perm (Fin b) := fun G => by
    letI : Group.IsNilpotent G.val := G.property.1
    exact (actualTarget G.val G.property.2.2 G.property.2.1,labelCode G.val G.property.2.2)
  have hinj : Function.Injective code := by
    intro G H he
    letI : Group.IsNilpotent G.val := G.property.1
    letI : Group.IsNilpotent H.val := H.property.1
    apply Subtype.ext
    exact source_eq G.val G.property.2.2 G.property.2.1 H.val H.property.2.2 H.property.2.1
      (congrArg Prod.fst he) (congrArg Prod.snd he)
  have h := Nat.card_le_card_of_injective code hinj
  simpa only [Nat.card_prod,Nat.card_perm,Nat.card_fin,Nat.mul_comm] using h

end SymmetricSubgroupAsymptotics.CFSGOddNilpotentBoundedWordEncoding
