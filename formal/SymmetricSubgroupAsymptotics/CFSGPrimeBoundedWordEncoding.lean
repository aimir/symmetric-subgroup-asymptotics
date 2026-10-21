import SymmetricSubgroupAsymptotics.MarkedC4BinaryWordOriginalRecovery
import SymmetricSubgroupAsymptotics.MarkedC4ActualWordMenuPartition

/-! A bounded prime-group action is encoded by its ACTUAL transitive
orbit images, their exact subdirect source and one original-label permutation.
The finite word shape and original action recovery are reused unchanged.
No action catalogue or subgroup-count estimate enters this construction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGPrimeBoundedWordEncoding
open MarkedC4 FiniteOrbitWordShapes FiniteBinaryWordTargets

abbrev Skeleton (p C b : ℕ) := {q : Σ S : Shape C b,LocalGroups S //
  (∀ i,IsPGroup p (q.2 i)) ∧
    ∀ i (x y : Fin (q.1.degrees i).val),∃ g : q.2 i,g.val x=y}

instance skeletonFinite (p C b : ℕ) : Finite (Skeleton p C b) := by
  unfold Skeleton
  infer_instance

abbrev Factors {p C b : ℕ} (q : Skeleton p C b) := fun i => ↥(q.val.2 i)
abbrev Target (p C b : ℕ) := Σ q : Skeleton p C b,ActualWordMenuPartition.Family (Factors q)

instance targetFinite (p C b : ℕ) : Finite (Target p C b) := by
  unfold Target
  infer_instance

variable {p C b : ℕ} [Fact p.Prime]
    (G : Subgroup (PermutationGroup b))
    (hcut : OrbitCutoffFamilies.OrbitCutoff C G) (hG : IsPGroup p G)

def actualSkeleton : Skeleton p C b :=
  ⟨⟨actualShape G hcut,actualLetters G hcut⟩,
    fun i => hG.of_surjective (ActualBinaryOrbitWord.projection G ((number G).symm i))
      (ActualBinaryOrbitWord.projection_surjective G ((number G).symm i)),
    fun i => ActualBinaryOrbitWord.letter_transitive G ((number G).symm i)⟩

/-- The target retains exactly the original correlated subdirect image. -/
def actualTarget : Target p C b := by
  let e : G ≃* (actualMap G hcut).range := MonoidHom.ofInjective (actualMap_injective G hcut)
  letI : Group.IsNilpotent G := hG.isNilpotent
  refine ⟨actualSkeleton G hcut hG,⟨(actualMap G hcut).range,?_,?_⟩⟩
  · intro i x
    obtain ⟨g,hg⟩ := ActualBinaryOrbitWord.projection_surjective G ((number G).symm i) x
    exact ⟨(actualMap G hcut).rangeRestrict g,hg⟩
  · exact Group.nilpotent_of_mulEquiv e

def representation (T : Target p C b) : T.2.val →* PermutationGroup b :=
  (canonicalPoints T.1.val.1).permCongrHom.toMonoidHom.comp
    ((BinaryWordOriginalRecovery.sigmaAction T.1.val.2).comp T.2.val.subtype)

/-- Original point labels intertwine the SAME original action. -/
theorem conjugate_eq (g : G) :
    (labelCode G hcut).permCongrHom g.val=
      representation (actualTarget G hcut hG) ((actualMap G hcut).rangeRestrict g) := by
  have happly (y : Fin b) :
      representation (actualTarget G hcut hG) ((actualMap G hcut).rangeRestrict g) y=
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
      (representation (actualTarget G hcut hG)).range := by
  apply le_antisymm
  · rintro z ⟨g,hg,rfl⟩
    exact ⟨(actualMap G hcut).rangeRestrict ⟨g,hg⟩,(conjugate_eq G hcut hG ⟨g,hg⟩).symm⟩
  · rintro z ⟨w,rfl⟩
    have hw : ∃ g : G,actualMap G hcut g=w.val := w.property
    obtain ⟨g,hg⟩ := hw
    have he : (actualMap G hcut).rangeRestrict g=w := Subtype.ext hg
    rw [←he]
    exact ⟨g.val,g.property,conjugate_eq G hcut hG g⟩

theorem source_eq (H : Subgroup (PermutationGroup b))
    (hHcut : OrbitCutoffFamilies.OrbitCutoff C H) (hH : IsPGroup p H)
    (ht : actualTarget G hcut hG=actualTarget H hHcut hH)
    (hl : labelCode G hcut=labelCode H hHcut) : G=H := by
  apply Subgroup.map_injective
    (f := (labelCode G hcut).permCongrHom.toMonoidHom)
    (labelCode G hcut).permCongrHom.injective
  calc
    G.map (labelCode G hcut).permCongrHom.toMonoidHom=
        (representation (actualTarget G hcut hG)).range := original_image G hcut hG
    _ = (representation (actualTarget H hHcut hH)).range :=
      congrArg (fun T : Target p C b => (representation T).range) ht
    _ = H.map (labelCode H hHcut).permCongrHom.toMonoidHom := (original_image H hHcut hH).symm
    _ = H.map (labelCode G hcut).permCongrHom.toMonoidHom := by rw [hl]

/-- The only label overhead is exactly b!, shared across the entire word. -/
theorem bounded_prime_card_le (p C b : ℕ) [Fact p.Prime] :
    Nat.card {G : Subgroup (PermutationGroup b) // IsPGroup p G ∧
      OrbitCutoffFamilies.OrbitCutoff C G}≤b.factorial*Nat.card (Target p C b) := by
  let A := {G : Subgroup (PermutationGroup b) // IsPGroup p G ∧
    OrbitCutoffFamilies.OrbitCutoff C G}
  let code : A → Target p C b × Equiv.Perm (Fin b) := fun G =>
    (actualTarget G.val G.property.2 G.property.1,labelCode G.val G.property.2)
  have hinj : Function.Injective code := by
    intro G H he
    apply Subtype.ext
    exact source_eq G.val G.property.2 G.property.1 H.val H.property.2 H.property.1
      (congrArg Prod.fst he) (congrArg Prod.snd he)
  have h := Nat.card_le_card_of_injective code hinj
  simpa only [Nat.card_prod,Nat.card_perm,Nat.card_fin,Nat.mul_comm] using h

end SymmetricSubgroupAsymptotics.CFSGPrimeBoundedWordEncoding
