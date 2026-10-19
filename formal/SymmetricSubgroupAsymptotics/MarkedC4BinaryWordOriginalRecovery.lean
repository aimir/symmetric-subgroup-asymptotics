import SymmetricSubgroupAsymptotics.MarkedC4FiniteBinaryWordTargets

/-! Universal word actions and ORIGINAL subgroup recovery.
The target action is defined from the retained physical letters; its image
is proved equal to the conjugate of the original subgroup by the stored
original-label permutation. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.BinaryWordOriginalRecovery
open FiniteOrbitWordShapes FiniteBinaryWordTargets

variable {C b : ℕ}

def sigmaAction {S : Shape C b} (L : LocalGroups S) :
    Product L →* Equiv.Perm (Points S) where
  toFun w := Equiv.sigmaCongrRight (fun i => (w i).val)
  map_one' := by apply Equiv.ext; rintro ⟨i,j⟩; rfl
  map_mul' u v := by apply Equiv.ext; rintro ⟨i,j⟩; rfl

/-- A single canonical physical action is attached to every finite target. -/
def representation (T : Target C b) : T.image →* PermutationGroup b :=
  (canonicalPoints T.shape).permCongrHom.toMonoidHom.comp
    ((sigmaAction T.letters).comp T.image.subtype)

variable (G : Subgroup (PermutationGroup b))
  (hcut : OrbitCutoffFamilies.OrbitCutoff C G) (hbin : IsPGroup 2 G)

theorem inverse_labels (z : Points (actualShape G hcut)) :
    (labels G hcut).symm z =
      ((ActualBinaryOrbitWord.coordinate G ((number G).symm z.1)).symm z.2).val := by
  rfl

/-- The physical word action on each original point is proved, not supplied
as an abstract equivariant chart. -/
theorem labels_equivariant (g : G) (x : Fin b) :
    labels G hcut (g.val x)=
      sigmaAction (actualLetters G hcut) (actualMap G hcut g) (labels G hcut x) := by
  obtain ⟨z,rfl⟩ := (labels G hcut).symm.surjective x
  apply (labels G hcut).symm.injective
  rw [(labels G hcut).symm_apply_apply,(labels G hcut).apply_symm_apply]
  rw [inverse_labels,inverse_labels]
  change g.val (((ActualBinaryOrbitWord.coordinate G ((number G).symm z.1)).symm z.2).val)=
    ((ActualBinaryOrbitWord.coordinate G ((number G).symm z.1)).symm
      ((ActualBinaryOrbitWord.coordinate G ((number G).symm z.1))
        (g • (ActualBinaryOrbitWord.coordinate G ((number G).symm z.1)).symm z.2))).val
  rw [Equiv.symm_apply_apply]
  rfl

/-- The stored label permutation conjugates the ORIGINAL action to the
canonical target action. -/
theorem conjugate_eq (g : G) :
    (labelCode G hcut).permCongrHom g.val =
      representation (actualTarget G hcut hbin) (originalEquiv G hcut hbin g) := by
  apply Equiv.ext
  intro y
  obtain ⟨x,rfl⟩ := (labelCode G hcut).surjective y
  change labelCode G hcut (g.val ((labelCode G hcut).symm (labelCode G hcut x)))=
    canonicalPoints (actualShape G hcut)
      (sigmaAction (actualLetters G hcut) (actualMap G hcut g)
        ((canonicalPoints (actualShape G hcut)).symm
          (canonicalPoints (actualShape G hcut) (labels G hcut x))))
  rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply]
  exact congrArg (canonicalPoints (actualShape G hcut)) (labels_equivariant G hcut g x)

/-- The exact canonical image plus stored labels recovers the SAME original
literal subgroup of S_b, not only its abstract group isomorphism type. -/
theorem original_image :
    G.map (labelCode G hcut).permCongrHom.toMonoidHom =
      (representation (actualTarget G hcut hbin)).range := by
  apply le_antisymm
  · rintro z ⟨g,hg,rfl⟩
    exact ⟨originalEquiv G hcut hbin ⟨g,hg⟩,(conjugate_eq G hcut hbin ⟨g,hg⟩).symm⟩
  · rintro z ⟨w,rfl⟩
    obtain ⟨g,rfl⟩ := (originalEquiv G hcut hbin).surjective w
    exact ⟨g.val,g.property,conjugate_eq G hcut hbin g⟩

/-- Code equality is enough: no additional source recovery hypothesis is
needed for the later weighted finite-family encoding. -/
theorem source_eq
    (H : Subgroup (PermutationGroup b))
    (hHcut : OrbitCutoffFamilies.OrbitCutoff C H) (hHbin : IsPGroup 2 H)
    (ht : actualTarget G hcut hbin=actualTarget H hHcut hHbin)
    (hl : labelCode G hcut=labelCode H hHcut) : G=H := by
  apply Subgroup.map_injective
    (f := (labelCode G hcut).permCongrHom.toMonoidHom)
    (labelCode G hcut).permCongrHom.injective
  calc
    G.map (labelCode G hcut).permCongrHom.toMonoidHom =
        (representation (actualTarget G hcut hbin)).range := original_image G hcut hbin
    _ = (representation (actualTarget H hHcut hHbin)).range :=
      congrArg (fun U : Target C b => (representation U).range) ht
    _ = H.map (labelCode H hHcut).permCongrHom.toMonoidHom := (original_image H hHcut hHbin).symm
    _ = H.map (labelCode G hcut).permCongrHom.toMonoidHom := by rw [hl]

end SymmetricSubgroupAsymptotics.MarkedC4.BinaryWordOriginalRecovery
