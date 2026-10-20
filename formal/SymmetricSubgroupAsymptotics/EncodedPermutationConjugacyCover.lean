import SymmetricSubgroupAsymptotics.EncodedPermutationRowChecks
import SymmetricSubgroupAsymptotics.FiniteConjugacyCover

/-!
# Original-row conjugacy covers checked on permutation points

This exposes the cover itself, rather than only a numerical class-count bound.
A future selected certificate must supply an actual retained-row conjugator
for each row and prove the displayed pointwise equations. There is no search
or witness generation here, and no class-separation or centralizer premise.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.EncodedCayleyCertificate

variable {ι : Type*} {d n : ℕ} {generators : ι → Equiv.Perm (Fin d)}
    (C : EncodedCayleyCertificate (permutationGeneratorEncoding generators) n)
    (hinj : Function.Injective C.rows)
    (prev : Fin n → ι → Fin n) (hprev : ∀ i j, C.next (prev i j) j = i)

/-- Evaluation of the faithful row homomorphism uses the retained code;
no parent-word multiplication is evaluated by the pointwise witness checks. -/
theorem rowHom_apply_code (i : Fin n) (x : Fin d) :
    (C.rowHom hinj prev hprev ⟨i⟩) x = finFunctionFinEquiv.symm (C.rows i) x := by
  have h := congrArg
    (fun z : Fin (d ^ d) => finFunctionFinEquiv.symm z x)
    (C.rowHom_permutationCode hinj prev hprev (⟨i⟩ : FiniteGroupRow n))
  simpa only [permutationCode, Equiv.symm_apply_apply] using h

/-- Every supplied conjugator is an original row. Pointwise equations in
its faithful permutation image prove conjugacy inside the original row group. -/
def rowConjugacyCoverOfPoints {c : ℕ}
    (representative : Fin c → Fin n) (label : Fin n → Fin c)
    (conjugator : Fin n → Fin n)
    (hconjugates : ∀ (i : Fin n) (x : Fin d),
      finFunctionFinEquiv.symm (C.rows (conjugator i))
          (finFunctionFinEquiv.symm (C.rows i) x) =
        finFunctionFinEquiv.symm (C.rows (representative (label i)))
          (finFunctionFinEquiv.symm (C.rows (conjugator i)) x)) :
    letI := C.rowGroup hinj prev hprev
    FiniteConjugacyCover (fun i : Fin n => (⟨i⟩ : FiniteGroupRow n)) c := by
  letI := C.rowGroup hinj prev hprev
  apply FiniteConjugacyCover.ofInjectiveMap
    (fun i : Fin n => (⟨i⟩ : FiniteGroupRow n))
    (fun x => ⟨x.index, rfl⟩)
    (C.rowHom hinj prev hprev) (C.rowHom_injective hinj prev hprev)
    representative label conjugator
  intro i
  apply Equiv.ext
  intro x
  change (C.rowHom hinj prev hprev ⟨conjugator i⟩)
      ((C.rowHom hinj prev hprev ⟨i⟩) x) =
    (C.rowHom hinj prev hprev ⟨representative (label i)⟩)
      ((C.rowHom hinj prev hprev ⟨conjugator i⟩) x)
  simp only [C.rowHom_apply_code hinj prev hprev]
  exact hconjugates i x

end SymmetricSubgroupAsymptotics.EncodedCayleyCertificate

end
