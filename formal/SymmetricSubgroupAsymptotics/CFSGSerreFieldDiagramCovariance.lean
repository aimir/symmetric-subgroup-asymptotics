import SymmetricSubgroupAsymptotics.CFSGSerreFieldDiagram

/-! The genuine original diagram--field ambient automorphism intertwines
the SAME original tensor-space action, on every vector and every group
element. No fixed or derived-group recognition is involved. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreFieldDiagramCovariance
open CFSG.Models.Chevalley
variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (K : Type) [Field K]
    (p : Equiv.Perm (Fin n)) (hA : ∀ i j, A (p i) (p j) = A i j) (σ : K ≃+* K)

theorem ambient_covariance (g : Ambient A K) (x : Space A K) :
    CFSGSerreFieldDiagram.ambientAutomorphism A K p hA σ g
      (CFSGSerreDiagram.spaceEquiv A K p hA (CFSGSerreField.semilinearEquiv A K σ x)) =
    CFSGSerreDiagram.spaceEquiv A K p hA (CFSGSerreField.semilinearEquiv A K σ (g x)) := by
  let D := CFSGSerreDiagram.spaceEquiv A K p hA
  let F := CFSGSerreField.semilinearEquiv A K σ
  change D (CFSGSerreField.ambientAutomorphism A K σ g (D.symm (D (F x)))) = D (F (g x))
  rw [D.symm_apply_apply, CFSGSerreField.ambientAutomorphism_apply]
  change D (F (g (F.symm (F x)))) = D (F (g x))
  rw [F.symm_apply_apply]

theorem model_covariance (g : Model A K) (x : Space A K) :
    (CFSGSerreFieldDiagram.modelAutomorphism A K p hA σ g).val
      (CFSGSerreDiagram.spaceEquiv A K p hA (CFSGSerreField.semilinearEquiv A K σ x)) =
    CFSGSerreDiagram.spaceEquiv A K p hA (CFSGSerreField.semilinearEquiv A K σ (g.val x)) :=
  ambient_covariance A K p hA σ g.val x

end SymmetricSubgroupAsymptotics.CFSGSerreFieldDiagramCovariance
