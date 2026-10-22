import SymmetricSubgroupAsymptotics.CFSGPolarSubspaceProjectiveRestriction
import SymmetricSubgroupAsymptotics.CFSGProjectiveSemilinearDecomposition

/-! Semilinearity on each original singular subspace of dimension at
least three. Coordinates are actual linear equivalences; their projective
restriction is proved to be a collineation before the projective theorem
is invoked. This does not assert an extension to the entire polar space. -/
set_option autoImplicit false
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGPolarSubspacePoints
open CFSGSingularPlaneTriangle
variable {K V T U : Type*} [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup T] [Module K T] [AddCommGroup U] [Module K U]

def linearProjectiveEquiv (e : T≃ₗ[K]U) : ℙ K T≃ℙ K U where
  toFun := Projectivization.map e.toLinearMap e.injective
  invFun := Projectivization.map e.symm.toLinearMap e.symm.injective
  left_inv p := by
    induction p using Projectivization.ind with
    | h v hv =>
      change Projectivization.mk K (e.symm (e v)) _=Projectivization.mk K v hv
      simp only [LinearEquiv.symm_apply_apply]
  right_inv p := by
    induction p using Projectivization.ind with
    | h v hv =>
      change Projectivization.mk K (e (e.symm v)) _=Projectivization.mk K v hv
      simp only [LinearEquiv.apply_symm_apply]

theorem linearProjectiveEquiv_submodule (e : T≃ₗ[K]U) (p : ℙ K T) :
    (linearProjectiveEquiv e p).submodule=p.submodule.map e.toLinearMap := by
  induction p using Projectivization.ind with
  | h v hv =>
    change K ∙ (e v)=(K ∙ v).map e.toLinearMap
    rw [Submodule.map_span,Set.image_singleton]
    rfl

theorem linearProjectiveEquiv_line (e : T≃ₗ[K]U) (p q r : ℙ K T) :
    (linearProjectiveEquiv e p).submodule ≤
      (linearProjectiveEquiv e q).submodule⊔(linearProjectiveEquiv e r).submodule ↔
      p.submodule≤q.submodule⊔r.submodule := by
  rw [linearProjectiveEquiv_submodule,linearProjectiveEquiv_submodule,
    linearProjectiveEquiv_submodule,←Submodule.map_sup]
  exact Submodule.map_le_map_iff_of_injective e.injective _ _

variable (B : LinearMap.BilinForm K V) (f : Points B≃Points B) (l : Planes B≃Planes B)
    (hinc : ∀P L,(f P).val ≤ (l L).val ↔ P.val ≤ L.val)
    (horth : ∀P Q,ZeroOn B (f P).val (f Q).val ↔ ZeroOn B P.val Q.val)

def coordinateRestriction (W : Subspaces B) (d : ℕ)
    (e : W.val≃ₗ[K](Fin d→K))
    (e' : (imageSubspace B f l hinc horth W).val≃ₗ[K](Fin d→K)) :
    CFSGProjectiveFrameCoordinates.collineationGroup (F:=K) (n:=Fin d) :=
  ⟨(linearProjectiveEquiv e.symm).trans ((projectiveRestriction B f l hinc horth W).trans
    (linearProjectiveEquiv e')),by
    intro p q r
    change (linearProjectiveEquiv e' (projectiveRestriction B f l hinc horth W
      (linearProjectiveEquiv e.symm p))).submodule ≤ _ ↔ _
    exact (linearProjectiveEquiv_line e' _ _ _).trans
      ((projectiveRestriction_line B f l hinc horth W _ _ _).trans
        (linearProjectiveEquiv_line e.symm p q r))⟩

theorem exists_coordinate_semilinear [Finite K] (W : Subspaces B) (d : ℕ)
    (e : W.val≃ₗ[K](Fin (d+3)→K))
    (e' : (imageSubspace B f l hinc horth W).val≃ₗ[K](Fin (d+3)→K)) :
    ∃(a : (Fin (d+3)→K)≃ₗ[K](Fin (d+3)→K)) (s : K≃+*K),
      ∀p,(coordinateRestriction B f l hinc horth W (d+3) e e').val p=
        CFSGProjectiveFrameCoordinates.linearPointEquiv a
          (CFSGProjectiveFieldAction.pointEquiv s p) := by
  exact CFSGProjectiveSemilinearDecomposition.exists_decomposition
    (coordinateRestriction B f l hinc horth W (d+3) e e')
    ⟨0,by omega⟩ ⟨1,by omega⟩ ⟨2,by omega⟩
    (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])

end SymmetricSubgroupAsymptotics.CFSGPolarSubspacePoints
