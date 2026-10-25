import SymmetricSubgroupAsymptotics.FiniteHermitianNormOneBasisScaling
import SymmetricSubgroupAsymptotics.CFSGHermitianSpecialIsometryCardinality

/-! The full determinant image of an actual Hermitian isometry group.
The witnesses scale one orthonormal basis vector. Exact kernel/image
counting therefore supplies the norm-one factor in the correct direction. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FiniteHermitianSpecialDeterminantSaving
open Module CFSGTwistedAUnitaryParameters CFSGHermitianSimilitudeGroup
open CFSGProjectiveLinearPointAction
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

theorem determinant_eq_linear (sigma : K ≃+* K) (H : (Matrix I I K)ˣ)
    (e : isometries sigma H) :
    (isometryDeterminantHom sigma H e : K)=LinearMap.det e.val.toLinearMap := by
  change Matrix.det (isometryMatrixHom sigma H e : Matrix I I K)=_
  rw [←LinearMap.det_toLin']
  apply congrArg LinearMap.det
  apply LinearMap.ext
  intro x
  change linearEquiv (linearEquiv.symm e.val) x=e.val x
  rw [linearEquiv.apply_symm_apply]

theorem determinant_surjective (sigma : K ≃+* K) (H : (Matrix I I K)ˣ)
    {n : ℕ} (b : Basis (Fin n) K (I → K))
    (hb : ∀ i j, hermitianPair sigma H.val (b i) (b j)=if i=j then 1 else 0)
    (i₀ : Fin n) : Function.Surjective (normOneDeterminantHom sigma H) := by
  intro z
  have hz : sigma (z.val : K)*(z.val : K)=1 := by
    have hh := congrArg (fun a : Kˣ => (a : K)) z.property
    exact hh
  obtain ⟨e,hp,hd⟩ := FiniteHermitianNormOneBasisScaling.exists_isometry_determinant
    sigma H.val b hb i₀ z.val hz
  let u : isometries sigma H := ⟨e,hp⟩
  refine ⟨u,?_⟩
  apply Subtype.ext
  apply Units.ext
  change (isometryDeterminantHom sigma H u : K)=(z.val : K)
  rw [determinant_eq_linear]
  exact hd

theorem card_eq_special_mul_normOne [Finite K]
    (sigma : K ≃+* K) (H : (Matrix I I K)ˣ)
    {n : ℕ} (b : Basis (Fin n) K (I → K))
    (hb : ∀ i j, hermitianPair sigma H.val (b i) (b j)=if i=j then 1 else 0)
    (i₀ : Fin n) :
    Nat.card (isometries sigma H)=
      Nat.card (specialIsometries sigma H)*Nat.card (normOneUnits sigma) := by
  let f := normOneDeterminantHom sigma H
  have hk : f.ker=specialIsometries sigma H := MonoidHom.ker_codRestrict _ _ _
  have hr : f.range=⊤ := MonoidHom.range_eq_top.mpr
    (determinant_surjective sigma H b hb i₀)
  calc
    _ = Nat.card f.ker*Nat.card f.range := by
      rw [←f.ker.card_mul_index,Subgroup.index_ker]
    _ = _ := by
      rw [hk,hr,Nat.card_congr (Subgroup.topEquiv :
        (⊤ : Subgroup (normOneUnits sigma)) ≃* normOneUnits sigma).toEquiv]

end SymmetricSubgroupAsymptotics.FiniteHermitianSpecialDeterminantSaving
