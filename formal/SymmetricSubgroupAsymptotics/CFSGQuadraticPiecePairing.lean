import SymmetricSubgroupAsymptotics.CFSGQuadraticPolarPointFunctionals
import SymmetricSubgroupAsymptotics.CFSGQuadraticPolarFieldCoherence

/-! Actual representatives of two quadratic-singular pieces retain the
same polar zero locus as their source vectors. Their images are genuinely
Q-zero; no assertion is inferred just from a characteristic-two polar form. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticSubspacePoints
open CFSGSingularPlaneTriangle
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem SemilinearPiece.quadratic_zero (q : QuadraticForm K V) (f : Points q≃Points q)
    (W : Subspaces q) (σ : K≃+*K) (F : SemilinearPiece q f W σ) (x : W.val) :
    q (F.map x)=0 := by
  by_cases hx : x=0
  · rw [hx,F.map.map_zero,q.map_zero]
  have he := F.point x hx
  apply (f (ray q x.val (fun h=>hx (Subtype.ext h)) (W.property x.val x.property))).property.2
  rw [←he]
  exact Submodule.mem_span_singleton_self _

theorem piece_pairing_zero_iff (q : QuadraticForm K V) (f : Points q≃Points q)
    (horth : ∀P R,ZeroOn q.polarBilin (f P).val (f R).val ↔ ZeroOn q.polarBilin P.val R.val)
    (P Z : Subspaces q) (σ τ : K≃+*K)
    (F : SemilinearPiece q f P σ) (G : SemilinearPiece q f Z τ)
    (x : P.val) (y : Z.val) : q.polarBilin (F.map x) (G.map y)=0 ↔ q.polarBilin x.val y.val=0 := by
  by_cases hx : x=0
  · simp only [hx,F.map.map_zero,ZeroMemClass.coe_zero,map_zero,LinearMap.zero_apply]
  by_cases hy : y=0
  · simp only [hy,G.map.map_zero,ZeroMemClass.coe_zero,map_zero]
  have hx0 : x.val≠0 := fun h=>hx (Subtype.ext h)
  have hy0 : y.val≠0 := fun h=>hy (Subtype.ext h)
  let A := ray q x.val hx0 (P.property x.val x.property)
  let B := ray q y.val hy0 (Z.property y.val y.property)
  have hxF : F.map x≠0 := fun h=>hx (F.injective (h.trans F.map.map_zero.symm))
  have hyG : G.map y≠0 := fun h=>hy (G.injective (h.trans G.map.map_zero.symm))
  have hF : F.map x∈(f A).val := (F.point x hx) ▸ Submodule.mem_span_singleton_self _
  have hG : G.map y∈(f B).val := (G.point y hy) ▸ Submodule.mem_span_singleton_self _
  exact (zeroOn_iff_representatives q (f A) (f B) _ _ hF hG hxF hyG).symm.trans
    ((horth A B).trans (zeroOn_iff_representatives q A B _ _
      (Submodule.mem_span_singleton_self _) (Submodule.mem_span_singleton_self _) hx0 hy0))

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticSubspacePoints
