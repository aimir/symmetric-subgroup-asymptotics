import SymmetricSubgroupAsymptotics.CFSGE6GeckProductTorusLeading

/-! Positive commutators with the actual E6 torus have the expected
leading coordinates. The calculation takes place in the same U subtype. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckProductTorusCommutatorLeading
open CFSGTwistedE6GeckDiagramCovariance CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGE6GeckProductTorus
open CFSGE6GeckProductTorusLeading CFSGNormTwoCoordinateLeadingFactor
open CFSGNormTwoCoordinateLeadingHom CFSGIntegerMatrixPowerHom
open CFSGNormTwoGeckPositivePGroup
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos
local notation "U" => rootGroup A hs hp E6Base E6Index

def torusConjugatePositive (K : Type) [Field K] (x : Fin 6→Kˣ) (u : U K false) :
    U K false :=
  ⟨rawProductTorus K x*u.val*(rawProductTorus K x)⁻¹,
    ((Subgroup.mem_normalizer_iff.mp (product_torus_normalizes_positive K x)) u.val).mp u.property⟩

theorem product_torus_commutator_positive (K : Type) [Field K] (x : Fin 6→Kˣ)
    (u : U K false) :
    rawProductTorus K x*u.val*(rawProductTorus K x)⁻¹*u.val⁻¹∈U K false :=
  (U K false).mul_mem (torusConjugatePositive K x u).property
    ((U K false).inv_mem u.property)

theorem product_torus_commutator_leading (K : Type) [Field K] (x : Fin 6→Kˣ)
    (u : U K false) (i : Fin 6) :
    leadingCoordinates A hd hs hp ho K
      (rawProductTorus K x*u.val*(rawProductTorus K x)⁻¹*u.val⁻¹) i=
      ((powerHom (G := Kˣ) A x i : K)-1)*leadingCoordinates A hd hs hp ho K u.val i := by
  let v := torusConjugatePositive K x u
  let L : U K false→*Multiplicative (Fin 6→K) := leadingHom A hd hs hp ho K
  have hL (w : U K false) :
      (L w).toAdd=leadingCoordinates A hd hs hp ho K w.val := rfl
  have he : L (v*u⁻¹)=L v*(L u)⁻¹ := by rw [map_mul,map_inv]
  have hc := congrArg (fun z : Multiplicative (Fin 6→K)=>z.toAdd) he
  dsimp only at hc
  simp only [_root_.toAdd_mul,_root_.toAdd_inv,hL] at hc
  have hi := congrArg (fun z : Fin 6→K=>z i) hc
  dsimp only [Pi.add_apply,Pi.neg_apply] at hi
  change leadingCoordinates A hd hs hp ho K
      (rawProductTorus K x*u.val*(rawProductTorus K x)⁻¹*u.val⁻¹) i=
    leadingCoordinates A hd hs hp ho K
      (rawProductTorus K x*u.val*(rawProductTorus K x)⁻¹) i+
    -leadingCoordinates A hd hs hp ho K u.val i at hi
  rw [hi,product_torus_leading_action]
  ring

end SymmetricSubgroupAsymptotics.CFSGE6GeckProductTorusCommutatorLeading
