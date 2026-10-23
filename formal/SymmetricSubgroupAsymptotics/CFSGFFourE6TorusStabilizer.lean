import SymmetricSubgroupAsymptotics.CFSGFFourE6StabilizerParameters
import SymmetricSubgroupAsymptotics.CFSGFFourE6ProductTorusAction
import SymmetricSubgroupAsymptotics.CFSGFFourE6ProductTorusNormalizer
import SymmetricSubgroupAsymptotics.CFSGSemilinearRootCosetIndex
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawSimpleIndex

/-! The actual original product tori realize all four scalar coordinates
inside the signed simple-label kernel. Their inner action has index at
most the actual field-automorphism count, since the relative Cartan map
is surjective on units over every field. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6TorusStabilizer
open CFSGFFourE6OriginalSimpleStabilizer CFSGFFourE6StabilizerParameters
open CFSGFFourE6ProductTorus CFSGFFourE6ProductTorusAction CFSGFFourE6ProductTorusNormalizer
open CFSGFFourE6OriginalSimpleParameters CFSGFFourRelativeScalarIndex
open CFSGSemilinearRootCosetIndex CFSGIntegerMatrixPowerHom CFSG.Models.Chevalley
variable (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective CartanMatrix.F₄ K)]

def productTorusPairHom : (Fin 4→Kˣ)→*pairStabilizer K p :=
  (MulAut.conj.comp (originalProductTorusHom K)).codRestrict (pairStabilizer K p) (by
    intro t neg
    cases neg
    · exact original_product_torus_positive K p t
    · exact original_product_torus_negative K t)

def productTorusSimpleHom : (Fin 4→Kˣ)→*simpleStabilizer K p :=
  (productTorusPairHom K p).codRestrict (simpleStabilizer K p) (by
    intro t z
    exact original_product_torus_chart K t z.1 z.2)

theorem product_torus_lift_action (t : Fin 4→Kˣ) (i : Fin 4) (a : K) :
    simpleStabilizerAction K p (productTorusSimpleHom K p t)
      (originalSimpleHom K false i (Multiplicative.ofAdd a))=
      originalSimpleHom K false i (Multiplicative.ofAdd
        ((powerHom (G := Kˣ) relativeCartan t i : K)*a)) := by
  change originalProductTorusHom K t*originalSimpleHom K false i (Multiplicative.ofAdd a)*
    (originalProductTorusHom K t)⁻¹=_
  exact original_product_torus_action K t false i a

theorem product_torus_inner (r : (productTorusSimpleHom K p).range) :
    (r.val.val.val : MulAut (Projective CartanMatrix.F₄ K))∈
      PrimitiveSocleRawStructure.Inner (Projective CartanMatrix.F₄ K) := by
  obtain ⟨t,ht⟩ := r.property
  refine ⟨originalProductTorusHom K t,?_⟩
  exact congrArg (fun f : simpleStabilizer K p =>
    (f.val.val : MulAut (Projective CartanMatrix.F₄ K))) ht

theorem product_torus_index_le :
    (productTorusSimpleHom K p).range.index≤Nat.card (RingAut K) := by
  have hindex := scalar_lift_index_le
    (fun i a => originalSimpleHom K false i (Multiplicative.ofAdd a))
    (simpleStabilizerAction K p) (parameters_faithful K p) (semilinear_parameters K p)
    (productTorusSimpleHom K p) (powerHom (G := Kˣ) relativeCartan)
    (product_torus_lift_action K p)
  simpa only [range_index_eq_one,one_mul] using hindex

end SymmetricSubgroupAsymptotics.CFSGFFourE6TorusStabilizer
