import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalStabilizerParameters
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalProductTorusRoots
import SymmetricSubgroupAsymptotics.CFSGSemilinearRootCosetIndex
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawSimpleIndex

/-! The ACTUAL original inner product torus lands in the literal
simple-line kernel and realizes the full Cartan monomial image. Actual
parameter faithfulness and common-field recognition give its index bound. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalTorusStabilizer
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGGeckSerreRepresentation CFSGNormTwoCoordinateOriginalPositiveCenter
open CFSGNormTwoCoordinateOriginalOppositeAlignment CFSGNormTwoCoordinateOriginalSimpleRootAction
open CFSGNormTwoCoordinateOriginalNormalizerIntersection
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylLatticeLinear
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    (K : Type) [Field K] [Finite K] [Nontrivial (Fin r)]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

open CFSGSubgroupFamilyStabilizer CFSGSubgroupFamilyIndex CFSGExceptionalDiagramAutomorphisms

open CFSGNormTwoCoordinateOriginalSimpleStabilizer CFSGNormTwoCoordinateOriginalStabilizerParameters
open CFSGNormTwoCoordinateOriginalSimpleParameters CFSGNormTwoCoordinateOriginalProductTorus
open CFSGNormTwoCoordinateOriginalProductTorusRoots CFSGNormTwoCoordinateOriginalAllRootLines
open CFSGIntegerMatrixPowerHom CFSGSemilinearRootCosetIndex

def productTorusPairHom
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) :
    (Fin r → Kˣ) →* originalPairStabilizer A hd hs hp ho K i :=
  (MulAut.conj.comp (originalProductTorusHom A hd hs hp ho K i)).codRestrict
    (originalPairStabilizer A hd hs hp ho K i) (by
      intro t neg
      cases neg
      · exact original_product_torus_positive A hd hs hp ho K i t
      · exact original_product_torus_negative A hd hs hp ho K i t)

 def productTorusSimpleHom
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) :
    (Fin r → Kˣ) →* originalSimpleStabilizer A hd hs hp ho K i :=
  (productTorusPairHom A hd hs hp ho K i).codRestrict
    (originalSimpleStabilizer A hd hs hp ho K i) (by
      intro t j
      change (originalSimpleRootGroup A hd hs hp ho K i j).map
        (MulAut.conj (originalProductTorusHom A hd hs hp ho K i t)).toMonoidHom =
          originalSimpleRootGroup A hd hs hp ho K i j
      rw [originalSimpleRootGroup_eq_fullRootLine A hd hs hp ho K i j]
      exact original_product_torus_root_line A hd hs hp ho K i t (s₀ j))

 theorem product_torus_lift_action
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r)
    (t : Fin r → Kˣ) (j : Fin r) (a : K) :
    simpleStabilizerAction A hd hs hp ho K i (productTorusSimpleHom A hd hs hp ho K i t)
      (simpleParameterHom A hd hs hp ho K i j (Multiplicative.ofAdd a)) =
    simpleParameterHom A hd hs hp ho K i j
      (Multiplicative.ofAdd ((powerHom (G := Kˣ) A t j : K) * a)) := by
  change originalProductTorusHom A hd hs hp ho K i t *
    simpleParameterHom A hd hs hp ho K i j (Multiplicative.ofAdd a) *
      (originalProductTorusHom A hd hs hp ho K i t)⁻¹ = _
  have he := original_product_torus_simple_action A hd hs hp ho K i t j a
  rw [mul_comm a (powerHom (G := Kˣ) A t j : K)] at he
  exact he

 theorem product_torus_lift_inner
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) (t : Fin r → Kˣ) :
    simpleStabilizerAction A hd hs hp ho K i (productTorusSimpleHom A hd hs hp ho K i t) ∈
      PrimitiveSocleRawStructure.Inner (Projective (cartan b₀ s₀) K) :=
  ⟨originalProductTorusHom A hd hs hp ho K i t, rfl⟩

theorem simple_stabilizer_torus_index_le
    (ε : Fin r→ℤ) (hε : ∀j,ε j*ε j=1) (hA : ∀i j,ε i*|A i j|=A j i*ε j)
    (hidentity : ∀w : List (Fin r),wordUnit A hs hp b₀ s₀ K w∈
      Subgroup.normalizer (rootGroup A hs hp b₀ s₀ K false : Set _)→wordLinear A hs hp b₀ s₀ w=1)
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) (θ : Roots A)
    (hθ : ∀j,0≤θ.val j)
    (hdom : ∀j,0 ≤ integerPairing A θ.val (Pi.single j (1:ℤ) : Fin r→ℤ))

    (j₀ k₀ : Fin r) (hjk : A j₀ k₀ = -1)
    (hconn : ∀ j, Relation.ReflTransGen (fun a b => A a b ≠ 0) j₀ j)
    (hneighbors : ∀ j, ∃ k, A j k = -1) :
    (productTorusSimpleHom A hd hs hp ho K i).range.index ≤
      (powerHom (G := Kˣ) A).range.index * Nat.card (K ≃+* K) := by
  exact scalar_lift_index_le
    (fun j a => simpleParameterHom A hd hs hp ho K i j (Multiplicative.ofAdd a))
    (simpleStabilizerAction A hd hs hp ho K i)
    (simple_stabilizer_parameter_faithful A hd hs hp ho K
      ε hε hA hidentity p i θ hθ hdom hneighbors)
    (simple_stabilizer_semilinear A hd hs hp ho K p i j₀ k₀ hjk hconn)
    (productTorusSimpleHom A hd hs hp ho K i) (powerHom (G := Kˣ) A)
    (product_torus_lift_action A hd hs hp ho K i)

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalTorusStabilizer
