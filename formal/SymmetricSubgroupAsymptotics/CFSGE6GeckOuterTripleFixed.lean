import SymmetricSubgroupAsymptotics.CFSGE6GeckOuterTripleChart
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckMatrixTwist

/-! The diagram involution swaps exactly the first two parameters of
the genuine outer triple chart. Injectivity gives its complete fixed
locus, over every field. No exceptional Ree fixedness is inferred here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckOuterTripleFixed
open CFSGE6GeckOuterTripleChart CFSGTwistedE6GeckDiagramCovariance
open CFSGTwistedE6GeckMatrixTwist CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGNormTwoGeckOrthogonalWeyl
open CFSGSerreQuadraticMatrix
local notation "A" => CartanMatrix.E₆
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite

theorem triple_diagram (K : Type) [Field K]
    (a : (Multiplicative K×Multiplicative K)×Multiplicative K) :
    unitTwist K (RingEquiv.refl K) (rawTripleHom K a)=
      rawTripleHom K ((a.1.2,a.1.1),a.2) := by
  rw [rawTripleHom_val,rawTripleHom_val,map_mul,map_mul,
    unitTwist_root,unitTwist_root,unitTwist_root]
  change (canonicalRoot rawData K false 5 a.1.1.toAdd*
      canonicalRoot rawData K false 0 a.1.2.toAdd)*canonicalRoot rawData K false 1 a.2.toAdd=
    (canonicalRoot rawData K false 0 a.1.2.toAdd*
      canonicalRoot rawData K false 5 a.1.1.toAdd)*canonicalRoot rawData K false 1 a.2.toAdd
  rw [(orthogonal_signed_roots A hs hp E6Base E6Index K 5 0
    (by rw [E6_cartan];decide) false false a.1.1.toAdd a.1.2.toAdd).eq]

theorem triple_fixed_iff (K : Type) [Field K]
    (a : (Multiplicative K×Multiplicative K)×Multiplicative K) :
    unitTwist K (RingEquiv.refl K) (rawTripleHom K a)=rawTripleHom K a ↔a.1.1=a.1.2 := by
  rw [triple_diagram]
  constructor
  · intro he
    exact (congrArg (fun z : (Multiplicative K×Multiplicative K)×Multiplicative K=>z.1.1)
      (rawTripleHom_injective K he)).symm
  · intro he
    exact congrArg (rawTripleHom K) (Prod.ext (Prod.ext he.symm he) rfl)

end SymmetricSubgroupAsymptotics.CFSGE6GeckOuterTripleFixed
