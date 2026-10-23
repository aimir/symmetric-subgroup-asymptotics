import SymmetricSubgroupAsymptotics.CFSGExceptionalHeisenbergProduct
import SymmetricSubgroupAsymptotics.CFSGHeisenbergKernelRigidity
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveRootCardinality
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootHeightQuotient

/-! The ordered root-product homomorphism lands in the literal positive
group and is faithful there. Faithfulness follows from its actual central
root parameter and the proved nondegenerate commutator pairing. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGExceptionalHeisenbergPositive
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoCoordinateRootSubgroup CFSGExceptionalHeisenbergRootPilot
open CFSGExceptionalHeisenbergRootRelations CFSGExceptionalHeisenbergProduct
open CFSGFiniteCommutingParameterHom CFSGNormTwoCoordinatePositiveRootGenerators
open CFSGNormTwoCoordinateSelectedRootAdditive CFSGNormTwoCoordinatePositiveRootCardinality
open CFSGNormTwoCoordinateRootHeightQuotient CFSGHeisenbergCoordinateGroup
variable {r m:ℕ}(A:Matrix (Fin r) (Fin r) ℤ)(hd:∀i,A i i=2)
  (hs:A.transpose=A)(hp:(rationalMatrix A).PosDef)(ho:∀i j,i≠j→A i j≤0)
  [Fintype (Roots A)][DecidableEq (Roots A)]
  [(rootPairing A hs hp).IsReduced][(rootPairing A hs hp).IsIrreducible]
  (C:RootConfig A m)(K:Type)[Field K]

private theorem parameter_mem (f:Fin m→Multiplicative K→*
      (Matrix ((coordinateBase A hd hs hp ho).support⊕Roots A)
        ((coordinateBase A hd hs hp ho).support⊕Roots A) K)ˣ)
    (hc:Pairwise (fun i j=>∀a b,Commute (f i a) (f j b)))
    (hf:∀i a,f i a∈PositiveGroup A hd hs hp ho K)(v:Fin m→K) :
    parameterHom f hc (Multiplicative.ofAdd v)∈PositiveGroup A hd hs hp ho K := by
  change Finset.univ.noncommProd (fun i=>f i (Multiplicative.ofAdd (v i)))
    (fun i _ j _ hij=>hc hij (Multiplicative.ofAdd (v i)) (Multiplicative.ofAdd (v j)))∈_
  apply Subgroup.noncommProd_mem
  exact fun i _=>hf i (Multiplicative.ofAdd (v i))

theorem rawHom_mem_positive (g:Element K m) :
    rawHom A hd hs hp ho C K g∈PositiveGroup A hd hs hp ho K := by
  have hx:X A hd hs hp ho C K (Multiplicative.ofAdd g.a)∈PositiveGroup A hd hs hp ho K := by
    apply parameter_mem
    intro i a
    exact selected_positive_root_mem A hd hs hp ho K (C.xRoot i).val (C.positive_x i) a.toAdd
  have hy:Y A hd hs hp ho C K (Multiplicative.ofAdd g.b)∈PositiveGroup A hd hs hp ho K := by
    apply parameter_mem
    intro i b
    exact selected_positive_root_mem A hd hs hp ho K (C.yRoot i).val (C.positive_y i)
      (((pairSign A hd hs hp ho C i:ℤ):K)*(-b.toAdd))
  have hz:zHom A hd hs hp ho C K (Multiplicative.ofAdd g.c)∈PositiveGroup A hd hs hp ho K :=
    selected_positive_root_mem A hd hs hp ho K C.zRoot.val C.positive_z g.c
  exact (PositiveGroup A hd hs hp ho K).mul_mem ((PositiveGroup A hd hs hp ho K).mul_mem hx hy) hz

def positiveHom : Element K m→*PositiveGroup A hd hs hp ho K :=
  (rawHom A hd hs hp ho C K).codRestrict (PositiveGroup A hd hs hp ho K)
    (rawHom_mem_positive A hd hs hp ho C K)

theorem rawHom_injective : Function.Injective (rawHom A hd hs hp ho C K) := by
  apply CFSGHeisenbergKernelRigidity.injective_of_central
  intro a b he
  have he':zHom A hd hs hp ho C K a=zHom A hd hs hp ho C K b := by
    change rawHom A hd hs hp ho C K (central a)=rawHom A hd hs hp ho C K (central b) at he
    simpa only [rawHom_central] using he
  exact selected_positive_rootHom_injective A hd hs hp ho K C.zRoot.val C.positive_z he'

theorem positiveHom_injective : Function.Injective (positiveHom A hd hs hp ho C K) := by
  intro g h he
  exact rawHom_injective A hd hs hp ho C K (congrArg Subtype.val he)

end SymmetricSubgroupAsymptotics.CFSGExceptionalHeisenbergPositive
