import SymmetricSubgroupAsymptotics.PrimitiveAffineFourNativeLinearKernel
import SymmetricSubgroupAsymptotics.WreathCompressionImageCoordinates
import SymmetricSubgroupAsymptotics.FourPointBlockZeroOddOrdinaryInduction

/-! The zero actual odd kernel costs no independent linear base positions
for a primitive four-point component. Its literal native local linear image
is the SAME profile complement, which has no normal binary subgroup. Full
component normality then makes the entire linear block kernel vanish.
No published generator theorem or quantitative tuple choice is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
attribute [local instance] Fintype.ofFinite
namespace SymmetricSubgroupAsymptotics.FourPointBlockPrimitiveZeroOddImage
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathIrreducible
open PermutationalWreathProduct

variable {G Ω X : Type} [Group G] [Finite G] [Finite Ω] [Finite X]
    [MulAction G Ω] [MulAction G X] [MulAction.IsPretransitive G X]
    [FaithfulSMul G Ω]
    (b : Ω → X) (hb : ∀ (g : G) (ω : Ω), b (g • ω) = g • b ω)
    (x₀ : X) (hfour : Nat.card (originalBlockFibre b x₀) = 4)

def localLinear : FourPointBlockAffineCoordinates.Component b hb x₀ →* Linear :=
  PrimitiveAffineFourNativeLinearKernel.linearHom (G := FourPointBlockAffineCoordinates.Component b hb x₀) (FourPointBlockAffineCoordinates.fibreChart b x₀ hfour)

omit [Finite G] [Finite X] in
theorem linearMap_eq_compression : FourPointBlockAffineCoordinates.linearMap b hb x₀ hfour =
    Compression.map (ActualBlockWreathEmbedding.embedding b hb x₀)
      (localLinear b hb x₀ hfour) := by
  apply MonoidHom.ext
  intro g
  let e := PermutationalWreathAffineCoordinates.equiv
    (R := FourPointBlockAffineCoordinates.Top (G := G) (X := X)) (I := X) BinaryPlaneWreathIrreducible.localAction
  let w := mapBase (Q := FourPointBlockAffineCoordinates.Top (G := G) (X := X)) (I := X)
    (FourPointBlockAffineCoordinates.localAffine b hb x₀ hfour) (ActualBlockWreathEmbedding.embedding b hb x₀ g)
  have he := e.apply_symm_apply w
  exact congrArg (fun z : PermutationalWreathProduct BinaryPlanePermutationAffineEquiv.Model
    (FourPointBlockAffineCoordinates.Top (G := G) (X := X)) X =>
      mapBase (SemidirectProduct.rightHom : BinaryPlanePermutationAffineEquiv.Model →* Linear) z) he

def nativeSign : Linear →* Multiplicative (ZMod 2) :=
  oddMarkerSign.comp BinaryPlaneWreathNormalGenerators.toThree

omit [Finite G] [Finite X] [MulAction.IsPretransitive G X] in
theorem sign_compression_kernel_eq_oddKernel
    (C : Subgroup (FourPointBlockAffineCoordinates.LinearFrame (G := G) (X := X))) :
    Compression.kernel C.subtype nativeSign = BinaryPlaneWreathActualOddKernel.oddKernel C := by
  ext g
  constructor
  · intro hg
    have he : mapBase nativeSign g.val = 1 := hg
    change BinaryPlaneWreathActualOddKernel.signProjection C g = 1
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      apply Subtype.ext
      funext i
      have hi := congrArg (fun z : PermutationalWreathProduct (Multiplicative (ZMod 2))
        (FourPointBlockAffineCoordinates.Top (G := G) (X := X)) X => z.left i) he
      exact congrArg Multiplicative.toAdd hi
    · exact congrArg right he
  · intro hg
    have he : BinaryPlaneWreathActualOddKernel.signProjection C g = 1 := hg
    change mapBase nativeSign g.val = 1
    apply PermutationalWreathProduct.ext
    · funext i
      apply Multiplicative.toAdd.injective
      exact congrArg (fun z : BinaryPlaneWreathActualOddKernel.Sign
        (R := FourPointBlockAffineCoordinates.Top (G := G) (X := X)) (I := X) => z.left.toAdd.val i) he
    · exact congrArg SemidirectProduct.right he

variable [Nontrivial (originalBlockFibre b x₀)]
    (P : PrimitiveAffineProfile (FourPointBlockAffineCoordinates.Component b hb x₀) (originalBlockFibre b x₀))

omit [Finite G] [Finite X] [MulAction.IsPretransitive G X] [FaithfulSMul G Ω] in
theorem local_normal_binary_subgroup_eq_bot
    (hprimitive : MulAction.IsPreprimitive (FourPointBlockAffineCoordinates.Component b hb x₀) (originalBlockFibre b x₀))
    (C : P.ElementaryChart hprimitive) (hp : P.p = 2)
    (K : Subgroup (localLinear b hb x₀ hfour).range) [K.Normal]
    (hK : IsPGroup 2 K) : K = ⊥ := by
  exact @PrimitiveAffineFourNativeLinearKernel.normal_binary_subgroup_eq_bot
    _ _ _ _ _ _ _ _ P (FourPointBlockAffineCoordinates.fibreChart b x₀ hfour) hprimitive C hp
    ((FourPointBlockAffineCoordinates.fibreChart b x₀ hfour).symm 0) K
    (inferInstance : K.Normal) hK

theorem top_injective_of_oddKernel_eq_bot
    (hprimitive : MulAction.IsPreprimitive (FourPointBlockAffineCoordinates.Component b hb x₀) (originalBlockFibre b x₀))
    (C : P.ElementaryChart hprimitive) (hp : P.p = 2)
    (hzero : BinaryPlaneWreathActualOddKernel.oddKernel (FourPointBlockAffineCoordinates.linearImage b hb x₀ hfour) = ⊥) :
    Function.Injective ((rightHom : FourPointBlockAffineCoordinates.LinearFrame (G := G) (X := X) →*
      FourPointBlockAffineCoordinates.Top (G := G) (X := X)).comp (FourPointBlockAffineCoordinates.linearImage b hb x₀ hfour).subtype) := by
  let rho := ActualBlockWreathEmbedding.embedding b hb x₀
  let phi := localLinear b hb x₀ hfour
  have hcore : Compression.kernel (FourPointBlockAffineCoordinates.linearImage b hb x₀ hfour).subtype nativeSign = ⊥ :=
    (sign_compression_kernel_eq_oddKernel (G := G) (X := X)
      (FourPointBlockAffineCoordinates.linearImage b hb x₀ hfour)).trans hzero
  have hC : WreathCompressionImageCoordinates.image rho phi =
      FourPointBlockAffineCoordinates.linearImage b hb x₀ hfour :=
    congrArg (fun f : G →* FourPointBlockAffineCoordinates.LinearFrame (G := G) (X := X) => f.range)
      (linearMap_eq_compression b hb x₀ hfour).symm
  have hcore' : Compression.kernel (WreathCompressionImageCoordinates.image rho phi).subtype
      nativeSign = ⊥ :=
    Eq.mpr (congrArg (fun D : Subgroup (FourPointBlockAffineCoordinates.LinearFrame (G := G) (X := X)) =>
      Compression.kernel D.subtype nativeSign = ⊥) hC) hcore
  have hlocal : ∀ K : Subgroup phi.range, K.Normal → IsPGroup 2 K → K = ⊥ := by
    intro K hn hK
    letI : K.Normal := hn
    exact local_normal_binary_subgroup_eq_bot b hb x₀ hfour P hprimitive C hp K hK
  have hs : ∀ s : Multiplicative (ZMod 2), s ^ 2 = 1 := by
    intro s
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow,toAdd_one]
    exact ZModModule.char_nsmul_eq_zero 2 s.toAdd
  have hh := WreathCompressionImageCoordinates.top_injective_of_sign_core_eq_bot rho phi
    2 (ActualBlockWreathEmbedding.fullComponent b hb x₀) hlocal nativeSign hs hcore'
  exact Eq.mp (congrArg (fun D : Subgroup (FourPointBlockAffineCoordinates.LinearFrame (G := G) (X := X)) =>
    Function.Injective ((rightHom : FourPointBlockAffineCoordinates.LinearFrame (G := G) (X := X) →*
      FourPointBlockAffineCoordinates.Top (G := G) (X := X)).comp D.subtype)) hC) hh

end SymmetricSubgroupAsymptotics.FourPointBlockPrimitiveZeroOddImage
