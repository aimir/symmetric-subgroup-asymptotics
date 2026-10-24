import SymmetricSubgroupAsymptotics.OddPrimePowerAffineBlockCoordinates
import SymmetricSubgroupAsymptotics.InversionPairKernelCoordinates
import SymmetricSubgroupAsymptotics.CentralBinaryCompressedKernelGenerators

/-! The actual affine-block linear quotient acts on inverse pairs of its
regular translation group. The further compression has a central binary
local kernel, including the possibility that this local kernel is trivial.
The original correlations survive both quotient embeddings. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.OddPrimePowerAffineBlockPairCompression
open OddPrimePowerAffineBlockCoordinates PermutationalWreathProduct

variable {G Ω X : Type} [Group G] [Finite G] [Finite Ω] [Finite X]
    [MulAction G Ω] [MulAction G X] [MulAction.IsPretransitive G X]
    [FaithfulSMul G Ω]
    (b : Ω → X) (hb : ∀ (g : G) (ω : Ω), b (g • ω) = g • b ω)
    (x₀ : X) [Nontrivial (originalBlockFibre b x₀)]
    (P : PrimitiveAffineProfile (Component b hb x₀) (originalBlockFibre b x₀))
    (hprimitive : MulAction.IsPreprimitive (Component b hb x₀) (originalBlockFibre b x₀))
    (C : P.ElementaryChart hprimitive) (origin : originalBlockFibre b x₀)

abbrev LinearQuotient := G ⧸ translationKernel b hb x₀ P origin

def linearWreath : LinearQuotient b hb x₀ P origin →*
    PermutationalWreathProduct (Complement b hb x₀ P origin) (Top (G:=G) (X:=X)) X :=
  Compression.quotientEmbedding (wreath b hb x₀) (localProjection b hb x₀ P origin)

omit [Finite G] [Finite Ω] [Finite X] [Nontrivial (originalBlockFibre b x₀)] in
theorem linearWreath_injective : Function.Injective (linearWreath b hb x₀ P origin) :=
  Compression.quotientEmbedding_injective (wreath b hb x₀) (localProjection b hb x₀ P origin)

def complementAut : Complement b hb x₀ P origin →* MulAut (Multiplicative C.V) :=
  (MulAut.congr C.equiv).toMonoidHom.comp (P.complementAction origin)

omit [Finite G] [Finite X] [MulAction.IsPretransitive G X] [FaithfulSMul G Ω] in
theorem complementAut_injective :
    Function.Injective (complementAut b hb x₀ P hprimitive C origin) :=
  (MulAut.congr C.equiv).injective.comp (P.complementAction_injective origin)

abbrev Pairs := AbelianAutomorphismInversionPairs.PairCarrier (Multiplicative C.V)
abbrev pairProjection := AbelianAutomorphismInversionPairs.pairAction
  (complementAut b hb x₀ P hprimitive C origin)
abbrev pairKernel : Subgroup (LinearQuotient b hb x₀ P origin) :=
  Compression.kernel (linearWreath b hb x₀ P origin)
    (pairProjection b hb x₀ P hprimitive C origin)

/-- The original action on the blocks descends through the actual
translation kernel. This is the action used for binary normal generation. -/
abbrev blockAction : MulAction (LinearQuotient b hb x₀ P origin) X :=
  MulAction.compHom X (rightHom.comp (linearWreath b hb x₀ P origin))

omit [Finite G] [Finite Ω] [Finite X] [Nontrivial (originalBlockFibre b x₀)] in
theorem block_transitive :
    letI := blockAction b hb x₀ P origin
    MulAction.IsPretransitive (LinearQuotient b hb x₀ P origin) X := by
  letI := blockAction b hb x₀ P origin
  constructor
  intro x y
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G x y
  refine ⟨QuotientGroup.mk' (translationKernel b hb x₀ P origin) g,?_⟩
  change (wreath b hb x₀ g).right • x = y
  exact hg

def quotientAction :
    LinearQuotient b hb x₀ P origin ⧸ pairKernel b hb x₀ P hprimitive C origin →*
      Equiv.Perm (Pairs b hb x₀ P hprimitive C × X) :=
  (PermutationalWreathProduct.toPerm
    (D:=Equiv.Perm (Pairs b hb x₀ P hprimitive C))
    (Q:=Top (G:=G) (X:=X)) (I:=X) (Lambda:=Pairs b hb x₀ P hprimitive C)).comp
      (Compression.quotientEmbedding (linearWreath b hb x₀ P origin)
        (pairProjection b hb x₀ P hprimitive C origin))

omit [Finite G] [Finite X] in
theorem quotientAction_injective [Nonempty X] [Nonempty (Pairs b hb x₀ P hprimitive C)] :
    Function.Injective (quotientAction b hb x₀ P hprimitive C origin) :=
  (PermutationalWreathProduct.toPerm_injective
    (D:=Equiv.Perm (Pairs b hb x₀ P hprimitive C))
    (Q:=Top (G:=G) (X:=X)) (I:=X) (Lambda:=Pairs b hb x₀ P hprimitive C)).comp
      (Compression.quotientEmbedding_injective (linearWreath b hb x₀ P origin)
        (pairProjection b hb x₀ P hprimitive C origin))

theorem pairKernel_isMulCommutative :
    IsMulCommutative (pairKernel b hb x₀ P hprimitive C origin) where
  is_comm.comm u v := by
    apply Compression.kernelCoordinate_joint_injective
      (linearWreath b hb x₀ P origin) (pairProjection b hb x₀ P hprimitive C origin)
      (linearWreath_injective b hb x₀ P origin)
    funext i
    apply InversionPairKernelCoordinates.kernelSign_injective
      (complementAut b hb x₀ P hprimitive C origin)
      (complementAut_injective b hb x₀ P hprimitive C origin)
    simp only [map_mul]
    exact mul_comm _ _

/-- The whole actual sign kernel needs at most half the number of original
blocks. No assumption that global inversion belongs to the component is made. -/
theorem normalGen_pairKernel_le_half [Nontrivial X] :
    MarkedC4.normalGen (pairKernel b hb x₀ P hprimitive C origin) ≤ Nat.card X / 2 := by
  letI : Fintype X := Fintype.ofFinite X
  letI := blockAction b hb x₀ P origin
  letI : MulAction.IsPretransitive (LinearQuotient b hb x₀ P origin) X :=
    block_transitive b hb x₀ P origin
  let rho := linearWreath b hb x₀ P origin
  let phi := pairProjection b hb x₀ P hprimitive C origin
  let psi := complementAut b hb x₀ P hprimitive C origin
  have hpsi := complementAut_injective b hb x₀ P hprimitive C origin
  by_cases hbot : phi.ker = ⊥
  · letI : Subsingleton phi.ker := by rw [hbot]; infer_instance
    have hE : pairKernel b hb x₀ P hprimitive C origin = ⊥ := by
      apply bot_unique
      intro g hg
      have he : (⟨g,hg⟩ : pairKernel b hb x₀ P hprimitive C origin) = 1 := by
        apply Compression.kernelCoordinate_joint_injective rho phi
          (linearWreath_injective b hb x₀ P origin)
        funext i
        exact Subsingleton.elim _ _
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val he)
    rw [hE,MarkedC4.normalGen_bot]
    exact Nat.zero_le _
  · letI : Nontrivial phi.ker := phi.ker.nontrivial_iff_ne_bot.mpr hbot
    have hcard : Nat.card phi.ker = 2 := by
      have hlo : 1 < Nat.card phi.ker := Finite.one_lt_card
      have hhi := AbelianAutomorphismInversionPairs.kernel_card_le_two psi hpsi
      change Nat.card phi.ker ≤ 2 at hhi
      omega
    let sign := InversionPairKernelCoordinates.kernelSign psi
    have hsign : Function.Injective sign :=
      InversionPairKernelCoordinates.kernelSign_injective psi hpsi
    have htwo : Nat.card (Multiplicative (ZMod 2)) = 2 := by
      rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 2) ≃ ZMod 2),Nat.card_zmod]
    have hbij : Function.Bijective sign :=
      (Nat.bijective_iff_injective_and_card sign).mpr ⟨hsign,hcard.trans htwo.symm⟩
    let e : Multiplicative (ZMod 2) ≃* phi.ker := (MulEquiv.ofBijective sign hbij).symm
    exact CentralBinaryCompressedKernelGenerators.normalGen_le_half rho phi e
      (linearWreath_injective b hb x₀ P origin)
      (InversionPairKernelCoordinates.kernel_conjugation psi hpsi) (fun _ _ => rfl)

end SymmetricSubgroupAsymptotics.OddPrimePowerAffineBlockPairCompression
