import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourTraceyLocalImage
import SymmetricSubgroupAsymptotics.PrimeBinaryPlaneOrbitQuotient
import SymmetricSubgroupAsymptotics.InducedNormalCoreDerangementHalf

/-! The degree-four nonzero-core induced half bound follows from its
actual globally normal ternary core and cyclic derangement quotient.
No soluble-orbit induced-module theorem is used. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre) [Nontrivial block.Fibre]

theorem degreeFourTernaryPreimage_le_stabilizer (i : block.Points) :
    degreeFourTernaryPreimage block P≤MulAction.stabilizer (preE7NonPairAction w U) i := by
  intro b hb
  have hright : (ambientEmbedding block b).right=1 :=
    MonoidHom.mem_ker.mp (degreeFourTernaryCore_le_blockKernel block P hb)
  change ((ambientEmbedding block b).right : Equiv.Perm block.Points) i=i
  rw [hright]
  rfl

def degreeFourCoreLocalQuotient (i : block.Points) :
    (degreeFourTernaryPreimage block P).subgroupOf
        (MulAction.stabilizer (preE7NonPairAction w U) i) →*
      degreeFourTernaryCore block P where
  toFun b := ⟨QuotientGroup.mk' (E block P) (b.val : preE7NonPairAction w U),b.property⟩
  map_one' := by ext; exact map_one (QuotientGroup.mk' (E block P))
  map_mul' a b := by ext; exact map_mul (QuotientGroup.mk' (E block P)) _ _

theorem degreeFourCoreLocalQuotient_surjective (i : block.Points) :
    Function.Surjective (degreeFourCoreLocalQuotient block P i) := by
  intro d
  obtain ⟨b,hb⟩ := QuotientGroup.mk'_surjective (E block P) d.val
  have hbB : b∈degreeFourTernaryPreimage block P := by
    change QuotientGroup.mk' (E block P) b∈degreeFourTernaryCore block P
    rw [hb]
    exact d.property
  let bH : MulAction.stabilizer (preE7NonPairAction w U) i :=
    ⟨b,degreeFourTernaryPreimage_le_stabilizer block P i hbB⟩
  exact ⟨⟨bH,hbB⟩,Subtype.ext hb⟩

/-- The same original local coefficient representation as the old Tracey
application, with its actual normal ternary preimage as coefficient core. -/
theorem degreeFourCoreLocalDualOrbitCard_eq_one
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre=4) (hD : degreeFourTernaryCore block P≠⊥)
    (i : block.Points) :
    let S := initialState hTraceyPerm block
    let C := localTranslationChart block P
    let rho := ActualWreathAffineCapacity.localRepresentation S (localMap block P) C i
    Nat.card (Quotient (representationNonzeroOrbitRel
      (Representation.dual (rho.comp
        ((degreeFourTernaryPreimage block P).subgroupOf
          (MulAction.stabilizer (preE7NonPairAction w U) i)).subtype))))=1 := by
  let S := initialState hTraceyPerm block
  let C := localTranslationChart block P
  let rho := ActualWreathAffineCapacity.localRepresentation S (localMap block P) C i
  let K := (degreeFourLocalBinarySign block P).ker
  let sigma : Representation (ZMod C.p) K C.V :=
    (degreeFiveLocalLinearRepresentation block P).ρ.comp K.subtype
  let f : (degreeFourTernaryPreimage block P).subgroupOf
        (MulAction.stabilizer (preE7NonPairAction w U) i) →* K :=
    (degreeFourTernaryCoordinate block P i).comp (degreeFourCoreLocalQuotient block P i)
  have hf : Function.Surjective f :=
    (degreeFourTernaryCoordinate_surjective block P hr hD i).comp
      (degreeFourCoreLocalQuotient_surjective block P i)
  have hp : C.p=2 := by
    simpa only [C,localTranslationChart] using degreeFour_profilePrime_eq_two block P hr
  have hdim : Module.finrank (ZMod C.p) C.V=2 := by
    let C0 := chart block P
    letI : Finite C0.V := Finite.of_injective
      (fun v : C0.V => C0.equiv.symm (Multiplicative.ofAdd v)) C0.equiv.symm.injective
    have hdegree : 4=P.p^C0.d := by
      rw [←hr]
      simpa [PrimitiveAffineProfile.ElementaryChart.d] using
        P.degree_eq_prime_pow_finrank C0.equiv (origin block)
    have hd0 : C0.d=2 :=
      (prime_pow_positive_injective (d := C0.d) (e := 2)
        P.p_prime Nat.prime_two C0.d_pos (by norm_num)
        (hdegree.symm.trans (by norm_num))).2
    simpa only [C,C0,localTranslationChart,PrimitiveAffineProfile.ElementaryChart.d] using hd0
  have hfaith : Function.Injective sigma :=
    (degreeFiveLocalLinearRepresentation_injective block P).comp K.subtype_injective
  apply prime_binaryPlane_dualOrbitCard_eq_one hp sigma
    (rho.comp ((degreeFourTernaryPreimage block P).subgroupOf
      (MulAction.stabilizer (preE7NonPairAction w U) i)).subtype)
    f hf (degreeFourLocalBinarySign_ker_card block P hr) hdim hfaith
  apply MonoidHom.ext
  intro b
  apply LinearMap.ext
  intro v
  change C.quotientRepresentation.ρ
      (QuotientGroup.mk' (localMap block P).ker
        (ActualWreathAffineCapacity.stabilizerComponent S i b.val)) v=
    (degreeFiveLocalLinearRepresentation block P).ρ
      (localMap block P (ActualWreathAffineCapacity.stabilizerComponent S i b.val)) v
  exact (degreeFiveLocalLinearRepresentation_apply_localMap block P hTraceyPerm _ v).symm

/-- The exact half-block capacity previously obtained from hTraceySoluble,
now on the same actual local representation and original induced module. -/
theorem degreeFourCoreInduced_uniform_half
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre=4) (hs : 2≤Nat.card block.Points)
    (hD : degreeFourTernaryCore block P≠⊥) (i : block.Points) :
    UniformSubrepresentationGeneratorBound
      (Representation.ind (MulAction.stabilizer (preE7NonPairAction w U) i).subtype
        (ActualWreathAffineCapacity.localRepresentation (initialState hTraceyPerm block)
          (localMap block P) (localTranslationChart block P) i)) (Nat.card block.Points/2) := by
  let C := localTranslationChart block P
  letI : Finite C.V := Module.finite_of_finite (ZMod C.p)
  have hdim : 0<Module.finrank (ZMod C.p) C.V := by
    let C0 := chart block P
    simpa only [C,C0,localTranslationChart,PrimitiveAffineProfile.ElementaryChart.d] using C0.d_pos
  letI : Nontrivial C.V := Module.nontrivial_of_finrank_pos hdim
  let N := degreeFourTraceySubgroup block P hTraceyPerm hs
  let B := degreeFourTernaryPreimage block P
  let rho := ActualWreathAffineCapacity.localRepresentation (initialState hTraceyPerm block)
    (localMap block P) C i
  apply induced_normalCore_derangement_uniform_half i N B
    (degreeFourTernaryPreimage_le_stabilizer block P i) le_sup_left rho
    (degreeFourCoreLocalDualOrbitCard_eq_one block P hTraceyPerm hr hD i)
    (degreeFourTraceyDerangement block P hTraceyPerm hs)
  intro x hfix
  have hfix' : (degreeFourTopDerangement block hs) • x=x := by
    change ((initialState hTraceyPerm block).rho
      (degreeFourAmbientDerangement block hTraceyPerm hs)).right • x=x at hfix
    rw [degreeFourAmbientDerangement_top block hTraceyPerm hs] at hfix
    exact hfix
  have hm : x∈MulAction.fixedBy block.Points (degreeFourTopDerangement block hs) := hfix'
  rw [degreeFourTopDerangement_fixedBy block hs] at hm
  exact hm

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics
