import SymmetricSubgroupAsymptotics.ActualFullWreathPreimage
import SymmetricSubgroupAsymptotics.ActualFullWreathCompressionState
import SymmetricSubgroupAsymptotics.ActualWreathElementaryFullImageCount
import SymmetricSubgroupAsymptotics.FullImageSameKernel
import SymmetricSubgroupAsymptotics.FullComponentRegularLocalWeakRank

/-! A complete fixed-local-image abelian fibre of the entire actual wreath
family. The original preimage, conjugation module, induced embedding and
compressed quotient are all constructed; no independent module or lift
capacity is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ActualFullWreathElementaryFibreCount
open PermutationalWreathProduct ActualFullWreathFamily ActualFullWreathPreimage

variable {R R' Q I : Type} [Group R] [Finite R] [Group R'] [Finite R']
    [Group Q] [Finite Q] [Fintype I] [Nonempty I] [MulAction Q I]
    [FaithfulSMul Q I] [MulAction.IsPretransitive Q I]
    (phi : R →* R') (hphi : Function.Surjective phi) (H : Family R' Q I)

local instance subgroupFinite {G : Type} [Group G] [Finite G] : Finite (Subgroup G) :=
  Finite.of_injective (fun K : Subgroup G => (K : Set G)) SetLike.coe_injective

local instance wreathFinite : Finite (PermutationalWreathProduct R Q I) :=
  Finite.of_injective (fun w : PermutationalWreathProduct R Q I => (w.left,w.right))
    (by
      intro a b h
      apply PermutationalWreathProduct.ext
      · exact congrArg Prod.fst h
      · exact congrArg Prod.snd h)

abbrev preimageState : ActualWreathCompressionState Q I :=
  ActualFullWreathCompressionState.state (preimage phi hphi H)

abbrev layerKernel : Subgroup (preimageState phi hphi H).A :=
  Compression.kernel (preimageState phi hphi H).rho phi

instance layerKernel_normal : (layerKernel phi hphi H).Normal := by
  change (Compression.kernel (preimageState phi hphi H).rho phi).Normal
  infer_instance

omit [Finite R'] in
theorem projection_kernel : (projection phi hphi H).ker=layerKernel phi hphi H := by
  ext w
  change projection phi hphi H w=1 ↔ mapBase phi w.val=1
  constructor
  · exact congrArg Subtype.val
  · intro hw
    apply Subtype.ext
    change mapBase phi w.val=1
    exact hw

theorem card_fibre_le_fullImage :
    Nat.card (Fibre phi hphi H)≤
      Nat.card (FiniteAbelianExtensionWholeLayerCount.FullImage
        (QuotientGroup.mk' (layerKernel phi hphi H))) := by
  have hf := Nat.card_le_card_of_injective (fibreCode phi hphi H)
    (fibreCode_injective phi hphi H)
  let q : (preimageState phi hphi H).A →*
      ((preimageState phi hphi H).A ⧸
        Compression.kernel (preimageState phi hphi H).rho phi) :=
    QuotientGroup.mk' (Compression.kernel (preimageState phi hphi H).rho phi)
  have hq := FullImageSameKernel.card_le (E := (preimageState phi hphi H).A)
    (projection phi hphi H) q
    (QuotientGroup.mk'_surjective (Compression.kernel (preimageState phi hphi H).rho phi))
    ((projection_kernel phi hphi H).trans
      (QuotientGroup.ker_mk' (Compression.kernel (preimageState phi hphi H).rho phi)).symm)
  exact hf.trans hq

variable (C : ElementaryMinimalNormalChart phi.ker)

abbrev capacity (i : I) : ℕ :=
  ActualWreathElementaryOrdinaryStep.layerCapacity (preimageState phi hphi H) phi C i

theorem card_fibre_le (i : I) :
    Nat.card (Fibre phi hphi H)≤
      (Nat.card phi.ker)^(Nat.card I *
        (capacity phi hphi H C i+
          MarkedC4.genRank ((preimageState phi hphi H).A ⧸ layerKernel phi hphi H))) := by
  let S := preimageState phi hphi H
  let A := (ActualWreathAffineCapacity.E S phi C).quotientRepresentation
  have hcount := ActualWreathElementaryFullImageCount.card_fullImage_le_capacity_add_rank
    S phi C i
  have hA : Nat.card A≤(Nat.card phi.ker)^Nat.card I := by
    have hinj := Compression.kernelCoordinate_joint_injective S.rho phi S.rho_injective
    have hk := Nat.card_le_card_of_injective
      (fun x j => Compression.kernelCoordinate S.rho phi j x) hinj
    have he : Nat.card A=Nat.card (Compression.kernel S.rho phi) := by
      calc
        Nat.card A=Nat.card (Multiplicative A) := Nat.card_congr Multiplicative.ofAdd
        _=Nat.card (Compression.kernel S.rho phi) :=
          Nat.card_congr (ActualWreathAffineCapacity.E S phi C).equiv.symm.toEquiv
    simpa only [he,Nat.card_fun] using hk
  have hp := Nat.pow_le_pow_left hA
    (capacity phi hphi H C i+MarkedC4.genRank (S.A ⧸ layerKernel phi hphi H))
  exact (card_fibre_le_fullImage phi hphi H).trans (hcount.trans
    (by simpa only [pow_mul] using hp))

omit [Finite R'] in
theorem capacity_le_root_log (i : I) (hI : 2≤Fintype.card I) :
    (capacity phi hphi H C i : ℝ)≤
      (Module.finrank (ZMod C.p) C.V : ℝ)*Fintype.card I /
        Real.sqrt (Real.logb 2 (Fintype.card I : ℝ)) :=
  ActualWreathElementaryFullImageCount.capacity_le_root_log
    (preimageState phi hphi H) phi C i hI

theorem quotient_rank_le_of_uniform
    (c : ℝ)
    (hbudget : ∀ n : ℕ,2≤n → ∀ J : Subgroup (Equiv.Perm (Fin n)),
      MulAction.IsPretransitive J (Fin n) →
        (MarkedC4.genRank J : ℝ)≤c*WeakTransitiveDegreeInduction.rate n)
    (hI : 2≤Nat.card I) :
    (MarkedC4.genRank ((preimageState phi hphi H).A ⧸ layerKernel phi hphi H) : ℝ)≤
      c*WeakTransitiveDegreeInduction.rate (Nat.card R'*Nat.card I) := by
  let T := (preimageState phi hphi H).quotient R' phi hphi
  exact FullComponentRegularLocalWeakRank.rank_le_of_uniform c hbudget
    T.rho T.rho_injective T.top_surjective T.fullComponent hI

end SymmetricSubgroupAsymptotics.ActualFullWreathElementaryFibreCount
