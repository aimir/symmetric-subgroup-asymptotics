import SymmetricSubgroupAsymptotics.ActualWreathAffineCapacity
import SymmetricSubgroupAsymptotics.OriginalKernelLabelRegularEmbedding
import SymmetricSubgroupAsymptotics.NormalGeneratorTypeSharing

/-!
# Published Clifford restriction in the block-homogeneous form

This file isolates the one representation-theoretic input used by the
small imprimitive affine frames.  It is the strong modular Clifford
theorem: the restriction of a simple module to a normal subgroup is
semisimple, and its homogeneous components are permuted transitively by
the ambient group.  See Curtis--Reiner, *Methods of Representation Theory*,
vol. II, Theorem 11.1.  An independently accessible statement is Tracey,
*Minimal generation of transitive permutation groups*, 2017 thesis,
Theorem 2.3.1 (citing its reference [13], Theorem 49.7).

The form below is its standard block-homogeneous corollary.  An actual
faithful full-component subgroup of `D wr Q` is compressed by a local
elementary normal subgroup.  If the resulting exact local representation
is faithful and irreducible and every coordinate image of the literal
linear block kernel is nontrivial, then that kernel acts faithfully on
every nonzero ambient section of the actual correlated elementary kernel.
Equivalently, an ambient normal subgroup cannot acquire a linear-kernel
component without swallowing the whole elementary kernel.

No affine catalogue assertion is included: the ambient group, local map,
correlated kernel, quotient embedding, and coordinate images are all
literal arguments.  Applications must prove irreducibility, faithfulness,
and nontriviality of every displayed coordinate from their actual action.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace CliffordHomogeneousRestriction

variable {Q I : Type} [Group Q] [Fintype I] [Nonempty I]
  [MulAction Q I] [FaithfulSMul Q I]

variable (S : ActualWreathCompressionState Q I)
  {D' : Type} [Group D'] [Finite D']
  (phi : S.D →* D') (hphi : Function.Surjective phi)
  (C : ElementaryMinimalNormalChart phi.ker)

/-- The actual correlated elementary kernel of the compression. -/
abbrev elementaryKernel : Subgroup S.A :=
  ActualWreathAffineCapacity.K S phi

/-- The literal quotient after removing that elementary kernel. -/
abbrev quotientGroup := S.A ⧸ elementaryKernel S phi

/-- The exact linear block kernel after elementary compression. -/
abbrev linearBlockKernel : Subgroup (quotientGroup S phi) :=
  ((PermutationalWreathProduct.rightHom).comp
    (PermutationalWreathProduct.Compression.quotientEmbedding S.rho phi)).ker

/-- Its literal preimage in the original ambient group. -/
abbrev corePreimage : Subgroup S.A :=
  (linearBlockKernel S phi).comap
    (QuotientGroup.mk' (elementaryKernel S phi))

/-- One coordinate of the exact linear block kernel in the compressed
local quotient. -/
def linearCoordinate (i : I) :
    linearBlockKernel S phi →* D' where
  toFun x :=
    (PermutationalWreathProduct.Compression.quotientEmbedding S.rho phi
      x.1).left i
  map_one' := by simp
  map_mul' x y := by
    change
      (PermutationalWreathProduct.Compression.quotientEmbedding S.rho phi
        (x.1 * y.1)).left i =
      (PermutationalWreathProduct.Compression.quotientEmbedding S.rho phi
        x.1).left i *
      (PermutationalWreathProduct.Compression.quotientEmbedding S.rho phi
        y.1).left i
    rw [map_mul, PermutationalWreathProduct.mul_left]
    have hx :
        (PermutationalWreathProduct.Compression.quotientEmbedding
          S.rho phi x.1).right = 1 :=
      MonoidHom.mem_ker.mp x.2
    rw [hx]
    simp

/-- The quotient by the local kernel is the displayed compressed local
group, using only the supplied surjectivity of the literal local map. -/
noncomputable def localQuotientEquiv : (S.D ⧸ phi.ker) ≃* D' :=
  QuotientGroup.liftEquiv phi.ker hphi rfl

/-- The exact local elementary representation transported to the displayed
compressed local group. -/
noncomputable abbrev localRepresentation : Rep.{0, 0, 0} (ZMod C.p) D' :=
  Rep.of (C.quotientRepresentation.ρ.comp
    (localQuotientEquiv S phi hphi).symm.toMonoidHom)

/-- The exact representation on the elementary section left by an ambient
normal subgroup.  Its acting group is the literal quotient
`A / (E ⊔ N)`. -/
noncomputable abbrev sectionTopRepresentation
    (N : Subgroup S.A) [N.Normal] :
    Rep.{0, 0, 0} (ZMod (ActualWreathAffineCapacity.E S phi C).p)
      (S.A ⧸ ((ActualWreathAffineCapacity.pi S phi).ker ⊔ N)) :=
  (ActualWreathAffineCapacity.originalChart S phi C).sectionRepresentation
    (ActualWreathAffineCapacity.pi S phi)
    (ActualWreathAffineCapacity.E S phi C).quotientRepresentation N

/-- The linear block kernel mapped into the exact acting group of a retained
elementary section. -/
def linearKernelToSectionTop
    (N : Subgroup S.A) [N.Normal] :
    linearBlockKernel S phi →*
      S.A ⧸ ((ActualWreathAffineCapacity.pi S phi).ker ⊔ N) :=
  (OriginalKernelModuleChart.labelTop
      (ActualWreathAffineCapacity.pi S phi) N
      (QuotientGroup.mk'_surjective
        (ActualWreathAffineCapacity.K S phi))).comp
    (linearBlockKernel S phi).subtype

/-- Restrict an ambient invariant constituent of a retained elementary
section to the literal linear block kernel.  The constituent remains a
subrepresentation for the full retained top; only its acting group is
restricted here. -/
noncomputable def constituentLinearKernelRepresentation
    (N : Subgroup S.A) [N.Normal]
    (W : Subrepresentation.{0, 0, 0}
      (sectionTopRepresentation S phi C N).ρ) :
    Rep.{0, 0, 0} (ZMod (ActualWreathAffineCapacity.E S phi C).p)
      (linearBlockKernel S phi) :=
  Rep.of (W.toRepresentation.comp
    (linearKernelToSectionTop S phi N))

/-- The retained image of the actual correlated elementary kernel. -/
abbrev retainedElementaryImage
    (N : Subgroup S.A) [N.Normal] : Subgroup (S.A ⧸ N) :=
  (elementaryKernel S phi).map (QuotientGroup.mk' N)

/-- The retained image of the literal linear-core preimage. -/
abbrev retainedCoreImage
    (N : Subgroup S.A) [N.Normal] : Subgroup (S.A ⧸ N) :=
  (corePreimage S phi).map (QuotientGroup.mk' N)

instance corePreimage_normal : (corePreimage S phi).Normal := inferInstance

instance retainedElementaryImage_normal
    (N : Subgroup S.A) [N.Normal] :
    (retainedElementaryImage S phi N).Normal :=
  Subgroup.Normal.map inferInstance
    (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

instance retainedCoreImage_normal
    (N : Subgroup S.A) [N.Normal] :
    (retainedCoreImage S phi N).Normal :=
  Subgroup.Normal.map (corePreimage_normal S phi)
    (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

/-- The invariant constituent corresponding to an ambient-normal subgroup
of the retained elementary image. -/
noncomputable abbrev retainedNormalConstituent
    (N : Subgroup S.A) [N.Normal]
    (M : Subgroup (S.A ⧸ N)) [M.Normal] :
    Subrepresentation (sectionTopRepresentation S phi C N).ρ :=
  (ActualWreathAffineCapacity.originalChart S phi C).quotientChart
      (ActualWreathAffineCapacity.pi S phi)
      (ActualWreathAffineCapacity.E S phi C).quotientRepresentation N
    |>.normalSubrepresentation
      (OriginalKernelModuleChart.base
        (ActualWreathAffineCapacity.pi S phi) N)
      (OriginalKernelModuleChart.base_surjective
        (ActualWreathAffineCapacity.pi S phi) N)
      (sectionTopRepresentation S phi C N) M

/-- A nontrivial ambient-normal subgroup carried by the retained elementary
kernel gives a nonzero invariant constituent in the exact quotient chart.
This is elementary quotient plumbing; no Clifford input is used. -/
theorem quotientNormalSubrepresentation_ne_bot
    {p : ℕ} [Fact p.Prime]
    {G B : Type} [Group G] [Group B]
    (π : G →* B) (hπ : Function.Surjective π)
    (A : Rep (ZMod p) B)
    (E : OriginalKernelModuleChart π A)
    (N : Subgroup G) [N.Normal]
    (M : Subgroup (G ⧸ N)) [M.Normal]
    (hMker : M ≤ π.ker.map (QuotientGroup.mk' N))
    (hM : M ≠ ⊥) :
    (E.quotientChart π A N).normalSubrepresentation
        (OriginalKernelModuleChart.base π N)
        (OriginalKernelModuleChart.base_surjective π N)
        (E.sectionRepresentation π A N) M ≠ ⊥ := by
  intro hbot
  let q := OriginalKernelModuleChart.base π N
  let C := E.quotientChart π A N
  let secRep := E.sectionRepresentation π A N
  apply hM
  rw [eq_bot_iff]
  intro m hm
  have hmker : m ∈ q.ker := by
    obtain ⟨k, hk, hkm⟩ := hMker hm
    change OriginalKernelModuleChart.base π N m = 1
    rw [← hkm]
    change QuotientGroup.mk' (π.ker ⊔ N) k = 1
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_sup_left hk)
  let k : q.ker := ⟨m, hmker⟩
  have hcoordKer :
      (C.kernelCoordinates q secRep).ker ≤ M.subgroupOf q.ker := by
    intro x hx
    have hxone : x = 1 := by
      apply C.equiv.symm.injective
      exact (MonoidHom.mem_ker.mp hx).trans (map_one C.equiv.symm).symm
    subst x
    exact Subgroup.one_mem _
  have hkW : (C.kernelCoordinates q secRep k).toAdd ∈
      C.normalSubrepresentation q
        (OriginalKernelModuleChart.base_surjective π N) secRep M := by
    exact (sectionSubgroupImage_mem_iff
      (C.kernelCoordinates q secRep) (M.subgroupOf q.ker)
      hcoordKer k).2 hm
  rw [hbot] at hkW
  have hzero : (C.kernelCoordinates q secRep k).toAdd = 0 := by
    simpa using hkW
  have hcoordOne : C.kernelCoordinates q secRep k = 1 := by
    simpa using congrArg Multiplicative.ofAdd hzero
  have hkone : k = 1 := by
    apply C.equiv.symm.injective
    simpa only [map_one] using hcoordOne
  exact congrArg Subtype.val hkone

/-- The constituent belonging to a nontrivial normal subgroup carried by
the retained elementary kernel is nonzero. -/
theorem retainedNormalConstituent_ne_bot
    (N : Subgroup S.A) [N.Normal]
    (M : Subgroup (S.A ⧸ N)) [M.Normal]
    (hMker : M ≤ retainedElementaryImage S phi N)
    (hM : M ≠ ⊥) :
    retainedNormalConstituent S phi C N M ≠ ⊥ := by
  exact quotientNormalSubrepresentation_ne_bot
    (ActualWreathAffineCapacity.pi S phi)
    (QuotientGroup.mk'_surjective (ActualWreathAffineCapacity.K S phi))
    (ActualWreathAffineCapacity.E S phi C).quotientRepresentation
    (ActualWreathAffineCapacity.originalChart S phi C) N M
    (by
      change M ≤ (ActualWreathAffineCapacity.pi S phi).ker.map
        (QuotientGroup.mk' N)
      rw [QuotientGroup.ker_mk']
      exact hMker) hM

/-- The retained invariant constituent embeds into the literal normal
subgroup it charts.  Only this direction is needed for the small-degree
cardinality argument, and it avoids choosing an inverse to the quotient
chart. -/
noncomputable def retainedNormalConstituentEmbedding
    (N : Subgroup S.A) [N.Normal]
    (M : Subgroup (S.A ⧸ N)) [M.Normal]
    (hMker : M ≤ retainedElementaryImage S phi N) :
    retainedNormalConstituent S phi C N M ↪ M := by
  let π := ActualWreathAffineCapacity.pi S phi
  let A := (ActualWreathAffineCapacity.E S phi C).quotientRepresentation
  let chart := ActualWreathAffineCapacity.originalChart S phi C
  let q : (S.A ⧸ N) →* S.A ⧸ (π.ker ⊔ N) :=
    OriginalKernelModuleChart.base π N
  let secRep : Rep.{0, 0, 0}
      (ZMod (ActualWreathAffineCapacity.E S phi C).p)
      (S.A ⧸ (π.ker ⊔ N)) :=
    chart.sectionRepresentation π A N
  let quotientChart := chart.quotientChart π A N
  let W := retainedNormalConstituent S phi C N M
  have hcoordKer :
      (quotientChart.kernelCoordinates q secRep).ker ≤
        M.subgroupOf q.ker := by
    intro x hx
    have hxone : x = 1 := by
      apply quotientChart.equiv.symm.injective
      exact (MonoidHom.mem_ker.mp hx).trans
        (map_one quotientChart.equiv.symm).symm
    subst x
    exact Subgroup.one_mem _
  have member_to (v : W) :
      ((quotientChart.equiv (Multiplicative.ofAdd v.1) : q.ker) :
        S.A ⧸ N) ∈ M := by
    let k : q.ker := quotientChart.equiv (Multiplicative.ofAdd v.1)
    have hkcoord :
        (quotientChart.kernelCoordinates q secRep k).toAdd = v.1 :=
      congrArg Multiplicative.toAdd
        (quotientChart.equiv.symm_apply_apply (Multiplicative.ofAdd v.1))
    apply (sectionSubgroupImage_mem_iff
      (p := (ActualWreathAffineCapacity.E S phi C).p)
      (quotientChart.kernelCoordinates q secRep)
      (M.subgroupOf q.ker) hcoordKer k).1
    rw [hkcoord]
    exact v.2
  exact
    { toFun := fun v =>
        ⟨(quotientChart.equiv (Multiplicative.ofAdd v.1) : q.ker).1,
          member_to v⟩
      inj' := by
        intro v z hvz
        apply Subtype.ext
        apply Multiplicative.ofAdd.injective
        apply quotientChart.equiv.injective
        apply Subtype.ext
        exact congrArg (fun x : M => (x.1 : S.A ⧸ N)) hvz }

/-- Cardinal comparison furnished by the literal quotient-chart
embedding. -/
theorem natCard_retainedNormalConstituent_le
    (N : Subgroup S.A) [N.Normal]
    (M : Subgroup (S.A ⧸ N)) [M.Normal]
    (hMker : M ≤ retainedElementaryImage S phi N) :
    Nat.card (retainedNormalConstituent S phi C N M) ≤ Nat.card M :=
  Nat.card_le_card_of_injective
    (retainedNormalConstituentEmbedding S phi C N M hMker)
    (retainedNormalConstituentEmbedding S phi C N M hMker).injective

/-- If the retained core centralizes an elementary-carried normal subgroup,
then its action on the corresponding invariant constituent is the trivial
representation.  This is the literal quotient-chart calculation which
turns the published Clifford statement into a group commutator statement. -/
theorem constituentLinearKernelRepresentation_eq_one_of_commutator_eq_bot
    (N : Subgroup S.A) [N.Normal]
    (M : Subgroup (S.A ⧸ N)) [M.Normal]
    (hMker : M ≤ retainedElementaryImage S phi N)
    (hcomm : ⁅retainedCoreImage S phi N, M⁆ = ⊥) :
    (constituentLinearKernelRepresentation S phi C N
      (retainedNormalConstituent S phi C N M)).ρ = 1 := by
  let π := ActualWreathAffineCapacity.pi S phi
  let A := (ActualWreathAffineCapacity.E S phi C).quotientRepresentation
  let chart := ActualWreathAffineCapacity.originalChart S phi C
  let q := OriginalKernelModuleChart.base π N
  let secRep := chart.sectionRepresentation π A N
  let quotientChart := chart.quotientChart π A N
  let W := retainedNormalConstituent S phi C N M
  have hcentral : retainedCoreImage S phi N ≤
      Subgroup.centralizer (M : Set (S.A ⧸ N)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  apply MonoidHom.ext
  intro k
  ext v
  apply Subtype.ext
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective
    (elementaryKernel S phi) k.1
  have hgcore : g ∈ corePreimage S phi := by
    change QuotientGroup.mk' (elementaryKernel S phi) g ∈
      linearBlockKernel S phi
    simpa only [hg] using k.2
  have hgretained : QuotientGroup.mk' N g ∈ retainedCoreImage S phi N :=
    ⟨g, hgcore, rfl⟩
  let m : q.ker := quotientChart.equiv (Multiplicative.ofAdd v.1)
  have hmcoord :
      (quotientChart.kernelCoordinates q secRep m).toAdd = v.1 := by
    exact congrArg Multiplicative.toAdd
      (quotientChart.equiv.symm_apply_apply (Multiplicative.ofAdd v.1))
  have hcoordKer :
      (quotientChart.kernelCoordinates q secRep).ker ≤
        M.subgroupOf q.ker := by
    intro x hx
    have hxone : x = 1 := by
      apply quotientChart.equiv.symm.injective
      exact (MonoidHom.mem_ker.mp hx).trans
        (map_one quotientChart.equiv.symm).symm
    subst x
    exact Subgroup.one_mem _
  have hmM : (m : S.A ⧸ N) ∈ M := by
    have hmSpace :
        (quotientChart.kernelCoordinates q secRep m).toAdd ∈
          quotientChart.normalSpace q secRep M := by
      rw [hmcoord]
      exact v.2
    exact (sectionSubgroupImage_mem_iff
      (quotientChart.kernelCoordinates q secRep)
      (M.subgroupOf q.ker) hcoordKer m).1 hmSpace
  have hcommute : Commute (QuotientGroup.mk' N g) (m : S.A ⧸ N) :=
    (hcentral hgretained (m : S.A ⧸ N) hmM).symm
  have htop : linearKernelToSectionTop S phi N k =
      q (QuotientGroup.mk' N g) := by
    change OriginalKernelModuleChart.labelTop π N
        (QuotientGroup.mk'_surjective
          (ActualWreathAffineCapacity.K S phi)) k.1 =
      QuotientGroup.mk' (π.ker ⊔ N) g
    rw [← hg]
    exact OriginalKernelModuleChart.labelTop_apply π N
      (QuotientGroup.mk'_surjective
        (ActualWreathAffineCapacity.K S phi)) g
  change secRep.ρ (linearKernelToSectionTop S phi N k) v.1 = v.1
  rw [htop]
  apply Multiplicative.ofAdd.injective
  apply quotientChart.equiv.injective
  apply Subtype.val_injective
  change ((quotientChart.equiv (Multiplicative.ofAdd
      ((chart.sectionRepresentation π A N).ρ
        (q (QuotientGroup.mk' N g)) v.1)) : q.ker) : S.A ⧸ N) =
    ((quotientChart.equiv (Multiplicative.ofAdd v.1) : q.ker) : S.A ⧸ N)
  rw [quotientChart.conjugate]
  calc
    (QuotientGroup.mk' N g) * (m : S.A ⧸ N) *
        (QuotientGroup.mk' N g)⁻¹ =
        (m : S.A ⧸ N) * (QuotientGroup.mk' N g) *
          (QuotientGroup.mk' N g)⁻¹ := by rw [hcommute.eq]
    _ = m := by simp

/-- The prepublished strong Clifford theorem, stated only in the generic
actual-wreath form consumed by this project.  The conclusion is precisely
semisimplicity plus the single ambient orbit of homogeneous constituents:
on every nonzero ambient invariant constituent of a retained elementary
section, the literal linear block kernel still acts faithfully.

The two representation hypotheses and every coordinate-nontriviality
hypothesis must be discharged on the literal action. -/
structure Input : Prop where
  faithfulNonzeroConstituent :
    ∀ {Q I : Type} [Group Q] [Fintype I] [Nonempty I]
      [MulAction Q I] [FaithfulSMul Q I]
      (S : ActualWreathCompressionState Q I)
      {D' : Type} [Group D'] [Finite D']
      (phi : S.D →* D') (hphi : Function.Surjective phi)
      (C : ElementaryMinimalNormalChart phi.ker),
      Representation.IsIrreducible
          (localRepresentation S phi hphi C).ρ →
      Function.Injective (localRepresentation S phi hphi C).ρ →
      (∀ i : I, (linearCoordinate S phi i).range ≠ ⊥) →
      ∀ (N : Subgroup S.A) [N.Normal],
        ¬ elementaryKernel S phi ≤ N →
        ∀ (W : Subrepresentation.{0, 0, 0}
          (sectionTopRepresentation S phi C N).ρ),
          W ≠ ⊥ →
          Function.Injective
            (constituentLinearKernelRepresentation S phi C N W).ρ

/-- The group-theoretic retained-core consequence of the published
homogeneous-restriction theorem.  A nonzero ambient minimal normal subgroup
inside the elementary image is acted on nontrivially by the retained linear
core, hence its mixed commutator is the whole subgroup. -/
theorem Input.commutator_eq_of_minimalNormal_le_retainedElementary
    (input : Input)
    (hirreducible : Representation.IsIrreducible
      (localRepresentation S phi hphi C).ρ)
    (hlocalFaithful : Function.Injective
      (localRepresentation S phi hphi C).ρ)
    (hcoordinate : ∀ i : I, (linearCoordinate S phi i).range ≠ ⊥)
    (N : Subgroup S.A) [N.Normal]
    (hretained : ¬ elementaryKernel S phi ≤ N)
    (M : Subgroup (S.A ⧸ N))
    (hM : IsMinimalNormalSubgroup M)
    (hME : M ≤ retainedElementaryImage S phi N) :
    ⁅retainedCoreImage S phi N, M⁆ = M := by
  rcases minimalNormal_commutator_full_or_trivial
      (retainedCoreImage S phi N) M hM with hfull | htrivial
  · exact hfull
  · exfalso
    letI : M.Normal := hM.1
    let W := retainedNormalConstituent S phi C N M
    have hW : W ≠ ⊥ := retainedNormalConstituent_ne_bot
      S phi C N M hME hM.2.1
    have hfaithful : Function.Injective
        (constituentLinearKernelRepresentation S phi C N W).ρ :=
      input.faithfulNonzeroConstituent S phi hphi C hirreducible
        hlocalFaithful hcoordinate N hretained W hW
    have htrivialRep :
        (constituentLinearKernelRepresentation S phi C N W).ρ = 1 :=
      constituentLinearKernelRepresentation_eq_one_of_commutator_eq_bot
        S phi C N M hME htrivial
    have hKbot : linearBlockKernel S phi = ⊥ := by
      rw [eq_bot_iff]
      intro k hk
      let x : linearBlockKernel S phi := ⟨k, hk⟩
      have hx : x = 1 := hfaithful (by rw [htrivialRep]; simp)
      exact congrArg Subtype.val hx
    obtain i := Classical.choice (inferInstance : Nonempty I)
    apply hcoordinate i
    rw [eq_bot_iff]
    rintro y ⟨k, rfl⟩
    have hk : k = 1 := by
      apply Subtype.ext
      exact Subgroup.mem_bot.mp (by simpa only [hKbot] using k.2)
    subst k
    simp

/-- Faithfulness on the nonzero retained elementary section gives the exact
kernel intersection `N ∩ B = N ∩ E`.  This is the first literal retained-core
consequence of Clifford homogeneity. -/
theorem Input.inf_corePreimage_eq_inf_elementaryKernel
    (input : Input)
    (hirreducible : Representation.IsIrreducible
      (localRepresentation S phi hphi C).ρ)
    (hlocalFaithful : Function.Injective
      (localRepresentation S phi hphi C).ρ)
    (hcoordinate : ∀ i : I, (linearCoordinate S phi i).range ≠ ⊥)
    (N : Subgroup S.A) [N.Normal]
    (hretained : ¬ elementaryKernel S phi ≤ N) :
    N ⊓ corePreimage S phi = N ⊓ elementaryKernel S phi := by
  have hEbar : retainedElementaryImage S phi N ≠ ⊥ := by
    intro hbot
    apply hretained
    have hle := (Subgroup.map_eq_bot_iff
      (H := elementaryKernel S phi) (f := QuotientGroup.mk' N)).mp hbot
    simpa only [QuotientGroup.ker_mk'] using hle
  let M := retainedElementaryImage S phi N
  let W := retainedNormalConstituent S phi C N M
  have hW : W ≠ ⊥ := retainedNormalConstituent_ne_bot
    S phi C N M le_rfl hEbar
  have hfaithful : Function.Injective
      (constituentLinearKernelRepresentation S phi C N W).ρ :=
    input.faithfulNonzeroConstituent S phi hphi C hirreducible
      hlocalFaithful hcoordinate N hretained W hW
  apply le_antisymm
  · rintro b ⟨hbN, hbcore⟩
    refine ⟨hbN, ?_⟩
    let k : linearBlockKernel S phi :=
      ⟨QuotientGroup.mk' (elementaryKernel S phi) b, hbcore⟩
    have htop : linearKernelToSectionTop S phi N k = 1 := by
      change OriginalKernelModuleChart.labelTop
          (ActualWreathAffineCapacity.pi S phi) N
          (QuotientGroup.mk'_surjective
            (ActualWreathAffineCapacity.K S phi))
          (QuotientGroup.mk' (ActualWreathAffineCapacity.K S phi) b) = 1
      rw [OriginalKernelModuleChart.labelTop_apply]
      exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_sup_right hbN)
    have hk : k = 1 := hfaithful (by
      have hrep := congrArg W.toRepresentation htop
      simpa only [map_one] using hrep)
    exact (QuotientGroup.eq_one_iff _).mp
      (congrArg Subtype.val hk)
  · exact inf_le_inf le_rfl (by
      intro e he
      change QuotientGroup.mk' (elementaryKernel S phi) e ∈
        linearBlockKernel S phi
      have heq : QuotientGroup.mk' (elementaryKernel S phi) e = 1 :=
        (QuotientGroup.eq_one_iff _).mpr he
      exact heq ▸ Subgroup.one_mem _)

/-- No ambient minimal normal subgroup can sit in the retained linear core
without already being carried by the retained elementary kernel.  Pulling
such a subgroup back to the original group and applying the exact
intersection theorem proves the claim. -/
theorem Input.minimalNormal_le_retainedCore_iff_le_retainedElementary
    (input : Input)
    (hirreducible : Representation.IsIrreducible
      (localRepresentation S phi hphi C).ρ)
    (hlocalFaithful : Function.Injective
      (localRepresentation S phi hphi C).ρ)
    (hcoordinate : ∀ i : I, (linearCoordinate S phi i).range ≠ ⊥)
    (N : Subgroup S.A) [N.Normal]
    (hretained : ¬ elementaryKernel S phi ≤ N)
    (M : Subgroup (S.A ⧸ N))
    (hM : IsMinimalNormalSubgroup M) :
    M ≤ retainedCoreImage S phi N ↔
      M ≤ retainedElementaryImage S phi N := by
  constructor
  · intro hMD
    by_contra hnot
    letI : M.Normal := hM.1
    let L : Subgroup S.A := M.comap (QuotientGroup.mk' N)
    letI : L.Normal := Subgroup.Normal.comap hM.1 (QuotientGroup.mk' N)
    have hEbar : retainedElementaryImage S phi N ≠ ⊥ := by
      intro hbot
      apply hretained
      have hle := (Subgroup.map_eq_bot_iff
        (H := elementaryKernel S phi) (f := QuotientGroup.mk' N)).mp hbot
      simpa only [QuotientGroup.ker_mk'] using hle
    have hEL : ¬ elementaryKernel S phi ≤ L := by
      intro hle
      have hEbarM : retainedElementaryImage S phi N ≤ M := by
        rintro y ⟨e, he, rfl⟩
        exact hle he
      have heq : retainedElementaryImage S phi N = M :=
        hM.2.2 (retainedElementaryImage S phi N)
          inferInstance hEbar hEbarM
      exact hnot (by rw [← heq])
    have hInf : L ⊓ corePreimage S phi =
        L ⊓ elementaryKernel S phi :=
      input.inf_corePreimage_eq_inf_elementaryKernel S phi hphi C
        hirreducible hlocalFaithful hcoordinate L hEL
    apply hM.2.1
    rw [eq_bot_iff]
    intro m hm
    obtain ⟨b, hbcore, hbm⟩ := hMD hm
    have hbL : b ∈ L := by
      change QuotientGroup.mk' N b ∈ M
      simpa only [hbm] using hm
    have hbInf : b ∈ L ⊓ corePreimage S phi := ⟨hbL, hbcore⟩
    rw [hInf] at hbInf
    have hmE : m ∈ retainedElementaryImage S phi N :=
      ⟨b, hbInf.2, hbm⟩
    have hdisjoint : Disjoint M (retainedElementaryImage S phi N) := by
      rw [disjoint_iff]
      by_contra hne
      have heq : M ⊓ retainedElementaryImage S phi N = M :=
        hM.2.2 (M ⊓ retainedElementaryImage S phi N)
          inferInstance hne inf_le_left
      exact hnot (by rw [← heq]; exact inf_le_right)
    have hmBot : m ∈ M ⊓ retainedElementaryImage S phi N := ⟨hm, hmE⟩
    rw [disjoint_iff.mp hdisjoint] at hmBot
    exact Subgroup.mem_bot.mp hmBot
  · exact fun hME => hME.trans (Subgroup.map_mono (by
      intro e he
      change QuotientGroup.mk' (elementaryKernel S phi) e ∈
        linearBlockKernel S phi
      have heq : QuotientGroup.mk' (elementaryKernel S phi) e = 1 :=
        (QuotientGroup.eq_one_iff _).mpr he
      exact heq ▸ Subgroup.one_mem _))

/-- A minimal normal subgroup outside the retained elementary image is
centralized by the retained linear core.  The proof pulls a hypothetical
active factor back to the original group and applies the exact intersection
theorem to that literal preimage. -/
theorem Input.commutator_eq_bot_of_minimalNormal_not_le_retainedElementary
    (input : Input)
    (hirreducible : Representation.IsIrreducible
      (localRepresentation S phi hphi C).ρ)
    (hlocalFaithful : Function.Injective
      (localRepresentation S phi hphi C).ρ)
    (hcoordinate : ∀ i : I, (linearCoordinate S phi i).range ≠ ⊥)
    (N : Subgroup S.A) [N.Normal]
    (hretained : ¬ elementaryKernel S phi ≤ N)
    (M : Subgroup (S.A ⧸ N))
    (hM : IsMinimalNormalSubgroup M)
    (hnot : ¬ M ≤ retainedElementaryImage S phi N) :
    ⁅retainedCoreImage S phi N, M⁆ = ⊥ := by
  rcases minimalNormal_commutator_full_or_trivial
      (retainedCoreImage S phi N) M hM with hfull | htrivial
  · exfalso
    letI : M.Normal := hM.1
    let L : Subgroup S.A := M.comap (QuotientGroup.mk' N)
    letI : L.Normal := Subgroup.Normal.comap hM.1 (QuotientGroup.mk' N)
    have hEbar : retainedElementaryImage S phi N ≠ ⊥ := by
      intro hbot
      apply hretained
      have hle := (Subgroup.map_eq_bot_iff
        (H := elementaryKernel S phi) (f := QuotientGroup.mk' N)).mp hbot
      simpa only [QuotientGroup.ker_mk'] using hle
    have hEL : ¬ elementaryKernel S phi ≤ L := by
      intro hle
      have hEbarM : retainedElementaryImage S phi N ≤ M := by
        rintro y ⟨e, he, rfl⟩
        exact hle he
      have heq : retainedElementaryImage S phi N = M :=
        hM.2.2 (retainedElementaryImage S phi N)
          inferInstance hEbar hEbarM
      exact hnot (by rw [← heq])
    have hInf : L ⊓ corePreimage S phi =
        L ⊓ elementaryKernel S phi :=
      input.inf_corePreimage_eq_inf_elementaryKernel S phi hphi C
        hirreducible hlocalFaithful hcoordinate L hEL
    have hMD : M ≤ retainedCoreImage S phi N := by
      rw [← hfull]
      exact Subgroup.commutator_le_left _ _
    have hdisjoint : Disjoint M (retainedElementaryImage S phi N) := by
      rw [disjoint_iff]
      by_contra hne
      have heq : M ⊓ retainedElementaryImage S phi N = M :=
        hM.2.2 (M ⊓ retainedElementaryImage S phi N)
          inferInstance hne inf_le_left
      exact hnot (by rw [← heq]; exact inf_le_right)
    apply hM.2.1
    rw [eq_bot_iff]
    intro m hm
    obtain ⟨b, hbcore, hbm⟩ := hMD hm
    have hbL : b ∈ L := by
      change QuotientGroup.mk' N b ∈ M
      simpa only [hbm] using hm
    have hbInf : b ∈ L ⊓ corePreimage S phi := ⟨hbL, hbcore⟩
    rw [hInf] at hbInf
    have hmE : m ∈ retainedElementaryImage S phi N := by
      refine ⟨b, hbInf.2, ?_⟩
      exact hbm
    have hmBot : m ∈ M ⊓ retainedElementaryImage S phi N := ⟨hm, hmE⟩
    rw [disjoint_iff.mp hdisjoint] at hmBot
    exact Subgroup.mem_bot.mp hmBot
  · exact htrivial

/-- Exact generic Clifford action dichotomy on every ambient minimal normal
factor of the literal retained quotient. -/
theorem Input.commutator_eq_iff_minimalNormal_le_retainedElementary
    (input : Input)
    (hirreducible : Representation.IsIrreducible
      (localRepresentation S phi hphi C).ρ)
    (hlocalFaithful : Function.Injective
      (localRepresentation S phi hphi C).ρ)
    (hcoordinate : ∀ i : I, (linearCoordinate S phi i).range ≠ ⊥)
    (N : Subgroup S.A) [N.Normal]
    (hretained : ¬ elementaryKernel S phi ≤ N)
    (M : Subgroup (S.A ⧸ N))
    (hM : IsMinimalNormalSubgroup M) :
    ⁅retainedCoreImage S phi N, M⁆ = M ↔
      M ≤ retainedElementaryImage S phi N := by
  constructor
  · intro hfull
    by_contra hnot
    have hbot :=
      input.commutator_eq_bot_of_minimalNormal_not_le_retainedElementary
        S phi hphi C hirreducible hlocalFaithful hcoordinate N hretained
        M hM hnot
    exact hM.2.1 (hfull.symm.trans hbot)
  · exact input.commutator_eq_of_minimalNormal_le_retainedElementary
      S phi hphi C hirreducible hlocalFaithful hcoordinate N hretained M hM

end CliffordHomogeneousRestriction
end SymmetricSubgroupAsymptotics

end
