import SymmetricSubgroupAsymptotics.CFSGFFourE6FixedPositiveProjection
import SymmetricSubgroupAsymptotics.CFSGFFourE6RelativeWords
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFixedRootFamilyCover
import SymmetricSubgroupAsymptotics.CFSGSubgroupConjugateRestriction
import SymmetricSubgroupAsymptotics.CFSGExceptionalRootCountBound

/-! The identity-field fixed E6 root-line family projects to the ORIGINAL
F4 model. Positive fixed lines and their actual relative-word translates
lie in the folded group, so restriction and projection retain the checked
family cover without a whole-source faithfulness assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalRootFamily
open CFSGFFourSerreMatrices CFSGFFourE6OriginalProjection CFSGFFourE6FixedPositiveProjection
open CFSGFFourE6RelativeWords CFSGFFourE6DiagramFixed CFSGFFourE6RootSubgroups
open CFSGTwistedE6GeckFixedRootFamilyCover CFSGTwistedE6GeckRelativeRootGenerated
open CFSGTwistedE6GeckPositiveTwist CFSGTwistedE6WeylChamber
open CFSGTwistedE6RelativeWeylOrbits CFSGTwistedE6FixedWordClassification
open CFSGNormTwoCoordinatePositiveRootGenerators CFSGNormTwoRootPairing
open CFSGNormTwoGeckIntegralWord CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGIntegerMatrixPairing CFSGSerreQuadraticMatrix CFSG.Models.Chevalley
open CFSGSubgroupConjugateRestriction
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos

def rootLineInFolded (K : Type) [Field K] (k : Roots A) :
    Subgroup (canonicalElementaryGroup realizationData K) :=
  (fixedRootLine K (RingEquiv.refl K) k).subgroupOf (canonicalElementaryGroup realizationData K)

def originalRootLine (K : Type) [Field K]
    [IsSimpleGroup (Projective CartanMatrix.F₄ K)] (k : Roots A) :
    Subgroup (Projective CartanMatrix.F₄ K) :=
  (rootLineInFolded K k).map (foldedToOriginal K)

theorem positive_fixed_line_le_folded (K : Type) [Field K] [Finite K]
    (theta : Roots A) (htheta : ∀i,0≤theta.val i) :
    fixedRootLine K (RingEquiv.refl K) theta≤canonicalElementaryGroup realizationData K := by
  intro x hx
  exact fixedPositive_mem_folded K
    ⟨x,⟨positive_root_subgroup_le A hd hs hp ho K theta htheta hx.1,hx.2⟩⟩

theorem menu_fixed_line_le_folded (K : Type) [Field K] [Finite K]
    (theta : Roots A) (htheta : ∀i,0≤theta.val i) (k : relativeRootMenu theta) :
    fixedRootLine K (RingEquiv.refl K) k.val≤canonicalElementaryGroup realizationData K := by
  obtain ⟨r,hr⟩ := k.property
  rw [←hr,←relative_fixedRootLine_map K (RingEquiv.refl K) r theta]
  rintro _ ⟨x,hx,rfl⟩
  have hW : CFSGNormTwoGeckWeylWordDegree.wordUnit A hs hp E6Base E6Index K
      (expandRelative r)∈canonicalElementaryGroup realizationData K := by
    rw [word_eq_canonicalWord]
    exact relativeWord_mem_folded K r
  exact (canonicalElementaryGroup realizationData K).mul_mem
    ((canonicalElementaryGroup realizationData K).mul_mem hW
      (positive_fixed_line_le_folded K theta htheta hx))
    ((canonicalElementaryGroup realizationData K).inv_mem hW)

theorem originalRootLine_le_fixedPositive (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)]
    (theta : Roots A) (htheta : ∀i,0≤theta.val i) :
    originalRootLine K theta≤originalFixedPositive K p := by
  rintro _ ⟨j,hj,rfl⟩
  let u : signedFixed K (RingEquiv.refl K) false :=
    ⟨j.val,⟨positive_root_subgroup_le A hd hs hp ho K theta htheta hj.1,hj.2⟩⟩
  exact ⟨u,rfl⟩

theorem originalRootLine_ne_top (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)]
    (theta : Roots A) (htheta : ∀i,0≤theta.val i) : originalRootLine K theta≠⊤ := by
  intro htop
  apply originalFixedPositive_ne_top K p
  apply top_unique
  rw [←htop]
  exact originalRootLine_le_fixedPositive K p theta htheta

private theorem restrict_conjugate_equality {G : Type*} [Group G]
    (H R S : Subgroup G) (hR : R≤H) (hS : S≤H) (g u : H)
    (he : R.map (MulAut.conj g.val).toMonoidHom=S.map (MulAut.conj u.val).toMonoidHom) :
    (R.subgroupOf H).map (MulAut.conj g).toMonoidHom=
      (S.subgroupOf H).map (MulAut.conj u).toMonoidHom := by
  apply Subgroup.map_injective (f:=H.subtype) H.subtype_injective
  rw [map_conjugate,map_conjugate,Subgroup.map_subgroupOf_eq_of_le hR,
    Subgroup.map_subgroupOf_eq_of_le hS]
  exact he

private theorem push_conjugate_equality {G Q : Type*} [Group G] [Group Q]
    (f : G→*Q) (R S : Subgroup G) (g u : G)
    (he : R.map (MulAut.conj g).toMonoidHom=S.map (MulAut.conj u).toMonoidHom) :
    (R.map f).map (MulAut.conj (f g)).toMonoidHom=
      (S.map f).map (MulAut.conj (f u)).toMonoidHom :=
  (map_conjugate f R g).symm.trans
    ((congrArg (fun T : Subgroup G=>T.map f) he).trans (map_conjugate f S u))

theorem original_fixed_root_family_cover (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)]
    (theta : Roots A) (htheta : ∀i,0≤theta.val i)
    (hdom : ∀i,0 ≤ integerPairing A theta.val (Pi.single i (1 : ℤ) : Fin 6→ℤ))
    (g : Projective CartanMatrix.F₄ K) :
    ∃k : relativeRootMenu theta, ∃u : signedFixed K (RingEquiv.refl K) false,
      (originalRootLine K theta).map (MulAut.conj g).toMonoidHom=
        (originalRootLine K k.val).map (MulAut.conj (fixedPositiveToOriginal K p u)).toMonoidHom := by
  obtain ⟨j,hj⟩ := foldedToOriginal_surjective K g
  have hjambient : j.val∈CFSGTwistedE6GeckSourceAction.MatrixGroup K :=
    foldedModel_le_ambient K j.property
  have hjfixed := foldedModel_le_diagramFixed K j.property
  obtain ⟨k,u,he⟩ := fixed_conjugate_eq_fixed_positive_conjugate K
    (RingEquiv.refl K) theta htheta hdom j.val hjambient hjfixed
  let uj := fixedPositiveToFolded K u
  have hr := restrict_conjugate_equality (canonicalElementaryGroup realizationData K) _ _
    (positive_fixed_line_le_folded K theta htheta)
    (menu_fixed_line_le_folded K theta htheta k) j uj he
  have hm := push_conjugate_equality (foldedToOriginal K)
    (rootLineInFolded K theta) (rootLineInFolded K k.val) j uj hr
  refine ⟨k,u,?_⟩
  calc
    _=(originalRootLine K theta).map (MulAut.conj (foldedToOriginal K j)).toMonoidHom :=
      congrArg (fun z=>(originalRootLine K theta).map (MulAut.conj z).toMonoidHom) hj.symm
    _=(originalRootLine K k.val).map (MulAut.conj (foldedToOriginal K uj)).toMonoidHom := hm
    _=_ := congrArg (fun z=>(originalRootLine K k.val).map (MulAut.conj z).toMonoidHom)
      (fixedPositiveToOriginal_apply K p u).symm

theorem original_root_menu_card_le (theta : Roots A) : Nat.card (relativeRootMenu theta)≤512 :=
  (relativeRootMenu_card_le theta).trans CFSGExceptionalRootCountBound.E6_root_card_le

end SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalRootFamily
