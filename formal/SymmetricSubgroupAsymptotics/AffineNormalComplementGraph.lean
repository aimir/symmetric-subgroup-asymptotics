import SymmetricSubgroupAsymptotics.AffineFixedTopNormalFibre
import SymmetricSubgroupAsymptotics.PrimeActionQuotient
import SymmetricSubgroupAsymptotics.PrimeSectionalCharacterRank
import SymmetricSubgroupAsymptotics.SchurRepresentation

/-!
# Normal complements as equivariant prime-field graphs

Fix an extension `G -> B` with elementary kernel and a normal subgroup
`D ◁ B`.  Normal subgroups of `G` with image `D` and trivial intersection
with the kernel are normal complements in the literal preimage of `D`.
After choosing one such complement, every other one has a difference graph
`D -> ker pi`.  Normality in the whole ambient group makes this graph
`B`-equivariant.  This file constructs that graph injectively and bounds it
by the Schur capacity of the original kernel representation and the
sectional prime rank of the original ambient group.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime]
variable {G B : Type} [Group G] [Finite G] [Group B] [Finite B]
variable (pi : G →* B) (hpi : Function.Surjective pi)
variable (A : Rep (ZMod p) B) [Finite A]
variable (E : OriginalKernelModuleChart pi A)

/-- Ambient-normal complements above one literal normal quotient subgroup. -/
abbrev NormalFixedImageComplementFibre
    (D : {D : Subgroup B // D.Normal}) :=
  {N : {N : Subgroup G // N.Normal} //
    N.1.map pi = D.1 ∧ N.1 ⊓ pi.ker = ⊥}

namespace NormalFixedImageComplementFibre

variable (D : {D : Subgroup B // D.Normal})

private theorem subgroup_le_preimage
    (N : NormalFixedImageComplementFibre pi D) :
    N.1.1 ≤ D.1.comap pi := by
  rw [← Subgroup.map_le_iff_le_comap, N.2.1]

/-- Restrict a normal complement to the literal preimage of its image. -/
private def restrictedSubgroup
    (N : NormalFixedImageComplementFibre pi D) :
    Subgroup (D.1.comap pi) :=
  N.1.1.subgroupOf (D.1.comap pi)

private theorem restricted_map_top
    (N : NormalFixedImageComplementFibre pi D) :
    (restrictedSubgroup pi D N).map (pi.subgroupComap D.1) = ⊤ := by
  apply top_unique
  intro d _
  have hd : (d : B) ∈ N.1.1.map pi := by
    rw [N.2.1]
    exact d.2
  obtain ⟨g, hg, hgd⟩ := Subgroup.mem_map.mp hd
  have hpre : g ∈ D.1.comap pi := by
    change pi g ∈ D.1
    rw [hgd]
    exact d.2
  exact ⟨⟨g, hpre⟩, hg, Subtype.ext hgd⟩

private theorem restricted_inf_kernel_bot
    (N : NormalFixedImageComplementFibre pi D) :
    restrictedSubgroup pi D N ⊓ (pi.subgroupComap D.1).ker = ⊥ := by
  apply le_antisymm
  · intro x hx
    have hxG : (x.1 : G) ∈ N.1.1 ⊓ pi.ker := by
      refine ⟨hx.1, ?_⟩
      change pi x.1 = 1
      exact congrArg Subtype.val hx.2
    rw [N.2.2] at hxG
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    exact Subgroup.mem_bot.mp hxG
  · exact bot_le

/-- The literal section subgroup belonging to the normal complement. -/
private def normalSectionSubgroup
    (N : NormalFixedImageComplementFibre pi D) :
    SectionSubgroup (pi.subgroupComap D.1) :=
  ⟨restrictedSubgroup pi D N, by
      constructor
      · intro x y hxy
        change (pi.subgroupComap D.1) x.1 =
          (pi.subgroupComap D.1) y.1 at hxy
        have hm : x.1 * y.1⁻¹ ∈
            restrictedSubgroup pi D N ⊓ (pi.subgroupComap D.1).ker := by
          refine ⟨(restrictedSubgroup pi D N).mul_mem x.2
              ((restrictedSubgroup pi D N).inv_mem y.2), ?_⟩
          change (pi.subgroupComap D.1) (x.1 * y.1⁻¹) = 1
          rw [map_mul, map_inv, hxy, mul_inv_cancel]
        rw [restricted_inf_kernel_bot pi D N] at hm
        apply Subtype.ext
        exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp hm)
      · intro d
        have hd : d ∈ (restrictedSubgroup pi D N).map
            (pi.subgroupComap D.1) := by
          rw [restricted_map_top pi D N]
          trivial
        obtain ⟨x, hx, hxd⟩ := Subgroup.mem_map.mp hd
        exact ⟨⟨x, hx⟩, hxd⟩⟩

/-- The homomorphic section belonging to the literal normal complement. -/
private def normalSection
    (N : NormalFixedImageComplementFibre pi D) :
    HomomorphicLift (pi.subgroupComap D.1) (MonoidHom.id D.1) :=
  SectionSubgroup.toSection (pi.subgroupComap D.1)
    (normalSectionSubgroup pi D N)

private theorem section_mem
    (N : NormalFixedImageComplementFibre pi D) (d : D.1) :
    ((normalSection pi D N).1 d : D.1.comap pi) ∈
      restrictedSubgroup pi D N := by
  have h : (normalSection pi D N).1 d ∈
      (normalSection pi D N).1.range := ⟨d, rfl⟩
  have hrange : (normalSection pi D N).1.range =
      restrictedSubgroup pi D N := by
    exact SectionSubgroup.section_range _ (normalSectionSubgroup pi D N)
  rw [hrange] at h
  exact h

private theorem section_coe_mem
    (N : NormalFixedImageComplementFibre pi D) (d : D.1) :
    (((normalSection pi D N).1 d : D.1.comap pi) : G) ∈ N.1.1 :=
  section_mem pi D N d

private theorem eq_of_mem_of_map_eq
    (N : NormalFixedImageComplementFibre pi D)
    {x y : G} (hx : x ∈ N.1.1) (hy : y ∈ N.1.1)
    (hxy : pi x = pi y) : x = y := by
  have hmem : x * y⁻¹ ∈ N.1.1 ⊓ pi.ker := by
    refine ⟨N.1.1.mul_mem hx (N.1.1.inv_mem hy), ?_⟩
    change pi (x * y⁻¹) = 1
    rw [map_mul, map_inv, hxy, mul_inv_cancel]
  rw [N.2.2] at hmem
  have h1 : x * y⁻¹ = 1 := Subgroup.mem_bot.mp hmem
  exact (mul_inv_eq_one.mp h1)

/-- Conjugating a normalSection value in the ambient group gives the normalSection
value at the conjugated element of the normal image. -/
private theorem section_conjugate
    (N : NormalFixedImageComplementFibre pi D)
    (q : G) (d : D.1) :
    (((normalSection pi D N).1
        (MulAut.conjNormal (pi q) d) : D.1.comap pi) : G) =
      q * (((normalSection pi D N).1 d : D.1.comap pi) : G) * q⁻¹ := by
  apply eq_of_mem_of_map_eq pi D N
  · exact section_coe_mem pi D N _
  · exact Subgroup.Normal.conj_mem N.1.2 _
      (section_coe_mem pi D N d) q
  · change pi (((normalSection pi D N).1
        (MulAut.conjNormal (pi q) d) : D.1.comap pi) : G) = _
    have hs (x : D.1) :
        pi (((normalSection pi D N).1 x : D.1.comap pi) : G) = x := by
      exact congrArg Subtype.val
        (homomorphicLift_above (pi.subgroupComap D.1)
          (MonoidHom.id D.1) (normalSection pi D N) x)
    rw [hs]
    simp only [map_mul, map_inv, hs]
    rfl

variable (N0 : NormalFixedImageComplementFibre pi D)

/-- Difference of two normal complements in the original kernel. -/
private def difference
    (N : NormalFixedImageComplementFibre pi D) (d : D.1) : pi.ker :=
  restrictedKernelEquiv pi D.1
    ⟨(normalSection pi D N).1 d * ((normalSection pi D N0).1 d)⁻¹, by
      apply Subtype.ext
      simp only [map_mul, map_inv, homomorphicLift_above,
        MonoidHom.id_apply, mul_inv_cancel]⟩

private theorem section0_commutes_kernel
    (d : D.1) (k : pi.ker) :
    Commute (((normalSection pi D N0).1 d : D.1.comap pi) : G) (k : G) := by
  apply Subgroup.commute_of_normal_of_disjoint N0.1.1 pi.ker
      N0.1.2 (by infer_instance)
  · rw [disjoint_iff, N0.2.2]
  · exact section_coe_mem pi D N0 d
  · exact k.2

private theorem difference_mul
    (N : NormalFixedImageComplementFibre pi D) (x y : D.1) :
    difference pi D N0 N (x * y) =
      difference pi D N0 N x * difference pi D N0 N y := by
  apply (restrictedKernelEquiv pi D.1).symm.injective
  simp only [map_mul, difference, MulEquiv.symm_apply_apply]
  apply Subtype.ext
  apply Subtype.ext
  change ((((normalSection pi D N).1 x : D.1.comap pi) : G) *
        (((normalSection pi D N).1 y : D.1.comap pi) : G)) *
      ((((normalSection pi D N0).1 x : D.1.comap pi) : G) *
        (((normalSection pi D N0).1 y : D.1.comap pi) : G))⁻¹ =
      ((((normalSection pi D N).1 x : D.1.comap pi) : G) *
        (((normalSection pi D N0).1 x : D.1.comap pi) : G)⁻¹) *
      ((((normalSection pi D N).1 y : D.1.comap pi) : G) *
        (((normalSection pi D N0).1 y : D.1.comap pi) : G)⁻¹)
  have hc := section0_commutes_kernel pi D N0 x
    (difference pi D N0 N y)
  change Commute
    (((normalSection pi D N0).1 x : D.1.comap pi) : G)
    ((((normalSection pi D N).1 y : D.1.comap pi) : G) *
      (((normalSection pi D N0).1 y : D.1.comap pi) : G)⁻¹) at hc
  calc
    _ = (((normalSection pi D N).1 x : D.1.comap pi) : G) *
        ((((normalSection pi D N).1 y : D.1.comap pi) : G) *
          (((normalSection pi D N0).1 y : D.1.comap pi) : G)⁻¹) *
        (((normalSection pi D N0).1 x : D.1.comap pi) : G)⁻¹ := by
      simp only [mul_inv_rev, mul_assoc]
    _ = (((normalSection pi D N).1 x : D.1.comap pi) : G) *
        ((((normalSection pi D N0).1 x : D.1.comap pi) : G)⁻¹ *
          ((((normalSection pi D N).1 y : D.1.comap pi) : G) *
            (((normalSection pi D N0).1 y : D.1.comap pi) : G)⁻¹)) := by
      rw [hc.inv_left.eq]
      simp only [mul_assoc]
    _ = _ := by group

/-- The difference graph as a literal group homomorphism. -/
private def differenceHom
    (N : NormalFixedImageComplementFibre pi D) : D.1 →* pi.ker where
  toFun := difference pi D N0 N
  map_one' := by
    apply (restrictedKernelEquiv pi D.1).symm.injective
    simp only [map_one, difference, MulEquiv.symm_apply_apply]
    apply Subtype.ext
    simp [difference]
  map_mul' := difference_mul pi D N0 N

/-- Additive kernel coordinates of the normal-complement graph. -/
private def coordinateHom
    (N : NormalFixedImageComplementFibre pi D) : Additive D.1 →+ A where
  toFun d := (E.equiv.symm (differenceHom pi D N0 N d.toMul)).toAdd
  map_zero' := by simp [differenceHom, difference]
  map_add' x y := by
    change (E.equiv.symm (differenceHom pi D N0 N (x.toMul * y.toMul))).toAdd = _
    rw [map_mul, map_mul]
    rfl

include hpi in
private theorem coordinateHom_equivariant
    (N : NormalFixedImageComplementFibre pi D)
    (b : B) (d : D.1) :
    coordinateHom p pi A E D N0 N
        (Additive.ofMul (MulAut.conjNormal b d)) =
      A.ρ b (coordinateHom p pi A E D N0 N (Additive.ofMul d)) := by
  obtain ⟨q, rfl⟩ := hpi b
  change (E.equiv.symm
      (differenceHom pi D N0 N (MulAut.conjNormal (pi q) d))).toAdd = _
  apply Multiplicative.ofAdd.injective
  apply E.equiv.injective
  apply Subtype.val_injective
  simp only [ofAdd_toAdd, E.equiv.apply_symm_apply]
  have hcoord : E.equiv
      (Multiplicative.ofAdd
        (coordinateHom p pi A E D N0 N (Additive.ofMul d))) =
      differenceHom pi D N0 N d := by
    change E.equiv
      (Multiplicative.ofAdd
        (E.equiv.symm (differenceHom pi D N0 N d)).toAdd) = _
    rw [ofAdd_toAdd, E.equiv.apply_symm_apply]
  rw [E.conjugate]
  change (((normalSection pi D N).1
      (MulAut.conjNormal (pi q) d) : D.1.comap pi) : G) *
        (((normalSection pi D N0).1
          (MulAut.conjNormal (pi q) d) : D.1.comap pi) : G)⁻¹ = _
  rw [section_conjugate pi D N q d,
    section_conjugate pi D N0 q d]
  rw [hcoord]
  have hdiff : ((differenceHom pi D N0 N d : pi.ker) : G) =
      (((normalSection pi D N).1 d : D.1.comap pi) : G) *
        (((normalSection pi D N0).1 d : D.1.comap pi) : G)⁻¹ := rfl
  rw [hdiff]
  group

/-- The retained normal graph, now in the exact equivariant-Hom space. -/
private def code
    (N : NormalFixedImageComplementFibre pi D) :
    {f : Additive D.1 →+ A // ∀ b d,
      f (Additive.ofMul (MulAut.conjNormal b d)) =
        A.ρ b (f (Additive.ofMul d))} :=
  let _ := hpi
  ⟨coordinateHom p pi A E D N0 N,
    coordinateHom_equivariant p pi hpi A E D N0 N⟩

private theorem code_injective :
    Function.Injective (code p pi hpi A E D N0) := by
  intro N M hNM
  have hcoord : coordinateHom p pi A E D N0 N =
      coordinateHom p pi A E D N0 M := congrArg Subtype.val hNM
  have hsection : normalSection pi D N = normalSection pi D M := by
    apply Subtype.ext
    apply MonoidHom.ext
    intro d
    apply Subtype.ext
    have hd := DFunLike.congr_fun hcoord (Additive.ofMul d)
    have hdiff : differenceHom pi D N0 N d =
        differenceHom pi D N0 M d := by
      apply E.equiv.symm.injective
      exact Multiplicative.toAdd.injective hd
    have hk := congrArg (fun z : pi.ker => (z : G)) hdiff
    change (((normalSection pi D N).1 d : D.1.comap pi) : G) *
        (((normalSection pi D N0).1 d : D.1.comap pi) : G)⁻¹ =
      (((normalSection pi D M).1 d : D.1.comap pi) : G) *
        (((normalSection pi D N0).1 d : D.1.comap pi) : G)⁻¹ at hk
    exact mul_right_cancel hk
  apply Subtype.ext
  apply Subtype.ext
  have hrange := congrArg (fun s : HomomorphicLift
      (pi.subgroupComap D.1) (MonoidHom.id D.1) => s.1.range) hsection
  change (normalSection pi D N).1.range =
    (normalSection pi D M).1.range at hrange
  have hN : (normalSection pi D N).1.range = restrictedSubgroup pi D N := by
    exact SectionSubgroup.section_range _ _
  have hM : (normalSection pi D M).1.range = restrictedSubgroup pi D M := by
    exact SectionSubgroup.section_range _ _
  rw [hN, hM] at hrange
  have hmap := congrArg
    (Subgroup.map (D.1.comap pi).subtype) hrange
  simpa [restrictedSubgroup,
    Subgroup.map_subgroupOf_eq_of_le (subgroup_le_preimage pi D N),
    Subgroup.map_subgroupOf_eq_of_le (subgroup_le_preimage pi D M)] using hmap

end NormalFixedImageComplementFibre

include hpi E in
/-- **Normal-complement graph bound.**  The fixed-image/trivial-intersection
normal fibre is bounded jointly, using the ambient sectional rank before the
quotient and the original kernel representation's Schur capacity. -/
theorem normalFixedImageComplementFibre_card_le
    (D : {D : Subgroup B // D.Normal})
    (r H : ℕ)
    (hRank : PrimeSectionalRankBound p G r)
    (hCapacity : representationSchurCapacity A.ρ ≤ H) :
    Nat.card (NormalFixedImageComplementFibre pi D) ≤ p ^ (H * r) := by
  classical
  by_cases hne : Nonempty (NormalFixedImageComplementFibre pi D)
  · let N0 := Classical.choice hne
    let C := {f : Additive D.1 →+ A // ∀ b d,
      f (Additive.ofMul (MulAut.conjNormal b d)) =
        A.ρ b (f (Additive.ofMul d))}
    letI : Finite (Additive D.1 →+ A) :=
      Finite.of_injective
        (fun f : Additive D.1 →+ A => (f : Additive D.1 → A))
        (by
          intro f g h
          ext d
          exact congrFun h d)
    letI : Finite C :=
      Finite.of_injective Subtype.val Subtype.val_injective
    have hcode : Nat.card (NormalFixedImageComplementFibre pi D) ≤ Nat.card C :=
      Nat.card_le_card_of_injective
        (NormalFixedImageComplementFibre.code p pi hpi A E D N0)
        (NormalFixedImageComplementFibre.code_injective p pi hpi A E D N0)
    have hcongr : Nat.card C = Nat.card
        ((primeAbelianizationRepresentation p (MulAut.conjNormal :
            B →* MulAut D.1)).IntertwiningMap A.ρ) :=
      Nat.card_congr
        (primeEquivariantHomEquiv p
          (MulAut.conjNormal : B →* MulAut D.1) A.ρ)
    have hrankD : Module.finrank (ZMod p)
        (PrimeAbelianization p D.1) ≤ r := by
      change Module.finrank (ZMod p)
        (Module.Dual (ZMod p) (PrimeCharacters p D.1)) ≤ r
      rw [Subspace.dual_finrank_eq]
      exact PrimeSectionalRankBound.quotient_rank_le p hRank (D.1.comap pi)
        (pi.subgroupComap D.1)
        (pi.subgroupComap_surjective_of_surjective D.1 hpi)
    have hfinrank : Module.finrank (ZMod p)
        ((primeAbelianizationRepresentation p (MulAut.conjNormal :
            B →* MulAut D.1)).IntertwiningMap A.ρ) ≤ H * r := by
      have hschur := intertwiningMap_finrank_le_schur
        (primeAbelianizationRepresentation p
          (MulAut.conjNormal : B →* MulAut D.1)) A.ρ
      have hcaprank : representationSchurCapacity A.ρ *
          Module.finrank (ZMod p) (PrimeAbelianization p D.1) ≤
          (H : ℝ) * r := by
        exact mul_le_mul hCapacity (by exact_mod_cast hrankD)
          (by positivity) (by positivity)
      exact_mod_cast hschur.trans hcaprank
    letI : Finite (PrimeAbelianization p D.1 →ₗ[ZMod p] A) :=
      Finite.of_injective
        (fun f : PrimeAbelianization p D.1 →ₗ[ZMod p] A =>
            (f : PrimeAbelianization p D.1 → A))
        (by
          intro f g h
          ext x
          exact congrFun h x)
    letI : Finite
        ((primeAbelianizationRepresentation p (MulAut.conjNormal :
          B →* MulAut D.1)).IntertwiningMap A.ρ) :=
      Finite.of_injective
        (fun f : (primeAbelianizationRepresentation p (MulAut.conjNormal :
          B →* MulAut D.1)).IntertwiningMap A.ρ =>
            (f : PrimeAbelianization p D.1 →ₗ[ZMod p] A))
        (by
          intro f g h
          apply Representation.IntertwiningMap.ext
          exact h)
    letI : Module.Finite (ZMod p)
        ((primeAbelianizationRepresentation p (MulAut.conjNormal :
          B →* MulAut D.1)).IntertwiningMap A.ρ) := Module.Finite.of_finite
    have hcard : Nat.card
        ((primeAbelianizationRepresentation p (MulAut.conjNormal :
          B →* MulAut D.1)).IntertwiningMap A.ρ) =
        p ^ Module.finrank (ZMod p)
          ((primeAbelianizationRepresentation p (MulAut.conjNormal :
            B →* MulAut D.1)).IntertwiningMap A.ρ) := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
    calc
      Nat.card (NormalFixedImageComplementFibre pi D) ≤ Nat.card C := hcode
      _ = p ^ Module.finrank (ZMod p)
          ((primeAbelianizationRepresentation p (MulAut.conjNormal :
            B →* MulAut D.1)).IntertwiningMap A.ρ) := by
        exact hcongr.trans hcard
      _ ≤ p ^ (H * r) := Nat.pow_le_pow_right (Fact.out : p.Prime).one_le hfinrank
  · letI : IsEmpty (NormalFixedImageComplementFibre pi D) :=
      not_nonempty_iff.mp hne
    simp

end SymmetricSubgroupAsymptotics

end
