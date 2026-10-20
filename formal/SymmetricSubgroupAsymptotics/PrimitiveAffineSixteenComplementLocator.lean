import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenCanonicalCatalogue
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenLiteralComplements
import SymmetricSubgroupAsymptotics.FaithfulFiniteActionImage
import SymmetricSubgroupAsymptotics.PrimitiveAffineMediumOddSource

/-! The degree16 small-affine complement locator is a consequence of the
already-retained full primitive degree16 correspondence. Every complement
is transported through the actual point chart; natural rows are excluded
by the elementary faithful affine order bound. This is a dependency
reduction, and the retained correspondence keeps its original C scope. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical Pointwise
attribute [local instance] Fintype.ofFinite
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenComplementLocator
open Non2UnipotentPrefixFiniteMenu

private def stabilizerChart
    {G X : Type} [Group G] [MulAction G X]
    (T : Subgroup (Equiv.Perm (Fin 16)))
    (eG : G ≃* T) (eX : X ≃ Fin 16)
    (hact : ∀ g x,(eG g).val (eX x)=eX (g • x)) :
    MulAction.stabilizer G (eX.symm 0) ≃* MulAction.stabilizer T (0 : Fin 16) where
  toFun g := ⟨eG g.val,by
    have h := hact g.val (eX.symm 0)
    rw [Equiv.apply_symm_apply] at h
    change (eG g.val).val 0=0
    have hg : g.val • eX.symm 0=eX.symm 0 := g.property
    rw [hg,Equiv.apply_symm_apply] at h
    exact h⟩
  invFun g := ⟨eG.symm g.val,by
    apply eX.injective
    have h := hact (eG.symm g.val) (eX.symm 0)
    rw [MulEquiv.apply_symm_apply,Equiv.apply_symm_apply] at h
    have hg : g.val.val 0=0 := g.property
    exact h.symm.trans (hg.trans (eX.apply_symm_apply 0).symm)⟩
  left_inv g := Subtype.ext (eG.symm_apply_apply g.val)
  right_inv g := Subtype.ext (eG.apply_symm_apply g.val)
  map_mul' g h := Subtype.ext (eG.map_mul g.val h.val)

private theorem affine_card_le_sixteen_fifth
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [Nontrivial X]
    (P : PrimitiveAffineProfile G X) (hp : MulAction.IsPreprimitive G X)
    (x : X) (hX : Nat.card X=16) : Nat.card G ≤ 1048576 := by
  let C := P.elementaryChart hp
  letI : Fact P.p.Prime := C.primeFact
  letI : AddCommGroup C.V := C.addCommGroup
  letI : Module (ZMod P.p) C.V := C.module
  letI : FiniteDimensional (ZMod P.p) C.V := C.finiteDimensional
  letI : Finite C.V := Finite.of_injective
    (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v)) C.equiv.symm.injective
  have hpower : P.p^C.d=2^4 := by
    simpa only [hX] using (P.degree_eq_prime_pow_finrank C.equiv x).symm
  have hd : C.d=4 :=
    (prime_pow_positive_injective P.p_prime Nat.prime_two C.d_pos (by decide) hpower).2
  have hb := P.card_le_degree_pow_finrank_succ C.equiv x
  change Nat.card G ≤ Nat.card X^(C.d+1) at hb
  simpa only [hX,hd] using hb

/-- No new degree16 classification premise: this is deduced from the
retained actual full primitive-degree correspondence. -/
theorem catalogue_locator
    (published : PrimitiveSixteenCanonicalCatalogue.PublishedClassification)
    {G X : Type} [Group G] [Finite G] [Fintype X] [MulAction G X]
    [FaithfulSMul G X] (hp : MulAction.IsPreprimitive G X)
    (P : PrimitiveAffineProfile G X) (x : X) (hX : Nat.card X=16) :
    ∃ r : SmallAffineCatalogueRow,r.degree=Nat.card X ∧
      Nonempty (P.complement x ≃* (SmallAffineCanonicalRepresentatives.representative r).Carrier) := by
  letI : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by rw [hX]; decide)
  let points : X ≃ Fin 16 := Finite.equivFinOfCardEq hX
  let S := labelledActionImage (A := G) points
  have hS : MulAction.IsPreprimitive S (Fin 16) :=
    (labelledAction_preprimitive_iff points).mp hp
  obtain ⟨j,g,hg⟩ := PrimitiveSixteenCanonicalCatalogue.originalClassification published S hS
  let eG : G ≃* PrimitiveAffineSixteenAllLiteralFrames.top j :=
    (faithfulLabelledActionEquiv points).trans (actionConjugacyEquiv g hg)
  let eX : X ≃ Fin 16 := points.trans g
  have hact : ∀ a y,(eG a).val (eX y)=eX (a • y) := by
    intro a y
    change g (labelledActionHom points a (g.symm (g (points y))))=g (points (a • y))
    rw [g.symm_apply_apply,labelledActionHom_apply]
  have hb := affine_card_le_sixteen_fifth P hp x hX
  have hj : j.val<20 := by
    by_contra hj
    have hj' : j.val=20 ∨ j.val=21 := by have := j.isLt; omega
    have hc := Nat.card_congr eG.toEquiv
    rcases hj' with h | h
    · have he : j=⟨20,by decide⟩ := Fin.ext h
      rw [he] at hc
      change Nat.card G=Nat.card (alternatingGroup (Fin 16)) at hc
      have hn : 1048576 < Nat.card (alternatingGroup (Fin 16)) := by
        rw [nat_card_alternatingGroup,Nat.card_fin]
        decide +kernel
      exact (not_lt_of_ge hb) (hn.trans_eq hc.symm)
    · have he : j=⟨21,by decide⟩ := Fin.ext h
      rw [he] at hc
      change Nat.card G=Nat.card (⊤ : Subgroup (Equiv.Perm (Fin 16))) at hc
      have hn : 1048576 < Nat.card (⊤ : Subgroup (Equiv.Perm (Fin 16))) := by
        rw [Subgroup.card_top,Nat.card_perm,Nat.card_fin]
        decide +kernel
      exact (not_lt_of_ge hb) (hn.trans_eq hc.symm)
  let i : Fin 20 := ⟨j.val,hj⟩
  let y := eX.symm 0
  obtain ⟨v,hv,_⟩ := P.regular x y
  let exy : P.complement x ≃* P.complement y :=
    MulAction.stabilizerEquivStabilizer (G := G) (g := (v : G)) hv.symm
  let eH := stabilizerChart (PrimitiveAffineSixteenAllLiteralFrames.top j) eG eX hact
  have eLiteral : MulAction.stabilizer (PrimitiveAffineSixteenAllLiteralFrames.top j) (0 : Fin 16) ≃*
      (SmallAffineCanonicalRepresentatives.degreeSixteen i).Carrier := by
    exact PrimitiveAffineSixteenLiteralComplements.complement i
  exact ⟨.degreeSixteen i,hX.symm,⟨exy.trans (eH.trans eLiteral)⟩⟩

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenComplementLocator
