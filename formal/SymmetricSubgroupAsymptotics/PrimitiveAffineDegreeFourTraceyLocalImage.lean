import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourTraceySubgroup
import SymmetricSubgroupAsymptotics.BinaryPlaneDualOrbit

/-!
# The literal local order-three image of the degree-four Hall subgroup

The odd Hall subgroup constructed in the actual soluble Tracey subgroup
maps onto every coordinate of the correlated ternary core.  Intersecting
with the core of a block stabilizer therefore still maps onto the literal
local `C₃`.  Conversely its local image has odd order, because it is a
quotient of a subgroup of the actual two-complement.  Since the local
complement has order three or six, the image has order exactly three.

This proves the local-dual orbit coefficient in Tracey's formula without
choosing a splitting of the Hall image and without a finite action label.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

/-- The local component of Tracey's literal subgroup
`P'_N ∩ core_N(H)`. -/
def degreeFourTraceyLocalHom
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hs : 2 ≤ Nat.card block.Points)
    (i : block.Points)
    (P₂ : Subgroup (degreeFourTraceySubgroup block P hTraceyPerm hs)) :
    traceyPrimeToCoreSubgroup i
        (degreeFourTraceySubgroup block P hTraceyPerm hs) P₂ →*
      LocalQuotient block P :=
  (localMap block P).comp
    ((ActualWreathAffineCapacity.stabilizerComponent
      (initialState hTraceyPerm block) i).comp
        (traceyPrimeToCoreSubgroup i
          (degreeFourTraceySubgroup block P hTraceyPerm hs) P₂).subtype)

/-- The actual Hall-image containment makes the preceding local map cover
all of the literal local ternary subgroup. -/
theorem degreeFourTraceyLocalHom_hits_ternary
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 4)
    (hs : 2 ≤ Nat.card block.Points)
    (hD : degreeFourTernaryCore block P ≠ ⊥)
    (P₂ : Subgroup (degreeFourTraceySubgroup block P hTraceyPerm hs))
    (hHall :
      (degreeFourTraceyCoreSubgroup block P hTraceyPerm hs).map
          (QuotientGroup.mk'
            (degreeFourTraceyTranslationSubgroup
              block P hTraceyPerm hs)) ≤
        P₂.map
          (QuotientGroup.mk'
            (degreeFourTraceyTranslationSubgroup
              block P hTraceyPerm hs)))
    (i : block.Points)
    (dloc : (degreeFourLocalBinarySign block P).ker) :
    ∃ l : traceyPrimeToCoreSubgroup i
        (degreeFourTraceySubgroup block P hTraceyPerm hs) P₂,
      degreeFourTraceyLocalHom block P hTraceyPerm hs i P₂ l = dloc.1 := by
  let A := preE7NonPairAction w U
  let S := initialState hTraceyPerm block
  let N := degreeFourTraceySubgroup block P hTraceyPerm hs
  let E0 := E block P
  let B := degreeFourTernaryPreimage block P
  let EN := degreeFourTraceyTranslationSubgroup block P hTraceyPerm hs
  let BN := degreeFourTraceyCoreSubgroup block P hTraceyPerm hs
  obtain ⟨d, hd⟩ :=
    degreeFourTernaryCoordinate_surjective block P hr hD i dloc
  obtain ⟨b, hb⟩ := QuotientGroup.mk'_surjective E0 d.1
  have hbB : b ∈ B := by
    change QuotientGroup.mk' E0 b ∈ degreeFourTernaryCore block P
    simpa only [hb] using d.2
  have hbN : b ∈ N :=
    (show B ≤ N from le_sup_left) hbB
  let bN : BN := ⟨⟨b, hbN⟩, hbB⟩
  have hbHall : QuotientGroup.mk' EN bN.1 ∈
      P₂.map (QuotientGroup.mk' EN) :=
    hHall ⟨bN.1, bN.2, rfl⟩
  obtain ⟨pN, hpP, hpq⟩ := hbHall
  let p : A := pN.1
  have hpdivEN : pN / bN.1 ∈ EN := by
    apply QuotientGroup.eq_iff_div_mem.mp
    exact hpq
  have hpdivE : p / b ∈ E0 := by
    exact hpdivEN
  have hbker : b ∈ block.topMap.ker := by
    apply MonoidHom.mem_ker.mpr
    have hbRight : (ambientEmbedding block b).right = 1 := by
      have htop : (quotientEmbedding block P d.1).right = 1 :=
        MonoidHom.mem_ker.mp
          (degreeFourTernaryCore_le_blockKernel block P d.2)
      rw [← hb] at htop
      exact htop
    simpa only [ambientEmbedding, ActualBlockWreathEmbedding.embedding]
      using congrArg Subtype.val hbRight
  have hpker : p ∈ block.topMap.ker := by
    apply MonoidHom.mem_ker.mpr
    have hdiv := MonoidHom.mem_ker.mp
      (degreeFive_translationIntersection_le_topMap_ker block P hpdivE)
    have hbtop := MonoidHom.mem_ker.mp hbker
    rw [map_div, hbtop, div_one] at hdiv
    exact hdiv
  have hker_le_stabilizer : block.topMap.ker ≤
      MulAction.stabilizer A i := by
    intro g hg
    change g • i = i
    have hperm := congrArg (fun q : Equiv.Perm block.Points ↦ q i)
      (MonoidHom.mem_ker.mp hg)
    simpa only [Equiv.Perm.one_apply] using hperm
  have hpCore : p ∈ (MulAction.stabilizer A i).normalCore :=
    (Subgroup.normal_le_normalCore.mpr hker_le_stabilizer) hpker
  let pStab : MulAction.stabilizer A i :=
    ⟨p, (MulAction.stabilizer A i).normalCore_le hpCore⟩
  have hpImage : p ∈ P₂.map N.subtype := ⟨pN, hpP, rfl⟩
  let l : traceyPrimeToCoreSubgroup i N P₂ :=
    ⟨pStab, ⟨hpImage, hpCore⟩⟩
  refine ⟨l, ?_⟩
  have hpClass : QuotientGroup.mk' E0 p = QuotientGroup.mk' E0 b :=
    QuotientGroup.eq_iff_div_mem.mpr hpdivE
  have hleft := congrArg
    (fun q : DegreeFourComplementQuotient block P ↦
      (quotientEmbedding block P q).left i) hpClass
  change localMap block P ((ambientEmbedding block p).left i) = dloc.1
  calc
    localMap block P ((ambientEmbedding block p).left i) =
        (quotientEmbedding block P (QuotientGroup.mk' E0 p)).left i := rfl
    _ = (quotientEmbedding block P (QuotientGroup.mk' E0 b)).left i := hleft
    _ = degreeFourTernaryCoordinate block P i d := by rw [hb]; rfl
    _ = dloc.1 := congrArg Subtype.val hd

omit [Nontrivial block.Fibre] in
/-- The local image injects into the actual Hall subgroup on cardinalities.
This is the only fact needed to retain oddness. -/
theorem degreeFourTraceyLocalHom_range_card_dvd_complement
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hs : 2 ≤ Nat.card block.Points)
    (i : block.Points)
    (P₂ : Subgroup (degreeFourTraceySubgroup block P hTraceyPerm hs)) :
    Nat.card (degreeFourTraceyLocalHom block P hTraceyPerm hs i P₂).range ∣
      Nat.card P₂ := by
  let N := degreeFourTraceySubgroup block P hTraceyPerm hs
  let L := traceyPrimeToCoreSubgroup i N P₂
  let j : L →* P₂.map N.subtype := {
    toFun := fun l ↦ ⟨l.1.1, l.2.1⟩
    map_one' := by ext; rfl
    map_mul' := by intro x y; ext; rfl }
  have hj : Function.Injective j := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg
      (fun z : P₂.map N.subtype ↦
        (z : preE7NonPairAction w U)) hxy
  exact (Subgroup.card_range_dvd
    (degreeFourTraceyLocalHom block P hTraceyPerm hs i P₂)).trans
      ((Subgroup.card_dvd_of_injective j hj).trans
        (P₂.card_map_dvd N.subtype))

/-- The literal local image has order exactly three. -/
theorem degreeFourTraceyLocalHom_range_card
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 4)
    (hs : 2 ≤ Nat.card block.Points)
    (hD : degreeFourTernaryCore block P ≠ ⊥)
    (P₂ : Subgroup (degreeFourTraceySubgroup block P hTraceyPerm hs))
    (hP₂ : IsTwoComplement P₂)
    (hHall :
      (degreeFourTraceyCoreSubgroup block P hTraceyPerm hs).map
          (QuotientGroup.mk'
            (degreeFourTraceyTranslationSubgroup
              block P hTraceyPerm hs)) ≤
        P₂.map
          (QuotientGroup.mk'
            (degreeFourTraceyTranslationSubgroup
              block P hTraceyPerm hs)))
    (i : block.Points) :
    Nat.card (degreeFourTraceyLocalHom block P hTraceyPerm hs i P₂).range = 3 := by
  let f := degreeFourTraceyLocalHom block P hTraceyPerm hs i P₂
  have hlower : 3 ≤ Nat.card f.range := by
    let j : (degreeFourLocalBinarySign block P).ker →* f.range := {
      toFun := fun d ↦ ⟨d.1, by
        obtain ⟨l, hl⟩ := degreeFourTraceyLocalHom_hits_ternary
          block P hTraceyPerm hr hs hD P₂ hHall i d
        exact ⟨l, hl⟩⟩
      map_one' := by ext; rfl
      map_mul' := by intro x y; ext; rfl }
    have hj : Function.Injective j := by
      intro x y hxy
      apply Subtype.ext
      exact congrArg
        (fun z : f.range ↦ (z : LocalQuotient block P)) hxy
    rw [← degreeFourLocalBinarySign_ker_card block P hr]
    exact Nat.card_le_card_of_injective j hj
  have hodd : ¬ 2 ∣ Nat.card f.range := by
    intro htwo
    have hdvdP : Nat.card f.range ∣ Nat.card P₂ :=
      degreeFourTraceyLocalHom_range_card_dvd_complement
        block P hTraceyPerm hs i P₂
    have : 2 ∣ Nat.card P₂ := htwo.trans hdvdP
    rw [hP₂] at this
    exact Nat.not_dvd_ordCompl Nat.prime_two
      (Nat.card_pos (α := degreeFourTraceySubgroup
        block P hTraceyPerm hs)).ne' this
  have hlocal : Nat.card (LocalQuotient block P) = 3 ∨
      Nat.card (LocalQuotient block P) = 6 := by
    have hcard : Nat.card (LocalQuotient block P) =
        Nat.card (P.complement (origin block)) :=
      Nat.card_congr (degreeFiveLocalComplementEquiv block P).symm.toEquiv
    simpa only [hcard] using
      degreeFour_complement_card_eq_three_or_six block P hr
  have hdvdLocal : Nat.card f.range ∣ Nat.card (LocalQuotient block P) :=
    f.range.card_subgroup_dvd_card
  change Nat.card f.range = 3
  rcases hlocal with hlocal | hlocal
  · have hupp : Nat.card f.range ≤ 3 := by
      exact Nat.le_of_dvd (by norm_num) (by simpa only [hlocal] using hdvdLocal)
    exact Nat.le_antisymm hupp hlower
  · have hupp : Nat.card f.range ≤ 6 := by
      exact Nat.le_of_dvd (by norm_num) (by simpa only [hlocal] using hdvdLocal)
    interval_cases h : Nat.card f.range
    · omega
    · exfalso
      apply hodd
      norm_num [h]
    · exfalso
      have hnot : ¬ 5 ∣ 6 := by norm_num
      apply hnot
      simpa only [h, hlocal] using hdvdLocal
    · exfalso
      apply hodd
      norm_num [h]

/-- The exact actual local representation factors through the displayed
order-three image. -/
theorem degreeFourTraceyLocalRepresentation_factor
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hs : 2 ≤ Nat.card block.Points)
    (i : block.Points)
    (P₂ : Subgroup (degreeFourTraceySubgroup block P hTraceyPerm hs)) :
    let S := initialState hTraceyPerm block
    let C := localTranslationChart block P
    let f := degreeFourTraceyLocalHom block P hTraceyPerm hs i P₂
    let sigma : Representation (ZMod C.p) f.range C.V :=
      (CliffordHomogeneousRestriction.localRepresentation
        S (localMap block P) (localMap_surjective block P) C).ρ.comp
          f.range.subtype
    (ActualWreathAffineCapacity.localRepresentation
        S (localMap block P) C i).comp
          (traceyPrimeToCoreSubgroup i
            (degreeFourTraceySubgroup block P hTraceyPerm hs) P₂).subtype =
      sigma.comp f.rangeRestrict := by
  let S := initialState hTraceyPerm block
  let C := localTranslationChart block P
  let f := degreeFourTraceyLocalHom block P hTraceyPerm hs i P₂
  let eps := CliffordHomogeneousRestriction.localQuotientEquiv
    S (localMap block P) (localMap_surjective block P)
  apply MonoidHom.ext
  intro l
  apply LinearMap.ext
  intro v
  let d := ActualWreathAffineCapacity.stabilizerComponent S i l.1
  have hclass : eps.symm (localMap block P d) =
      QuotientGroup.mk' (localMap block P).ker d := by
    apply eps.injective
    rw [eps.apply_symm_apply]
    rfl
  change C.quotientRepresentation.ρ
      (QuotientGroup.mk' (localMap block P).ker d) v =
    C.quotientRepresentation.ρ
      (eps.symm (localMap block P d)) v
  rw [hclass]

/-- The prime-indexed form of Tracey's local dual-orbit count.  Keeping the
prime as an explicit binder lets the degree-four proof specialize it to two
without transporting a representation whose scalar field carries dependent
typeclass data. -/
def primeTraceyLocalDualOrbitCount
    {p : ℕ} [Fact p.Prime]
    {G I V : Type} [Group G] [MulAction G I]
    [AddCommGroup V] [Module (ZMod p) V]
    (i : I)
    (rho : Representation (ZMod p) (MulAction.stabilizer G i) V)
    (N : Subgroup G) (P : Subgroup N) : ℕ :=
  Nat.card (Quotient (representationNonzeroOrbitRel
    (rho.dual.comp (traceyPrimeToCoreSubgroup i N P).subtype)))

/-- The binary-plane quotient theorem with the characteristic retained as
an explicit binder until the final specialization. -/
theorem primeTraceyLocalDualOrbitCount_eq_one_of_surjective_three_quotient
    {p : ℕ} [Fact p.Prime]
    {G I V C : Type} [Group G] [MulAction G I]
    [AddCommGroup V] [Module (ZMod p) V]
    [FiniteDimensional (ZMod p) V]
    [Group C] [Finite C]
    (hp : p = 2)
    (i : I)
    (rho : Representation (ZMod p) (MulAction.stabilizer G i) V)
    (N : Subgroup G) (P : Subgroup N)
    (sigma : Representation (ZMod p) C V)
    (f : traceyPrimeToCoreSubgroup i N P →* C)
    (hf : Function.Surjective f)
    (hC : Nat.card C = 3)
    (hdim : Module.finrank (ZMod p) V = 2)
    (hsigma : Function.Injective sigma)
    (hfactor : rho.comp
        (traceyPrimeToCoreSubgroup i N P).subtype = sigma.comp f) :
    primeTraceyLocalDualOrbitCount i rho N P = 1 := by
  subst p
  simpa only [primeTraceyLocalDualOrbitCount,
    traceyLocalDualOrbitCount] using
      traceyLocalDualOrbitCount_eq_one_of_surjective_three_quotient
        i rho N P sigma f hf hC hdim hsigma hfactor

set_option maxHeartbeats 800000 in
/-- Consequently Tracey's literal local-dual coefficient is one.

The comparison unfolds the two quotient representations through the
surjective local map.  Keep the enlarged heartbeat budget local to this
single definitional comparison; the surrounding module retains Lean's
default budget. -/
theorem degreeFourTraceyLocalDualOrbitCount_eq_one
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 4)
    (hs : 2 ≤ Nat.card block.Points)
    (hD : degreeFourTernaryCore block P ≠ ⊥)
    (P₂ : Subgroup (degreeFourTraceySubgroup block P hTraceyPerm hs))
    (hP₂ : IsTwoComplement P₂)
    (hHall :
      (degreeFourTraceyCoreSubgroup block P hTraceyPerm hs).map
          (QuotientGroup.mk'
            (degreeFourTraceyTranslationSubgroup
              block P hTraceyPerm hs)) ≤
        P₂.map
          (QuotientGroup.mk'
            (degreeFourTraceyTranslationSubgroup
              block P hTraceyPerm hs)))
    (i : block.Points) :
    let S := initialState hTraceyPerm block
    let C := localTranslationChart block P
    primeTraceyLocalDualOrbitCount i
      (ActualWreathAffineCapacity.localRepresentation
        S (localMap block P) C i)
      (degreeFourTraceySubgroup block P hTraceyPerm hs) P₂ = 1 := by
  let S := initialState hTraceyPerm block
  let C := localTranslationChart block P
  let f := degreeFourTraceyLocalHom block P hTraceyPerm hs i P₂
  let sigma : Representation (ZMod C.p) f.range C.V :=
    (CliffordHomogeneousRestriction.localRepresentation
      S (localMap block P) (localMap_surjective block P) C).ρ.comp
        f.range.subtype
  have hp : C.p = 2 := by
    simpa only [C, localTranslationChart] using
      degreeFour_profilePrime_eq_two block P hr
  have hdim : Module.finrank (ZMod C.p) C.V = 2 := by
    let C0 := chart block P
    letI : Finite C0.V := Finite.of_injective
      (fun v : C0.V ↦ C0.equiv.symm (Multiplicative.ofAdd v))
      C0.equiv.symm.injective
    have hdegree : 4 = P.p ^ C0.d := by
      rw [← hr]
      simpa [PrimitiveAffineProfile.ElementaryChart.d] using
        P.degree_eq_prime_pow_finrank C0.equiv (origin block)
    have hd0 : C0.d = 2 :=
      (prime_pow_positive_injective (d := C0.d) (e := 2)
        P.p_prime Nat.prime_two C0.d_pos (by norm_num)
        (hdegree.symm.trans (by norm_num))).2
    simpa only [C, C0, localTranslationChart,
      PrimitiveAffineProfile.ElementaryChart.d] using hd0
  have hlocalRep :
      (CliffordHomogeneousRestriction.localRepresentation
        S (localMap block P) (localMap_surjective block P) C).ρ =
        (degreeFiveLocalLinearRepresentation block P).ρ := by
    let eps := CliffordHomogeneousRestriction.localQuotientEquiv
      S (localMap block P) (localMap_surjective block P)
    apply MonoidHom.ext
    intro q
    apply LinearMap.ext
    intro v
    obtain ⟨d, hd⟩ := localMap_surjective block P q
    have hclass : eps.symm q =
        QuotientGroup.mk' (localMap block P).ker d := by
      apply eps.injective
      rw [eps.apply_symm_apply]
      exact hd.symm
    change C.quotientRepresentation.ρ (eps.symm q) v =
      (degreeFiveLocalLinearRepresentation block P).ρ q v
    rw [hclass, ← hd]
    exact (degreeFiveLocalLinearRepresentation_apply_localMap
      block P hTraceyPerm d v).symm
  have hsigma : Function.Injective sigma := by
    change Function.Injective
      ((CliffordHomogeneousRestriction.localRepresentation
        S (localMap block P) (localMap_surjective block P) C).ρ.comp
          f.range.subtype)
    rw [hlocalRep]
    exact (degreeFiveLocalLinearRepresentation_injective block P).comp
      f.range.subtype_injective
  apply primeTraceyLocalDualOrbitCount_eq_one_of_surjective_three_quotient
    hp i (ActualWreathAffineCapacity.localRepresentation
      S (localMap block P) C i)
    (degreeFourTraceySubgroup block P hTraceyPerm hs) P₂
    sigma f.rangeRestrict f.rangeRestrict_surjective
    (degreeFourTraceyLocalHom_range_card
      block P hTraceyPerm hr hs hD P₂ hP₂ hHall i)
    hdim hsigma
  exact degreeFourTraceyLocalRepresentation_factor
    block P hTraceyPerm hs i P₂

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
