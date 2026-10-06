import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockSignedIsotypeSplit
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockTwoSignStructural

/-!
# Literal structure of the two-sign four-block branch

The two-sign branch is already defined from the four actual coordinate
characters of the retained pair kernel.  This file extracts the elementary
finite-group consequences of that definition.

* neither of the two realized characters is zero;
* evaluation at one coordinate in each sign class identifies the complete
  pair kernel with `C₂ × C₂`;
* the actual four-point top is a transitive two-subgroup of `S₄`, hence has
  order four or eight;
* consequently the literal signed quotient has order sixteen or thirty-two.

No action catalogue, abstract replacement group, or independently chosen
character list occurs.  The equivalence with `C₂ × C₂` is built from the
two coordinate characters of the original physical pair frame.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

private abbrev C2 := Multiplicative (ZMod 2)

/-! ## Two independent binary characters -/

/-- Two distinct nontrivial binary characters jointly map onto `C₂²`.

This is the small algebraic fact used below.  It is stated for arbitrary
groups so the proof does not smuggle in an elementary-abelian model for the
source. -/
theorem c2_character_prod_surjective_of_ne_one_of_ne
    {G : Type*} [Group G]
    (chi psi : G →* C2)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1) (hne : chi ≠ psi) :
    Function.Surjective (chi.prod psi) := by
  have hchiWitness : ∃ x : G, chi x ≠ 1 := by
    by_contra h
    push Not at h
    apply hchi
    ext x
    simpa using h x
  have hpsiWitness : ∃ x : G, psi x ≠ 1 := by
    by_contra h
    push Not at h
    apply hpsi
    ext x
    simpa using h x
  have hdiff : ∃ x : G, chi x ≠ psi x := by
    by_contra h
    push Not at h
    exact hne (MonoidHom.ext h)
  obtain ⟨z, hz⟩ := hdiff
  have hbasis :
      (∃ a : G, chi a = C2Wreath.gen ∧ psi a = 1) ∧
        ∃ b : G, chi b = 1 ∧ psi b = C2Wreath.gen := by
    rcases C2Wreath.cases (chi z) with hzchi | hzchi <;>
      rcases C2Wreath.cases (psi z) with hzpsi | hzpsi
    · exact (hz (hzchi.trans hzpsi.symm)).elim
    · obtain ⟨x, hx⟩ := hchiWitness
      have hxchi : chi x = C2Wreath.gen :=
        (C2Wreath.cases (chi x)).resolve_left hx
      rcases C2Wreath.cases (psi x) with hxpsi | hxpsi
      · exact ⟨⟨x, hxchi, hxpsi⟩, ⟨z, hzchi, hzpsi⟩⟩
      · refine ⟨⟨x * z, ?_, ?_⟩, ⟨z, hzchi, hzpsi⟩⟩
        · rw [map_mul, hxchi, hzchi, mul_one]
        · rw [map_mul, hxpsi, hzpsi, C2Wreath.gen_mul_gen]
    · obtain ⟨x, hx⟩ := hpsiWitness
      have hxpsi : psi x = C2Wreath.gen :=
        (C2Wreath.cases (psi x)).resolve_left hx
      rcases C2Wreath.cases (chi x) with hxchi | hxchi
      · exact ⟨⟨z, hzchi, hzpsi⟩, ⟨x, hxchi, hxpsi⟩⟩
      · refine ⟨⟨z, hzchi, hzpsi⟩, ⟨z * x, ?_, ?_⟩⟩
        · rw [map_mul, hzchi, hxchi, C2Wreath.gen_mul_gen]
        · rw [map_mul, hzpsi, hxpsi, one_mul]
    · exact (hz (hzchi.trans hzpsi.symm)).elim
  obtain ⟨⟨a, hachi, hapsi⟩, ⟨b, hbchi, hbpsi⟩⟩ := hbasis
  intro q
  rcases C2Wreath.cases q.1 with hqchi | hqchi <;>
    rcases C2Wreath.cases q.2 with hqpsi | hqpsi
  · refine ⟨1, ?_⟩
    apply Prod.ext <;> simp [hqchi, hqpsi]
  · refine ⟨b, ?_⟩
    apply Prod.ext <;> simp [hbchi, hbpsi, hqchi, hqpsi]
  · refine ⟨a, ?_⟩
    apply Prod.ext <;> simp [hachi, hapsi, hqchi, hqpsi]
  · refine ⟨a * b, ?_⟩
    apply Prod.ext <;>
      simp [map_mul, hachi, hapsi, hbchi, hbpsi, hqchi, hqpsi]

namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace BinaryPairFrame

variable {X : Type} {G : Subgroup (Equiv.Perm X)}

/-- The literal coordinate bit, regarded as a multiplicative binary
character of the complete pair kernel. -/
def fourCoordinateSignHom
    (F : BinaryPairFrame G (Fin 4)) (i : Fin 4) : F.top.ker →* C2 where
  toFun k := Multiplicative.ofAdd (F.bits k i)
  map_one' := by
    change Multiplicative.ofAdd ((F.bitsHom 1).toAdd i) = 1
    rw [map_one]
    rfl
  map_mul' a b := by
    change Multiplicative.ofAdd ((F.bitsHom (a * b)).toAdd i) =
      Multiplicative.ofAdd ((F.bitsHom a).toAdd i) *
        Multiplicative.ofAdd ((F.bitsHom b).toAdd i)
    rw [map_mul]
    rfl

/-- In the two-sign case, no realized coordinate character is zero.

Indeed zero is fixed under precomposition by conjugation.  Transitivity of
the actual four-point top would therefore make all four characters zero,
contradicting the existence of two sign classes. -/
theorem fourCoordinateSignFunction_ne_zero_of_count_eq_two
    (F : BinaryPairFrame G (Fin 4))
    (htrans : MulAction.IsPretransitive G X)
    (htwo : Nat.card (FourCoordinateSign F) = 2)
    (i : Fin 4) :
    fourCoordinateSignFunction F i ≠ 0 := by
  intro hi
  letI : MulAction.IsPretransitive G X := htrans
  letI : MulAction.IsPretransitive F.top.range (Fin 4) := F.top_pretransitive
  have hall : ∀ j : Fin 4, fourCoordinateSign F j = fourCoordinateSign F i := by
    intro j
    obtain ⟨t, ht⟩ := MulAction.exists_smul_eq F.top.range i j
    obtain ⟨u, rfl⟩ := F.top.rangeRestrict_surjective t
    have htop : F.top u i = j := by simpa using ht
    rw [← htop]
    apply Subtype.ext
    funext k
    change F.bits k (F.top u i) = F.bits k i
    have hleft : F.bits k (F.top u i) = 0 := by
      have hconj := F.bits_conjNormal u⁻¹ k i
      simpa only [map_inv, inv_inv] using hconj.symm.trans
        (congrFun hi (MulAut.conjNormal u⁻¹ k))
    exact hleft.trans (congrFun hi k).symm
  have hone : Nat.card (FourCoordinateSign F) = 1 := by
    apply Nat.card_eq_one_iff_unique.mpr
    refine ⟨?_, ⟨fourCoordinateSign F i⟩⟩
    constructor
    intro chi psi
    obtain ⟨j, rfl⟩ := fourCoordinateSign_surjective F chi
    obtain ⟨k, rfl⟩ := fourCoordinateSign_surjective F psi
    exact (hall j).trans (hall k).symm
  omega

/-- A realized nonzero coordinate function gives a nontrivial binary
character of the literal kernel. -/
theorem fourCoordinateSignHom_ne_one_of_function_ne_zero
    (F : BinaryPairFrame G (Fin 4)) (i : Fin 4)
    (hi : fourCoordinateSignFunction F i ≠ 0) :
    fourCoordinateSignHom F i ≠ 1 := by
  intro h
  apply hi
  funext k
  have hk := DFunLike.congr_fun h k
  change Multiplicative.ofAdd (F.bits k i) = 1 at hk
  exact congrArg Multiplicative.toAdd hk

/-- Choose one literal coordinate over each of the two realized sign
classes. -/
noncomputable def twoSignCoordinate
    (F : BinaryPairFrame G (Fin 4))
    (htwo : Nat.card (FourCoordinateSign F) = 2)
    (a : Fin 2) : Fin 4 :=
  Classical.choose (fourCoordinateSign_surjective F
    ((Finite.equivFinOfCardEq htwo).symm a))

@[simp] theorem fourCoordinateSign_twoSignCoordinate
    (F : BinaryPairFrame G (Fin 4))
    (htwo : Nat.card (FourCoordinateSign F) = 2)
    (a : Fin 2) :
    fourCoordinateSign F (twoSignCoordinate F htwo a) =
      (Finite.equivFinOfCardEq htwo).symm a :=
  Classical.choose_spec (fourCoordinateSign_surjective F
    ((Finite.equivFinOfCardEq htwo).symm a))

/-- Evaluation on the two actual sign classes. -/
def twoSignKernelHom
    (F : BinaryPairFrame G (Fin 4))
    (htwo : Nat.card (FourCoordinateSign F) = 2) :
    F.top.ker →* C2 × C2 :=
  (fourCoordinateSignHom F (twoSignCoordinate F htwo 0)).prod
    (fourCoordinateSignHom F (twoSignCoordinate F htwo 1))

private theorem fourCoordinateSign_eq_first_or_second
    (F : BinaryPairFrame G (Fin 4))
    (htwo : Nat.card (FourCoordinateSign F) = 2)
    (i : Fin 4) :
    fourCoordinateSign F i =
        fourCoordinateSign F (twoSignCoordinate F htwo 0) ∨
      fourCoordinateSign F i =
        fourCoordinateSign F (twoSignCoordinate F htwo 1) := by
  let e : FourCoordinateSign F ≃ Fin 2 := Finite.equivFinOfCardEq htwo
  have hle : (e (fourCoordinateSign F i)).val ≤ 1 := by omega
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with hzero | hone
  · left
    apply e.injective
    simpa only [e, fourCoordinateSign_twoSignCoordinate, Equiv.apply_symm_apply]
      using Fin.ext hzero
  · right
    apply e.injective
    simpa only [e, fourCoordinateSign_twoSignCoordinate, Equiv.apply_symm_apply]
      using Fin.ext hone

/-- The two literal coordinate characters jointly separate the complete
pair kernel.  This uses `bitsHom_injective`, so every correlation present
in the original physical kernel is retained. -/
theorem twoSignKernelHom_injective
    (F : BinaryPairFrame G (Fin 4))
    (htwo : Nat.card (FourCoordinateSign F) = 2) :
    Function.Injective (twoSignKernelHom F htwo) := by
  intro x y hxy
  apply F.bitsHom_injective
  apply congrArg Multiplicative.ofAdd
  funext i
  have h0 := congrArg Prod.fst hxy
  have h1 := congrArg Prod.snd hxy
  change Multiplicative.ofAdd
      (F.bits x (twoSignCoordinate F htwo 0)) =
    Multiplicative.ofAdd
      (F.bits y (twoSignCoordinate F htwo 0)) at h0
  change Multiplicative.ofAdd
      (F.bits x (twoSignCoordinate F htwo 1)) =
    Multiplicative.ofAdd
      (F.bits y (twoSignCoordinate F htwo 1)) at h1
  rcases fourCoordinateSign_eq_first_or_second F htwo i with hi | hi
  · have hfun := congrArg Subtype.val hi
    have hx := congrFun hfun x
    have hy := congrFun hfun y
    exact hx.trans ((congrArg Multiplicative.toAdd h0).trans hy.symm)
  · have hfun := congrArg Subtype.val hi
    have hx := congrFun hfun x
    have hy := congrFun hfun y
    exact hx.trans ((congrArg Multiplicative.toAdd h1).trans hy.symm)

/-- The two literal coordinate characters jointly fill `C₂²`. -/
theorem twoSignKernelHom_surjective
    (F : BinaryPairFrame G (Fin 4))
    (htrans : MulAction.IsPretransitive G X)
    (htwo : Nat.card (FourCoordinateSign F) = 2) :
    Function.Surjective (twoSignKernelHom F htwo) := by
  let i0 := twoSignCoordinate F htwo 0
  let i1 := twoSignCoordinate F htwo 1
  have h0fun := fourCoordinateSignFunction_ne_zero_of_count_eq_two
    F htrans htwo i0
  have h1fun := fourCoordinateSignFunction_ne_zero_of_count_eq_two
    F htrans htwo i1
  have h0 := fourCoordinateSignHom_ne_one_of_function_ne_zero F i0 h0fun
  have h1 := fourCoordinateSignHom_ne_one_of_function_ne_zero F i1 h1fun
  have hne : fourCoordinateSignHom F i0 ≠ fourCoordinateSignHom F i1 := by
    intro h
    have hfun : fourCoordinateSignFunction F i0 =
        fourCoordinateSignFunction F i1 := by
      funext k
      have hk := DFunLike.congr_fun h k
      exact congrArg Multiplicative.toAdd hk
    have hsign : fourCoordinateSign F i0 = fourCoordinateSign F i1 :=
      Subtype.ext hfun
    have he := congrArg (Finite.equivFinOfCardEq htwo) hsign
    have h01 : (0 : Fin 2) = 1 := by
      simpa only [i0, i1, fourCoordinateSign_twoSignCoordinate,
        Equiv.apply_symm_apply] using he
    exact Fin.zero_ne_one h01
  exact c2_character_prod_surjective_of_ne_one_of_ne
    (fourCoordinateSignHom F i0) (fourCoordinateSignHom F i1)
    h0 h1 hne

/-- Reversible identification of the actual pair kernel with `C₂²`. -/
def twoSignKernelEquiv
    (F : BinaryPairFrame G (Fin 4))
    (htrans : MulAction.IsPretransitive G X)
    (htwo : Nat.card (FourCoordinateSign F) = 2) :
    F.top.ker ≃* C2 × C2 :=
  MulEquiv.ofBijective (twoSignKernelHom F htwo)
    ⟨twoSignKernelHom_injective F htwo,
      twoSignKernelHom_surjective F htrans htwo⟩

/-- The literal pair-top kernel has order four in the two-sign branch. -/
theorem twoSignKernel_card
    (F : BinaryPairFrame G (Fin 4))
    (htrans : MulAction.IsPretransitive G X)
    (htwo : Nat.card (FourCoordinateSign F) = 2) :
    Nat.card F.top.ker = 4 := by
  calc
    Nat.card F.top.ker = Nat.card (C2 × C2) :=
      Nat.card_congr (twoSignKernelEquiv F htrans htwo).toEquiv
    _ = 4 := by
      rw [Nat.card_prod]
      norm_num [C2, Nat.card_zmod]

end BinaryPairFrame

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

/-- The actual pair-top kernel is `C₂²`; this is the direct bridge from the
retained isotype count, rather than a finite-action census. -/
def degreeThreeFourBlockTwoSign_pairKernelEquiv
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2) :
    let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
    C.frame.top.ker ≃* C2 × C2 := by
  let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
  have htwo' : Nat.card (BinaryPairFrame.FourCoordinateSign C.frame) = 2 := by
    simpa only [degreeThreeFourBlockSignedIsotypeProfile,
      BinaryPairFrame.fourCoordinateSignedIsotypeProfile,
      DegreeThreeFourBlockSignedIsotypeProfile.isotypeCount, C] using htwo
  exact BinaryPairFrame.twoSignKernelEquiv C.frame C.pretransitive htwo'

/-- Exact order of the actual pair-top kernel. -/
theorem degreeThreeFourBlockTwoSign_pairKernel_card
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2) :
    Nat.card (degreeThreeFourBlockPairChart
      block P hr hs hcomponent).frame.top.ker = 4 := by
  let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
  have htwo' : Nat.card (BinaryPairFrame.FourCoordinateSign C.frame) = 2 := by
    simpa only [degreeThreeFourBlockSignedIsotypeProfile,
      BinaryPairFrame.fourCoordinateSignedIsotypeProfile,
      DegreeThreeFourBlockSignedIsotypeProfile.isotypeCount, C] using htwo
  exact BinaryPairFrame.twoSignKernel_card C.frame C.pretransitive htwo'

/-- The actual four-point top preserves the two sign classes. -/
theorem degreeThreeFourBlockTwoSign_top_preserves_sign_partition
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (u : (degreeThreeFourBlockPairChart
      block P hr hs hcomponent).action)
    (i j : Fin 4) :
    let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
    BinaryPairFrame.fourCoordinateSign C.frame (C.frame.top u i) =
        BinaryPairFrame.fourCoordinateSign C.frame (C.frame.top u j) ↔
      BinaryPairFrame.fourCoordinateSign C.frame i =
        BinaryPairFrame.fourCoordinateSign C.frame j := by
  let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
  exact BinaryPairFrame.fourCoordinateSign_top_eq_iff C.frame u i j

/-- A transitive binary top on four points has order four or eight. -/
theorem degreeThreeFourBlockTwoSign_top_card_cases
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action) :
    let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
    Nat.card C.frame.top.range = 4 ∨ Nat.card C.frame.top.range = 8 := by
  let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
  letI : MulAction.IsPretransitive C.action (Fin (2 * 4)) := C.pretransitive
  letI : MulAction.IsPretransitive C.frame.top.range (Fin 4) :=
    C.frame.top_pretransitive
  have htopP : IsPGroup 2 C.frame.top.range := C.frame.top_isPGroup hbinary
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp htopP
  have hdvd : Nat.card C.frame.top.range ∣ 24 := by
    have h := Subgroup.card_dvd_of_injective C.frame.top.range.subtype
      Subtype.val_injective
    simpa only [Nat.card_perm, Nat.card_fin, Nat.factorial] using h
  have hle : Nat.card C.frame.top.range ≤ 24 :=
    Nat.le_of_dvd (by norm_num) hdvd
  have hindex :
      (MulAction.stabilizer C.frame.top.range (0 : Fin 4)).index = 4 := by
    simpa only [Nat.card_fin] using
      MulAction.index_stabilizer_of_transitive C.frame.top.range (0 : Fin 4)
  have hmul :=
    (MulAction.stabilizer C.frame.top.range (0 : Fin 4)).card_mul_index
  have hfour : 4 ∣ Nat.card C.frame.top.range := by
    rw [hindex] at hmul
    exact ⟨Nat.card (MulAction.stabilizer C.frame.top.range (0 : Fin 4)), by
      omega⟩
  have hnle : n ≤ 4 := by
    by_contra h
    have hpow : 2 ^ 5 ≤ 2 ^ n :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [← hn] at hpow
    omega
  change Nat.card C.frame.top.range = 4 ∨ Nat.card C.frame.top.range = 8
  rw [hn] at hfour hle hdvd ⊢
  interval_cases n
  · norm_num at hfour
  · norm_num at hfour
  · norm_num
  · norm_num
  · norm_num at hdvd

/-- The actual signed quotient has order sixteen or thirty-two. -/
theorem degreeThreeFourBlockTwoSign_signedQuotient_card_cases
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2) :
    Nat.card (preE7NonPairAction w U ⧸ E block P) = 16 ∨
      Nat.card (preE7NonPairAction w U ⧸ E block P) = 32 := by
  let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
  have hker : Nat.card C.frame.top.ker = 4 :=
    degreeThreeFourBlockTwoSign_pairKernel_card
      block P hr hs hcomponent htwo
  have htop := degreeThreeFourBlockTwoSign_top_card_cases
    block P hr hs hcomponent hbinary
  have hsource := C.frame.top.ker.card_mul_index
  rw [Subgroup.index_ker, hker] at hsource
  have haction : Nat.card C.action = 16 ∨ Nat.card C.action = 32 := by
    rcases htop with htop | htop <;> rw [htop] at hsource <;> omega
  have hcard : Nat.card (preE7NonPairAction w U ⧸ E block P) =
      Nat.card C.action := Nat.card_congr C.sourceEquiv.toEquiv
  rwa [hcard]

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
