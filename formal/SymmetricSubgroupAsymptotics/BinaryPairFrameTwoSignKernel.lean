import SymmetricSubgroupAsymptotics.BinaryPairFrameOneSignKernel
import SymmetricSubgroupAsymptotics.SemidirectBinaryKernelCentralAxis

/-!
# The two-sign kernel of a transitive binary pair frame

If exactly two coordinate characters occur in a transitive binary pair
frame, neither character is zero and the two characters are linearly
independent over `F₂`.  Evaluation on one coordinate from each class
therefore identifies the literal pair kernel with `C₂ × C₂`.

The kernel of the sum of the two evaluations is the simultaneous-flip
axis.  It has order two and is central in the whole source group.  This
gives a canonical two-step central series for the pair kernel without any
assumption that the ambient source is a 2-group.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace BinaryPairFrame

private abbrev C2 := Multiplicative (ZMod 2)

variable {X I : Type} {G : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame G I)

/-- A literal coordinate bit, regarded as a multiplicative binary
character of the complete pair kernel. -/
def coordinateSignHom (i : I) : F.top.ker →* C2 where
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

/-- In a transitive frame with two realized signs, every realized
coordinate character is nonzero. -/
theorem coordinateSignFunction_ne_zero_of_count_eq_two
    [Finite I] [Nonempty I]
    (htrans : MulAction.IsPretransitive G X)
    (htwo : Nat.card (CoordinateSign F) = 2)
    (i : I) :
    coordinateSignFunction F i ≠ 0 := by
  intro hi
  letI : MulAction.IsPretransitive G X := htrans
  letI : MulAction.IsPretransitive F.top.range I := F.top_pretransitive
  have hall : ∀ j : I,
      coordinateSignFunction F j = coordinateSignFunction F i := by
    intro j
    obtain ⟨t, ht⟩ := MulAction.exists_smul_eq F.top.range i j
    obtain ⟨u, rfl⟩ := F.top.rangeRestrict_surjective t
    have htop : F.top u i = j := by simpa using ht
    rw [← htop]
    funext k
    have hleft : F.bits k (F.top u i) = 0 := by
      have hconj := F.bits_conjNormal u⁻¹ k i
      simpa only [map_inv, inv_inv] using hconj.symm.trans
        (congrFun hi (MulAut.conjNormal u⁻¹ k))
    exact hleft.trans (congrFun hi k).symm
  have hone : Nat.card (CoordinateSign F) = 1 := by
    apply Nat.card_eq_one_iff_unique.mpr
    refine ⟨?_, ⟨coordinateSign F i⟩⟩
    constructor
    intro chi psi
    obtain ⟨j, rfl⟩ := coordinateSign_surjective F chi
    obtain ⟨k, rfl⟩ := coordinateSign_surjective F psi
    exact Subtype.ext ((hall j).trans (hall k).symm)
  omega

/-- A nonzero realized coordinate function gives a nontrivial binary
character. -/
theorem coordinateSignHom_ne_one_of_function_ne_zero
    (i : I) (hi : coordinateSignFunction F i ≠ 0) :
    coordinateSignHom F i ≠ 1 := by
  intro h
  apply hi
  funext k
  have hk := DFunLike.congr_fun h k
  change Multiplicative.ofAdd (F.bits k i) = 1 at hk
  exact congrArg Multiplicative.toAdd hk

/-- Choose one literal coordinate over each of the two realized sign
classes. -/
noncomputable def twoSignCoordinate
    [Finite I]
    (htwo : Nat.card (CoordinateSign F) = 2)
    (a : Fin 2) : I :=
  Classical.choose (coordinateSign_surjective F
    ((Finite.equivFinOfCardEq htwo).symm a))

@[simp] theorem coordinateSign_twoSignCoordinate
    [Finite I]
    (htwo : Nat.card (CoordinateSign F) = 2)
    (a : Fin 2) :
    coordinateSign F (twoSignCoordinate F htwo a) =
      (Finite.equivFinOfCardEq htwo).symm a :=
  Classical.choose_spec (coordinateSign_surjective F
    ((Finite.equivFinOfCardEq htwo).symm a))

/-- Evaluation on one representative of each actual sign class. -/
def twoSignKernelHom
    [Finite I]
    (htwo : Nat.card (CoordinateSign F) = 2) :
    F.top.ker →* C2 × C2 :=
  (coordinateSignHom F (twoSignCoordinate F htwo 0)).prod
    (coordinateSignHom F (twoSignCoordinate F htwo 1))

private theorem coordinateSign_eq_first_or_second
    [Finite I]
    (htwo : Nat.card (CoordinateSign F) = 2)
    (i : I) :
    coordinateSign F i = coordinateSign F (twoSignCoordinate F htwo 0) ∨
      coordinateSign F i = coordinateSign F (twoSignCoordinate F htwo 1) := by
  let e : CoordinateSign F ≃ Fin 2 := Finite.equivFinOfCardEq htwo
  have hle : (e (coordinateSign F i)).val ≤ 1 := by omega
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with hzero | hone
  · left
    apply e.injective
    simpa only [e, coordinateSign_twoSignCoordinate,
      Equiv.apply_symm_apply] using Fin.ext hzero
  · right
    apply e.injective
    simpa only [e, coordinateSign_twoSignCoordinate,
      Equiv.apply_symm_apply] using Fin.ext hone

/-- The two evaluations separate the complete pair kernel. -/
theorem twoSignKernelHom_injective
    [Finite I]
    (htwo : Nat.card (CoordinateSign F) = 2) :
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
  rcases coordinateSign_eq_first_or_second F htwo i with hi | hi
  · have hfun := congrArg Subtype.val hi
    exact (congrFun hfun x).trans
      ((congrArg Multiplicative.toAdd h0).trans (congrFun hfun y).symm)
  · have hfun := congrArg Subtype.val hi
    exact (congrFun hfun x).trans
      ((congrArg Multiplicative.toAdd h1).trans (congrFun hfun y).symm)

private theorem c2_character_prod_surjective
    {H : Type*} [Group H]
    (chi psi : H →* C2)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1) (hne : chi ≠ psi) :
    Function.Surjective (chi.prod psi) := by
  have hchiWitness : ∃ x : H, chi x ≠ 1 := by
    by_contra h
    push Not at h
    exact hchi (MonoidHom.ext h)
  have hpsiWitness : ∃ x : H, psi x ≠ 1 := by
    by_contra h
    push Not at h
    exact hpsi (MonoidHom.ext h)
  obtain ⟨z, hz⟩ : ∃ x : H, chi x ≠ psi x := by
    by_contra h
    push Not at h
    exact hne (MonoidHom.ext h)
  obtain ⟨⟨a, hachi, hapsi⟩, ⟨b, hbchi, hbpsi⟩⟩ :
      (∃ a : H, chi a = C2Wreath.gen ∧ psi a = 1) ∧
        ∃ b : H, chi b = 1 ∧ psi b = C2Wreath.gen := by
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

/-- The two evaluations fill `C₂²`. -/
theorem twoSignKernelHom_surjective
    [Finite I] [Nonempty I]
    (htrans : MulAction.IsPretransitive G X)
    (htwo : Nat.card (CoordinateSign F) = 2) :
    Function.Surjective (twoSignKernelHom F htwo) := by
  let i0 := twoSignCoordinate F htwo 0
  let i1 := twoSignCoordinate F htwo 1
  have h0fun := coordinateSignFunction_ne_zero_of_count_eq_two
    F htrans htwo i0
  have h1fun := coordinateSignFunction_ne_zero_of_count_eq_two
    F htrans htwo i1
  have h0 := coordinateSignHom_ne_one_of_function_ne_zero F i0 h0fun
  have h1 := coordinateSignHom_ne_one_of_function_ne_zero F i1 h1fun
  have hne : coordinateSignHom F i0 ≠ coordinateSignHom F i1 := by
    intro h
    have hfun : coordinateSignFunction F i0 =
        coordinateSignFunction F i1 := by
      funext k
      exact congrArg Multiplicative.toAdd (DFunLike.congr_fun h k)
    have hsign : coordinateSign F i0 = coordinateSign F i1 :=
      Subtype.ext hfun
    have he := congrArg (Finite.equivFinOfCardEq htwo) hsign
    have h01 : (0 : Fin 2) = 1 := by
      simpa only [i0, i1, coordinateSign_twoSignCoordinate,
        Equiv.apply_symm_apply] using he
    exact Fin.zero_ne_one h01
  exact c2_character_prod_surjective
    (coordinateSignHom F i0) (coordinateSignHom F i1) h0 h1 hne

/-- Literal identification of a two-sign pair kernel with `C₂²`. -/
def twoSignKernelEquiv
    [Finite I] [Nonempty I]
    (htrans : MulAction.IsPretransitive G X)
    (htwo : Nat.card (CoordinateSign F) = 2) :
    F.top.ker ≃* C2 × C2 :=
  MulEquiv.ofBijective (twoSignKernelHom F htwo)
    ⟨twoSignKernelHom_injective F htwo,
      twoSignKernelHom_surjective F htrans htwo⟩

/-- A two-sign pair kernel has order four. -/
theorem top_ker_card_eq_four_of_sign_count_two
    [Finite X] [Finite I] [Nonempty I]
    (htrans : MulAction.IsPretransitive G X)
    (htwo : Nat.card (CoordinateSign F) = 2) :
    Nat.card F.top.ker = 4 := by
  calc
    Nat.card F.top.ker = Nat.card (C2 × C2) :=
      Nat.card_congr (twoSignKernelEquiv F htrans htwo).toEquiv
    _ = 4 := by
      rw [Nat.card_prod]
      norm_num [C2, Nat.card_zmod]

/-- Multiplication of two binary coordinates. -/
def binaryProduct : C2 × C2 →* C2 where
  toFun x := x.1 * x.2
  map_one' := by simp
  map_mul' x y := by
    simp only [Prod.fst_mul, Prod.snd_mul]
    ac_rfl

/-- The sum of the two realized sign characters. -/
def twoSignDifferenceHom
    [Finite I]
    (htwo : Nat.card (CoordinateSign F) = 2) : F.top.ker →* C2 :=
  binaryProduct.comp (twoSignKernelHom F htwo)

theorem twoSignDifferenceHom_surjective
    [Finite I] [Nonempty I]
    (htrans : MulAction.IsPretransitive G X)
    (htwo : Nat.card (CoordinateSign F) = 2) :
    Function.Surjective (twoSignDifferenceHom F htwo) := by
  intro c
  obtain ⟨k, hk⟩ := twoSignKernelHom_surjective F htrans htwo (c, 1)
  refine ⟨k, ?_⟩
  simp only [twoSignDifferenceHom, MonoidHom.comp_apply, binaryProduct]
  rw [hk]
  exact mul_one c

/-- The diagonal sign kernel has order two. -/
theorem twoSignDifferenceKernel_card
    [Finite X] [Finite I] [Nonempty I]
    (htrans : MulAction.IsPretransitive G X)
    (htwo : Nat.card (CoordinateSign F) = 2) :
    Nat.card (twoSignDifferenceHom F htwo).ker = 2 := by
  let d := twoSignDifferenceHom F htwo
  have hd : Function.Surjective d :=
    twoSignDifferenceHom_surjective F htrans htwo
  have hcard := d.ker.card_mul_index
  rw [Subgroup.index_ker, d.range_eq_top_of_surjective hd,
    Nat.card_congr Subgroup.topEquiv.toEquiv,
    top_ker_card_eq_four_of_sign_count_two F htrans htwo] at hcard
  have hC2 : Nat.card C2 = 2 := by norm_num [C2, Nat.card_zmod]
  rw [hC2] at hcard
  have hcard' : Nat.card (twoSignDifferenceHom F htwo).ker * 2 = 4 := by
    exact hcard
  omega

/-- The actual diagonal subgroup, embedded back in the source group. -/
def twoSignCentralAxis
    [Finite I]
    (htwo : Nat.card (CoordinateSign F) = 2) : Subgroup G :=
  (twoSignDifferenceHom F htwo).ker.map F.top.ker.subtype

theorem twoSignCentralAxis_le_top_ker
    [Finite I]
    (htwo : Nat.card (CoordinateSign F) = 2) :
    twoSignCentralAxis F htwo ≤ F.top.ker := by
  intro z hz
  obtain ⟨k, _hk, rfl⟩ := hz
  exact k.property

theorem twoSignCentralAxis_card
    [Finite X] [Finite I] [Nonempty I]
    (htrans : MulAction.IsPretransitive G X)
    (htwo : Nat.card (CoordinateSign F) = 2) :
    Nat.card (twoSignCentralAxis F htwo) = 2 := by
  exact (Nat.card_congr
    ((twoSignDifferenceHom F htwo).ker.equivMapOfInjective
      F.top.ker.subtype Subtype.val_injective).toEquiv).symm.trans
        (twoSignDifferenceKernel_card F htrans htwo)

private theorem twoSignDifferenceKernel_bits_constant
    [Finite I]
    (htwo : Nat.card (CoordinateSign F) = 2)
    (k : (twoSignDifferenceHom F htwo).ker)
    (i j : I) : F.bits k i = F.bits k j := by
  let i0 := twoSignCoordinate F htwo 0
  let i1 := twoSignCoordinate F htwo 1
  have hk := MonoidHom.mem_ker.mp k.property
  change Multiplicative.ofAdd (F.bits k i0) *
      Multiplicative.ofAdd (F.bits k i1) = 1 at hk
  have hadd := congrArg Multiplicative.toAdd hk
  change F.bits k i0 + F.bits k i1 = 0 at hadd
  have hself : ∀ a : ZMod 2, a + a = 0 := by decide
  have h01 : F.bits k i0 = F.bits k i1 := by
    apply add_left_cancel (a := F.bits k i0)
    rw [hadd, hself]
  have hi : F.bits k i = F.bits k i0 := by
    rcases coordinateSign_eq_first_or_second F htwo i with h | h
    · exact congrFun (congrArg Subtype.val h) k
    · exact (congrFun (congrArg Subtype.val h) k).trans h01.symm
  have hj : F.bits k j = F.bits k i0 := by
    rcases coordinateSign_eq_first_or_second F htwo j with h | h
    · exact congrFun (congrArg Subtype.val h) k
    · exact (congrFun (congrArg Subtype.val h) k).trans h01.symm
  exact hi.trans hj.symm

/-- The diagonal sign axis consists of simultaneous flips, hence is
central in the original source group. -/
theorem twoSignCentralAxis_le_center
    [Finite I]
    (htwo : Nat.card (CoordinateSign F) = 2) :
    twoSignCentralAxis F htwo ≤ Subgroup.center G := by
  intro z hz
  obtain ⟨k, hk, rfl⟩ := hz
  rw [Subgroup.mem_center_iff]
  intro u
  have hkfixed : MulAut.conjNormal u (k : F.top.ker) = k := by
    apply F.bitsHom_injective
    apply congrArg Multiplicative.ofAdd
    funext i
    rw [F.bits_conjNormal]
    exact twoSignDifferenceKernel_bits_constant F htwo
      ⟨k, hk⟩ ((F.top u)⁻¹ i) i
  have hkfixed' := congrArg Subtype.val hkfixed
  change u * (k : G) * u⁻¹ = k at hkfixed'
  calc
    u * (k : G) = (u * k * u⁻¹) * u := by simp [mul_assoc]
    _ = k * u := by rw [hkfixed']

/-- The diagonal sign axis, packaged inside the literal top projection. -/
noncomputable def twoSignTopCentralAxis
    [Finite X] [Finite I] [Nonempty I]
    (htrans : MulAction.IsPretransitive G X)
    (htwo : Nat.card (CoordinateSign F) = 2) :
    CentralOrderTwoKernelAxis F.top.rangeRestrict := by
  let C := twoSignCentralAxis F htwo
  have hCnormal : C.Normal := by
    constructor
    intro z hz u
    have hzc := twoSignCentralAxis_le_center F htwo hz
    simpa [Subgroup.mem_center_iff.mp hzc u, mul_assoc] using hz
  letI : C.Normal := hCnormal
  exact
    { C := C
      normalC := hCnormal
      C_le_kernel := by
        intro z hz
        apply MonoidHom.mem_ker.mpr
        apply Subtype.ext
        exact MonoidHom.mem_ker.mp
          (twoSignCentralAxis_le_top_ker F htwo hz)
      C_card := twoSignCentralAxis_card F htrans htwo
      C_le_center := twoSignCentralAxis_le_center F htwo }

/-- The literal pair kernel has a two-step central series obtained from
the diagonal sign axis. -/
noncomputable def twoSignKernelCentralSeries
    [Finite X] [Finite I] [Nonempty I]
    (htrans : MulAction.IsPretransitive G X)
    (htwo : Nat.card (CoordinateSign F) = 2) :
    BinaryNormalKernelCentralSeries G F.top.ker := by
  let C := twoSignCentralAxis F htwo
  have hCnormal : C.Normal := by
    constructor
    intro z hz u
    have hzc := twoSignCentralAxis_le_center F htwo hz
    simpa [Subgroup.mem_center_iff.mp hzc u, mul_assoc] using hz
  letI : C.Normal := hCnormal
  exact binaryNormalKernelCentralSeries_of_central_order_two
    F.top.ker C
    (twoSignCentralAxis_le_top_ker F htwo)
    (twoSignCentralAxis_card F htrans htwo)
    (twoSignCentralAxis_le_center F htwo)
    (by rw [top_ker_card_eq_four_of_sign_count_two F htrans htwo])

end BinaryPairFrame
end SymmetricSubgroupAsymptotics

end
