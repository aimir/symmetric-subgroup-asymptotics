import SymmetricSubgroupAsymptotics.AllLifts
import SymmetricSubgroupAsymptotics.BinaryC3CyclicModule
import SymmetricSubgroupAsymptotics.BinaryPairInvariantAxes
import SymmetricSubgroupAsymptotics.C1FiniteOwnerTransport
import SymmetricSubgroupAsymptotics.DegreeSixTernaryBlockOwner
import SymmetricSubgroupAsymptotics.OriginalNormalChiefHead
import SymmetricSubgroupAsymptotics.TernaryDegreeNineClosure
import Mathlib.GroupTheory.SchurZassenhaus

/-!
# The two-by-three degree-six owner

This file treats an actual minimal block system with two-point fibres and
three blocks.  Highness forces the faithful three-point top to be `C₃`.
The literal block kernel is charted as its actual invariant submodule of
`F₂^3`; Schur--Zassenhaus supplies an actual complement, and the cyclicity
theorem for three-coordinate binary submodules supplies the distinguished
vector and its conjugate words.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace OriginalMinimalBlock

variable {A Ω : Type} [Group A] [MulAction A Ω]
variable [MulAction.IsPretransitive A Ω]
variable {ω₀ : Ω} (D : OriginalMinimalBlock (A := A) ω₀)

include D in
/-- A high normal pair in the two-point-fibre branch forces the actual
three-point top to have order three. -/
theorem degreeSix_binaryBlock_top_card
    [Finite A] [Finite Ω] [FaithfulSMul A Ω]
    (N : Subgroup A) [N.Normal]
    (hFibre : Nat.card D.Fibre = 2)
    (hPoints : Nat.card D.Points = 3)
    (hHigh : 3 * Nat.card Ω <
      20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)) :
    Nat.card D.Top = 3 := by
  letI : Nonempty Ω := ⟨ω₀⟩
  letI : Nontrivial D.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  letI : Finite D.Component :=
    Finite.of_surjective
      (originalBlockFibreAction D.map D.map_equivariant D.base).rangeRestrict
      (originalBlockFibreAction D.map D.map_equivariant D.base).rangeRestrict_surjective
  letI : MulAction.IsPreprimitive D.Component D.Fibre := D.component_preprimitive
  letI : MulAction.IsPretransitive D.Top D.Points := D.top_pretransitive
  letI : FaithfulSMul D.Top D.Points := D.top_faithful
  letI : Finite D.Top := D.top_finite
  letI : Nonempty D.Points := ⟨D.base⟩
  let c := actualChiefSeries D.Component
  let T := originalNormalRange D.topMap N
  let d := Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)
  let t := Module.finrank (ZMod 3) (primeRelativeCharacters 3 T)
  have hc : actualChiefSeriesTernaryWeight c = 0 := by
    apply permutationChiefWeight_eq_zero_of_card_le_two D.Component c
    omega
  have hdt : d ≤ t := by
    have h := D.head_bound_nat N c
    simpa only [d, t, T, hc, zero_mul, zero_add] using h
  have ht : t ≤ 1 := by
    simpa only [t, T] using
      permutationRelativeHead_le_one_of_card_le_five D.Top T (by omega)
  have hdpos : 1 ≤ d := by
    have hΩ : Nat.card Ω = 6 := by
      calc
        Nat.card Ω = Nat.card D.Fibre * Nat.card D.Points := D.degree_product.symm
        _ = 2 * 3 := by rw [hFibre, hPoints]
        _ = 6 := by norm_num
    rw [hΩ] at hHigh
    omega
  have htExact : t = 1 := by omega
  have hTopPGroup : IsPGroup 3 D.Top :=
    degreeThree_rankOne_isPGroup hPoints T (by simpa only [t] using htExact)
  have hUpper : Nat.card D.Top ≤ 6 := by
    have h := Subgroup.card_le_card_group D.Top
    have hPerm : Nat.card (Equiv.Perm D.Points) = 6 := by
      rw [Nat.card_perm, hPoints]
      norm_num
    simpa only [hPerm] using h
  have hLower : 3 ≤ Nat.card D.Top := by
    have hIndex : (MulAction.stabilizer D.Top D.base).index = 3 := by
      simpa only [hPoints] using
        MulAction.index_stabilizer_of_transitive D.Top D.base
    have hMul := (MulAction.stabilizer D.Top D.base).card_mul_index
    have hPos : 0 < Nat.card (MulAction.stabilizer D.Top D.base) := Nat.card_pos
    rw [hIndex] at hMul
    omega
  obtain ⟨k, hk⟩ := hTopPGroup.exists_card_eq
  have hpowUpper : 3 ^ k ≤ 6 := by
    rw [← hk]
    exact hUpper
  have hkLe : k ≤ 1 := by
    by_contra h
    have hp : 3 ^ 2 ≤ 3 ^ k :=
      Nat.pow_le_pow_right (by decide : 0 < (3 : ℕ)) (by omega)
    norm_num at hp
    omega
  have hkPos : 0 < k := by
    by_contra h
    have hkZero : k = 0 := by omega
    rw [hkZero, pow_zero] at hk
    omega
  have : k = 1 := by omega
  rw [this, pow_one] at hk
  exact hk

/-- Every literal fibre in the selected binary block system has two points. -/
theorem binaryBlock_fibre_card [Finite A] [Finite Ω]
    (hFibre : Nat.card D.Fibre = 2) (x : D.Points) :
    Nat.card (originalBlockFibre D.map x) = 2 := by
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq A D.base x
  calc
    Nat.card (originalBlockFibre D.map x) =
        Nat.card (originalBlockFibre D.map (a • D.base)) := by rw [ha]
    _ = Nat.card D.Fibre :=
      (Nat.card_congr
        (OriginalBlockSignCoordinates.fibreTransport D.map D.map_equivariant
          a D.base)).symm
    _ = 2 := hFibre

abbrev originalPermutationImage [FaithfulSMul A Ω]
    (D : OriginalMinimalBlock (A := A) ω₀) :
    Subgroup (Equiv.Perm Ω) := (MulAction.toPermHom A Ω).range

def originalPermutationEquiv [FaithfulSMul A Ω]
    (D : OriginalMinimalBlock (A := A) ω₀) :
    A ≃* D.originalPermutationImage :=
  MonoidHom.ofInjective MulAction.toPerm_injective

/-- The actual pair frame after relabelling only the three blocks. -/
def binaryBlockFrame [Finite A] [Finite Ω] [FaithfulSMul A Ω]
    (hFibre : Nat.card D.Fibre = 2)
    (points : D.Points ≃ Fin 3) :
    BinaryPairFrame D.originalPermutationImage (Fin 3) := by
  let top : D.originalPermutationImage →* Equiv.Perm (Fin 3) :=
    points.permCongrHom.toMonoidHom.comp
      (D.topMap.comp D.originalPermutationEquiv.symm.toMonoidHom)
  let b : Ω → Fin 3 := fun ω => points (D.map ω)
  have hb : ∀ (u : D.originalPermutationImage) (ω : Ω),
      b ((u : Equiv.Perm Ω) ω) = top u (b ω) := by
    intro u ω
    let a := D.originalPermutationEquiv.symm u
    simp only [b, top, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    have hcongr :
        (points.permCongrHom (D.topMap a)) (points (D.map ω)) =
          points (D.topMap a (D.map ω)) := by
      change points.permCongr (D.topMap a) (points (D.map ω)) = _
      rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
    rw [hcongr]
    have hu : MulAction.toPermHom A Ω a = (u : Equiv.Perm Ω) :=
      congrArg Subtype.val (D.originalPermutationEquiv.apply_symm_apply u)
    rw [← hu]
    change points (D.map (a • ω)) = points (D.topMap a (D.map ω))
    exact congrArg points (D.map_equivariant a ω)
  have hcard : ∀ i : Fin 3, Nat.card {ω : Ω // b ω = i} = 2 := by
    intro i
    let e : {ω : Ω // b ω = i} ≃
        originalBlockFibre D.map (points.symm i) :=
      { toFun := fun ω => ⟨ω.1, points.injective (ω.2.trans (points.apply_symm_apply i).symm)⟩
        invFun := fun ω => ⟨ω.1, by
          change points (D.map ω.1) = i
          rw [ω.2, points.apply_symm_apply]⟩
        left_inv := fun ω => rfl
        right_inv := fun ω => rfl }
    rw [Nat.card_congr e]
    exact D.binaryBlock_fibre_card hFibre (points.symm i)
  exact binaryPairFrameOfFibreCardTwo D.originalPermutationImage top b hb hcard

@[simp]
theorem binaryBlockFrame_top_apply [Finite A] [Finite Ω] [FaithfulSMul A Ω]
    (hFibre : Nat.card D.Fibre = 2)
    (points : D.Points ≃ Fin 3)
    (u : D.originalPermutationImage) :
    (D.binaryBlockFrame hFibre points).top u =
      points.permCongrHom
        (D.topMap (D.originalPermutationEquiv.symm u)) := by
  rfl

include D in
/-- The frame top is the relabelled original block top, so it has the same
order three forced by highness. -/
theorem binaryBlockFrame_top_card
    [Finite A] [Finite Ω] [FaithfulSMul A Ω]
    (N : Subgroup A) [N.Normal]
    (hFibre : Nat.card D.Fibre = 2)
    (hPoints : Nat.card D.Points = 3)
    (hHigh : 3 * Nat.card Ω <
      20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N))
    (points : D.Points ≃ Fin 3) :
    Nat.card (D.binaryBlockFrame hFibre points).top.range = 3 := by
  let F := D.binaryBlockFrame hFibre points
  have hRange : F.top.range = Subgroup.map points.permCongrHom D.Top := by
    ext g
    constructor
    · rintro ⟨u, rfl⟩
      let a := D.originalPermutationEquiv.symm u
      refine ⟨D.topMap a, ⟨a, rfl⟩, ?_⟩
      simp only [F, binaryBlockFrame_top_apply, a]
      rfl
    · rintro ⟨g, ⟨a, rfl⟩, rfl⟩
      refine ⟨D.originalPermutationEquiv a, ?_⟩
      simp only [F, binaryBlockFrame_top_apply, MulEquiv.symm_apply_apply]
      rfl
  rw [hRange, ← Nat.card_congr (points.permCongrHom.subgroupMap D.Top).toEquiv]
  exact D.degreeSix_binaryBlock_top_card N hFibre hPoints hHigh

theorem binaryBlockFrame_kernel_isPGroup
    {U : Subgroup (Equiv.Perm Ω)}
    (F : BinaryPairFrame U (Fin 3)) :
    IsPGroup 2 F.top.ker := by
  have hM : IsPGroup 2 (Multiplicative F.kernelSpace) := by
    intro w
    refine ⟨1, ?_⟩
    rw [pow_one]
    change 2 • w.toAdd = 0
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2), ZMod.natCast_self, zero_smul]
  exact hM.of_equiv F.kernelChart.symm

theorem binaryBlockFrame_kernel_exponent_two
    {U : Subgroup (Equiv.Perm Ω)}
    (F : BinaryPairFrame U (Fin 3)) :
    ∀ x : F.top.ker, x ^ 2 = 1 := by
  intro x
  apply F.kernelChart.injective
  rw [map_pow, map_one]
  exact binary_mul_pow_two (F.kernelChart x)

theorem binaryBlockFrame_kernel_index_three
    {U : Subgroup (Equiv.Perm Ω)}
    (F : BinaryPairFrame U (Fin 3))
    (hTop : Nat.card F.top.range = 3) :
    F.top.ker.index = 3 := by
  rw [Subgroup.index_ker]
  exact hTop

theorem binaryBlockFrame_complement_exists
    [Finite Ω]
    {U : Subgroup (Equiv.Perm Ω)}
    (F : BinaryPairFrame U (Fin 3))
    (hTop : Nat.card F.top.range = 3) :
    ∃ P : Subgroup U, Subgroup.IsComplement' F.top.ker P := by
  have hK : IsPGroup 2 F.top.ker := binaryBlockFrame_kernel_isPGroup F
  obtain ⟨n, hn⟩ := hK.exists_card_eq
  apply Subgroup.exists_right_complement'_of_coprime
  rw [hn, binaryBlockFrame_kernel_index_three F hTop]
  exact Nat.Coprime.pow_left n (by decide)

def binaryBlockFrame_complementTopHom
    {U : Subgroup (Equiv.Perm Ω)}
    (F : BinaryPairFrame U (Fin 3))
    (P : Subgroup U) : P →* F.top.range :=
  F.top.rangeRestrict.comp P.subtype

theorem binaryBlockFrame_complementTopHom_injective
    {U : Subgroup (Equiv.Perm Ω)}
    (F : BinaryPairFrame U (Fin 3))
    (P : Subgroup U)
    (hP : Subgroup.IsComplement' F.top.ker P) :
    Function.Injective (binaryBlockFrame_complementTopHom F P) := by
  intro p q hpq
  have htop : F.top (p : U) = F.top (q : U) :=
    congrArg Subtype.val hpq
  have hker : (p : U)⁻¹ * (q : U) ∈ F.top.ker := by
    change F.top ((p : U)⁻¹ * (q : U)) = 1
    rw [map_mul, map_inv, htop, inv_mul_cancel]
  have hmemP : (p : U)⁻¹ * (q : U) ∈ P :=
    P.mul_mem (P.inv_mem p.property) q.property
  have hbot : (p : U)⁻¹ * (q : U) ∈ (⊥ : Subgroup U) :=
    hP.disjoint.le_bot ⟨hker, hmemP⟩
  apply Subtype.ext
  exact inv_mul_eq_one.mp (Subgroup.mem_bot.mp hbot)

theorem binaryBlockFrame_complement_card
    [Finite Ω]
    {U : Subgroup (Equiv.Perm Ω)}
    (F : BinaryPairFrame U (Fin 3))
    (P : Subgroup U)
    (hTop : Nat.card F.top.range = 3)
    (hP : Subgroup.IsComplement' F.top.ker P) :
    Nat.card P = 3 := by
  have hIndex := binaryBlockFrame_kernel_index_three F hTop
  have hMul := F.top.ker.card_mul_index
  rw [hIndex] at hMul
  have h := hP.card_mul.trans hMul.symm
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h

def binaryBlockFrame_complementTopEquiv
    [Finite Ω]
    {U : Subgroup (Equiv.Perm Ω)}
    (F : BinaryPairFrame U (Fin 3))
    (P : Subgroup U)
    (hTop : Nat.card F.top.range = 3)
    (hP : Subgroup.IsComplement' F.top.ker P) :
    P ≃* F.top.range :=
  MulEquiv.ofBijective (binaryBlockFrame_complementTopHom F P)
    ((Nat.bijective_iff_injective_and_card _).mpr
      ⟨binaryBlockFrame_complementTopHom_injective F P hP,
        (binaryBlockFrame_complement_card F P hTop hP).trans hTop.symm⟩)

@[simp]
theorem binaryBlockFrame_complementTopEquiv_apply
    [Finite Ω]
    {U : Subgroup (Equiv.Perm Ω)}
    (F : BinaryPairFrame U (Fin 3))
    (P : Subgroup U)
    (hTop : Nat.card F.top.range = 3)
    (hP : Subgroup.IsComplement' F.top.ker P)
    (p : P) :
    binaryBlockFrame_complementTopEquiv F P hTop hP p =
      F.top.rangeRestrict (p : U) := rfl

theorem binaryBlockFrame_kernelChart_normalConjugate
    {U : Subgroup (Equiv.Perm Ω)}
    (F : BinaryPairFrame U (Fin 3))
    (v : F.top.ker) (u : U) :
    F.kernelChart
        (normalConjugate F.top.ker (by infer_instance) v (u : U)) =
      Multiplicative.ofAdd
        (F.kernelSubrepresentation.toRepresentation
          (F.top.rangeRestrict u) (F.kernelChart v).toAdd) := by
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  change F.bits (normalConjugate F.top.ker (by infer_instance) v (u : U)) =
    F.coordinateTopAction (F.top.rangeRestrict u) (F.bits v)
  rw [F.coordinateTopAction_bits]
  rfl

theorem binaryBlockFrame_kernelChart_conjugateWord
    {U : Subgroup (Equiv.Perm Ω)}
    (F : BinaryPairFrame U (Fin 3))
    (P : Subgroup U)
    (v : F.top.ker) (l : List P) :
    F.kernelChart
        ((l.map fun c : P =>
          normalConjugate F.top.ker (by infer_instance) v (c : U)).prod) =
      Multiplicative.ofAdd
        ((l.map fun c : P =>
          F.kernelSubrepresentation.toRepresentation
            (F.top.rangeRestrict (c : U)) (F.kernelChart v).toAdd).sum) := by
  induction l with
  | nil =>
      simp only [List.map_nil, List.prod_nil, List.sum_nil, map_one]
      rfl
  | cons c l ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons, map_mul]
      rw [binaryBlockFrame_kernelChart_normalConjugate F v (c : U), ih]
      rfl

/-- A finite binary pair frame on three blocks whose actual top has order
three supplies the intrinsic cyclic binary-module earlier owner. -/
theorem binaryBlockFrame_cyclicOwnerWithCard
    [Finite Ω]
    {U : Subgroup (Equiv.Perm Ω)}
    (F : BinaryPairFrame U (Fin 3))
    (hTop : Nat.card F.top.range = 3) :
    ∃ W : C1CyclicBinaryModuleOwnerWitness U,
      Nat.card W.complement = 3 := by
  obtain ⟨P, hP⟩ := binaryBlockFrame_complement_exists F hTop
  let topEquiv : P ≃* F.top.range :=
    binaryBlockFrame_complementTopEquiv F P hTop hP
  obtain ⟨v, hv⟩ :=
    binaryThree_subrepresentation_cyclic
      F.top.range hTop F.kernelSubrepresentation
  let vector : F.top.ker :=
    F.kernelChart.symm (Multiplicative.ofAdd v)
  let split : F.top.ker × P ≃ U :=
    Equiv.ofBijective
      (fun z : F.top.ker × P => (z.1 : U) * (z.2 : U)) hP
  let topWord : F.top.ker → List F.top.range := fun x =>
    Classical.choose (hv (F.kernelChart x).toAdd)
  have topWord_eq : ∀ x : F.top.ker,
      ((topWord x).map fun g =>
        F.kernelSubrepresentation.toRepresentation g v).sum =
          (F.kernelChart x).toAdd := by
    intro x
    exact Classical.choose_spec (hv (F.kernelChart x).toAdd)
  let word : F.top.ker → List P := fun x =>
    (topWord x).map topEquiv.symm
  have topEquiv_symm_top : ∀ g : F.top.range,
      F.top.rangeRestrict ((topEquiv.symm g : P) : U) = g := by
    intro g
    rw [← binaryBlockFrame_complementTopEquiv_apply F P hTop hP]
    exact topEquiv.apply_symm_apply g
  have hvector : (F.kernelChart vector).toAdd = v := by
    change Multiplicative.toAdd
      (F.kernelChart (F.kernelChart.symm (Multiplicative.ofAdd v))) = v
    rw [F.kernelChart.apply_symm_apply]
    rfl
  have hPcard : Nat.card P = 3 :=
    binaryBlockFrame_complement_card F P hTop hP
  refine ⟨{
    base := F.top.ker
    complement := P
    base_normal := inferInstance
    basePGroup := binaryBlockFrame_kernel_isPGroup F
    complementPGroup := IsPGroup.of_card (n := 1) (by
      simpa only [pow_one] using hPcard)
    base_exponent_two := binaryBlockFrame_kernel_exponent_two F
    complement_exponent_three := by
      intro x
      have hx := pow_card_eq_one' (x := x)
      simpa only [hPcard] using hx
    intersection_trivial := by
      intro x hxK hxP'
      have hbot : x ∈ (⊥ : Subgroup U) :=
        hP.disjoint.le_bot ⟨hxK, hxP'⟩
      exact Subgroup.mem_bot.mp hbot
    factorBase := fun x => (split.symm x).1
    factorComplement := fun x => (split.symm x).2
    factorization := by
      intro x
      change split (split.symm x) = x
      exact split.apply_symm_apply x
    vector := vector
    cyclicWord := word
    cyclic_word_eq := by
      intro x
      apply F.kernelChart.injective
      rw [binaryBlockFrame_kernelChart_conjugateWord F P vector (word x)]
      apply congrArg Multiplicative.ofAdd
      change
        ((word x).map fun c : P =>
          F.kernelSubrepresentation.toRepresentation
            (F.top.rangeRestrict (c : U)) (F.kernelChart vector).toAdd).sum =
          (F.kernelChart x).toAdd
      rw [hvector]
      calc
        ((word x).map fun c : P =>
            F.kernelSubrepresentation.toRepresentation
              (F.top.rangeRestrict (c : U)) v).sum =
            ((topWord x).map fun g =>
              F.kernelSubrepresentation.toRepresentation g v).sum := by
          apply congrArg List.sum
          simp only [word, List.map_map]
          apply List.map_congr_left
          intro g hg
          rw [Function.comp_apply, topEquiv_symm_top g]
        _ = (F.kernelChart x).toAdd := topWord_eq x
  }, hPcard⟩

/-- Forgetting the retained complement cardinal recovers the original
owner interface. -/
theorem binaryBlockFrame_cyclicOwner
    [Finite Ω]
    {U : Subgroup (Equiv.Perm Ω)}
    (F : BinaryPairFrame U (Fin 3))
    (hTop : Nat.card F.top.range = 3) :
    Nonempty (C1CyclicBinaryModuleOwnerWitness U) := by
  obtain ⟨W, _⟩ := binaryBlockFrame_cyclicOwnerWithCard F hTop
  exact ⟨W⟩

include D in
/-- The actual two-point-fibre degree-six branch has the cyclic
binary-module owner, transported back from the literal permutation image to
the original group. -/
theorem degreeSix_binaryBlock_owner
    [Finite A] [Finite Ω] [FaithfulSMul A Ω]
    (N : Subgroup A) [N.Normal]
    (hFibre : Nat.card D.Fibre = 2)
    (hPoints : Nat.card D.Points = 3)
    (hHigh : 3 * Nat.card Ω <
      20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)) :
    Nonempty (C1CyclicBinaryModuleOwnerWitness A) := by
  let points : D.Points ≃ Fin 3 := Finite.equivFinOfCardEq hPoints
  let F := D.binaryBlockFrame hFibre points
  have hTop : Nat.card F.top.range = 3 :=
    D.binaryBlockFrame_top_card N hFibre hPoints hHigh points
  obtain ⟨W⟩ := binaryBlockFrame_cyclicOwner F hTop
  exact ⟨W.map D.originalPermutationEquiv.symm⟩

include D in
/-- The refined binary-block owner retains the literal order-three
complement through transport back to the original group. -/
theorem degreeSix_binaryBlock_ownerWithCard
    [Finite A] [Finite Ω] [FaithfulSMul A Ω]
    (N : Subgroup A) [N.Normal]
    (hFibre : Nat.card D.Fibre = 2)
    (hPoints : Nat.card D.Points = 3)
    (hHigh : 3 * Nat.card Ω <
      20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)) :
    ∃ W : C1CyclicBinaryModuleOwnerWitness A,
      Nat.card W.complement = 3 := by
  let points : D.Points ≃ Fin 3 := Finite.equivFinOfCardEq hPoints
  let F := D.binaryBlockFrame hFibre points
  have hTop : Nat.card F.top.range = 3 :=
    D.binaryBlockFrame_top_card N hFibre hPoints hHigh points
  obtain ⟨W, hW⟩ := binaryBlockFrame_cyclicOwnerWithCard F hTop
  let e := D.originalPermutationEquiv.symm
  refine ⟨W.map e, ?_⟩
  change Nat.card (W.complement.map e.toMonoidHom) = 3
  rw [Subgroup.card_map_of_injective e.injective, hW]

end OriginalMinimalBlock

/-- Every high degree-six pair has one of the two intrinsic structural
earlier owners.  No transitive-action catalogue remains in this degree. -/
theorem degreeSix_high_structuralOwner
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    {A Ω : Type} [Group A] [Finite A] [Finite Ω] [MulAction A Ω]
    [FaithfulSMul A Ω] [MulAction.IsPretransitive A Ω]
    (N : Subgroup A) [N.Normal]
    (hDegree : Nat.card Ω = 6)
    (hHigh : 3 * Nat.card Ω <
      20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)) :
    Nonempty (C1OddIndexTwoOwnerWitness A) ∨
      Nonempty (C1CyclicBinaryModuleOwnerWitness A) := by
  rcases degreeSix_high_oddIndexOwner_or_binaryBlock
      hPrimitive N hDegree hHigh with hOdd | ⟨ω₀, D, hFibre, hPoints⟩
  · exact Or.inl hOdd
  · exact Or.inr (D.degreeSix_binaryBlock_owner N hFibre hPoints hHigh)

/-- The high degree-six split with the complement cardinal retained for
the sharp induced-head estimate. -/
theorem degreeSix_high_structuralOwnerWithComplementCard
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    {A Ω : Type} [Group A] [Finite A] [Finite Ω] [MulAction A Ω]
    [FaithfulSMul A Ω] [MulAction.IsPretransitive A Ω]
    (N : Subgroup A) [N.Normal]
    (hDegree : Nat.card Ω = 6)
    (hHigh : 3 * Nat.card Ω <
      20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)) :
    Nonempty (C1OddIndexTwoOwnerWitness A) ∨
      ∃ W : C1CyclicBinaryModuleOwnerWitness A,
        Nat.card W.complement = 3 := by
  rcases degreeSix_high_oddIndexOwner_or_binaryBlock
      hPrimitive N hDegree hHigh with hOdd | ⟨ω₀, D, hFibre, hPoints⟩
  · exact Or.inl hOdd
  · exact Or.inr (D.degreeSix_binaryBlock_ownerWithCard N hFibre hPoints hHigh)

end SymmetricSubgroupAsymptotics

end
