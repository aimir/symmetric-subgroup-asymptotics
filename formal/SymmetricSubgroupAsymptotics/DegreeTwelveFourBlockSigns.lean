import SymmetricSubgroupAsymptotics.DegreeTwelveFourBlockCore
import SymmetricSubgroupAsymptotics.PrimeSubdirectNormalHead
import SymmetricSubgroupAsymptotics.RelativeAmbientSubgroup

/-!
# Sign elimination in the original four-by-three block kernel

A finite full subdirect family controls the relative head of every original
normal subgroup, with its whole ambient conjugation action retained.  An odd
transitive four-point image has zero relative ternary head on every normal
subgroup.  Original ambient conjugation propagates an odd fibre to all fibres,
contradicting the nonzero saturated original kernel intersection.

The block kernel is never replaced by the whole coordinate product.  The
endpoint applies to every literal choice of four-point fibre charts.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics

/-- Relative-normal version of the coordinate head bound.  Unlike the bound
for the head of K itself, this retains an arbitrary original normal M of K. -/
theorem primeRelativeHead_coordinate_le (p : ℕ) [Fact p.Prime] (n : ℕ)
    (A : Fin n → Type*) [∀ i, Group (A i)] [∀ i, Finite (A i)]
    (c : Fin n → ℕ)
    (hbound : ∀ i (N : Subgroup (A i)) (hN : N.Normal),
      letI := hN
      Module.finrank (ZMod p) (primeRelativeCharacters p N) ≤ c i)
    (K : Subgroup (∀ i, A i))
    (hfull : ∀ i, Function.Surjective (fun k : K => (k : ∀ i, A i) i))
    (M : Subgroup K) [M.Normal] :
    Module.finrank (ZMod p) (primeRelativeCharacters p M) ≤ ∑ i, c i := by
  induction n with
  | zero =>
    have hc : Subsingleton (PrimeCharacters p M) := by
      refine ⟨fun χ ψ => ?_⟩
      apply AddMonoidHom.ext
      intro m
      have hm : m = 0 := Subsingleton.elim _ _
      rw [hm, map_zero, map_zero]
    letI := hc
    have hz : Module.finrank (ZMod p) (primeRelativeCharacters p M) = 0 :=
      Module.finrank_zero_of_subsingleton
    simp only [hz, Nat.zero_le]
  | succ n ih =>
    let tail : (∀ i : Fin (n+1), A i) →* (∀ i : Fin n, A i.succ) := {
      toFun := fun x i => x i.succ
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
    let B : Subgroup (∀ i : Fin n, A i.succ) := K.map tail
    let φ : K →* (A 0 × B) := {
      toFun := fun k => ((k : ∀ i, A i) 0, ⟨tail k, ⟨k, k.2, rfl⟩⟩)
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
    have hφ : Function.Injective φ := by
      intro x y he
      apply Subtype.ext
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact congrArg Prod.fst he
      · exact congrArg (fun z : A 0 × B => (z.2 : ∀ i : Fin n, A i.succ) j) he
    let R := φ.range
    let e : K ≃* R := MonoidHom.ofInjective (f := φ) hφ
    let M' : Subgroup R := M.map e.toMonoidHom
    letI : M'.Normal := Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective
    have hA : Function.Surjective (Prod.fst ∘ R.subtype) := by
      intro a
      obtain ⟨k, hk⟩ := hfull 0 a
      exact ⟨⟨φ k, ⟨k, rfl⟩⟩, hk⟩
    have hB : Function.Surjective (Prod.snd ∘ R.subtype) := by
      rintro ⟨b, hb⟩
      obtain ⟨k, hk, hkb⟩ := hb
      exact ⟨⟨φ ⟨k, hk⟩, ⟨⟨k, hk⟩, rfl⟩⟩, Subtype.ext hkb⟩
    have htail : ∀ i : Fin n,
        Function.Surjective (fun b : B => (b : ∀ i : Fin n, A i.succ) i) := by
      intro i a
      obtain ⟨k, hk⟩ := hfull i.succ a
      exact ⟨⟨tail k, ⟨k, k.2, rfl⟩⟩, hk⟩
    letI := SubdirectNormalHead.firstAxis_normal R M' hA
    letI := SubdirectNormalHead.secondImage_normal R M' hB
    have hrec := ih (fun i : Fin n => A i.succ) (fun i => c i.succ)
      (fun i => hbound i.succ) B htail (SubdirectNormalHead.secondImage R M')
    have haxis := hbound 0 (SubdirectNormalHead.firstAxis R M') inferInstance
    have hpair := SubdirectNormalHead.relativeHead_le R M' p hA hB
    have he := (relativeCharacterAmbientCongr p e M M' rfl).finrank_eq
    rw [← he, Fin.sum_univ_succ]
    exact (hpair.trans (Nat.add_le_add hrec haxis)).trans_eq (Nat.add_comm _ _)

/-- Vanishing on the actual coordinate images implies vanishing for every
original normal subgroup of a faithfully represented source. -/
theorem primeRelativeHead_faithful_family_eq_zero
    (p : ℕ) [Fact p.Prime] {G I : Type*} [Group G] [Finite G] [Finite I]
    (A : I → Type*) [∀ i, Group (A i)] [∀ i, Finite (A i)]
    (ρ : ∀ i, G →* A i) (honto : ∀ i, Function.Surjective (ρ i))
    (hfaithful : Function.Injective (fun g i => ρ i g))
    (hzero : ∀ i (N : Subgroup (A i)) (hN : N.Normal),
      letI := hN
      Module.finrank (ZMod p) (primeRelativeCharacters p N) = 0)
    (M : Subgroup G) [M.Normal] :
    Module.finrank (ZMod p) (primeRelativeCharacters p M) = 0 := by
  letI : Fintype I := Fintype.ofFinite I
  let enum : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let f : G →* (∀ i : Fin (Fintype.card I), A (enum i)) := {
    toFun := fun g i => ρ (enum i) g
    map_one' := by funext i; exact (ρ (enum i)).map_one
    map_mul' := by intro g h; funext i; exact (ρ (enum i)).map_mul g h }
  have hf : Function.Injective f := by
    intro g h he
    apply hfaithful
    funext i
    obtain ⟨j, rfl⟩ := enum.surjective i
    exact congrFun he j
  let e : G ≃* f.range := MonoidHom.ofInjective (f := f) hf
  let M' := M.map e.toMonoidHom
  letI : M'.Normal := Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective
  have hfull : ∀ i, Function.Surjective
      (fun k : f.range => (k : ∀ i : Fin (Fintype.card I), A (enum i)) i) := by
    intro i a
    obtain ⟨g, hg⟩ := honto (enum i) a
    exact ⟨⟨f g, ⟨g, rfl⟩⟩, hg⟩
  have h := primeRelativeHead_coordinate_le p (Fintype.card I)
    (fun i => A (enum i)) (fun _ => 0)
    (fun i N hN => by letI := hN; exact le_of_eq (hzero (enum i) N hN))
    f.range hfull M'
  have he := (relativeCharacterAmbientCongr p e M M' rfl).finrank_eq
  rw [he] at h
  simpa only [Finset.sum_const_zero, Nat.le_zero] using h

/-- Positivity, rather than a supplied exact local rank, already forces the
literal natural alternating action in degree four. -/
theorem degreeFour_positive_relativeHead_eq_alternating
    (U : Subgroup (Equiv.Perm (Fin 4)))
    [MulAction.IsPretransitive U (Fin 4)] (M : Subgroup U) [M.Normal]
    (hRank : 0 < Module.finrank (ZMod 3) (primeRelativeCharacters 3 M)) :
    U = alternatingGroup (Fin 4) := by
  letI : Nontrivial (primeRelativeCharacters 3 M) := Module.finrank_pos_iff.mp hRank
  obtain ⟨θ, hθ⟩ := exists_ne (0 : primeRelativeCharacters 3 M)
  have hθ0 : (θ.1 : PrimeCharacters 3 M) ≠ 0 := by
    intro hz
    apply hθ
    exact Subtype.ext hz
  have h3M : 3 ∣ Nat.card M := by
    have hd := Subgroup.card_dvd_of_surjective (ternaryCharacterHom θ.1)
      ((ternaryCharacter_surjective_iff_ne_zero θ.1).mpr hθ0)
    simpa only [TernaryCyclic, Nat.card_eq_fintype_card, ZMod.card] using hd
  have h3U := h3M.trans M.card_subgroup_dvd_card
  have hIndex : (MulAction.stabilizer U (0 : Fin 4)).index = 4 := by
    simpa only [Nat.card_fin] using MulAction.index_stabilizer_of_transitive U (0 : Fin 4)
  have hMul := (MulAction.stabilizer U (0 : Fin 4)).card_mul_index
  rw [hIndex] at hMul
  have h4U : 4 ∣ Nat.card U :=
    ⟨Nat.card (MulAction.stabilizer U (0 : Fin 4)), by omega⟩
  have hUpper : Nat.card U ≤ 24 := by
    have h := Subgroup.card_le_card_group U
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm] at h ⊢
    exact h
  have hPos : 0 < Nat.card U := Nat.card_pos
  obtain ⟨a, ha⟩ := h3U
  obtain ⟨b, hb⟩ := h4U
  have hCard : Nat.card U = 12 ∨ Nat.card U = 24 := by omega
  rcases hCard with h12 | h24
  · apply Equiv.Perm.eq_alternatingGroup_of_index_eq_two
    have h := U.card_mul_index
    have hPerm : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
      norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
    rw [h12, hPerm] at h
    omega
  · have hTop : U = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [h24]
      norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
    have hz := degreeFour_top_relativeHead_eq_zero U hTop M
    omega

namespace DegreeTwelveFourBlockSigns

open DegreeTwelveFourBlockCore

variable {A Ω X : Type} [Group A] [Finite A] [Finite Ω] [Finite X]
    [MulAction A Ω] [MulAction A X]
    [FaithfulSMul A Ω] [MulAction.IsPretransitive A Ω]
    [MulAction.IsPretransitive A X]
    (b : Ω → X) (hb : ∀ (a : A) (ω : Ω), b (a • ω) = a • b ω)
    (e : ∀ x : X, Fin 4 ≃ originalBlockFibre b x)

omit [Finite A] in
/-- A top image of the same order as its transitive degree acts regularly;
thus an original element fixing any block lies in the original top kernel. -/
theorem fixes_block_mem_kernel
    (hTop : Nat.card (MulAction.toPermHom A X).range = Nat.card X)
    (a : A) (x : X) (hax : a • x = x) :
    a ∈ (MulAction.toPermHom A X).ker := by
  let T := (MulAction.toPermHom A X).range
  letI : MulAction.IsPretransitive T X := ⟨fun y z => by
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A y z
    exact ⟨⟨MulAction.toPermHom A X g, ⟨g, rfl⟩⟩, hg⟩⟩
  have hi : (MulAction.stabilizer T x).index = Nat.card X :=
    MulAction.index_stabilizer_of_transitive T x
  have hm := (MulAction.stabilizer T x).card_mul_index
  have hp : 0 < Nat.card X := by
    letI : Nonempty X := ⟨x⟩
    exact Nat.card_pos
  have hs : Nat.card (MulAction.stabilizer T x) = 1 := by
    rw [hi, hTop] at hm
    nlinarith
  have hbot := (MulAction.stabilizer T x).eq_bot_of_card_eq hs
  let t : T := ⟨MulAction.toPermHom A X a, ⟨a, rfl⟩⟩
  have ht : t ∈ MulAction.stabilizer T x := hax
  rw [hbot, Subgroup.mem_bot] at ht
  exact congrArg Subtype.val ht

omit [Finite A] [Finite Ω] [FaithfulSMul A Ω] in
include hb in
/-- Every literal fibre image of the original kernel is transitive once
the original top is regular. No full direct-product projection is inferred. -/
theorem fibreCoordinate_pretransitive
    (hTop : Nat.card (MulAction.toPermHom A X).range = Nat.card X) (x : X) :
    MulAction.IsPretransitive (fibreCoordinate b hb e x).range (Fin 4) := by
  constructor
  intro i j
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq A ((e x i : originalBlockFibre b x) : Ω)
    ((e x j : originalBlockFibre b x) : Ω)
  have hax : a • x = x := by
    have h := congrArg b ha
    rw [hb, (e x i).2, (e x j).2] at h
    exact h
  have hak := fixes_block_mem_kernel hTop a x hax
  let k : Kernel (A := A) (X := X) := ⟨a, hak⟩
  refine ⟨⟨fibreCoordinate b hb e x k, ⟨k, rfl⟩⟩, ?_⟩
  change (e x).symm (OriginalBlockClassBound.coordinate b hb x k (e x i)) = j
  apply (e x).symm_apply_eq.mpr
  exact Subtype.ext ha

/-- The obstruction to an odd local branch, expressed on the whole original
normal intersection. It works for any number of four-point fibres with
regular original top. -/
theorem allEven_of_intersection_head_pos
    (hTop : Nat.card (MulAction.toPermHom A X).range = Nat.card X)
    (N : Subgroup A) [N.Normal]
    (hHead : 0 < Module.finrank (ZMod 3)
      (primeRelativeCharacters 3 (N ⊓ (MulAction.toPermHom A X).ker))) :
    AllEven b hb e := by
  letI : ∀ x : X, Fintype (originalBlockFibre b x) := fun _ => Fintype.ofFinite _
  by_contra hEven
  change ¬ ∀ (x : X) (k : Kernel (A := A) (X := X)),
    fibreCoordinate b hb e x k ∈ alternatingGroup (Fin 4) at hEven
  push Not at hEven
  obtain ⟨x₀, k₀, hk₀⟩ := hEven
  have hsign₀ : OriginalBlockSignCoordinates.coordinateSign b hb x₀ ≠ 1 := by
    intro hz
    apply hk₀
    rw [Equiv.Perm.mem_alternatingGroup]
    have h := congrArg (fun f : Kernel (A := A) (X := X) →* Multiplicative (ZMod 2) => f k₀) hz
    have hbin : permutationBinarySign (Fin 4) (fibreCoordinate b hb e x₀ k₀) = 1 := by
      change permutationBinarySign (Fin 4)
        ((e x₀).symm.permCongr (OriginalBlockClassBound.coordinate b hb x₀ k₀)) = 1
      rw [permutationBinarySign_permCongr]
      exact h
    have hs := (permutationBinarySign_eq_one _ _).mp hbin
    rw [show instDecidableEqFin 4 = Classical.decEq (Fin 4) from Subsingleton.elim _ _]
    exact hs
  have hsign := OriginalBlockSignCoordinates.all_coordinateSigns_nontrivial b hb x₀ hsign₀
  let U : X → Subgroup (Equiv.Perm (Fin 4)) := fun x => (fibreCoordinate b hb e x).range
  let ρ : ∀ x, Kernel (A := A) (X := X) →* U x :=
    fun x => (fibreCoordinate b hb e x).rangeRestrict
  have hfaithful : Function.Injective (fun k x => ρ x k) := by
    intro k l hkl
    apply OriginalBlockClassBound.coordinates_injective b hb
    funext x
    apply (e x).symm.permCongrHom.injective
    exact congrArg Subtype.val (congrFun hkl x)
  have hzero : ∀ x (M : Subgroup (U x)) (hM : M.Normal),
      letI := hM
      Module.finrank (ZMod 3) (primeRelativeCharacters 3 M) = 0 := by
    intro x M hM
    letI := hM
    letI : MulAction.IsPretransitive (U x) (Fin 4) :=
      fibreCoordinate_pretransitive b hb e hTop x
    by_contra hz
    have hpos : 0 < Module.finrank (ZMod 3) (primeRelativeCharacters 3 M) := by omega
    have hU := degreeFour_positive_relativeHead_eq_alternating (U x) M hpos
    apply hsign x
    apply MonoidHom.ext
    intro k
    have heven : fibreCoordinate b hb e x k ∈ alternatingGroup (Fin 4) := by
      rw [← hU]
      exact ⟨k, rfl⟩
    change permutationBinarySign (originalBlockFibre b x)
      (OriginalBlockClassBound.coordinate b hb x k) = 1
    calc
      _ = permutationBinarySign (Fin 4) (fibreCoordinate b hb e x k) := by
        change permutationBinarySign (originalBlockFibre b x)
          (OriginalBlockClassBound.coordinate b hb x k) =
            permutationBinarySign (Fin 4)
              ((e x).symm.permCongr (OriginalBlockClassBound.coordinate b hb x k))
        exact (permutationBinarySign_permCongr (e x).symm _).symm
      _ = 1 := by
        apply (permutationBinarySign_eq_one _ _).mpr
        have heven' : (fibreCoordinate b hb e x k) ∈
            @alternatingGroup (Fin 4) _ (Classical.decEq (Fin 4)) := by
          rw [show Classical.decEq (Fin 4) = instDecidableEqFin 4 from
            Subsingleton.elim _ _]
          exact heven
        exact (@Equiv.Perm.mem_alternatingGroup (Fin 4) _
          (Classical.decEq (Fin 4)) _).mp heven'
  have hz := primeRelativeHead_faithful_family_eq_zero 3 (fun x => U x) ρ
    (fun x => (fibreCoordinate b hb e x).rangeRestrict_surjective) hfaithful hzero
    (N.subgroupOf (MulAction.toPermHom A X).ker)
  have hle := primeRelativeHead_inf_le_subgroupOf 3 N (MulAction.toPermHom A X).ker
  rw [hz] at hle
  omega

end DegreeTwelveFourBlockSigns

namespace OriginalMinimalBlock

variable {A Ω : Type} [Group A] [Finite A] [Finite Ω] [MulAction A Ω]
    [FaithfulSMul A Ω] [MulAction.IsPretransitive A Ω]
    {ω₀ : Ω} (D : OriginalMinimalBlock (A := A) ω₀)

/-- Complete sign elimination in the saturated original 4-by-3 branch.
It holds for every choice of literal four-point fibre labels. -/
theorem fourByThree_allEven
    (N : Subgroup A) [N.Normal] (c : ActualChiefSeries D.Component)
    (hPoints : Nat.card D.Points = 3) (hTopOrder : Nat.card D.Top = 3)
    (hWeight : actualChiefSeriesTernaryWeight c = 1)
    (hTop : Module.finrank (ZMod 3)
      (primeRelativeCharacters 3 (originalNormalRange D.topMap N)) = 1)
    (hRank : Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) = 2)
    (e : ∀ x : D.Points, Fin 4 ≃ originalBlockFibre D.map x) :
    DegreeTwelveFourBlockCore.AllEven D.map D.map_equivariant e := by
  have hHead := D.fourByThree_intersection_head_eq_one N c hPoints hWeight hTop hRank
  apply DegreeTwelveFourBlockSigns.allEven_of_intersection_head_pos
    D.map D.map_equivariant e (hTopOrder.trans hPoints.symm) N
  rw [hHead]
  norm_num

end OriginalMinimalBlock
end SymmetricSubgroupAsymptotics
