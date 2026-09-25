import SymmetricSubgroupAsymptotics.FiniteCayleyGroup
import SymmetricSubgroupAsymptotics.BinaryNormalGeneratorSteps

/-!
# Exact quotient coset rows for original normal states

Local right-generator equations are checked modulo the original literal
normal subgroup. They prove coset coverage. A separately proved original
kernel cardinality then proves distinctness; no source-membership table or
quotient order declared by a producer is accepted as evidence.
-/

set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {G ι : Type*} [Group G]

/-- Quotient representatives with local original-generator and parent
witnesses. `step_mem` is a statement in the original group. -/
structure BinaryNormalCosetCertificate (generators : ι → G)
    (N : Subgroup G) [N.Normal] (q : ℕ) where
  representatives : Fin q → G
  identity : Fin q
  identity_mem : representatives identity ∈ N
  next : Fin q → ι → Fin q
  step_mem : ∀ i j, representatives (next i j) /
    (representatives i * generators j) ∈ N
  rank : Fin q → ℕ
  parent : ∀ i, i≠identity → Fin q
  letter : ∀ i, i≠identity → ι
  parent_lt : ∀ i hi, rank (parent i hi)<rank i
  parent_next : ∀ i hi, next (parent i hi) (letter i hi)=i

namespace BinaryNormalCosetCertificate

variable {generators : ι → G} {N : Subgroup G} [N.Normal] {q : ℕ}
    (C : BinaryNormalCosetCertificate generators N q)

def words (i : Fin q) : List ι :=
  if hi : i=C.identity then [] else words (C.parent i hi) ++ [C.letter i hi]
termination_by C.rank i
decreasing_by exact C.parent_lt i hi

def quotientRow (i : Fin q) : G ⧸ N := QuotientGroup.mk' N (C.representatives i)

theorem quotientRow_identity : C.quotientRow C.identity=1 :=
  (QuotientGroup.eq_one_iff _).mpr C.identity_mem

theorem quotientRow_next (i : Fin q) (j : ι) :
    C.quotientRow (C.next i j)=C.quotientRow i*QuotientGroup.mk' N (generators j) := by
  unfold quotientRow
  rw [← map_mul]
  exact QuotientGroup.eq_iff_div_mem.mpr (C.step_mem i j)

theorem quotientRow_word (i : Fin q) :
    C.quotientRow i=((C.words i).map (fun j => QuotientGroup.mk' N (generators j))).prod := by
  by_cases hi : i=C.identity
  · subst i
    rw [words]
    simp only [dite_true,List.map_nil,List.prod_nil,C.quotientRow_identity]
  · rw [words,dif_neg hi,List.map_append,List.prod_append,List.map_singleton,List.prod_singleton]
    rw [← quotientRow_word (C.parent i hi),← C.quotientRow_next,C.parent_next]
termination_by C.rank i
decreasing_by exact C.parent_lt i hi

/-- The finite table is an actual Cayley certificate for the original quotient. -/
def toCayley : FiniteCayleyCertificate (fun j => QuotientGroup.mk' N (generators j)) q where
  elements := C.quotientRow
  identity := C.identity
  identity_eq := C.quotientRow_identity
  next := C.next
  next_eq := C.quotientRow_next
  words := C.words
  words_eq := C.quotientRow_word

/-- The exact original generators generate their actual quotient. -/
theorem quotient_generators_full (hgen : Subgroup.closure (Set.range generators)=⊤) :
    Subgroup.closure (Set.range (fun j => QuotientGroup.mk' N (generators j)))=⊤ := by
  have h := congrArg (Subgroup.map (QuotientGroup.mk' N)) hgen
  rw [MonoidHom.map_closure,Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)] at h
  rw [show Set.range (fun j => QuotientGroup.mk' N (generators j))=
    (QuotientGroup.mk' N) '' Set.range generators by ext x; simp]
  exact h

theorem quotientRow_surjective [Finite G]
    (hgen : Subgroup.closure (Set.range generators)=⊤) : Function.Surjective C.quotientRow := by
  intro x
  exact (C.toCayley.mem_closure_iff x).mp (by rw [quotient_generators_full (N := N) hgen]; trivial)

omit [N.Normal] in
/-- A checked original kernel cardinal establishes the quotient order. -/
theorem quotient_card [Finite G] (hcard : Nat.card N*q=Nat.card G) : Nat.card (G ⧸ N)=q := by
  have h := N.card_mul_index
  rw [N.index_eq_card] at h
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h.trans hcard.symm)

/-- Surjectivity plus the actual cardinal identity forces distinct cosets. -/
theorem quotientRow_bijective [Finite G]
    (hgen : Subgroup.closure (Set.range generators)=⊤)
    (hcard : Nat.card N*q=Nat.card G) : Function.Bijective C.quotientRow := by
  apply (Nat.bijective_iff_surjective_and_card C.quotientRow).mpr
  exact ⟨C.quotientRow_surjective hgen,by rw [Nat.card_fin,quotient_card hcard]⟩

def quotientEquiv [Finite G]
    (hgen : Subgroup.closure (Set.range generators)=⊤)
    (hcard : Nat.card N*q=Nat.card G) : Fin q ≃ G ⧸ N :=
  Equiv.ofBijective C.quotientRow (C.quotientRow_bijective hgen hcard)

/-- The proved quotient bijection becomes a faithful numeric encoding.
Its executable generator step is the supplied quotient transition table. -/
def quotientEncoding [Finite G]
    (hgen : Subgroup.closure (Set.range generators)=⊤)
    (hcard : Nat.card N*q=Nat.card G) :
    GeneratorEncoding (fun j => QuotientGroup.mk' N (generators j)) (Fin q) where
  encode := (C.quotientEquiv hgen hcard).symm
  injective := (C.quotientEquiv hgen hcard).symm.injective
  one := C.identity
  encode_one := by
    apply (C.quotientEquiv hgen hcard).symm_apply_eq.mpr
    exact C.quotientRow_identity.symm
  step := C.next
  encode_step x j := by
    obtain ⟨i,rfl⟩ := C.quotientRow_surjective hgen x
    change (C.quotientEquiv hgen hcard).symm
      ((C.quotientEquiv hgen hcard) i*QuotientGroup.mk' N (generators j))=
      C.next ((C.quotientEquiv hgen hcard).symm ((C.quotientEquiv hgen hcard) i)) j
    rw [Equiv.symm_apply_apply]
    apply (C.quotientEquiv hgen hcard).symm_apply_eq.mpr
    exact (C.quotientRow_next i j).symm

def toEncoded [Finite G]
    (hgen : Subgroup.closure (Set.range generators)=⊤)
    (hcard : Nat.card N*q=Nat.card G) :
    EncodedCayleyCertificate (C.quotientEncoding hgen hcard) q where
  rows := id
  identity := C.identity
  identity_eq := rfl
  next := C.next
  next_eq := fun _ _ => rfl
  rank := C.rank
  parent := C.parent
  letter := C.letter
  parent_lt := C.parent_lt
  parent_next := C.parent_next

/-- Executable quotient multiplication retains the original quotient map. -/
@[reducible] def rowGroup [Finite G]
    (hgen : Subgroup.closure (Set.range generators)=⊤)
    (hcard : Nat.card N*q=Nat.card G)
    (prev : Fin q → ι → Fin q) (hprev : ∀ i j, C.next (prev i j) j=i) :
    Group (FiniteGroupRow q) :=
  (C.toEncoded hgen hcard).rowGroup Function.injective_id prev hprev

def rowQuotientHom [Finite G]
    (hgen : Subgroup.closure (Set.range generators)=⊤)
    (hcard : Nat.card N*q=Nat.card G)
    (prev : Fin q → ι → Fin q) (hprev : ∀ i j, C.next (prev i j) j=i) :
    letI := C.rowGroup hgen hcard prev hprev
    FiniteGroupRow q →* G ⧸ N :=
  (C.toEncoded hgen hcard).rowHom Function.injective_id prev hprev

theorem rowQuotientHom_bijective [Finite G]
    (hgen : Subgroup.closure (Set.range generators)=⊤)
    (hcard : Nat.card N*q=Nat.card G)
    (prev : Fin q → ι → Fin q) (hprev : ∀ i j, C.next (prev i j) j=i) :
    Function.Bijective (C.rowQuotientHom hgen hcard prev hprev) := by
  letI := C.rowGroup hgen hcard prev hprev
  refine ⟨(C.toEncoded hgen hcard).rowHom_injective Function.injective_id prev hprev,?_⟩
  apply MonoidHom.range_eq_top.mp
  change ((C.toEncoded hgen hcard).rowHom Function.injective_id prev hprev).range=⊤
  rw [EncodedCayleyCertificate.rowHom_range,quotient_generators_full hgen]

def rowQuotientEquiv [Finite G]
    (hgen : Subgroup.closure (Set.range generators)=⊤)
    (hcard : Nat.card N*q=Nat.card G)
    (prev : Fin q → ι → Fin q) (hprev : ∀ i j, C.next (prev i j) j=i) :
    letI := C.rowGroup hgen hcard prev hprev
    FiniteGroupRow q ≃* G ⧸ N := by
  letI := C.rowGroup hgen hcard prev hprev
  exact MulEquiv.ofBijective (C.rowQuotientHom hgen hcard prev hprev)
    (C.rowQuotientHom_bijective hgen hcard prev hprev)

/-- The quotient table defines a surjection on the original source group. -/
def originalMap [Finite G]
    (hgen : Subgroup.closure (Set.range generators)=⊤)
    (hcard : Nat.card N*q=Nat.card G)
    (prev : Fin q → ι → Fin q) (hprev : ∀ i j, C.next (prev i j) j=i) :
    letI := C.rowGroup hgen hcard prev hprev
    G →* FiniteGroupRow q := by
  letI := C.rowGroup hgen hcard prev hprev
  exact (C.rowQuotientEquiv hgen hcard prev hprev).symm.toMonoidHom.comp (QuotientGroup.mk' N)

theorem originalMap_kernel [Finite G]
    (hgen : Subgroup.closure (Set.range generators)=⊤)
    (hcard : Nat.card N*q=Nat.card G)
    (prev : Fin q → ι → Fin q) (hprev : ∀ i j, C.next (prev i j) j=i) :
    letI := C.rowGroup hgen hcard prev hprev
    (C.originalMap hgen hcard prev hprev).ker=N := by
  letI := C.rowGroup hgen hcard prev hprev
  ext g
  change (C.rowQuotientEquiv hgen hcard prev hprev).symm (QuotientGroup.mk' N g)=1 ↔ g∈N
  rw [← (C.rowQuotientEquiv hgen hcard prev hprev).symm.map_one,
    (C.rowQuotientEquiv hgen hcard prev hprev).symm.injective.eq_iff]
  exact QuotientGroup.eq_one_iff g

theorem rowQuotientEquiv_apply [Finite G]
    (hgen : Subgroup.closure (Set.range generators)=⊤)
    (hcard : Nat.card N*q=Nat.card G)
    (prev : Fin q → ι → Fin q) (hprev : ∀ i j, C.next (prev i j) j=i)
    (i : FiniteGroupRow q) :
    C.rowQuotientEquiv hgen hcard prev hprev i=C.quotientRow i.index := by
  change (C.toEncoded hgen hcard).toCayley.elements i.index=C.quotientRow i.index
  apply (C.quotientEncoding hgen hcard).injective
  rw [EncodedCayleyCertificate.encode_elements]
  change i.index=(C.quotientEquiv hgen hcard).symm ((C.quotientEquiv hgen hcard) i.index)
  exact ((C.quotientEquiv hgen hcard).symm_apply_apply i.index).symm

theorem originalMap_surjective [Finite G]
    (hgen : Subgroup.closure (Set.range generators)=⊤)
    (hcard : Nat.card N*q=Nat.card G)
    (prev : Fin q → ι → Fin q) (hprev : ∀ i j, C.next (prev i j) j=i) :
    Function.Surjective (C.originalMap hgen hcard prev hprev) := by
  letI := C.rowGroup hgen hcard prev hprev
  exact (C.rowQuotientEquiv hgen hcard prev hprev).symm.surjective.comp
    (QuotientGroup.mk'_surjective N)

theorem originalMap_representative [Finite G]
    (hgen : Subgroup.closure (Set.range generators)=⊤)
    (hcard : Nat.card N*q=Nat.card G)
    (prev : Fin q → ι → Fin q) (hprev : ∀ i j, C.next (prev i j) j=i)
    (i : FiniteGroupRow q) :
    C.originalMap hgen hcard prev hprev (C.representatives i.index)=i := by
  letI := C.rowGroup hgen hcard prev hprev
  apply (C.rowQuotientEquiv hgen hcard prev hprev).injective
  change (C.rowQuotientEquiv hgen hcard prev hprev)
    ((C.rowQuotientEquiv hgen hcard prev hprev).symm (C.quotientRow i.index))=_
  rw [MulEquiv.apply_symm_apply,C.rowQuotientEquiv_apply]

end BinaryNormalCosetCertificate
end SymmetricSubgroupAsymptotics
