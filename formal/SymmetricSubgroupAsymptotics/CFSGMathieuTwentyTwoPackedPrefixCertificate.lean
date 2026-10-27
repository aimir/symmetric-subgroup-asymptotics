import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoPackedBooleanScalarPilot
import Mathlib.Data.Finset.Card

/-! Shared actual-original semantic template for one first-prefix certificate.
The numerical inputs are a Nat selector, raw coordinate whitelist, and PROVED
fixed-second Bool checks. No survivor bound, outer bound, class bound, or
presentation converse is assumed. The accepted cover is a finite image of
the whitelist and has cardinality at most its length, even for invalid raw
entries. Only the post-certificate realization uses classical choice; the
checker path remains pure Nat/List/Bool and packed point evaluation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoPackedPrefixCertificate
open FiniteListBooleanReflection CFSGMathieuTwentyTwoPackedPointMaps
open CFSGMathieuTwentyTwoFiveTransversalCover
open CFSGMathieuTwentyTwoElevenGeneration CFSGMathieuTwentyTwoRecoveredPairRelations
open CFSGMathieuTwentyTwoScalarRelationWords
open CFSGMathieuTwentyTwoPackedBooleanScalarPilot
  (rawThirdDomain rawFourthDomain rawFifthDomain
    mem_rawThirdDomain mem_rawFourthDomain mem_rawFifthDomain)

abbrev Tail : Type := Second × (Third × (Fourth × Fifth))
abbrev RawTail : Type := ℕ × (ℕ × (ℕ × ℕ))
abbrev Selector : Type := ℕ → ℕ → ℕ → ℕ → ℕ

def coordinates (t : Tail) : RawTail :=
  (t.1.val.val,(t.2.1.val.val,(t.2.2.1.val.val,t.2.2.2.val.val)))

def code (i : Fin 22) (t : Tail) : Code := ((i,t.1),t.2)

theorem coordinates_injective : Function.Injective coordinates := by
  rintro ⟨j,k,l,m⟩ ⟨j',k',l',m'⟩ h
  have hj : j = j' := Subtype.ext (Fin.ext (congrArg (fun q : RawTail => q.1) h))
  have hk : k = k' := Subtype.ext (Fin.ext (congrArg (fun q : RawTail => q.2.1) h))
  have hl : l = l' := Subtype.ext (Fin.ext (congrArg (fun q : RawTail => q.2.2.1) h))
  have hm : m = m' := Subtype.ext (Fin.ext (congrArg (fun q : RawTail => q.2.2.2) h))
  subst j'
  subst k'
  subst l'
  subst m'
  rfl

private def defaultTail : Tail :=
  (⟨1,by decide⟩,(⟨2,by decide⟩,(⟨5,by decide⟩,⟨3,by decide⟩)))

/-- A total semantic realization; invalid coordinates add at most one image
per invalid whitelist entry and therefore cannot invalidate the size bound. -/
def realize (q : RawTail) : Tail := by
  classical
  exact if h : ∃ t : Tail, coordinates t = q then Classical.choose h else defaultTail

theorem realize_coordinates (t : Tail) : realize (coordinates t) = t := by
  classical
  have h : ∃ u : Tail, coordinates u = coordinates t := ⟨t,rfl⟩
  simp only [realize,dif_pos h]
  exact coordinates_injective (Classical.choose_spec h)

def codeCheck (i : ℕ) (failure : Selector) (whitelist : List RawTail)
    (j k l m : ℕ) : Bool :=
  whitelist.contains (j,(k,(l,m))) ||
    (let n := failure j k l m
     let r := (n / 22) % 5
     let p := n % 22
     !(packedScalarRelation r i j k l m p == p))

def batchCheck (i : ℕ) (failure : Selector) (whitelist : List RawTail) (j : ℕ) : Bool :=
  rawThirdDomain.all (fun k => rawFourthDomain.all (fun l =>
    rawFifthDomain.all (codeCheck i failure whitelist j k l)))

def failureRelator (failure : Selector) (t : Tail) : Fin 5 :=
  ⟨(failure t.1.val.val t.2.1.val.val t.2.2.1.val.val t.2.2.2.val.val / 22) % 5,
    Nat.mod_lt _ (by decide)⟩

def failurePoint (failure : Selector) (t : Tail) : Fin 22 :=
  ⟨failure t.1.val.val t.2.1.val.val t.2.2.1.val.val t.2.2.2.val.val % 22,
    Nat.mod_lt _ (by decide)⟩

theorem accepts_coordinates_mem (i : Fin 22) (failure : Selector) (whitelist : List RawTail)
    (hbatches : ∀ j : Second, batchCheck i.val failure whitelist j.val.val = true)
    (t : Tail) (h : Accepts (decode (code i t))) : coordinates t ∈ whitelist := by
  have hk := all_true_at rawThirdDomain _ (hbatches t.1)
    t.2.1.val.val (mem_rawThirdDomain t.2.1)
  have hl := all_true_at rawFourthDomain _ hk
    t.2.2.1.val.val (mem_rawFourthDomain t.2.2.1)
  have hm := all_true_at rawFifthDomain _ hl
    t.2.2.2.val.val (mem_rawFifthDomain t.2.2.2)
  change (whitelist.contains (coordinates t) || _) = true at hm
  rw [Bool.or_eq_true_eq_eq_true_or_eq_true] at hm
  rcases hm with hw | hn
  · exact List.contains_iff_mem.mp hw
  · exfalso
    apply not_beq_sound _ _ hn
    have he := accepts_scalarRelation (code i t) h (failureRelator failure t) (failurePoint failure t)
    exact (packedScalarRelation_eq (failureRelator failure t) (code i t)
      (failurePoint failure t)).trans (congrArg (fun p : Fin 22 => p.val) he)

def acceptedElements (i : Fin 22) (whitelist : List RawTail) : Finset CFSG.Models.Mathieu22 := by
  classical
  exact (whitelist.map (fun q => decode (code i (realize q)))).toFinset

theorem accepts_mem_acceptedElements (i : Fin 22) (failure : Selector) (whitelist : List RawTail)
    (hbatches : ∀ j : Second, batchCheck i.val failure whitelist j.val.val = true)
    (c : Code) (hfirst : c.1.1 = i) (h : Accepts (decode c)) :
    decode c ∈ acceptedElements i whitelist := by
  classical
  rcases c with ⟨⟨a,j⟩,⟨k,⟨l,m⟩⟩⟩
  change a = i at hfirst
  subst a
  let t : Tail := (j,(k,(l,m)))
  have hw : coordinates t ∈ whitelist := accepts_coordinates_mem i failure whitelist hbatches t h
  change decode (code i t) ∈ (whitelist.map (fun q => decode (code i (realize q)))).toFinset
  apply List.mem_toFinset.mpr
  apply List.mem_map.mpr
  refine ⟨coordinates t,hw,?_⟩
  rw [realize_coordinates]

theorem acceptedElements_card_le_length (i : Fin 22) (whitelist : List RawTail) :
    (acceptedElements i whitelist).card ≤ whitelist.length := by
  classical
  change (whitelist.map (fun q => decode (code i (realize q)))).toFinset.card ≤ whitelist.length
  simpa only [List.length_map] using
    (List.toFinset_card_le (whitelist.map (fun q => decode (code i (realize q)))))

theorem map_second_mem_acceptedElements (i : Fin 22) (failure : Selector) (whitelist : List RawTail)
    (hbatches : ∀ j : Second, batchCheck i.val failure whitelist j.val.val = true)
    (f : MulAut CFSG.Models.Mathieu22) (hf : f firstElement = firstElement)
    (c : Code) (hc : decode c = f secondElement) (hfirst : c.1.1 = i) :
    f secondElement ∈ acceptedElements i whitelist := by
  rw [← hc]
  apply accepts_mem_acceptedElements i failure whitelist hbatches c hfirst
  rw [hc]
  exact accepts_of_fixed_first f hf

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoPackedPrefixCertificate
