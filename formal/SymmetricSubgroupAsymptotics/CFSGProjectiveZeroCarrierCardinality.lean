import SymmetricSubgroupAsymptotics.CFSGProjectivePolynomialCount

/-! A projective carrier retains all nonzero scalar representatives,
while an origin in the vector carrier is omitted by those fibres.
This gives the strict one-vector saving without a projective order
formula or a choice of normalized coordinate charts. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGProjectiveZeroCarrierCardinality
open CFSGProjectivePolynomialCount
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Finite K] [Finite V]

theorem projective_carrier_card_mul_units_add_one_le
    (P : Set (Projectivization K V)) (W : Set V) (hzero : (0:V)∈W)
    (hW : ∀ p : P,∀a : Kˣ,a • p.val.rep∈W) :
    Nat.card P*(Nat.card K-1)+1≤Nat.card W := by
  classical
  let f : P×Kˣ→W := fun x=>⟨x.2 • x.1.val.rep,hW x.1 x.2⟩
  have hf : Function.Injective f := by
    rintro ⟨p,a⟩ ⟨q,b⟩ he
    have hh : (p.val,a)=(q.val,b) := scalarRep_injective (congrArg Subtype.val he)
    have hp : p=q := Subtype.ext
      (congrArg (fun z : Projectivization K V×Kˣ=>z.1) hh)
    have hab : a=b := congrArg (fun z : Projectivization K V×Kˣ=>z.2) hh
    exact Prod.ext hp hab
  have horigin : (⟨0,hzero⟩:W)∉Set.range f := by
    rintro ⟨⟨p,a⟩,he⟩
    have hz := congrArg Subtype.val he
    change (a:K) • p.val.rep=0 at hz
    exact (smul_ne_zero (Units.ne_zero a) p.val.rep_nonzero) hz
  letI : Fintype (P×Kˣ) := Fintype.ofFinite _
  letI : Fintype W := Fintype.ofFinite _
  have hlt : Nat.card (P×Kˣ)<Nat.card W := by
    simpa only [Nat.card_eq_fintype_card] using
      Fintype.card_lt_of_injective_of_notMem f hf horigin
  simpa only [Nat.card_prod,Nat.card_units,Nat.succ_eq_add_one] using Nat.succ_le_of_lt hlt

end SymmetricSubgroupAsymptotics.CFSGProjectiveZeroCarrierCardinality
