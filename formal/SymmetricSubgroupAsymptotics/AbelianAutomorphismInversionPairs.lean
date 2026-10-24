import SymmetricSubgroupAsymptotics.PermutationAutomorphismPuncturedAction
import SymmetricSubgroupAsymptotics.FreeInvolutionPairQuotient
import SymmetricSubgroupAsymptotics.FiniteGroupBinaryOrderGenerators

/-! Actual inverse pairs of nonidentity elements of an abelian group.
An automorphism fixing every pair is globally identity or inversion;
therefore the kernel of a faithful complement's pair action has order
at most two. This uses no guessed projective scalar recognition. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.AbelianAutomorphismInversionPairs
open PermutationAutomorphismPuncturedAction

variable (V : Type) [CommGroup V]

def inversionAut : MulAut V where
  toEquiv := Equiv.inv V
  map_mul' x y := by
    change (x*y)⁻¹=x⁻¹*y⁻¹
    exact (mul_inv_rev x y).trans (mul_comm _ _)

def inversion (v : Punctured V) : Punctured V :=
  ⟨v.val⁻¹,fun h=>v.property (inv_eq_one.mp h)⟩

theorem inversion_involutive : Function.Involutive (inversion V) :=
  fun v=>Subtype.ext (inv_inv v.val)

abbrev PairCarrier := FreeInvolutionPairQuotient.Pairs (inversion V) (inversion_involutive V)

theorem automorphism_eq_one_or_inversion (f : MulAut V)
    (hf : ∀v:V,f v=v ∨ f v=v⁻¹) : f=1 ∨ f=inversionAut V := by
  by_cases hall:∀v:V,f v=v
  · exact Or.inl (MulEquiv.ext hall)
  · right
    obtain ⟨u,hu⟩ := not_forall.mp hall
    have hu' : f u=u⁻¹ := (hf u).resolve_left hu
    apply MulEquiv.ext
    intro v
    change f v=v⁻¹
    rcases hf v with hv|hv
    · rcases hf (u*v) with hprod|hprod
      · have he : u⁻¹*v=u*v := by
          calc
            u⁻¹*v=f (u*v) := by rw [map_mul,hu',hv]
            _=u*v := hprod
        exact (hu (hu'.trans (mul_right_cancel he))).elim
      · have he : u⁻¹*v=u⁻¹*v⁻¹ := by
          calc
            u⁻¹*v=f (u*v) := by rw [map_mul,hu',hv]
            _=(u*v)⁻¹ := hprod
            _=u⁻¹*v⁻¹ := by rw [mul_inv_rev,mul_comm]
        exact hv.trans (mul_left_cancel he)
    · exact hv

variable {V} {H : Type} [Group H] (φ : H→*MulAut V)

private theorem punctured_commutes_inversion (h : H) (v : Punctured V) :
    puncturedHom φ h (inversion V v)=inversion V (puncturedHom φ h v) := by
  apply Subtype.ext
  exact map_inv (φ h) v.val

def pairAction : H→*Equiv.Perm (PairCarrier V) :=
  FreeInvolutionPairQuotient.pairHom (inversion V) (inversion_involutive V)
    (puncturedHom φ) (punctured_commutes_inversion φ)

theorem kernel_scalar (h : (pairAction φ).ker) : φ h.val=1 ∨ φ h.val=inversionAut V := by
  apply automorphism_eq_one_or_inversion V (φ h.val)
  intro v
  by_cases hv:v=1
  · exact Or.inl (by rw [hv,map_one])
  · let x : Punctured V := ⟨v,hv⟩
    have he := Equiv.congr_fun h.property
      (FreeInvolutionPairQuotient.mk (inversion V) (inversion_involutive V) x)
    change FreeInvolutionPairQuotient.mk (inversion V) (inversion_involutive V)
        (puncturedHom φ h.val x)=
      FreeInvolutionPairQuotient.mk (inversion V) (inversion_involutive V) x at he
    rcases (FreeInvolutionPairQuotient.mk_eq_mk (inversion V)
      (inversion_involutive V) _ _).mp he with he|he
    · exact Or.inl (congrArg Subtype.val he)
    · exact Or.inr (congrArg Subtype.val he)

theorem kernel_card_le_two (hφ : Function.Injective φ) : Nat.card (pairAction φ).ker≤2 := by
  let tag : (pairAction φ).ker→Bool := fun h=>if φ h.val=1 then false else true
  have hinj : Function.Injective tag := by
    intro h k he
    apply Subtype.ext
    apply hφ
    by_cases hh:φ h.val=1
    · by_cases hk:φ k.val=1
      · exact hh.trans hk.symm
      · have hbad : (false:Bool)=true := by simpa only [tag,if_pos hh,if_neg hk] using he
        cases hbad
    · by_cases hk:φ k.val=1
      · have hbad : (true:Bool)=false := by simpa only [tag,if_neg hh,if_pos hk] using he
        cases hbad
      · exact ((kernel_scalar φ h).resolve_left hh).trans
          ((kernel_scalar φ k).resolve_left hk).symm
  have hh := Nat.card_le_card_of_injective tag hinj
  simpa using hh

theorem kernel_genRank_le_one [Finite H] (hφ : Function.Injective φ) :
    MarkedC4.genRank (pairAction φ).ker≤1 :=
  FiniteGroupBinaryOrderGenerators.genRank_le_of_card_le_two_pow (pairAction φ).ker 1
    (by simpa using kernel_card_le_two φ hφ)

theorem two_mul_pairCard_le [Finite V] (hfree : ∀v:V,v≠1→v⁻¹≠v) :
    2*Nat.card (PairCarrier V)≤Nat.card V-1 := by
  have hh := FreeInvolutionPairQuotient.two_mul_card_le (inversion V)
    (inversion_involutive V) (fun v h=>hfree v.val v.property (congrArg Subtype.val h))
  simpa only [punctured_card] using hh

end SymmetricSubgroupAsymptotics.AbelianAutomorphismInversionPairs
