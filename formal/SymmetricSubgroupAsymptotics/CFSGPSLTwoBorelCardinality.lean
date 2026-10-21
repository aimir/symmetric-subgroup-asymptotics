import SymmetricSubgroupAsymptotics.CFSGPSLTwoCosetCardinality
import SymmetricSubgroupAsymptotics.CFSGPSLTwoBorelIntersection
import SymmetricSubgroupAsymptotics.CFSGPSLTwoTorusCardinality
import SymmetricSubgroupAsymptotics.CFSGPSLTwoProjectiveScalars

/-! Original Borel/product coordinates and order comparison for PSL2.
The actual projective torus is retained, so no unjustified division by
two in even characteristic or small-field recognition is needed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGPSLTwoGeometry
open Matrix CFSGTypeASLTwoWeyl CFSGTypeARootTorus CFSGSLTwoUpperRoots
open CFSGPSLTwoRootCoordinates CFSGSLTwoBruhat
variable {F : Type*} [Field F]

theorem pairTorus_le_borel : pairTorus (F:=F)≤projectiveBorel (F:=F) := by
  rintro _ ⟨c,rfl⟩
  exact projective_torus_mem_borel c

theorem pairTorus_inf_root : pairTorus (F:=F) ⊓ projectiveRoot (F:=F)=⊥ := by
  apply bot_unique
  rintro x ⟨⟨c,hc⟩,⟨a,ha⟩⟩
  have he : projection (torusHom c)=projection (upper a.toAdd) := hc.trans ha.symm
  obtain ⟨r,hr,hm⟩ := projection_eq_implies_scalar_mul (torusHom c) (upper a.toAdd) he
  have hn : r≠0 := by intro he; simp [he] at hr
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 1) hm
  change (torus (by decide : (0 : Fin 2)≠1) c).val 0 1=
    (Matrix.scalar (Fin 2) r*(upper a.toAdd).val) 0 1 at h01
  rw [torus_coe] at h01
  have hz : r*a.toAdd=0 := by
    simpa [Matrix.scalar_apply,Matrix.diagonal_mul] using h01.symm
  have ha0 : a.toAdd=0 := (mul_eq_zero.mp hz).resolve_left hn
  change x=1
  rw [←ha]
  change projectiveUpper a.toAdd=1
  rw [ha0,projectiveUpper_zero]

def borelProduct (z : pairTorus (F:=F)×projectiveRoot (F:=F)) : projectiveBorel (F:=F) :=
  ⟨z.1.val*z.2.val,(projectiveBorel (F:=F)).mul_mem
    (pairTorus_le_borel z.1.property) (projectiveRoot_le_borel z.2.property)⟩

theorem borelProduct_injective : Function.Injective (borelProduct (F:=F)) := by
  have hc : pairTorus (F:=F) ⊓ (projectiveRoot (F:=F)).map
      (MulAut.conj (1 : PSL (F:=F))).toMonoidHom=⊥ := by
    have hid : (MulAut.conj (1 : PSL (F:=F))).toMonoidHom =
        MonoidHom.id (PSL (F:=F)) := by
      apply MonoidHom.ext
      intro g
      simp [MulAut.conj_apply]
    rw [hid, Subgroup.map_id]
    exact pairTorus_inf_root (F:=F)
  have hi := CFSGRankOneTwoCellCardinality.large_injective
    (pairTorus (F:=F)) (projectiveRoot (F:=F)) 1 hc
  intro a b he
  apply hi
  simpa only [mul_one] using congrArg (fun z : projectiveBorel (F:=F) => z.val) he

theorem borelProduct_surjective : Function.Surjective (borelProduct (F:=F)) := by
  intro b
  obtain ⟨g,hg,he⟩ := b.property
  obtain ⟨c,a,hg⟩ := borel_factor g hg
  have hprod : projection g=projectiveTorus c*projectiveUpper a := by
    rw [hg,map_mul]
    rfl
  refine ⟨(⟨projectiveTorus c,⟨c,rfl⟩⟩,⟨projectiveUpper a,projectiveUpper_mem a⟩),?_⟩
  apply Subtype.ext
  exact hprod.symm.trans he

theorem projectiveBorel_card :
    Nat.card (projectiveBorel (F:=F))=Nat.card (pairTorus (F:=F))*Nat.card F := by
  let e := Equiv.ofBijective (borelProduct (F:=F))
    ⟨borelProduct_injective,borelProduct_surjective⟩
  calc
    _ = Nat.card (pairTorus (F:=F)×projectiveRoot (F:=F)) := Nat.card_congr e.symm
    _ = Nat.card (pairTorus (F:=F))*Nat.card F := by
      rw [Nat.card_prod,projectiveRoot_card]

theorem projective_card_eq_torus_mul [Finite F] :
    Nat.card (PSL (F:=F))=Nat.card (pairTorus (F:=F))*Nat.card F*(Nat.card F+1) := by
  rw [projective_card_eq_borel_mul,projectiveBorel_card]
  simp only [Nat.add_comm]

theorem twice_projective_card_ge_classical_order [Finite F] :
    Nat.card F*(Nat.card F-1)*(Nat.card F+1)≤2*Nat.card (PSL (F:=F)) := by
  calc
    _ = (Nat.card F-1)*(Nat.card F*(Nat.card F+1)) := by ring
    _ ≤ (2*Nat.card (pairTorus (F:=F)))*(Nat.card F*(Nat.card F+1)) :=
      Nat.mul_le_mul_right _ field_card_sub_one_le_twice_pairTorus
    _ = _ := by rw [projective_card_eq_torus_mul]; ring

theorem projectiveBorel_index_square_lt_card [Finite F] (hq : 4≤Nat.card F) :
    (projectiveBorel (F:=F)).index^2<Nat.card (PSL (F:=F)) := by
  rw [projectiveBorel_index]
  have hm : 3*Nat.card F≤Nat.card F*(Nat.card F-1) := by
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_left (Nat.card F)
      (by omega : 3≤Nat.card F-1)
  have hs : 2*(Nat.card F+1)<Nat.card F*(Nat.card F-1) := by omega
  have ht := Nat.mul_lt_mul_of_pos_right hs (by omega : 0<Nat.card F+1)
  have ho := twice_projective_card_ge_classical_order (F:=F)
  nlinarith [ht,ho]

end SymmetricSubgroupAsymptotics.CFSGPSLTwoGeometry
