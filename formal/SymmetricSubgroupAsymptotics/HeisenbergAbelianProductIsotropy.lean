import SymmetricSubgroupAsymptotics.ScalarCentralLineIsotropicCardinality

/-! A Heisenberg group times arbitrary additive central coordinates has
the same isotropic vector-image bound. The SAME central preimage may be
diagonal across the scalar line and the extra centre. No full-field
linearity or invariance of the subgroup is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.HeisenbergAbelianProductIsotropy
open CFSGHeisenbergCoordinateGroup CFSGHeisenbergSymplecticQuotient
variable {K E : Type*} [Field K] [AddCommGroup E] {m : ℕ}
private abbrev R := Element K m × Multiplicative E
private abbrev V := (Fin m → K) × (Fin m → K)

def fullCentralHom : Multiplicative (K × E) →* R (K := K) (E := E) (m := m) where
  toFun z := (central (Multiplicative.ofAdd z.toAdd.1),Multiplicative.ofAdd z.toAdd.2)
  map_one' := rfl
  map_mul' z t := by
    apply Prod.ext
    · exact (central (K := K) (m := m)).map_mul _ _
    · rfl

def vectorHom : R (K := K) (E := E) (m := m) →* Multiplicative (V (K := K) (m := m)) :=
  projection.comp (MonoidHom.fst _ _)

def vectorImage (J : Subgroup (R (K := K) (E := E) (m := m))) :
    AddSubgroup (V (K := K) (m := m)) := (J.map vectorHom).toAddSubgroup'

def centralPreimage (J : Subgroup (R (K := K) (E := E) (m := m))) : AddSubgroup (K × E) :=
  (J.comap fullCentralHom).toAddSubgroup'

private def scalarLine : K →+ K × E where
  toFun t := (t,0)
  map_zero' := rfl
  map_add' a b := Prod.ext rfl (zero_add 0).symm

theorem vectorImage_pairing_mem (J : Subgroup (R (K := K) (E := E) (m := m)))
    (v w : V (K := K) (m := m)) (hv : v ∈ vectorImage J) (hw : w ∈ vectorImage J) :
    (pairing v w,(0 : E)) ∈ centralPreimage J := by
  change Multiplicative.ofAdd v ∈ J.map vectorHom at hv
  change Multiplicative.ofAdd w ∈ J.map vectorHom at hw
  obtain ⟨g,hg,hgv⟩ := hv
  obtain ⟨h,hh,hhw⟩ := hw
  have hgv' : (g.1.a,g.1.b)=v := congrArg Multiplicative.toAdd hgv
  have hhw' : (h.1.a,h.1.b)=w := congrArg Multiplicative.toAdd hhw
  have hc : g*h*g⁻¹*h⁻¹ = fullCentralHom (Multiplicative.ofAdd (pairing v w,(0 : E))) := by
    apply Prod.ext
    · change g.1*h.1*g.1⁻¹*h.1⁻¹ = central (Multiplicative.ofAdd (pairing v w))
      rw [commutator_eq_pairing,hgv',hhw']
    · change g.2*h.2*g.2⁻¹*h.2⁻¹ = (1 : Multiplicative E)
      simp [mul_comm]
  change fullCentralHom (Multiplicative.ofAdd (pairing v w,(0 : E))) ∈ J
  rw [←hc]
  exact J.mul_mem (J.mul_mem (J.mul_mem hg hh) (J.inv_mem hg)) (J.inv_mem hh)

theorem vectorImage_card_le [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (J : Subgroup (R (K := K) (E := E) (m := m)))
    (hJ : fullCentralHom (Multiplicative.ofAdd ((1 : K),(0 : E))) ∉ J) :
    Nat.card (vectorImage J) ≤ Nat.card K^m := by
  have hdim : Module.finrank K (V (K := K) (m := m))=2*m := by
    simp only [V,Module.finrank_prod,Module.finrank_fintype_fun_eq_card,Fintype.card_fin]
    omega
  exact ScalarCentralLineIsotropicCardinality.card_le_of_scalar_line_pairing p m
    (pairing (K := K) (m := m)) pairing_alt pairing_full hdim
    scalarLine (centralPreimage J) hJ (vectorImage J)
    (fun v hv w hw => vectorImage_pairing_mem J v w hv hw)

end SymmetricSubgroupAsymptotics.HeisenbergAbelianProductIsotropy
