import LeanIrisX.Algebra.Agreement
import LeanIrisX.Algebra.Core

/-! Step-indexed view relations and the authoritative view relation. -/

namespace LeanIrisX

abbrev ViewRel (A B : Type _) := Nat → A → B → Prop

class IsViewRel {A : Type u} {B : Type v} [OFE A] [OFE B] [CMRA B] [UCMRA B]
    (R : ViewRel A B) : Prop where
  mono : ∀ {n₁ n₂ a₁ a₂ b₁ b₂},
    R n₁ a₁ b₁ → a₁ ≡{n₂}≡ a₂ → CMRA.IncludedN n₂ b₂ b₁ → n₂ ≤ n₁ →
      R n₂ a₂ b₂
  rel_validN : ∀ n a b, R n a b → CMRA.validN n b
  rel_unit : ∀ n, ∃ a, R n a UCMRA.unit

namespace CMRA

variable {M : Type u} [OFE M] [CMRA M]

theorem validN_of_includedN {n : Nat} {x y : M}
    (hxy : CMRA.IncludedN n x y) (hy : CMRA.validN n y) :
    CMRA.validN n x := by
  obtain ⟨f, hf⟩ := hxy
  have hxf : CMRA.validN n (CMRA.op x f) :=
    CMRA.validN_ne hf hy
  exact CMRA.validN_op_left hxf

theorem includedN_mono {n m : Nat} (hmn : m ≤ n) {x y : M}
    (hxy : CMRA.IncludedN n x y) : CMRA.IncludedN m x y := by
  obtain ⟨f, hf⟩ := hxy
  exact ⟨f, OFE.mono hmn hf⟩

theorem includedN_trans {n : Nat} {x y z : M}
    (hxy : CMRA.IncludedN n x y) (hyz : CMRA.IncludedN n y z) :
    CMRA.IncludedN n x z := by
  obtain ⟨f, hf⟩ := hxy
  obtain ⟨g, hg⟩ := hyz
  exact ⟨CMRA.op f g, OFE.trans hg <| OFE.trans (CMRA.op_ne_left g n hf)
    (OFE.of_eq (CMRA.op_assoc x f g).symm)⟩

theorem includedN_of_dist {n : Nat} [UCMRA M] {x y : M}
    (hxy : x ≡{n}≡ y) : CMRA.IncludedN n x y :=
  ⟨UCMRA.unit, OFE.trans (OFE.symm hxy)
    (OFE.of_eq (UCMRA.unit_right x).symm)⟩

end CMRA

namespace ViewRel

variable {A : Type u} {B : Type v}
variable [OFE A] [OFE B] [CMRA B] [UCMRA B]
variable {R : ViewRel A B} [IsViewRel R]

theorem iff_of_dist {n : Nat} {a₁ a₂ : A} {b₁ b₂ : B}
    (ha : a₁ ≡{n}≡ a₂) (hb : b₁ ≡{n}≡ b₂) :
    R n a₁ b₁ ↔ R n a₂ b₂ := by
  constructor
  · intro h
    exact IsViewRel.mono h ha (CMRA.includedN_of_dist (OFE.symm hb))
      (Nat.le_refl n)
  · intro h
    exact IsViewRel.mono h (OFE.symm ha) (CMRA.includedN_of_dist hb)
      (Nat.le_refl n)

end ViewRel

/-- The authoritative relation: the fragment is included in the authoritative
resource at the current observation depth, and the authority is valid. -/
def AuthViewRel {A : Type u} [OFE A] [CMRA A] [UCMRA A] : ViewRel A A :=
  fun n authority fragment =>
    CMRA.validN n authority ∧ CMRA.IncludedN n fragment authority

namespace AuthViewRel

variable {A : Type u} [OFE A] [CMRA A] [UCMRA A]

instance : IsViewRel (AuthViewRel (A := A)) where
  mono := by
    intro n₁ n₂ a₁ a₂ b₁ b₂ hrel ha hb hle
    have ha₁v : CMRA.validN n₂ a₁ := CMRA.validN_mono hle hrel.1
    have ha₂v : CMRA.validN n₂ a₂ := CMRA.validN_ne ha ha₁v
    have hb₁a₁ : CMRA.IncludedN n₂ b₁ a₁ :=
      CMRA.includedN_mono hle hrel.2
    have ha₁a₂ : CMRA.IncludedN n₂ a₁ a₂ := CMRA.includedN_of_dist ha
    exact ⟨ha₂v, CMRA.includedN_trans hb (CMRA.includedN_trans hb₁a₁ ha₁a₂)⟩
  rel_validN := by
    intro n a b h
    exact CMRA.validN_of_includedN h.2 h.1
  rel_unit := by
    intro n
    refine ⟨UCMRA.unit, CMRA.validN_of_valid UCMRA.unit_valid n, ?_⟩
    exact ⟨UCMRA.unit, OFE.of_eq (UCMRA.unit_left UCMRA.unit).symm⟩

theorem authority_valid {n : Nat} {a b : A}
    (h : AuthViewRel n a b) : CMRA.validN n a := h.1

theorem fragment_included {n : Nat} {a b : A}
    (h : AuthViewRel n a b) : CMRA.IncludedN n b a := h.2

theorem fragment_valid {n : Nat} {a b : A}
    (h : AuthViewRel n a b) : CMRA.validN n b :=
  CMRA.validN_of_includedN h.2 h.1

end AuthViewRel
end LeanIrisX
