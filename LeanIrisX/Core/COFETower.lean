import LeanIrisX.Core.OFunctor

/-! Finite stages and embedding/projection maps for the COFE tower solver. -/

namespace LeanIrisX
namespace COFETower

universe u

structure PackedCOFE where
  Carrier : Type u
  ofe : OFE Carrier
  cofe : @COFE Carrier ofe

instance (X : PackedCOFE) : OFE X.Carrier := X.ofe
instance (X : PackedCOFE) : COFE X.Carrier := X.cofe

variable (F : OFunctorPre) [OFunctor F]

def stagePack : Nat → PackedCOFE
  | 0 => {
      Carrier := Unit
      ofe := inferInstance
      cofe := inferInstance
    }
  | n + 1 =>
      let X := stagePack n
      {
        Carrier := F X.Carrier X.Carrier
        ofe := OFunctor.ofe X.Carrier X.Carrier
        cofe := OFunctor.cofe X.Carrier X.Carrier
      }

abbrev Stage (F : OFunctorPre) [OFunctor F] (n : Nat) :=
  (stagePack F n).Carrier

instance stageOFE (F : OFunctorPre) [OFunctor F] (n : Nat) : OFE (Stage F n) :=
  (stagePack F n).ofe
instance stageCOFE (F : OFunctorPre) [OFunctor F] (n : Nat) : COFE (Stage F n) :=
  (stagePack F n).cofe

def upDown (seed : Stage F 1) : ∀ n, (Stage F n -n> Stage F (n + 1)) ×
    (Stage F (n + 1) -n> Stage F n)
  | 0 =>
      (OFEMor.const seed, OFEMor.const ())
  | n + 1 =>
      let previous := upDown seed n
      (OFunctor.map previous.2 previous.1,
        OFunctor.map previous.1 previous.2)

def up (seed : Stage F 1) (n : Nat) : Stage F n -n> Stage F (n + 1) :=
  (upDown F seed n).1
def down (seed : Stage F 1) (n : Nat) : Stage F (n + 1) -n> Stage F n :=
  (upDown F seed n).2

@[simp] theorem up_zero (seed : Stage F 1) (x : Stage F 0) : up F seed 0 x = seed := rfl
@[simp] theorem down_zero (seed : Stage F 1) (x : Stage F 1) : down F seed 0 x = () := rfl

theorem down_up_zero (seed : Stage F 1) (x : Stage F 0) :
    down F seed 0 (up F seed 0 x) = x := by
  cases x
  rfl

/-- Every finite-stage embedding has the corresponding projection as an exact
left inverse.  This is the section/retraction law used throughout the tower. -/
theorem down_up (seed : Stage F 1) :
    ∀ (n : Nat) (x : Stage F n), down F seed n (up F seed n x) = x
  | 0, x => down_up_zero F seed x
  | n + 1, x => by
      let p := upDown F seed n
      change OFunctor.map p.1 p.2 (OFunctor.map p.2 p.1 x) = x
      rw [OFunctor.map_comp]
      apply OFE.eq_of_dist
      intro k
      exact OFE.trans
        (OFunctor.map_ne k
          (OFEMor.comp p.2 p.1) OFEMor.id
          (OFEMor.comp p.2 p.1) OFEMor.id
          (fun y => OFE.of_eq (down_up seed n y))
          (fun y => OFE.of_eq (down_up seed n y)) x)
        (OFE.of_eq (OFunctor.map_id x))

/-- The other composite need not be equal on the nose, but contractiveness
gives exactly the approximation required by the COFE tower construction. -/
theorem up_down [OFunctorContractive F] (seed : Stage F 1) :
    ∀ (n : Nat) (x : Stage F (n + 2)),
      up F seed (n + 1) (down F seed (n + 1) x) ≡{n}≡ x
  | 0, x => by
      let p := upDown F seed 0
      change OFunctor.map p.2 p.1 (OFunctor.map p.1 p.2 x) ≡{0}≡ x
      exact OFE.trans
        (OFE.of_eq (OFunctor.map_comp p.1 p.2 p.2 p.1 x))
        (OFE.trans
          (OFunctorContractive.map_contractive 0
            (OFEMor.comp p.1 p.2) OFEMor.id
            (OFEMor.comp p.1 p.2) OFEMor.id
            (OFE.distLater_zero _ _) (OFE.distLater_zero _ _) x)
          (OFE.of_eq (OFunctor.map_id x)))
  | n + 1, x => by
      let p := upDown F seed (n + 1)
      change OFunctor.map p.2 p.1 (OFunctor.map p.1 p.2 x) ≡{n + 1}≡ x
      exact OFE.trans
        (OFE.of_eq (OFunctor.map_comp p.1 p.2 p.2 p.1 x))
        (OFE.trans
          (OFunctorContractive.map_contractive (n + 1)
            (OFEMor.comp p.1 p.2) OFEMor.id
            (OFEMor.comp p.1 p.2) OFEMor.id
            (by
              intro m hm y
              exact OFE.mono (Nat.le_of_lt_succ hm) (up_down seed n y))
            (by
              intro m hm y
              exact OFE.mono (Nat.le_of_lt_succ hm) (up_down seed n y)) x)
          (OFE.of_eq (OFunctor.map_id x)))

theorem up_nonExpansive (seed : Stage F 1) (n : Nat) : NonExpansive (up F seed n) :=
  (up F seed n).nonExpansive

theorem down_nonExpansive (seed : Stage F 1) (n : Nat) : NonExpansive (down F seed n) :=
  (down F seed n).nonExpansive

/-- A point of the inverse limit: one value at every finite approximation,
with exact compatibility under the projection maps. -/
structure Tower (seed : Stage F 1) where
  val : ∀ n, Stage F n
  coherent : ∀ n, down F seed n (val (n + 1)) = val n

instance towerCoeFun (seed : Stage F 1) :
    CoeFun (Tower F seed) (fun _ => ∀ n, Stage F n) := ⟨Tower.val⟩

instance towerOFE (seed : Stage F 1) : OFE (Tower F seed) where
  dist n x y := ∀ k, x k ≡{n}≡ y k
  dist_equivalence n := by
    constructor
    · intro x k; exact OFE.refl n _
    · intro x y h k; exact OFE.symm (h k)
    · intro x y z hxy hyz k; exact OFE.trans (hxy k) (hyz k)
  eq_dist x y := by
    constructor
    · intro h n k; subst y; exact OFE.refl n _
    · intro h
      cases x with
      | mk xv xh =>
        cases y with
        | mk yv yh =>
          congr
          funext k
          exact OFE.eq_of_dist (fun n => h n k)
  dist_mono hnm h k := OFE.mono hnm (h k)

def towerChain (seed : Stage F 1) (c : OFEChain (Tower F seed)) (k : Nat) :
    OFEChain (Stage F k) where
  approx n := c n k
  coherent := by
    intro n m hnm
    exact c.coherent hnm k

instance towerCOFE (seed : Stage F 1) : COFE (Tower F seed) where
  limit c := {
    val := fun k => COFE.lim (towerChain F seed c k)
    coherent := by
      intro k
      apply OFE.eq_of_dist
      intro n
      exact OFE.trans
        ((down F seed k).nonExpansive n (COFE.lim_dist (towerChain F seed c (k + 1)) n))
        (OFE.trans
          (OFE.of_eq ((c n).coherent k))
          (OFE.symm (COFE.lim_dist (towerChain F seed c k) n)))
  }
  limit_spec := by
    intro c n k
    exact COFE.lim_dist (towerChain F seed c k) n

def Tower.proj (seed : Stage F 1) (k : Nat) : Tower F seed -n> Stage F k where
  toFun X := X k
  nonExpansive := by intro n x y h; exact h k

def upN (seed : Stage F 1) {k : Nat} : ∀ n, Stage F k -n> Stage F (k + n)
  | 0 => OFEMor.id
  | n + 1 => OFEMor.comp (up F seed (k + n)) (upN seed n)

def downN (seed : Stage F 1) {k : Nat} : ∀ n, Stage F (k + n) -n> Stage F k
  | 0 => OFEMor.id
  | n + 1 => OFEMor.comp (downN seed n) (down F seed (k + n))

theorem downN_upN (seed : Stage F 1) {k : Nat} (x : Stage F k) :
    ∀ n, downN F seed n (upN F seed n x) = x
  | 0 => rfl
  | n + 1 => by
      change downN F seed n
        (down F seed (k + n) (up F seed (k + n) (upN F seed n x))) = x
      rw [down_up]
      exact downN_upN seed x n

theorem Tower.up_approx [OFunctorContractive F] (seed : Stage F 1)
    (X : Tower F seed) (k : Nat) :
    up F seed (k + 1) (X (k + 1)) ≡{k}≡ X (k + 2) :=
  OFE.trans
    ((up F seed (k + 1)).nonExpansive k (OFE.of_eq (X.coherent (k + 1)).symm))
    (up_down F seed k (X (k + 2)))

theorem Tower.upN_approx [OFunctorContractive F] (seed : Stage F 1)
    (X : Tower F seed) (k : Nat) :
    ∀ i, upN F seed i (X (k + 1)) ≡{k}≡ X (k + 1 + i)
  | 0 => OFE.refl k _
  | i + 1 => by
      have hstep : ∀ j, k + i + 1 = j →
          up F seed j (X j) ≡{k}≡ X (j + 1) := by
        intro j hj
        subst j
        exact OFE.mono (Nat.le_add_right k i)
          (Tower.up_approx (F := F) seed X (k + i))
      exact OFE.trans
        ((up F seed (k + 1 + i)).nonExpansive k
          (Tower.upN_approx seed X k i))
        (hstep _ (Nat.add_right_comm k i 1))

theorem Tower.downN_exact (seed : Stage F 1) (X : Tower F seed) (k : Nat) :
    ∀ i, downN F seed i (X (k + i)) = X k
  | 0 => rfl
  | i + 1 => by
      change downN F seed i (down F seed (k + i) (X (k + i + 1))) = X k
      rw [X.coherent (k + i)]
      exact Tower.downN_exact seed X k i

def eqToMor {i k : Nat} (e : i = k) : Stage F i -n> Stage F k := by
  subst k
  exact OFEMor.id

theorem eqToMor_up (seed : Stage F 1) {k k' : Nat} {x : Stage F k} (e : k = k') :
    eqToMor F (congrArg Nat.succ e) (up F seed k x) =
      up F seed k' (eqToMor F e x) := by
  cases e
  rfl

theorem down_eqToMor (seed : Stage F 1) {k k' : Nat} {x : Stage F (k + 1)} (e : k = k') :
    down F seed k' (eqToMor F (congrArg Nat.succ e) x) =
      eqToMor F e (down F seed k x) := by
  cases e
  rfl

theorem eqToMor_tower (seed : Stage F 1) (X : Tower F seed) {i j : Nat} (e : i = j) :
    eqToMor F e (X i) = X j := by
  cases e
  rfl

def embedStage (seed : Stage F 1) {k i : Nat} : Stage F k -n> Stage F i :=
  if h : k ≤ i then
    OFEMor.comp (eqToMor F (Nat.add_sub_cancel' h)) (upN F seed (i - k))
  else
    OFEMor.comp (downN F seed (k - i))
      (eqToMor F (Nat.add_sub_cancel' (Nat.le_of_not_ge h)).symm)

def Tower.embed [OFunctorContractive F] (seed : Stage F 1) (k : Nat) :
    Stage F k -n> Tower F seed where
  toFun x := {
    val := fun i => embedStage F seed x
    coherent := by
      intro i
      dsimp [embedStage]
      split <;> rename_i h₁
      · split <;> rename_i h₂
        · suffices ∀ a b (e₁ : k + a = i + 1) (e₂ : k + b = i),
              down F seed i (eqToMor F e₁ (upN F seed a x)) =
                eqToMor F e₂ (upN F seed b x) from this _ _ _ _
          intro a b e₁ e₂
          subst i
          rw [Nat.add_assoc, Nat.add_left_cancel_iff] at e₁
          subst a
          exact down_up F seed (k + b) (upN F seed b x)
        · cases (Nat.lt_or_eq_of_le h₁).resolve_left (h₂ ∘ Nat.lt_succ_iff.1)
          suffices ∀ a b (e₁ : i + 1 + a = i + 1) (e₂ : i + 1 = i + b),
              down F seed i (eqToMor F e₁ (upN F seed a x)) =
                downN F seed b (eqToMor F e₂ x) from this _ _ _ _
          intro a b e₁ e₂
          have ha : a = 0 := by omega
          have hb : b = 1 := by omega
          subst a
          subst b
          rfl
      · rw [dif_neg (fun hk => h₁ (Nat.le_trans hk (Nat.le_succ i)))]
        suffices ∀ k a b (e₁ : k = i + 1 + a) (e₂ : k = i + b) (x : Stage F k),
            down F seed i (downN F seed a (eqToMor F e₁ x)) =
              downN F seed b (eqToMor F e₂ x) from this _ _ _ _ _ _
        rintro j a b e₁ rfl y
        rw [Nat.add_assoc, Nat.add_left_cancel_iff, Nat.add_comm] at e₁
        subst b
        show down F seed i (downN F seed a (eqToMor F e₁ y)) =
          downN F seed a (down F seed (i + a) y)
        induction a with
        | zero => rfl
        | succ a ih =>
          dsimp [downN, OFEMor.comp]
          rw [down_eqToMor F seed (Nat.add_right_comm i a 1)]
          apply ih
  }
  nonExpansive := by
    intro n x y h i
    exact (embedStage F seed).nonExpansive n h

theorem Tower.embed_up [OFunctorContractive F] (seed : Stage F 1)
    {k : Nat} (x : Stage F k) :
    Tower.embed F seed (k + 1) (up F seed k x) = Tower.embed F seed k x := by
  apply OFE.eq_of_dist
  intro n i
  dsimp [Tower.embed, embedStage]
  split <;> rename_i h₁
  · simp only [dif_pos (Nat.le_trans (Nat.le_succ k) h₁)]
    suffices ∀ a b (e₁ : k + 1 + a = i) (e₂ : k + b = i),
        eqToMor F e₁ (upN F seed a (up F seed k x)) =
          eqToMor F e₂ (upN F seed b x) from OFE.of_eq (this _ _ _ _)
    rintro a b e₁ rfl
    rw [Nat.add_right_comm, Nat.add_assoc, Nat.add_left_cancel_iff] at e₁
    subst b
    show eqToMor F e₁ (upN F seed a (up F seed k x)) =
      up F seed (k + a) (upN F seed a x)
    clear h₁
    induction a with
    | zero => rfl
    | succ a ih =>
      dsimp [upN, OFEMor.comp]
      rw [eqToMor_up F seed (Nat.add_right_comm k 1 a)]
      congr 1
      exact ih _
  · split <;> rename_i h₂
    · cases Nat.le_antisymm h₂ (Nat.not_lt.1 h₁)
      have h {a b : Nat} {e₁ : k + 1 = k + a} {e₂ : k + b = k + 0} :
          downN F seed a (eqToMor F e₁ (up F seed k x)) ≡{n}≡
            eqToMor F e₂ (upN F seed b x) := by
        have ha : a = 1 := (Nat.add_left_cancel e₁).symm
        have hb : b = 0 := Nat.add_left_cancel e₂
        subst a
        subst b
        exact OFE.of_eq (down_up F seed k x)
      exact h
    · suffices ∀ a b (e₁ : k + 1 = i + a) (e₂ : k = i + b),
          downN F seed a (eqToMor F e₁ (up F seed k x)) ≡{n}≡
            downN F seed b (eqToMor F e₂ x) from this _ _ _ _
      rintro a b e₁ rfl
      have ha : a = b + 1 := by omega
      subst a
      exact (downN F seed b).nonExpansive n
        (OFE.of_eq (down_up F seed (i + b) x))

theorem Tower.embed_self [OFunctorContractive F] (seed : Stage F 1)
    (X : Tower F seed) (k : Nat) :
    Tower.embed F seed (k + 1) (X (k + 1)) ≡{k}≡ X := by
  intro i
  dsimp [Tower.embed, embedStage]
  split <;> rename_i h₁
  · exact OFE.trans
      ((eqToMor F _).nonExpansive k
        (Tower.upN_approx (F := F) seed X k (i - (k + 1))))
      (by
        suffices ∀ a (e : k + 1 + a = i), eqToMor F e (X (k + 1 + a)) = X i
          from OFE.of_eq (this _ _)
        intro a e
        cases e
        rfl)
  · suffices ∀ a (e : k + 1 = i + a),
        downN F seed a (eqToMor F e (X (k + 1))) ≡{k}≡ X i from this _ _
    intro a e
    cases a with
    | zero =>
      have hik : k + 1 = i := by simpa using e
      subst i
      exact OFE.refl k _
    | succ a =>
      have hk : k = i + a := by omega
      subst k
      exact OFE.of_eq (Tower.downN_exact (F := F) seed X i (a + 1))

instance towerInhabited [OFunctorContractive F] (seed : Stage F 1) :
    Inhabited (Tower F seed) :=
  ⟨Tower.embed F seed 0 ()⟩

def unfoldApprox [OFunctorContractive F] (seed : Stage F 1)
    (X : Tower F seed) (n : Nat) : F (Tower F seed) (Tower F seed) :=
  OFunctor.map (F := F) (Tower.proj F seed n) (Tower.embed F seed n) (X (n + 1))

theorem unfoldApprox_step [OFunctorContractive F] (seed : Stage F 1)
    (X : Tower F seed) (j : Nat) :
    unfoldApprox F seed X j ≡{j}≡ unfoldApprox F seed X (j + 1) := by
  let outer := OFunctor.map (F := F)
    (Tower.proj F seed (j + 1)) (Tower.embed F seed (j + 1))
  have hbase := Tower.up_approx (F := F) seed X j
  change OFunctor.map (F := F) (down F seed j) (up F seed j) (X (j + 1)) ≡{j}≡
    X (j + 2) at hbase
  have hx := outer.nonExpansive j hbase
  have hcomp := OFunctor.map_comp (F := F)
    (down F seed j) (up F seed j)
    (Tower.proj F seed (j + 1)) (Tower.embed F seed (j + 1)) (X (j + 1))
  have hmaps :
      OFunctor.map (F := F)
          (OFEMor.comp (down F seed j) (Tower.proj F seed (j + 1)))
          (OFEMor.comp (Tower.embed F seed (j + 1)) (up F seed j))
          (X (j + 1)) ≡{j}≡
        OFunctor.map (F := F) (Tower.proj F seed j) (Tower.embed F seed j) (X (j + 1)) :=
    OFunctor.map_ne (F := F) j _ _ _ _
      (fun Y => OFE.of_eq (Y.coherent j))
      (fun y => OFE.of_eq (Tower.embed_up (F := F) seed y))
      (X (j + 1))
  exact OFE.trans (OFE.symm hmaps)
    (OFE.trans (OFE.of_eq hcomp.symm) (by
      simpa only [outer, unfoldApprox, Nat.add_assoc] using hx))

def unfoldChain [OFunctorContractive F] (seed : Stage F 1)
    (X : Tower F seed) : OFEChain (F (Tower F seed) (Tower F seed)) where
  approx n := unfoldApprox F seed X n
  coherent := by
    intro n m hnm
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
    induction d with
    | zero => exact OFE.refl n _
    | succ d ih =>
      exact OFE.trans (ih (Nat.le_add_right n d))
        (OFE.mono (Nat.le_add_right n d)
          (unfoldApprox_step (F := F) seed X (n + d)))

def towerFold [OFunctorContractive F] (seed : Stage F 1) :
    F (Tower F seed) (Tower F seed) -n> Tower F seed where
  toFun X := {
    val := fun n => down F seed n
      (OFunctor.map (F := F) (Tower.embed F seed n) (Tower.proj F seed n) X)
    coherent := by
      intro n
      apply OFE.eq_of_dist
      intro m
      apply (down F seed n).nonExpansive m
      change OFunctor.map (F := F) (up F seed n) (down F seed n)
          (OFunctor.map (F := F)
            (Tower.embed F seed (n + 1)) (Tower.proj F seed (n + 1)) X) ≡{m}≡
        OFunctor.map (F := F) (Tower.embed F seed n) (Tower.proj F seed n) X
      exact OFE.trans
        (OFE.of_eq (OFunctor.map_comp
          (Tower.embed F seed (n + 1)) (Tower.proj F seed (n + 1))
          (up F seed n) (down F seed n) X))
        (OFunctor.map_ne m _ _ _ _
          (fun y => OFE.of_eq (Tower.embed_up (F := F) seed y))
          (fun Y => OFE.of_eq (Y.coherent n)) X)
  }
  nonExpansive := by
    intro n X Y h k
    exact (down F seed k).nonExpansive n
      ((OFunctor.map (F := F)
        (Tower.embed F seed k) (Tower.proj F seed k)).nonExpansive n h)

def towerUnfold [OFunctorContractive F] (seed : Stage F 1) :
    Tower F seed -n> F (Tower F seed) (Tower F seed) where
  toFun X := COFE.lim (unfoldChain F seed X)
  nonExpansive := by
    intro n X Y h
    exact OFE.trans
      (COFE.lim_dist (unfoldChain F seed X) n)
      (OFE.trans
        ((OFunctor.map (F := F)
          (Tower.proj F seed n) (Tower.embed F seed n)).nonExpansive n (h (n + 1)))
        (OFE.symm (COFE.lim_dist (unfoldChain F seed Y) n)))

theorem towerFold_unfold [OFunctorContractive F] (seed : Stage F 1)
    (X : Tower F seed) : towerFold F seed (towerUnfold F seed X) = X := by
  apply OFE.eq_of_dist
  intro n k
  refine OFE.trans ((down F seed k).nonExpansive n ?_) (OFE.of_eq (X.coherent k))
  refine OFE.trans ?_ (OFE.of_eq (Tower.downN_exact (F := F) seed X (k + 1) n))
  refine OFE.trans
    ((OFunctor.map (F := F) (Tower.embed F seed k) (Tower.proj F seed k)).nonExpansive n
      (OFE.trans (COFE.lim_dist (unfoldChain F seed X) n)
        ((unfoldChain F seed X).coherent (by omega : n ≤ k + n + 1)))) ?_
  change OFunctor.map (F := F) (Tower.embed F seed k) (Tower.proj F seed k)
      (OFunctor.map (F := F) (Tower.proj F seed (k + n + 1))
        (Tower.embed F seed (k + n + 1)) (X (k + n + 2))) ≡{n}≡
    downN F seed n (X (k + 1 + n))
  refine OFE.trans
    ((OFunctor.map (F := F) (Tower.embed F seed k) (Tower.proj F seed k)).nonExpansive n
      ((OFunctor.map (F := F) (Tower.proj F seed (k + n + 1))
        (Tower.embed F seed (k + n + 1))).nonExpansive n
          (OFE.symm (OFE.mono (by omega : n ≤ k + n)
            (Tower.up_approx (F := F) seed X (k + n)))))) ?_
  rw [OFunctor.map_comp]
  change OFunctor.map (F := F)
      (OFEMor.comp (Tower.proj F seed (k + n + 1)) (Tower.embed F seed k))
      (OFEMor.comp (Tower.proj F seed k) (Tower.embed F seed (k + n + 1)))
      (OFunctor.map (F := F) (down F seed (k + n)) (up F seed (k + n))
        (X (k + n + 1))) ≡{n}≡ downN F seed n (X (k + 1 + n))
  rw [OFunctor.map_comp]
  refine OFE.trans
    (OFunctor.map_ne n _ _ _ _
      (fun y => by
        simp [OFEMor.comp, Tower.proj, Tower.embed, embedStage,
          show k ≤ k + n + 1 by omega]
        have h {a : Nat} {e : k + a = k + n + 1} :
            down F seed (k + n) (eqToMor F e (upN F seed a y)) =
              upN F seed n y := by
          have ha : a = n + 1 := by omega
          subst a
          exact down_up F seed (k + n) (upN F seed n y)
        exact OFE.of_eq h)
      (fun y => by
        simp [OFEMor.comp, Tower.proj, Tower.embed, embedStage,
          show ¬k + n + 1 ≤ k by omega]
        have h {a : Nat} {e : k + n + 1 = k + a} :
            downN F seed a (eqToMor F e (up F seed (k + n) y)) =
              downN F seed n y := by
          have ha : a = n + 1 := by omega
          subst a
          exact congrArg (fun z => downN F seed n z)
            (down_up F seed (k + n) y)
        exact OFE.of_eq h)
      (X (k + n + 1))) ?_
  change OFunctor.map (F := F) (upN F seed n) (downN F seed n)
      (X (k + n + 1)) ≡{n}≡ downN F seed n (X (k + 1 + n))
  have e : k + n + 1 = k + 1 + n := Nat.add_right_comm k n 1
  suffices ∀ (x : Stage F (k + n + 1)) (y : Stage F (k + 1 + n)),
      eqToMor F e x = y → ∀ m,
        OFunctor.map (F := F) (upN F seed n) (downN F seed n) x ≡{m}≡
          downN F seed n y from by
            have hcast : eqToMor F e (X (k + n + 1)) = X (k + 1 + n) :=
              eqToMor_tower (F := F) seed X e
            exact this _ _ hcast n
  intro x y hxy
  subst y
  intro m
  induction n with
  | zero => exact OFE.of_eq (OFunctor.map_id x)
  | succ n ih =>
    have hcomp := OFunctor.map_comp (F := F)
      (up F seed (k + n)) (down F seed (k + n))
      (upN F seed n) (downN F seed n) x
    exact OFE.trans (OFE.of_eq hcomp.symm)
      (OFE.trans (ih (Nat.succ.inj e)
          (OFunctor.map (F := F) (up F seed (k + n)) (down F seed (k + n)) x))
        (OFE.of_eq (congrArg (fun z => downN F seed n z)
          (down_eqToMor F seed (Nat.add_right_comm k n 1)).symm)))

theorem towerUnfold_fold [OFunctorContractive F] (seed : Stage F 1)
    (X : F (Tower F seed) (Tower F seed)) :
    towerUnfold F seed (towerFold F seed X) = X := by
  apply OFE.eq_of_dist
  intro n
  refine OFE.trans
    (OFE.trans (COFE.lim_dist (unfoldChain F seed (towerFold F seed X)) n)
      ((unfoldChain F seed (towerFold F seed X)).coherent (Nat.le_succ n))) ?_
  change OFunctor.map (F := F)
      (Tower.proj F seed (n + 1)) (Tower.embed F seed (n + 1))
      (down F seed (n + 2)
        (OFunctor.map (F := F)
          (Tower.embed F seed (n + 2)) (Tower.proj F seed (n + 2)) X)) ≡{n}≡ X
  change OFunctor.map (F := F)
      (Tower.proj F seed (n + 1)) (Tower.embed F seed (n + 1))
      (OFunctor.map (F := F) (up F seed (n + 1)) (down F seed (n + 1))
        (OFunctor.map (F := F)
          (Tower.embed F seed (n + 2)) (Tower.proj F seed (n + 2)) X)) ≡{n}≡ X
  rw [OFunctor.map_comp, OFunctor.map_comp]
  exact OFE.trans
    (OFunctor.map_ne n
      (OFEMor.comp (Tower.embed F seed (n + 2))
        (OFEMor.comp (up F seed (n + 1)) (Tower.proj F seed (n + 1))))
      OFEMor.id
      (OFEMor.comp
        (OFEMor.comp (Tower.embed F seed (n + 1)) (down F seed (n + 1)))
        (Tower.proj F seed (n + 2)))
      OFEMor.id
      (fun Y => OFE.trans
        (OFE.of_eq (Tower.embed_up (F := F) seed (Y (n + 1))))
        (Tower.embed_self (F := F) seed Y n))
      (fun Y => OFE.trans
        ((Tower.embed F seed (n + 1)).nonExpansive n (OFE.of_eq (Y.coherent (n + 1))))
        (Tower.embed_self (F := F) seed Y n))
      X)
    (OFE.of_eq (OFunctor.map_id X))

def towerIso [OFunctorContractive F] (seed : Stage F 1) :
    OFEIso (F (Tower F seed) (Tower F seed)) (Tower F seed) where
  hom := towerFold F seed
  inv := towerUnfold F seed
  hom_inv := towerFold_unfold F seed
  inv_hom := towerUnfold_fold F seed

abbrev Fix [OFunctorContractive F] (seed : Stage F 1) := Tower F seed

def Fix.fold [OFunctorContractive F] (seed : Stage F 1) :
    F (Fix F seed) (Fix F seed) -n> Fix F seed := towerFold F seed

def Fix.unfold [OFunctorContractive F] (seed : Stage F 1) :
    Fix F seed -n> F (Fix F seed) (Fix F seed) := towerUnfold F seed

theorem Fix.fold_unfold [OFunctorContractive F] (seed : Stage F 1)
    (X : Fix F seed) : Fix.fold F seed (Fix.unfold F seed X) = X :=
  towerFold_unfold F seed X

theorem Fix.unfold_fold [OFunctorContractive F] (seed : Stage F 1)
    (X : F (Fix F seed) (Fix F seed)) : Fix.unfold F seed (Fix.fold F seed X) = X :=
  towerUnfold_fold F seed X

end COFETower
end LeanIrisX
