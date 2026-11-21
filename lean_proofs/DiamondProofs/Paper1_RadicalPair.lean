/-
  Paper 1: Radical-Pair Quantum Compass under Non-Markovian Spin Relaxation
  Pure Lean 4.16.0 Formal Verification (Zero Mathlib, Zero sorry, Zero admit, Zero custom axioms)
-/

namespace DiamondProofs.Paper1

/-! ## 1. Exact Gaussian Integers Z[i], Rationals Q, and Complex Rationals Q[i] -/

structure ZGauss where
  re : Int
  im : Int
  deriving DecidableEq, Repr

namespace ZGauss

def zero : ZGauss := ⟨0, 0⟩
def one : ZGauss := ⟨1, 0⟩
def iUnit : ZGauss := ⟨0, 1⟩
def ofInt (n : Int) : ZGauss := ⟨n, 0⟩
def add (a b : ZGauss) : ZGauss := ⟨a.re + b.re, a.im + b.im⟩
def sub (a b : ZGauss) : ZGauss := ⟨a.re - b.re, a.im - b.im⟩
def neg (a : ZGauss) : ZGauss := ⟨-a.re, -a.im⟩
def mul (a b : ZGauss) : ZGauss := ⟨a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re⟩
def conj (a : ZGauss) : ZGauss := ⟨a.re, -a.im⟩
def normSq (a : ZGauss) : Int := a.re * a.re + a.im * a.im

instance : Zero ZGauss := ⟨zero⟩
instance : Add ZGauss := ⟨add⟩
instance : Sub ZGauss := ⟨sub⟩
instance : Neg ZGauss := ⟨neg⟩
instance : Mul ZGauss := ⟨mul⟩
instance : OfNat ZGauss 0 := ⟨zero⟩
instance : OfNat ZGauss 1 := ⟨one⟩

@[simp] theorem zero_re : (0 : ZGauss).re = 0 := rfl
@[simp] theorem zero_im : (0 : ZGauss).im = 0 := rfl
@[simp] theorem one_re : (1 : ZGauss).re = 1 := rfl
@[simp] theorem one_im : (1 : ZGauss).im = 0 := rfl
@[simp] theorem add_re (a b : ZGauss) : (a + b).re = a.re + b.re := rfl
@[simp] theorem add_im (a b : ZGauss) : (a + b).im = a.im + b.im := rfl
@[simp] theorem sub_re (a b : ZGauss) : (a - b).re = a.re - b.re := rfl
@[simp] theorem sub_im (a b : ZGauss) : (a - b).im = a.im - b.im := rfl
@[simp] theorem neg_re (a : ZGauss) : (-a).re = -a.re := rfl
@[simp] theorem neg_im (a : ZGauss) : (-a).im = -a.im := rfl
@[simp] theorem mul_re (a b : ZGauss) : (a * b).re = a.re * b.re - a.im * b.im := rfl
@[simp] theorem mul_im (a b : ZGauss) : (a * b).im = a.re * b.im + a.im * b.re := rfl
@[simp] theorem conj_re (a : ZGauss) : a.conj.re = a.re := rfl
@[simp] theorem conj_im (a : ZGauss) : a.conj.im = -a.im := rfl

theorem ext {a b : ZGauss} (h1 : a.re = b.re) (h2 : a.im = b.im) : a = b := by
  cases a; cases b; simp_all

theorem add_comm (a b : ZGauss) : a + b = b + a := by
  apply ext <;> simp [Int.add_comm]

theorem add_assoc (a b c : ZGauss) : a + b + c = a + (b + c) := by
  apply ext <;> simp [Int.add_assoc]

theorem zero_add (a : ZGauss) : 0 + a = a := by
  apply ext <;> simp

theorem add_zero (a : ZGauss) : a + 0 = a := by
  apply ext <;> simp

theorem mul_comm (a b : ZGauss) : a * b = b * a := by
  apply ext <;> simp [Int.mul_comm, Int.add_comm]

theorem mul_assoc (a b c : ZGauss) : a * b * c = a * (b * c) := by
  apply ext
  · simp [Int.mul_sub, Int.sub_mul, Int.mul_add, Int.add_mul, Int.mul_assoc]
    omega
  · simp [Int.mul_sub, Int.sub_mul, Int.mul_add, Int.add_mul, Int.mul_assoc]
    omega

theorem one_mul (a : ZGauss) : 1 * a = a := by
  apply ext <;> simp

theorem mul_one (a : ZGauss) : a * 1 = a := by
  apply ext <;> simp

theorem left_distrib (a b c : ZGauss) : a * (b + c) = a * b + a * c := by
  apply ext <;> simp [Int.mul_add] <;> omega

theorem right_distrib (a b c : ZGauss) : (a + b) * c = a * c + b * c := by
  apply ext <;> simp [Int.add_mul] <;> omega

private theorem int_sq_nonneg (x : Int) : 0 ≤ x * x := by
  cases Int.le_total 0 x with
  | inl h => exact Int.mul_nonneg h h
  | inr h =>
    have hn : 0 ≤ -x := Int.neg_nonneg_of_nonpos h
    have heq : x * x = (-x) * (-x) := (Int.neg_mul_neg x x).symm
    rw [heq]
    exact Int.mul_nonneg hn hn

theorem normSq_nonneg (a : ZGauss) : 0 ≤ a.normSq :=
  Int.add_nonneg (int_sq_nonneg a.re) (int_sq_nonneg a.im)

theorem mul_conj (a : ZGauss) : a * a.conj = ofInt a.normSq := by
  apply ext
  · simp [ofInt, normSq, Int.mul_neg]
  · simp [ofInt, Int.mul_neg, Int.mul_comm]
    omega

end ZGauss

/-! ### Exact Rationals Q via Quotient over Z × N+ -/

structure QRaw where
  num : Int
  denM1 : Nat
  deriving DecidableEq, Repr

def QRaw.den (x : QRaw) : Int := (x.denM1 : Int) + 1

theorem QRaw.den_pos (x : QRaw) : 0 < x.den := by
  unfold QRaw.den
  omega

theorem QRaw.den_ne_zero (x : QRaw) : x.den ≠ 0 := by
  have h := x.den_pos
  omega

def QRel (a b : QRaw) : Prop := a.num * b.den = b.num * a.den

theorem QRel.refl (a : QRaw) : QRel a a := rfl
theorem QRel.symm {a b : QRaw} (h : QRel a b) : QRel b a := Eq.symm h
theorem QRel.trans {a b c : QRaw} (hab : QRel a b) (hbc : QRel b c) : QRel a c := by
  unfold QRel at *
  have hb : b.den ≠ 0 := b.den_ne_zero
  have h1 : (a.num * c.den) * b.den = (c.num * a.den) * b.den := by
    calc (a.num * c.den) * b.den
        = (a.num * b.den) * c.den := by ac_rfl
      _ = (b.num * a.den) * c.den := by rw [hab]
      _ = (b.num * c.den) * a.den := by ac_rfl
      _ = (c.num * b.den) * a.den := by rw [hbc]
      _ = (c.num * a.den) * b.den := by ac_rfl
  exact Int.eq_of_mul_eq_mul_right hb h1

instance qSetoid : Setoid QRaw where
  r := QRel
  iseqv := ⟨QRel.refl, QRel.symm, QRel.trans⟩

abbrev Q := Quotient qSetoid

namespace Q

def mk (n : Int) (dM1 : Nat) : Q := Quotient.mk qSetoid ⟨n, dM1⟩
def ofInt (n : Int) : Q := mk n 0
def frac (n : Int) (d : Nat) : Q := mk n (d - 1)

def zero : Q := ofInt 0
def one : Q := ofInt 1

instance : Zero Q := ⟨zero⟩
instance : OfNat Q 0 := ⟨zero⟩
instance : OfNat Q 1 := ⟨one⟩

def rawAdd (a b : QRaw) : QRaw :=
  ⟨a.num * b.den + b.num * a.den, a.denM1 * b.denM1 + a.denM1 + b.denM1⟩

theorem rawAdd_den (a b : QRaw) : (rawAdd a b).den = a.den * b.den := by
  unfold rawAdd QRaw.den
  simp only [Int.natCast_add, Int.natCast_mul]
  rw [Int.add_mul, Int.mul_add, Int.mul_add]
  omega

def rawNeg (a : QRaw) : QRaw := ⟨-a.num, a.denM1⟩

theorem rawNeg_den (a : QRaw) : (rawNeg a).den = a.den := rfl

def rawMul (a b : QRaw) : QRaw :=
  ⟨a.num * b.num, a.denM1 * b.denM1 + a.denM1 + b.denM1⟩

theorem rawMul_den (a b : QRaw) : (rawMul a b).den = a.den * b.den := by
  unfold rawMul QRaw.den
  simp only [Int.natCast_add, Int.natCast_mul]
  rw [Int.add_mul, Int.mul_add, Int.mul_add]
  omega

def rawInv (a : QRaw) : QRaw :=
  if a.num = 0 then ⟨0, 0⟩
  else if 0 < a.num then ⟨a.den, a.num.natAbs - 1⟩
  else ⟨-a.den, a.num.natAbs - 1⟩

theorem rawInv_den_of_pos {a : QRaw} (h : 0 < a.num) : (rawInv a).den = a.num := by
  unfold rawInv
  have hne : a.num ≠ 0 := by omega
  simp only [hne, ↓reduceIte, h, QRaw.den]
  omega

theorem rawInv_den_of_neg {a : QRaw} (h : a.num < 0) : (rawInv a).den = -a.num := by
  unfold rawInv
  have hne : a.num ≠ 0 := by omega
  have hnot : ¬ (0 < a.num) := by omega
  simp only [hne, ↓reduceIte, hnot, QRaw.den]
  omega

def add : Q → Q → Q :=
  Quotient.lift₂ (fun a b => Quotient.mk qSetoid (rawAdd a b)) (by
    intro a₁ b₁ a₂ b₂ ha hb
    apply Quotient.sound
    change QRel a₁ a₂ at ha
    change QRel b₁ b₂ at hb
    change QRel (rawAdd a₁ b₁) (rawAdd a₂ b₂)
    unfold QRel at ha hb ⊢
    rw [rawAdd_den, rawAdd_den]
    simp only [rawAdd]
    rw [Int.add_mul, Int.add_mul]
    have h1 : a₁.num * b₁.den * (a₂.den * b₂.den) = a₂.num * b₂.den * (a₁.den * b₁.den) := by
      calc a₁.num * b₁.den * (a₂.den * b₂.den)
          = (a₁.num * a₂.den) * (b₁.den * b₂.den) := by ac_rfl
        _ = (a₂.num * a₁.den) * (b₁.den * b₂.den) := by rw [ha]
        _ = a₂.num * b₂.den * (a₁.den * b₁.den) := by ac_rfl
    have h2 : b₁.num * a₁.den * (a₂.den * b₂.den) = b₂.num * a₂.den * (a₁.den * b₁.den) := by
      calc b₁.num * a₁.den * (a₂.den * b₂.den)
          = (b₁.num * b₂.den) * (a₁.den * a₂.den) := by ac_rfl
        _ = (b₂.num * b₁.den) * (a₁.den * a₂.den) := by rw [hb]
        _ = b₂.num * a₂.den * (a₁.den * b₁.den) := by ac_rfl
    rw [h1, h2])

def neg : Q → Q :=
  Quotient.lift (fun a => Quotient.mk qSetoid (rawNeg a)) (by
    intro a₁ a₂ ha
    apply Quotient.sound
    change QRel a₁ a₂ at ha
    change QRel (rawNeg a₁) (rawNeg a₂)
    unfold QRel at ha ⊢
    rw [rawNeg_den, rawNeg_den]
    simp only [rawNeg, Int.neg_mul, ha])

def sub (a b : Q) : Q := add a (neg b)

def mul : Q → Q → Q :=
  Quotient.lift₂ (fun a b => Quotient.mk qSetoid (rawMul a b)) (by
    intro a₁ b₁ a₂ b₂ ha hb
    apply Quotient.sound
    change QRel a₁ a₂ at ha
    change QRel b₁ b₂ at hb
    change QRel (rawMul a₁ b₁) (rawMul a₂ b₂)
    unfold QRel at ha hb ⊢
    rw [rawMul_den, rawMul_den]
    simp only [rawMul]
    calc a₁.num * b₁.num * (a₂.den * b₂.den)
        = (a₁.num * a₂.den) * (b₁.num * b₂.den) := by ac_rfl
      _ = (a₂.num * a₁.den) * (b₂.num * b₁.den) := by rw [ha, hb]
      _ = a₂.num * b₂.num * (a₁.den * b₁.den) := by ac_rfl)

def inv : Q → Q :=
  Quotient.lift (fun a => Quotient.mk qSetoid (rawInv a)) (by
    intro a₁ a₂ ha
    apply Quotient.sound
    change QRel a₁ a₂ at ha
    change QRel (rawInv a₁) (rawInv a₂)
    unfold QRel at ha ⊢
    have d1 : 0 < a₁.den := a₁.den_pos
    have d2 : 0 < a₂.den := a₂.den_pos
    by_cases h1z : a₁.num = 0
    · have h2z : a₂.num = 0 := by
        rw [h1z, Int.zero_mul] at ha
        rcases Int.mul_eq_zero.mp ha.symm with h | h
        · exact h
        · exfalso; omega
      simp [rawInv, h1z, h2z]
    · have h2z : a₂.num ≠ 0 := by
        intro hz
        rw [hz, Int.zero_mul] at ha
        rcases Int.mul_eq_zero.mp ha with h | h
        · exact h1z h
        · omega
      rcases Int.lt_trichotomy a₁.num 0 with h1n | h1z' | h1p
      · have h2n : a₂.num < 0 := by
          have : a₁.num * a₂.den < 0 := Int.mul_neg_of_neg_of_pos h1n d2
          rw [ha] at this
          by_cases hp : 0 ≤ a₂.num
          · exfalso; have := Int.mul_nonneg hp (Int.le_of_lt d1); omega
          · omega
        rw [rawInv_den_of_neg h1n, rawInv_den_of_neg h2n]
        have h1not : ¬ (0 < a₁.num) := by omega
        have h2not : ¬ (0 < a₂.num) := by omega
        simp only [rawInv, h1z, h2z, h1not, h2not, ↓reduceIte]
        rw [Int.neg_mul_neg, Int.neg_mul_neg, Int.mul_comm a₁.den a₂.num, Int.mul_comm a₂.den a₁.num]
        exact ha.symm
      · exact absurd h1z' h1z
      · have h2p : 0 < a₂.num := by
          have : 0 < a₁.num * a₂.den := Int.mul_pos h1p d2
          rw [ha] at this
          by_cases hn : a₂.num ≤ 0
          · exfalso; have := Int.mul_nonpos_of_nonpos_of_nonneg hn (Int.le_of_lt d1); omega
          · omega
        rw [rawInv_den_of_pos h1p, rawInv_den_of_pos h2p]
        simp only [rawInv, h1z, h2z, h1p, h2p, ↓reduceIte]
        rw [Int.mul_comm a₁.den a₂.num, Int.mul_comm a₂.den a₁.num]
        exact ha.symm)

def div (a b : Q) : Q := mul a (inv b)

instance : Add Q := ⟨add⟩
instance : Neg Q := ⟨neg⟩
instance : Sub Q := ⟨sub⟩
instance : Mul Q := ⟨mul⟩
instance : Div Q := ⟨div⟩

def le : Q → Q → Prop :=
  Quotient.lift₂ (fun a b => a.num * b.den ≤ b.num * a.den) (by
    intro a₁ b₁ a₂ b₂ ha hb
    change QRel a₁ a₂ at ha
    change QRel b₁ b₂ at hb
    unfold QRel at ha hb
    apply propext
    have ha1 : 0 < a₁.den := a₁.den_pos
    have ha2 : 0 < a₂.den := a₂.den_pos
    have hb1 : 0 < b₁.den := b₁.den_pos
    have hb2 : 0 < b₂.den := b₂.den_pos
    have hpos1 : 0 < a₂.den * b₂.den := Int.mul_pos ha2 hb2
    have hpos2 : 0 < a₁.den * b₁.den := Int.mul_pos ha1 hb1
    constructor
    · intro h
      have hm : (a₁.num * b₁.den) * (a₂.den * b₂.den) ≤ (b₁.num * a₁.den) * (a₂.den * b₂.den) :=
        Int.mul_le_mul_of_nonneg_right h (Int.le_of_lt hpos1)
      have hL : (a₁.num * b₁.den) * (a₂.den * b₂.den) = (a₂.num * b₂.den) * (a₁.den * b₁.den) := by
        calc (a₁.num * b₁.den) * (a₂.den * b₂.den)
            = (a₁.num * a₂.den) * (b₁.den * b₂.den) := by ac_rfl
          _ = (a₂.num * a₁.den) * (b₁.den * b₂.den) := by rw [ha]
          _ = (a₂.num * b₂.den) * (a₁.den * b₁.den) := by ac_rfl
      have hR : (b₁.num * a₁.den) * (a₂.den * b₂.den) = (b₂.num * a₂.den) * (a₁.den * b₁.den) := by
        calc (b₁.num * a₁.den) * (a₂.den * b₂.den)
            = (b₁.num * b₂.den) * (a₁.den * a₂.den) := by ac_rfl
          _ = (b₂.num * b₁.den) * (a₁.den * a₂.den) := by rw [hb]
          _ = (b₂.num * a₂.den) * (a₁.den * b₁.den) := by ac_rfl
      rw [hL, hR] at hm
      exact Int.le_of_mul_le_mul_right hm hpos2
    · intro h
      have hm : (a₂.num * b₂.den) * (a₁.den * b₁.den) ≤ (b₂.num * a₂.den) * (a₁.den * b₁.den) :=
        Int.mul_le_mul_of_nonneg_right h (Int.le_of_lt hpos2)
      have hL : (a₂.num * b₂.den) * (a₁.den * b₁.den) = (a₁.num * b₁.den) * (a₂.den * b₂.den) := by
        calc (a₂.num * b₂.den) * (a₁.den * b₁.den)
            = (a₂.num * a₁.den) * (b₂.den * b₁.den) := by ac_rfl
          _ = (a₁.num * a₂.den) * (b₂.den * b₁.den) := by rw [← ha]
          _ = (a₁.num * b₁.den) * (a₂.den * b₂.den) := by ac_rfl
      have hR : (b₂.num * a₂.den) * (a₁.den * b₁.den) = (b₁.num * a₁.den) * (a₂.den * b₂.den) := by
        calc (b₂.num * a₂.den) * (a₁.den * b₁.den)
            = (b₂.num * b₁.den) * (a₂.den * a₁.den) := by ac_rfl
          _ = (b₁.num * b₂.den) * (a₂.den * a₁.den) := by rw [← hb]
          _ = (b₁.num * a₁.den) * (a₂.den * b₂.den) := by ac_rfl
      rw [hL, hR] at hm
      exact Int.le_of_mul_le_mul_right hm hpos1)

def lt (a b : Q) : Prop := le a b ∧ a ≠ b

instance : LE Q := ⟨le⟩
instance : LT Q := ⟨lt⟩

theorem add_comm (a b : Q) : a + b = b + a := by
  induction a using Quotient.ind with
  | _ a =>
    induction b using Quotient.ind with
    | _ b =>
      apply Quotient.sound
      change QRel (rawAdd a b) (rawAdd b a)
      unfold QRel
      rw [rawAdd_den, rawAdd_den]
      simp only [rawAdd]
      rw [Int.add_comm (a.num * b.den), Int.mul_comm a.den b.den]

private theorem den_prod_eq (n : Int) (x y : QRaw) :
    ({ num := n, denM1 := x.denM1 * y.denM1 + x.denM1 + y.denM1 } : QRaw).den = x.den * y.den := by
  unfold QRaw.den
  simp only [Int.natCast_add, Int.natCast_mul]
  rw [Int.add_mul, Int.mul_add, Int.mul_add]
  omega

private theorem den_prod_eq' (n : Int) (x y : QRaw) :
    ({ num := n, denM1 := x.denM1 + (y.denM1 + x.denM1 * y.denM1) } : QRaw).den = x.den * y.den := by
  unfold QRaw.den
  simp only [Int.natCast_add, Int.natCast_mul]
  rw [Int.add_mul, Int.mul_add, Int.mul_add]
  omega

theorem add_assoc (a b c : Q) : a + b + c = a + (b + c) := by
  induction a using Quotient.ind with
  | _ a =>
    induction b using Quotient.ind with
    | _ b =>
      induction c using Quotient.ind with
      | _ c =>
        apply Quotient.sound
        change QRel (rawAdd (rawAdd a b) c) (rawAdd a (rawAdd b c))
        unfold QRel
        change (rawAdd (rawAdd a b) c).num * (rawAdd a (rawAdd b c)).den =
               (rawAdd a (rawAdd b c)).num * (rawAdd (rawAdd a b) c).den
        rw [rawAdd_den, rawAdd_den, rawAdd_den, rawAdd_den]
        simp only [rawAdd, den_prod_eq, den_prod_eq', Int.add_mul, Int.mul_add]
        ac_rfl

theorem zero_add (a : Q) : 0 + a = a := by
  induction a using Quotient.ind with
  | _ a =>
    apply Quotient.sound
    change QRel (rawAdd ⟨0, 0⟩ a) a
    unfold QRel
    rw [rawAdd_den]
    simp [rawAdd, QRaw.den]

theorem add_zero (a : Q) : a + 0 = a := by
  rw [add_comm, zero_add]

theorem add_left_neg (a : Q) : -a + a = 0 := by
  induction a using Quotient.ind with
  | _ a =>
    apply Quotient.sound
    change QRel (rawAdd (rawNeg a) a) ⟨0, 0⟩
    unfold QRel
    rw [rawAdd_den]
    simp [rawAdd, rawNeg, rawNeg_den, QRaw.den, Int.neg_mul, Int.add_left_neg]

theorem add_right_neg (a : Q) : a + (-a) = 0 := by
  rw [add_comm, add_left_neg]

theorem mul_comm (a b : Q) : a * b = b * a := by
  induction a using Quotient.ind with
  | _ a =>
    induction b using Quotient.ind with
    | _ b =>
      apply Quotient.sound
      change QRel (rawMul a b) (rawMul b a)
      unfold QRel
      rw [rawMul_den, rawMul_den]
      simp only [rawMul]
      ac_rfl

theorem mul_assoc (a b c : Q) : a * b * c = a * (b * c) := by
  induction a using Quotient.ind with
  | _ a =>
    induction b using Quotient.ind with
    | _ b =>
      induction c using Quotient.ind with
      | _ c =>
        apply Quotient.sound
        change QRel (rawMul (rawMul a b) c) (rawMul a (rawMul b c))
        unfold QRel
        change (rawMul (rawMul a b) c).num * (rawMul a (rawMul b c)).den =
               (rawMul a (rawMul b c)).num * (rawMul (rawMul a b) c).den
        rw [rawMul_den, rawMul_den, rawMul_den, rawMul_den]
        simp only [rawMul]
        ac_rfl

theorem one_mul (a : Q) : 1 * a = a := by
  induction a using Quotient.ind with
  | _ a =>
    apply Quotient.sound
    change QRel (rawMul ⟨1, 0⟩ a) a
    unfold QRel
    rw [rawMul_den]
    simp [rawMul, QRaw.den]

theorem mul_one (a : Q) : a * 1 = a := by
  rw [mul_comm, one_mul]

theorem left_distrib (a b c : Q) : a * (b + c) = a * b + a * c := by
  induction a using Quotient.ind with
  | _ a =>
    induction b using Quotient.ind with
    | _ b =>
      induction c using Quotient.ind with
      | _ c =>
        apply Quotient.sound
        change QRel (rawMul a (rawAdd b c)) (rawAdd (rawMul a b) (rawMul a c))
        unfold QRel
        change (rawMul a (rawAdd b c)).num * (rawAdd (rawMul a b) (rawMul a c)).den =
               (rawAdd (rawMul a b) (rawMul a c)).num * (rawMul a (rawAdd b c)).den
        rw [rawMul_den, rawAdd_den, rawAdd_den, rawMul_den, rawMul_den]
        simp only [rawMul, rawAdd, den_prod_eq, den_prod_eq', Int.mul_add, Int.add_mul]
        ac_rfl

theorem right_distrib (a b c : Q) : (a + b) * c = a * c + b * c := by
  rw [mul_comm, left_distrib, mul_comm c a, mul_comm c b]

theorem mul_inv_cancel {a : Q} (ha : a ≠ 0) : a * inv a = 1 := by
  induction a using Quotient.ind with
  | _ a =>
    have hnum : a.num ≠ 0 := by
      intro hz
      apply ha
      apply Quotient.sound
      change QRel a ⟨0, 0⟩
      simp [QRel, hz]
    apply Quotient.sound
    change QRel (rawMul a (rawInv a)) ⟨1, 0⟩
    unfold QRel
    change (rawMul a (rawInv a)).num * QRaw.den ⟨1, 0⟩ = (1 : Int) * (rawMul a (rawInv a)).den
    rw [rawMul_den]
    have hd1 : (QRaw.den ⟨1, 0⟩) = 1 := rfl
    rw [hd1, Int.mul_one, Int.one_mul]
    rcases Int.lt_trichotomy a.num 0 with hn | hz | hp
    · have hnot : ¬ (0 < a.num) := by omega
      have hden := rawInv_den_of_neg hn
      have hnum_inv : (rawInv a).num = -a.den := by simp [rawInv, hnum, hnot]
      change a.num * (rawInv a).num = a.den * (rawInv a).den
      rw [hden, hnum_inv, Int.mul_neg, Int.mul_neg, Int.mul_comm]
    · exact absurd hz hnum
    · have hden := rawInv_den_of_pos hp
      have hnum_inv : (rawInv a).num = a.den := by simp [rawInv, hnum, hp]
      change a.num * (rawInv a).num = a.den * (rawInv a).den
      rw [hden, hnum_inv, Int.mul_comm]

instance : Std.Associative (α := Q) (· + ·) := ⟨add_assoc⟩
instance : Std.Commutative (α := Q) (· + ·) := ⟨add_comm⟩
instance : Std.Associative (α := Q) (· * ·) := ⟨mul_assoc⟩
instance : Std.Commutative (α := Q) (· * ·) := ⟨mul_comm⟩

theorem sub_eq_add_neg (a b : Q) : a - b = a + (-b) := rfl

theorem zero_mul (a : Q) : 0 * a = 0 := by
  induction a using Quotient.ind with
  | _ a =>
    apply Quotient.sound
    change QRel (rawMul ⟨0, 0⟩ a) ⟨0, 0⟩
    simp [QRel, rawMul]

theorem mul_zero (a : Q) : a * 0 = 0 := by
  rw [mul_comm, zero_mul]

theorem neg_mul (a b : Q) : (-a) * b = -(a * b) := by
  induction a using Quotient.ind with
  | _ a =>
    induction b using Quotient.ind with
    | _ b =>
      apply Quotient.sound
      change QRel (rawMul (rawNeg a) b) (rawNeg (rawMul a b))
      unfold QRel
      rw [rawMul_den, rawNeg_den, rawMul_den]
      simp only [rawMul, rawNeg, Int.neg_mul]
      rfl

theorem mul_neg (a b : Q) : a * (-b) = -(a * b) := by
  rw [mul_comm, neg_mul, mul_comm]

theorem neg_neg (a : Q) : -(-a) = a := by
  induction a using Quotient.ind with
  | _ a =>
    apply Quotient.sound
    change QRel (rawNeg (rawNeg a)) a
    simp [QRel, rawNeg, rawNeg_den, Int.neg_neg]

theorem neg_add (a b : Q) : -(a + b) = (-a) + (-b) := by
  induction a using Quotient.ind with
  | _ a =>
    induction b using Quotient.ind with
    | _ b =>
      apply Quotient.sound
      change QRel (rawNeg (rawAdd a b)) (rawAdd (rawNeg a) (rawNeg b))
      unfold QRel
      rw [rawNeg_den, rawAdd_den, rawAdd_den]
      simp only [rawNeg, rawAdd, rawNeg_den, Int.neg_add, Int.neg_mul]
      rfl

theorem sub_self (a : Q) : a - a = 0 := add_right_neg a

theorem ofInt_add (m n : Int) : ofInt (m + n) = ofInt m + ofInt n := by
  apply Quotient.sound
  change QRel ⟨m + n, 0⟩ (rawAdd ⟨m, 0⟩ ⟨n, 0⟩)
  unfold QRel
  rw [rawAdd_den]
  simp [rawAdd, QRaw.den]

theorem ofInt_mul (m n : Int) : ofInt (m * n) = ofInt m * ofInt n := by
  apply Quotient.sound
  change QRel ⟨m * n, 0⟩ (rawMul ⟨m, 0⟩ ⟨n, 0⟩)
  unfold QRel
  rw [rawMul_den]
  simp [rawMul, QRaw.den]

theorem ofInt_neg (m : Int) : ofInt (-m) = -ofInt m := by
  apply Quotient.sound
  change QRel ⟨-m, 0⟩ (rawNeg ⟨m, 0⟩)
  simp [QRel, rawNeg]

theorem ofInt_sub (m n : Int) : ofInt (m - n) = ofInt m - ofInt n := by
  rw [Int.sub_eq_add_neg, ofInt_add, ofInt_neg, sub_eq_add_neg]

@[simp] theorem neg_zero : -(0 : Q) = 0 := by
  rw [← zero_add (-(0 : Q)), add_right_neg]

theorem zero_lt_one : (0 : Q) < 1 := by
  constructor
  · change (0 : Int) * QRaw.den ⟨1, 0⟩ ≤ (1 : Int) * QRaw.den ⟨0, 0⟩
    simp [QRaw.den]
  · intro h
    have hrel : QRel ⟨0, 0⟩ ⟨1, 0⟩ := Quotient.exact h
    simp [QRel, QRaw.den] at hrel

theorem le_refl (a : Q) : a ≤ a := by
  induction a using Quotient.ind with
  | _ a => exact Int.le_refl _

theorem le_trans {a b c : Q} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  induction a using Quotient.ind with
  | _ a =>
    induction b using Quotient.ind with
    | _ b =>
      induction c using Quotient.ind with
      | _ c =>
        change a.num * b.den ≤ b.num * a.den at hab
        change b.num * c.den ≤ c.num * b.den at hbc
        change a.num * c.den ≤ c.num * a.den
        have hb : 0 < b.den := b.den_pos
        have h1 : (a.num * c.den) * b.den ≤ (c.num * a.den) * b.den := by
          calc (a.num * c.den) * b.den
              = (a.num * b.den) * c.den := by ac_rfl
            _ ≤ (b.num * a.den) * c.den := Int.mul_le_mul_of_nonneg_right hab (Int.le_of_lt c.den_pos)
            _ = (b.num * c.den) * a.den := by ac_rfl
            _ ≤ (c.num * b.den) * a.den := Int.mul_le_mul_of_nonneg_right hbc (Int.le_of_lt a.den_pos)
            _ = (c.num * a.den) * b.den := by ac_rfl
        exact Int.le_of_mul_le_mul_right h1 hb

theorem le_antisymm {a b : Q} (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  induction a using Quotient.ind with
  | _ a =>
    induction b using Quotient.ind with
    | _ b =>
      apply Quotient.sound
      change QRel a b
      exact Int.le_antisymm hab hba

theorem le_total (a b : Q) : a ≤ b ∨ b ≤ a := by
  induction a using Quotient.ind with
  | _ a =>
    induction b using Quotient.ind with
    | _ b => exact Int.le_total _ _

theorem le_of_lt {a b : Q} (h : a < b) : a ≤ b := h.1

theorem ne_of_lt {a b : Q} (h : a < b) : a ≠ b := h.2

theorem ne_zero_of_pos {a : Q} (h : 0 < a) : a ≠ 0 := h.2.symm

theorem lt_of_le_of_lt {a b c : Q} (hab : a ≤ b) (hbc : b < c) : a < c := by
  refine ⟨le_trans hab hbc.1, ?_⟩
  intro hac
  apply hbc.2
  subst hac
  exact le_antisymm hbc.1 hab

theorem lt_of_lt_of_le {a b c : Q} (hab : a < b) (hbc : b ≤ c) : a < c := by
  refine ⟨le_trans hab.1 hbc, ?_⟩
  intro hac
  apply hab.2
  subst hac
  exact le_antisymm hab.1 hbc

theorem add_le_add_left {a b : Q} (h : a ≤ b) (c : Q) : c + a ≤ c + b := by
  induction a using Quotient.ind with
  | _ a =>
    induction b using Quotient.ind with
    | _ b =>
      induction c using Quotient.ind with
      | _ c =>
        change a.num * b.den ≤ b.num * a.den at h
        change (rawAdd c a).num * (rawAdd c b).den ≤ (rawAdd c b).num * (rawAdd c a).den
        rw [rawAdd_den, rawAdd_den]
        simp only [rawAdd, Int.add_mul]
        have h1 : c.num * a.den * (c.den * b.den) = c.num * b.den * (c.den * a.den) := by ac_rfl
        have h2 : a.num * c.den * (c.den * b.den) ≤ b.num * c.den * (c.den * a.den) := by
          have hc2 : 0 ≤ c.den * c.den := Int.mul_nonneg (Int.le_of_lt c.den_pos) (Int.le_of_lt c.den_pos)
          have hm := Int.mul_le_mul_of_nonneg_right h hc2
          have e1 : a.num * b.den * (c.den * c.den) = a.num * c.den * (c.den * b.den) := by ac_rfl
          have e2 : b.num * a.den * (c.den * c.den) = b.num * c.den * (c.den * a.den) := by ac_rfl
          rw [e1, e2] at hm
          exact hm
        omega

theorem add_le_add_right {a b : Q} (h : a ≤ b) (c : Q) : a + c ≤ b + c := by
  rw [add_comm a c, add_comm b c]
  exact add_le_add_left h c

theorem sub_nonneg_of_le {a b : Q} (h : a ≤ b) : 0 ≤ b - a := by
  have h1 := add_le_add_right h (-a)
  rwa [add_right_neg] at h1

theorem le_of_sub_nonneg {a b : Q} (h : 0 ≤ b - a) : a ≤ b := by
  have h1 := add_le_add_right h a
  rw [zero_add, sub_eq_add_neg, add_assoc, add_left_neg, add_zero] at h1
  exact h1

theorem mul_le_mul_of_nonneg_right {a b c : Q} (hab : a ≤ b) (hc : 0 ≤ c) : a * c ≤ b * c := by
  induction a using Quotient.ind with
  | _ a =>
    induction b using Quotient.ind with
    | _ b =>
      induction c using Quotient.ind with
      | _ c =>
        change a.num * b.den ≤ b.num * a.den at hab
        change (0 : Int) * c.den ≤ c.num * (QRaw.den ⟨0, 0⟩) at hc
        change (0 : Int) * c.den ≤ c.num * 1 at hc
        rw [Int.zero_mul, Int.mul_one] at hc
        change (rawMul a c).num * (rawMul b c).den ≤ (rawMul b c).num * (rawMul a c).den
        rw [rawMul_den, rawMul_den]
        simp only [rawMul]
        have hcc : 0 ≤ c.num * (c.den * c.den) := by
          have hc2 : 0 ≤ c.den * c.den := Int.mul_nonneg (Int.le_of_lt c.den_pos) (Int.le_of_lt c.den_pos)
          exact Int.mul_nonneg hc hc2
        have hm := Int.mul_le_mul_of_nonneg_right hab hcc
        have e1 : a.num * b.den * (c.num * (c.den * c.den)) = a.num * c.num * (b.den * c.den) * c.den := by ac_rfl
        have e2 : b.num * a.den * (c.num * (c.den * c.den)) = b.num * c.num * (a.den * c.den) * c.den := by ac_rfl
        rw [e1, e2] at hm
        exact Int.le_of_mul_le_mul_right hm c.den_pos

theorem mul_le_mul_of_nonneg_left {a b c : Q} (hab : a ≤ b) (hc : 0 ≤ c) : c * a ≤ c * b := by
  rw [mul_comm c a, mul_comm c b]
  exact mul_le_mul_of_nonneg_right hab hc

theorem mul_nonneg {a b : Q} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  have h := mul_le_mul_of_nonneg_right ha hb
  rwa [zero_mul] at h

theorem mul_pos {a b : Q} (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  induction a using Quotient.ind with
  | _ a =>
    induction b using Quotient.ind with
    | _ b =>
      have ha_le : (0 : Int) < a.num := by
        have h1 : (0 : Int) * a.den ≤ a.num * (QRaw.den ⟨0, 0⟩) := ha.1
        simp only [Int.zero_mul, QRaw.den, Int.mul_one] at h1
        by_cases hz : a.num = 0
        · exfalso; apply ha.2; apply Quotient.sound; change QRel ⟨0, 0⟩ a; simp [QRel, hz]
        · omega
      have hb_le : (0 : Int) < b.num := by
        have h1 : (0 : Int) * b.den ≤ b.num * (QRaw.den ⟨0, 0⟩) := hb.1
        simp only [Int.zero_mul, QRaw.den, Int.mul_one] at h1
        by_cases hz : b.num = 0
        · exfalso; apply hb.2; apply Quotient.sound; change QRel ⟨0, 0⟩ b; simp [QRel, hz]
        · omega
      constructor
      · exact mul_nonneg ha.1 hb.1
      · intro heq
        have hrel : QRel ⟨0, 0⟩ (rawMul a b) := Quotient.exact heq
        simp only [QRel, rawMul, Int.zero_mul] at hrel
        have hp : 0 < a.num * b.num := Int.mul_pos ha_le hb_le
        have h1 : 0 < a.num * b.num * (QRaw.den ⟨0, 0⟩) := Int.mul_pos hp (by simp [QRaw.den])
        omega

theorem sq_nonneg (a : Q) : 0 ≤ a * a := by
  cases le_total 0 a with
  | inl h => exact mul_nonneg h h
  | inr h =>
    have hn : 0 ≤ -a := by
      have := add_le_add_right h (-a)
      rwa [add_right_neg, zero_add] at this
    have heq : a * a = (-a) * (-a) := by rw [neg_mul, mul_neg, neg_neg]
    rw [heq]
    exact mul_nonneg hn hn

theorem inv_pos {a : Q} (ha : 0 < a) : 0 < inv a := by
  cases le_total (inv a) 0 with
  | inr h =>
    refine ⟨h, ?_⟩
    intro hzero
    have hmul := mul_inv_cancel (ne_zero_of_pos ha)
    rw [← hzero, mul_zero] at hmul
    exact zero_lt_one.2 hmul
  | inl h =>
    exfalso
    have hmul : a * inv a ≤ 0 := by
      have := mul_le_mul_of_nonneg_left h ha.1
      rwa [mul_zero] at this
    rw [mul_inv_cancel (ne_zero_of_pos ha)] at hmul
    exact zero_lt_one.2 (le_antisymm zero_lt_one.1 hmul)

theorem div_le_div_of_nonneg_right {a b c : Q} (hab : a ≤ b) (hc : 0 < c) : a / c ≤ b / c :=
  mul_le_mul_of_nonneg_right hab (le_of_lt (inv_pos hc))

theorem div_self {a : Q} (ha : a ≠ 0) : a / a = 1 := mul_inv_cancel ha

theorem mul_div_cancel {a b : Q} (hb : b ≠ 0) : (a * b) / b = a := by
  change (a * b) * inv b = a
  rw [mul_assoc, mul_inv_cancel hb, mul_one]

theorem div_mul_cancel {a b : Q} (hb : b ≠ 0) : (a / b) * b = a := by
  change (a * inv b) * b = a
  rw [mul_assoc, mul_comm (inv b) b, mul_inv_cancel hb, mul_one]

theorem add_div (a b c : Q) : (a + b) / c = a / c + b / c :=
  right_distrib a b (inv c)

theorem sub_div (a b c : Q) : (a - b) / c = a / c - b / c := by
  change (a + (-b)) * inv c = a * inv c + (-(b * inv c))
  rw [right_distrib, neg_mul]

end Q

/-! ### Complex Rationals Q[i] (`CQ`) -/

structure CQ where
  re : Q
  im : Q

namespace CQ

def zero : CQ := ⟨0, 0⟩
def one : CQ := ⟨1, 0⟩
def iUnit : CQ := ⟨0, 1⟩
def ofQ (q : Q) : CQ := ⟨q, 0⟩
def ofZGauss (z : ZGauss) : CQ := ⟨Q.ofInt z.re, Q.ofInt z.im⟩

def add (a b : CQ) : CQ := ⟨a.re + b.re, a.im + b.im⟩
def neg (a : CQ) : CQ := ⟨-a.re, -a.im⟩
def sub (a b : CQ) : CQ := add a (neg b)
def mul (a b : CQ) : CQ :=
  ⟨a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re⟩
def conj (a : CQ) : CQ := ⟨a.re, -a.im⟩
def normSq (a : CQ) : Q := a.re * a.re + a.im * a.im

instance : Zero CQ := ⟨zero⟩
instance : Add CQ := ⟨add⟩
instance : Neg CQ := ⟨neg⟩
instance : Sub CQ := ⟨sub⟩
instance : Mul CQ := ⟨mul⟩
instance : OfNat CQ 0 := ⟨zero⟩
instance : OfNat CQ 1 := ⟨one⟩

@[simp] theorem zero_re : (0 : CQ).re = 0 := rfl
@[simp] theorem zero_im : (0 : CQ).im = 0 := rfl
@[simp] theorem one_re : (1 : CQ).re = 1 := rfl
@[simp] theorem one_im : (1 : CQ).im = 0 := rfl
@[simp] theorem add_re (a b : CQ) : (a + b).re = a.re + b.re := rfl
@[simp] theorem add_im (a b : CQ) : (a + b).im = a.im + b.im := rfl
@[simp] theorem neg_re (a : CQ) : (-a).re = -a.re := rfl
@[simp] theorem neg_im (a : CQ) : (-a).im = -a.im := rfl
@[simp] theorem sub_re (a b : CQ) : (a - b).re = a.re - b.re := rfl
@[simp] theorem sub_im (a b : CQ) : (a - b).im = a.im - b.im := rfl
@[simp] theorem mul_re (a b : CQ) : (a * b).re = a.re * b.re - a.im * b.im := rfl
@[simp] theorem mul_im (a b : CQ) : (a * b).im = a.re * b.im + a.im * b.re := rfl
@[simp] theorem conj_re (a : CQ) : a.conj.re = a.re := rfl
@[simp] theorem conj_im (a : CQ) : a.conj.im = -a.im := rfl
@[simp] theorem ofQ_re (q : Q) : (ofQ q).re = q := rfl
@[simp] theorem ofQ_im (q : Q) : (ofQ q).im = 0 := rfl

theorem ext {a b : CQ} (h1 : a.re = b.re) (h2 : a.im = b.im) : a = b := by
  cases a; cases b; simp_all

theorem add_comm (a b : CQ) : a + b = b + a := by
  apply ext <;> simp [Q.add_comm]

theorem add_assoc (a b c : CQ) : a + b + c = a + (b + c) := by
  apply ext <;> simp [Q.add_assoc]

theorem zero_add (a : CQ) : 0 + a = a := by
  apply ext <;> simp [Q.zero_add]

theorem add_zero (a : CQ) : a + 0 = a := by
  apply ext <;> simp [Q.add_zero]

theorem add_left_neg (a : CQ) : -a + a = 0 := by
  apply ext <;> simp [Q.add_left_neg]

theorem add_right_neg (a : CQ) : a + (-a) = 0 := by
  rw [add_comm, add_left_neg]

theorem mul_comm (a b : CQ) : a * b = b * a := by
  apply ext <;> simp [Q.mul_comm, Q.add_comm]

theorem one_mul (a : CQ) : 1 * a = a := by
  apply ext <;> simp [Q.one_mul, Q.zero_mul, Q.sub_eq_add_neg, Q.add_zero, Q.zero_add, Q.neg_zero]

theorem mul_one (a : CQ) : a * 1 = a := by
  rw [mul_comm, one_mul]

theorem zero_mul (a : CQ) : 0 * a = 0 := by
  apply ext <;> simp [Q.zero_mul, Q.sub_eq_add_neg, Q.add_zero, Q.neg_zero]

theorem mul_zero (a : CQ) : a * 0 = 0 := by
  rw [mul_comm, zero_mul]

theorem left_distrib (a b c : CQ) : a * (b + c) = a * b + a * c := by
  apply ext
  · simp only [mul_re, add_re, add_im, Q.left_distrib, Q.sub_eq_add_neg, Q.neg_add, Q.add_assoc]
    ac_rfl
  · simp only [mul_im, add_re, add_im, Q.left_distrib, Q.add_assoc]
    ac_rfl

theorem right_distrib (a b c : CQ) : (a + b) * c = a * c + b * c := by
  rw [mul_comm, left_distrib, mul_comm c a, mul_comm c b]

theorem mul_assoc (a b c : CQ) : a * b * c = a * (b * c) := by
  apply ext
  · simp only [mul_re, mul_im, Q.left_distrib, Q.right_distrib, Q.sub_eq_add_neg, Q.neg_add,
      Q.neg_mul, Q.mul_neg, Q.neg_neg, Q.add_assoc]
    ac_rfl
  · simp only [mul_re, mul_im, Q.left_distrib, Q.right_distrib, Q.sub_eq_add_neg, Q.neg_add,
      Q.neg_mul, Q.mul_neg, Q.neg_neg, Q.add_assoc]
    ac_rfl

theorem neg_mul (a b : CQ) : (-a) * b = -(a * b) := by
  apply ext
  · simp only [mul_re, neg_re, neg_im, Q.neg_mul, Q.sub_eq_add_neg, Q.neg_add, Q.neg_neg]
  · simp only [mul_im, neg_re, neg_im, Q.neg_mul, Q.neg_add]

theorem mul_neg (a b : CQ) : a * (-b) = -(a * b) := by
  rw [mul_comm, neg_mul, mul_comm]

theorem conj_add (a b : CQ) : (a + b).conj = a.conj + b.conj := by
  apply ext <;> simp [Q.neg_add]

theorem conj_mul (a b : CQ) : (a * b).conj = a.conj * b.conj := by
  apply ext
  · simp only [conj_re, mul_re, conj_im, Q.neg_mul, Q.mul_neg, Q.neg_neg]
  · simp only [conj_im, mul_im, conj_re, Q.neg_mul, Q.mul_neg, Q.neg_add]

theorem conj_conj (a : CQ) : a.conj.conj = a := by
  apply ext <;> simp [Q.neg_neg]

theorem ofQ_add (p q : Q) : ofQ (p + q) = ofQ p + ofQ q := by
  apply ext <;> simp [Q.add_zero]

theorem ofQ_mul (p q : Q) : ofQ (p * q) = ofQ p * ofQ q := by
  apply ext <;> simp [Q.zero_mul, Q.mul_zero, Q.sub_eq_add_neg, Q.add_zero, Q.neg_zero]

theorem ofQ_conj (p : Q) : (ofQ p).conj = ofQ p := by
  apply ext
  · rfl
  · simp only [conj_im, ofQ_im, Q.neg_zero]

theorem ofZGauss_zero : ofZGauss 0 = 0 := rfl
theorem ofZGauss_one : ofZGauss 1 = 1 := rfl

theorem ofZGauss_add (a b : ZGauss) : ofZGauss (a + b) = ofZGauss a + ofZGauss b := by
  apply ext <;> simp [ofZGauss, Q.ofInt_add]

theorem ofZGauss_mul (a b : ZGauss) : ofZGauss (a * b) = ofZGauss a * ofZGauss b := by
  apply ext
  · simp [ofZGauss, Q.ofInt_add, Q.ofInt_sub, Q.ofInt_mul, Q.sub_eq_add_neg]
  · simp [ofZGauss, Q.ofInt_add, Q.ofInt_mul]

theorem ofZGauss_conj (a : ZGauss) : ofZGauss a.conj = (ofZGauss a).conj := by
  apply ext <;> simp [ofZGauss, Q.ofInt_neg]

theorem normSq_nonneg (a : CQ) : 0 ≤ a.normSq :=
  have h0 : (0 : Q) = 0 + 0 := (Q.add_zero 0).symm
  by
    unfold normSq
    rw [h0]
    have h1 := Q.add_le_add_right (Q.sq_nonneg a.re) 0
    have h2 := Q.add_le_add_left (Q.sq_nonneg a.im) (a.re * a.re)
    exact Q.le_trans h1 h2

instance : Std.Associative (α := CQ) (· + ·) := ⟨add_assoc⟩
instance : Std.Commutative (α := CQ) (· + ·) := ⟨add_comm⟩
instance : Std.Associative (α := CQ) (· * ·) := ⟨mul_assoc⟩
instance : Std.Commutative (α := CQ) (· * ·) := ⟨mul_comm⟩

end CQ

/-! ## 2. Exact Matrix Algebra & Z[i] -> Q[i] Lifting Bridge -/

def sumFin {α : Type} (z : α) [Add α] : ∀ {n : Nat}, (Fin n → α) → α
  | 0, _ => z
  | _ + 1, f => f 0 + sumFin z (fun i => f i.succ)

namespace SumFin

theorem cq_eq_zero {n : Nat} (f : Fin n → CQ) (h : ∀ i, f i = 0) : sumFin (0 : CQ) f = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumFin]
    rw [h 0, ih (fun i => f i.succ) (fun i => h i.succ), CQ.zero_add]

theorem cq_add {n : Nat} (f g : Fin n → CQ) :
    sumFin (0 : CQ) (fun i => f i + g i) = sumFin (0 : CQ) f + sumFin (0 : CQ) g := by
  induction n with
  | zero => simp [sumFin, CQ.zero_add]
  | succ n ih =>
    simp only [sumFin]
    rw [ih (fun i => f i.succ) (fun i => g i.succ)]
    simp only [CQ.add_assoc]
    ac_rfl

theorem cq_neg {n : Nat} (f : Fin n → CQ) :
    sumFin (0 : CQ) (fun i => -(f i)) = -(sumFin (0 : CQ) f) := by
  induction n with
  | zero =>
    apply CQ.ext <;> simp [sumFin, Q.neg_zero]
  | succ n ih =>
    simp only [sumFin]
    rw [ih (fun i => f i.succ)]
    apply CQ.ext <;> simp [Q.neg_add]

theorem cq_sub {n : Nat} (f g : Fin n → CQ) :
    sumFin (0 : CQ) (fun i => f i - g i) = sumFin (0 : CQ) f - sumFin (0 : CQ) g := by
  have h1 : (fun i => f i - g i) = (fun i => f i + (-(g i))) := rfl
  rw [h1, cq_add, cq_neg]
  rfl

theorem cq_mul_left {n : Nat} (c : CQ) (f : Fin n → CQ) :
    sumFin (0 : CQ) (fun i => c * f i) = c * sumFin (0 : CQ) f := by
  induction n with
  | zero => simp [sumFin, CQ.mul_zero]
  | succ n ih =>
    simp only [sumFin]
    rw [ih (fun i => f i.succ), CQ.left_distrib]

theorem cq_mul_right {n : Nat} (c : CQ) (f : Fin n → CQ) :
    sumFin (0 : CQ) (fun i => f i * c) = sumFin (0 : CQ) f * c := by
  induction n with
  | zero => simp [sumFin, CQ.zero_mul]
  | succ n ih =>
    simp only [sumFin]
    rw [ih (fun i => f i.succ), CQ.right_distrib]

theorem cq_conj {n : Nat} (f : Fin n → CQ) :
    (sumFin (0 : CQ) f).conj = sumFin (0 : CQ) (fun i => (f i).conj) := by
  induction n with
  | zero =>
    apply CQ.ext <;> simp [sumFin, Q.neg_zero]
  | succ n ih =>
    simp only [sumFin, CQ.conj_add]
    rw [ih (fun i => f i.succ)]

theorem cq_swap {n m : Nat} (f : Fin n → Fin m → CQ) :
    sumFin (0 : CQ) (fun i => sumFin (0 : CQ) (fun j => f i j)) =
    sumFin (0 : CQ) (fun j => sumFin (0 : CQ) (fun i => f i j)) := by
  induction n with
  | zero =>
    simp only [sumFin]
    symm
    exact cq_eq_zero _ (fun _ => rfl)
  | succ n ih =>
    simp only [sumFin]
    rw [ih (fun i j => f i.succ j)]
    rw [← cq_add]

theorem ofZGauss_sum {n : Nat} (f : Fin n → ZGauss) :
    CQ.ofZGauss (sumFin (0 : ZGauss) f) = sumFin (0 : CQ) (fun i => CQ.ofZGauss (f i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumFin]
    rw [CQ.ofZGauss_add, ih (fun i => f i.succ)]

end SumFin

abbrev Mat (d : Nat) (α : Type) := Fin d → Fin d → α

namespace MatCQ

def zero {d : Nat} : Mat d CQ := fun _ _ => 0
def id {d : Nat} : Mat d CQ := fun i j => if i = j then 1 else 0
def add {d : Nat} (A B : Mat d CQ) : Mat d CQ := fun i j => A i j + B i j
def neg {d : Nat} (A : Mat d CQ) : Mat d CQ := fun i j => -(A i j)
def sub {d : Nat} (A B : Mat d CQ) : Mat d CQ := fun i j => A i j - B i j
def scale {d : Nat} (c : CQ) (A : Mat d CQ) : Mat d CQ := fun i j => c * A i j
def mul {d : Nat} (A B : Mat d CQ) : Mat d CQ := fun i j => sumFin (0 : CQ) (fun k => A i k * B k j)
def conjT {d : Nat} (A : Mat d CQ) : Mat d CQ := fun i j => (A j i).conj
def trace {d : Nat} (A : Mat d CQ) : CQ := sumFin (0 : CQ) (fun i => A i i)
def comm {d : Nat} (A B : Mat d CQ) : Mat d CQ := sub (mul A B) (mul B A)
def frobInner {d : Nat} (A B : Mat d CQ) : CQ := trace (mul (conjT A) B)
def frobDot {d : Nat} (A B : Mat d CQ) : CQ :=
  sumFin (0 : CQ) (fun i => sumFin (0 : CQ) (fun j => (A i j).conj * B i j))

theorem add_comm {d : Nat} (A B : Mat d CQ) : add A B = add B A := by
  funext i j; exact CQ.add_comm _ _

theorem add_assoc {d : Nat} (A B C : Mat d CQ) : add (add A B) C = add A (add B C) := by
  funext i j; exact CQ.add_assoc _ _ _

theorem zero_add {d : Nat} (A : Mat d CQ) : add zero A = A := by
  funext i j; exact CQ.zero_add _

theorem add_zero {d : Nat} (A : Mat d CQ) : add A zero = A := by
  funext i j; exact CQ.add_zero _

theorem sub_eq_add_neg {d : Nat} (A B : Mat d CQ) : sub A B = add A (neg B) := rfl

theorem mul_add {d : Nat} (A B C : Mat d CQ) : mul A (add B C) = add (mul A B) (mul A C) := by
  funext i j
  simp only [mul, add, CQ.left_distrib]
  exact SumFin.cq_add _ _

theorem add_mul {d : Nat} (A B C : Mat d CQ) : mul (add A B) C = add (mul A C) (mul B C) := by
  funext i j
  simp only [mul, add, CQ.right_distrib]
  exact SumFin.cq_add _ _

theorem scale_mul_left {d : Nat} (c : CQ) (A B : Mat d CQ) : mul (scale c A) B = scale c (mul A B) := by
  funext i j
  simp only [mul, scale, CQ.mul_assoc]
  exact SumFin.cq_mul_left c _

theorem scale_mul_right {d : Nat} (c : CQ) (A B : Mat d CQ) : mul A (scale c B) = scale c (mul A B) := by
  funext i j
  simp only [mul, scale]
  have hf : (fun k => A i k * (c * B k j)) = (fun k => c * (A i k * B k j)) := by
    funext k; ac_rfl
  rw [hf]
  exact SumFin.cq_mul_left c _

theorem comm_add_left {d : Nat} (A B C : Mat d CQ) :
    comm (add A B) C = add (comm A C) (comm B C) := by
  funext i j
  simp only [comm, add_mul, mul_add, add, sub, CQ.sub]
  change (mul A C i j + mul B C i j) + -(mul C A i j + mul C B i j) =
         (mul A C i j + -(mul C A i j)) + (mul B C i j + -(mul C B i j))
  have hneg : -(mul C A i j + mul C B i j) = -(mul C A i j) + -(mul C B i j) := by
    apply CQ.ext <;> simp [Q.neg_add]
  rw [hneg]
  ac_rfl

theorem comm_add_right {d : Nat} (A B C : Mat d CQ) :
    comm A (add B C) = add (comm A B) (comm A C) := by
  funext i j
  simp only [comm, add_mul, mul_add, add, sub, CQ.sub]
  change (mul A B i j + mul A C i j) + -(mul B A i j + mul C A i j) =
         (mul A B i j + -(mul B A i j)) + (mul A C i j + -(mul C A i j))
  have hneg : -(mul B A i j + mul C A i j) = -(mul B A i j) + -(mul C A i j) := by
    apply CQ.ext <;> simp [Q.neg_add]
  rw [hneg]
  ac_rfl

theorem comm_scale_left {d : Nat} (c : CQ) (A B : Mat d CQ) :
    comm (scale c A) B = scale c (comm A B) := by
  funext i j
  simp only [comm, scale_mul_left, scale_mul_right, scale, sub, CQ.sub]
  change c * mul A B i j + -(c * mul B A i j) = c * (mul A B i j + -(mul B A i j))
  rw [CQ.left_distrib, CQ.mul_neg]

theorem comm_scale_right {d : Nat} (c : CQ) (A B : Mat d CQ) :
    comm A (scale c B) = scale c (comm A B) := by
  funext i j
  simp only [comm, scale_mul_left, scale_mul_right, scale, sub, CQ.sub]
  change c * mul A B i j + -(c * mul B A i j) = c * (mul A B i j + -(mul B A i j))
  rw [CQ.left_distrib, CQ.mul_neg]

theorem comm_zero_add {d : Nat} {A B C : Mat d CQ} (hA : comm A C = zero) (hB : comm B C = zero) :
    comm (add A B) C = zero := by
  rw [comm_add_left, hA, hB, zero_add]

theorem comm_zero_scale {d : Nat} (c : CQ) {A B : Mat d CQ} (hA : comm A B = zero) :
    comm (scale c A) B = zero := by
  rw [comm_scale_left, hA]
  funext i j; exact CQ.mul_zero c

theorem frobInner_eq_frobDot {d : Nat} (A B : Mat d CQ) : frobInner A B = frobDot A B := by
  unfold frobInner trace mul conjT frobDot
  exact SumFin.cq_swap (fun i k => (A k i).conj * B k i)

theorem frobInner_add_left {d : Nat} (A B C : Mat d CQ) :
    frobInner (add A B) C = frobInner A C + frobInner B C := by
  rw [frobInner_eq_frobDot, frobInner_eq_frobDot, frobInner_eq_frobDot]
  unfold frobDot add
  simp only [CQ.conj_add, CQ.right_distrib]
  have hr : (fun i => sumFin (0 : CQ) (fun j => (A i j).conj * C i j + (B i j).conj * C i j)) =
            (fun i => sumFin (0 : CQ) (fun j => (A i j).conj * C i j) +
                      sumFin (0 : CQ) (fun j => (B i j).conj * C i j)) :=
    funext (fun i => SumFin.cq_add _ _)
  rw [hr]
  exact SumFin.cq_add _ _

theorem frobInner_add_right {d : Nat} (A B C : Mat d CQ) :
    frobInner A (add B C) = frobInner A B + frobInner A C := by
  rw [frobInner_eq_frobDot, frobInner_eq_frobDot, frobInner_eq_frobDot]
  unfold frobDot add
  simp only [CQ.left_distrib]
  have hr : (fun i => sumFin (0 : CQ) (fun j => (A i j).conj * B i j + (A i j).conj * C i j)) =
            (fun i => sumFin (0 : CQ) (fun j => (A i j).conj * B i j) +
                      sumFin (0 : CQ) (fun j => (A i j).conj * C i j)) :=
    funext (fun i => SumFin.cq_add _ _)
  rw [hr]
  exact SumFin.cq_add _ _

theorem frobInner_scale_left {d : Nat} (c : CQ) (A B : Mat d CQ) :
    frobInner (scale c A) B = c.conj * frobInner A B := by
  rw [frobInner_eq_frobDot, frobInner_eq_frobDot]
  unfold frobDot scale
  simp only [CQ.conj_mul, CQ.mul_assoc]
  have hr : (fun i => sumFin (0 : CQ) (fun j => c.conj * ((A i j).conj * B i j))) =
            (fun i => c.conj * sumFin (0 : CQ) (fun j => (A i j).conj * B i j)) :=
    funext (fun i => SumFin.cq_mul_left c.conj _)
  rw [hr]
  exact SumFin.cq_mul_left c.conj _

theorem frobInner_scale_right {d : Nat} (c : CQ) (A B : Mat d CQ) :
    frobInner A (scale c B) = c * frobInner A B := by
  rw [frobInner_eq_frobDot, frobInner_eq_frobDot]
  unfold frobDot scale
  have hf : (fun i => sumFin (0 : CQ) (fun j => (A i j).conj * (c * B i j))) =
            (fun i => c * sumFin (0 : CQ) (fun j => (A i j).conj * B i j)) := by
    funext i
    have hf' : (fun j => (A i j).conj * (c * B i j)) = (fun j => c * ((A i j).conj * B i j)) :=
      funext (fun j => by ac_rfl)
    rw [hf']
    exact SumFin.cq_mul_left c _
  rw [hf]
  exact SumFin.cq_mul_left c _

theorem frobInner_zero_left {d : Nat} (A : Mat d CQ) : frobInner zero A = 0 := by
  rw [frobInner_eq_frobDot]
  unfold frobDot zero
  apply SumFin.cq_eq_zero; intro i
  apply SumFin.cq_eq_zero; intro j
  have hc : (0 : CQ).conj = 0 := by apply CQ.ext <;> simp [Q.neg_zero]
  rw [hc, CQ.zero_mul]

theorem frobInner_zero_right {d : Nat} (A : Mat d CQ) : frobInner A zero = 0 := by
  rw [frobInner_eq_frobDot]
  unfold frobDot zero
  apply SumFin.cq_eq_zero; intro i
  apply SumFin.cq_eq_zero; intro j
  exact CQ.mul_zero _

end MatCQ

/-! ### Exact Z[i] Matrix Lists (`MatZList`) & Kernel-Checked Lifting Bridge -/

abbrev MatZList := List (List ZGauss)

def lget {α : Type} (d : α) : List α → Nat → α
  | [], _ => d
  | x :: _, 0 => x
  | _ :: xs, k + 1 => lget d xs k

def toFinZ (d : Nat) (A : MatZList) : Mat d ZGauss :=
  fun i j => lget 0 (lget [] A i.val) j.val

def liftMat {d : Nat} (c : Q) (A : Mat d ZGauss) : Mat d CQ :=
  fun i j => CQ.ofQ c * CQ.ofZGauss (A i j)

def finMatMulZ {d : Nat} (A B : Mat d ZGauss) : Mat d ZGauss :=
  fun i j => sumFin (0 : ZGauss) (fun k => A i k * B k j)

def finMatAddZ {d : Nat} (A B : Mat d ZGauss) : Mat d ZGauss :=
  fun i j => A i j + B i j

def finMatSubZ {d : Nat} (A B : Mat d ZGauss) : Mat d ZGauss :=
  fun i j => A i j - B i j

def finMatScaleZ {d : Nat} (c : ZGauss) (A : Mat d ZGauss) : Mat d ZGauss :=
  fun i j => c * A i j

def finMatConjTZ {d : Nat} (A : Mat d ZGauss) : Mat d ZGauss :=
  fun i j => (A j i).conj

def finMatTraceZ {d : Nat} (A : Mat d ZGauss) : ZGauss :=
  sumFin (0 : ZGauss) (fun i => A i i)

def finMatFrobDotZ {d : Nat} (A B : Mat d ZGauss) : ZGauss :=
  sumFin (0 : ZGauss) (fun i => sumFin (0 : ZGauss) (fun j => (A i j).conj * B i j))

namespace Lift

theorem liftMat_add {d : Nat} (c : Q) (A B : Mat d ZGauss) :
    MatCQ.add (liftMat c A) (liftMat c B) = liftMat c (finMatAddZ A B) := by
  funext i j
  simp only [MatCQ.add, liftMat, finMatAddZ, CQ.ofZGauss_add, CQ.left_distrib]

theorem liftMat_sub {d : Nat} (c : Q) (A B : Mat d ZGauss) :
    MatCQ.sub (liftMat c A) (liftMat c B) = liftMat c (finMatSubZ A B) := by
  funext i j
  simp only [MatCQ.sub, liftMat, finMatSubZ, CQ.sub]
  have hs : CQ.ofZGauss (A i j - B i j) = CQ.ofZGauss (A i j) + -(CQ.ofZGauss (B i j)) := by
    apply CQ.ext <;> simp [CQ.ofZGauss, Q.ofInt_sub, Q.ofInt_neg, Q.sub_eq_add_neg]
  rw [hs, CQ.left_distrib, CQ.mul_neg]
  rfl

theorem liftMat_scale {d : Nat} (s : Q) (c : Q) (A : Mat d ZGauss) :
    MatCQ.scale (CQ.ofQ s) (liftMat c A) = liftMat (s * c) A := by
  funext i j
  simp only [MatCQ.scale, liftMat, CQ.ofQ_mul, CQ.mul_assoc]

theorem liftMat_scaleZ {d : Nat} (c : Q) (z : ZGauss) (A : Mat d ZGauss) :
    liftMat c (finMatScaleZ z A) = MatCQ.scale (CQ.ofZGauss z) (liftMat c A) := by
  funext i j
  simp only [liftMat, finMatScaleZ, MatCQ.scale, CQ.ofZGauss_mul]
  ac_rfl

theorem liftMat_mul {d : Nat} (a b : Q) (A B : Mat d ZGauss) :
    MatCQ.mul (liftMat a A) (liftMat b B) = liftMat (a * b) (finMatMulZ A B) := by
  funext i j
  simp only [MatCQ.mul, liftMat, finMatMulZ, SumFin.ofZGauss_sum, CQ.ofQ_mul]
  have h1 : (fun k => (CQ.ofQ a * CQ.ofZGauss (A i k)) * (CQ.ofQ b * CQ.ofZGauss (B k j))) =
            (fun k => (CQ.ofQ a * CQ.ofQ b) * CQ.ofZGauss (A i k * B k j)) := by
    funext k
    rw [CQ.ofZGauss_mul]
    ac_rfl
  rw [h1, SumFin.cq_mul_left]

theorem liftMat_conjT {d : Nat} (c : Q) (A : Mat d ZGauss) :
    MatCQ.conjT (liftMat c A) = liftMat c (finMatConjTZ A) := by
  funext i j
  simp only [MatCQ.conjT, liftMat, finMatConjTZ, CQ.conj_mul, CQ.ofQ_conj, CQ.ofZGauss_conj]

theorem liftMat_trace {d : Nat} (c : Q) (A : Mat d ZGauss) :
    MatCQ.trace (liftMat c A) = CQ.ofQ c * CQ.ofZGauss (finMatTraceZ A) := by
  unfold MatCQ.trace liftMat finMatTraceZ
  rw [SumFin.ofZGauss_sum, SumFin.cq_mul_left]

theorem liftMat_comm {d : Nat} (a b : Q) (A B : Mat d ZGauss) :
    MatCQ.comm (liftMat a A) (liftMat b B) =
    liftMat (a * b) (finMatSubZ (finMatMulZ A B) (finMatMulZ B A)) := by
  unfold MatCQ.comm
  rw [liftMat_mul, liftMat_mul, Q.mul_comm b a, liftMat_sub]

theorem liftMat_frobInner {d : Nat} (a b : Q) (A B : Mat d ZGauss) :
    MatCQ.frobInner (liftMat a A) (liftMat b B) =
    CQ.ofQ (a * b) * CQ.ofZGauss (finMatFrobDotZ A B) := by
  rw [MatCQ.frobInner_eq_frobDot]
  unfold MatCQ.frobDot liftMat finMatFrobDotZ
  simp only [CQ.conj_mul, CQ.ofQ_conj, CQ.ofZGauss_conj, CQ.ofQ_mul, SumFin.ofZGauss_sum]
  have hf : (fun i => sumFin (0 : CQ) (fun j => (CQ.ofQ a * (CQ.ofZGauss (A i j)).conj) * (CQ.ofQ b * CQ.ofZGauss (B i j)))) =
            (fun i => (CQ.ofQ a * CQ.ofQ b) * sumFin (0 : CQ) (fun j => CQ.ofZGauss ((A i j).conj * B i j))) := by
    funext i
    have hf' : (fun j => (CQ.ofQ a * (CQ.ofZGauss (A i j)).conj) * (CQ.ofQ b * CQ.ofZGauss (B i j))) =
               (fun j => (CQ.ofQ a * CQ.ofQ b) * CQ.ofZGauss ((A i j).conj * B i j)) := by
      funext j
      rw [CQ.ofZGauss_mul, CQ.ofZGauss_conj]
      ac_rfl
    rw [hf']
    exact SumFin.cq_mul_left _ _
  rw [hf]
  rw [SumFin.cq_mul_left]

end Lift

/-! ### List-Based Kernel Evaluators for Fast `decide` -/

def dotZ : List ZGauss → List ZGauss → ZGauss
  | x :: xs, y :: ys => x * y + dotZ xs ys
  | _, _ => 0

def dotConjZ : List ZGauss → List ZGauss → ZGauss
  | x :: xs, y :: ys => x.conj * y + dotConjZ xs ys
  | _, _ => 0

def matAddZ (A B : MatZList) : MatZList := List.zipWith (List.zipWith (· + ·)) A B
def matSubZ (A B : MatZList) : MatZList := List.zipWith (List.zipWith (· - ·)) A B
def matScaleZ (c : ZGauss) (A : MatZList) : MatZList := A.map (·.map (c * ·))
def matMulZ (d : Nat) (A B : MatZList) : MatZList :=
  let cols := (List.range d).map (fun j => B.map (fun r => lget 0 r j))
  A.map (fun row => cols.map (dotZ row))
def matCommZ (d : Nat) (A B : MatZList) : MatZList := matSubZ (matMulZ d A B) (matMulZ d B A)
def matConjTZ (d : Nat) (A : MatZList) : MatZList :=
  (List.range d).map (fun i => (List.range d).map (fun j => (lget 0 (lget [] A j) i).conj))
def matTraceZ (d : Nat) (A : MatZList) : ZGauss :=
  (List.range d).foldr (fun i acc => lget 0 (lget [] A i) i + acc) 0
def frobDotZ (A B : MatZList) : ZGauss :=
  (List.zipWith dotConjZ A B).foldr (· + ·) 0
def kronZ (A B : MatZList) : MatZList :=
  A.flatMap (fun rowA => B.map (fun rowB => rowA.flatMap (fun a => rowB.map (fun b => a * b))))
def isSqZ (d : Nat) (A : MatZList) : Bool := A.length == d && A.all (·.length == d)

/-! ### Bridge Theorems: `MatZList` -> `Mat d ZGauss` -/

private theorem lget_map {α β : Type} (d1 : α) (d2 : β) (f : α → β) (l : List α) (k : Nat)
    (hk : k < l.length) : lget d2 (l.map f) k = f (lget d1 l k) := by
  induction l generalizing k with
  | nil => simp at hk
  | cons x xs ih =>
    cases k with
    | zero => rfl
    | succ k' =>
      simp only [List.length_cons] at hk
      exact ih k' (Nat.lt_of_succ_lt_succ hk)

private theorem lget_range_aux (n start k : Nat) (hk : k < n) :
    lget 0 ((List.range n).map (· + start)) k = k + start := by
  induction n generalizing start k with
  | zero => contradiction
  | succ n ih =>
    rw [List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map]
    cases k with
    | zero => simp [lget]
    | succ k' =>
      have hk' : k' < n := Nat.lt_of_succ_lt_succ hk
      change lget 0 ((List.range n).map (fun x => (x + 1) + start)) k' = k' + 1 + start
      have hfn : (fun x => (x + 1) + start) = (fun x => x + (start + 1)) := by
        funext x; omega
      rw [hfn, ih (start + 1) k' hk']
      omega

private theorem lget_range (n k : Nat) (hk : k < n) : lget 0 (List.range n) k = k := by
  have h := lget_range_aux n 0 k hk
  have hid : ((List.range n).map (· + 0)) = List.range n := by
    have h1 : (fun x : Nat => x + 0) = id := funext (fun x => Nat.add_zero x)
    rw [h1, List.map_id]
  rw [hid] at h
  omega

private theorem lget_zipWith {α β γ : Type} (d1 : α) (d2 : β) (d3 : γ) (f : α → β → γ)
    (xs : List α) (ys : List β) (k : Nat) (hx : k < xs.length) (hy : k < ys.length) :
    lget d3 (List.zipWith f xs ys) k = f (lget d1 xs k) (lget d2 ys k) := by
  induction xs generalizing ys k with
  | nil => simp at hx
  | cons x xs' ih =>
    cases ys with
    | nil => simp at hy
    | cons y ys' =>
      cases k with
      | zero => rfl
      | succ k' =>
        simp only [List.length_cons] at hx hy
        exact ih ys' k' (Nat.lt_of_succ_lt_succ hx) (Nat.lt_of_succ_lt_succ hy)

private theorem all_len_eq {d : Nat} {A : MatZList} (h : isSqZ d A = true) :
    A.length = d ∧ ∀ r, r ∈ A → r.length = d := by
  unfold isSqZ at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  exact ⟨h.1, fun r hr => h.2 r hr⟩

private theorem lget_mem {α : Type} (d : α) (l : List α) (k : Nat) (hk : k < l.length) :
    lget d l k ∈ l := by
  induction l generalizing k with
  | nil => simp at hk
  | cons x xs ih =>
    cases k with
    | zero => exact List.Mem.head _
    | succ k' =>
      simp only [List.length_cons] at hk
      exact List.Mem.tail _ (ih k' (Nat.lt_of_succ_lt_succ hk))

theorem toFinZ_add {d : Nat} (A B : MatZList) (hA : isSqZ d A = true) (hB : isSqZ d B = true) :
    toFinZ d (matAddZ A B) = finMatAddZ (toFinZ d A) (toFinZ d B) := by
  obtain ⟨hAl, hAr⟩ := all_len_eq hA
  obtain ⟨hBl, hBr⟩ := all_len_eq hB
  funext i j
  unfold toFinZ finMatAddZ matAddZ
  have hiA : i.val < A.length := by rw [hAl]; exact i.isLt
  have hiB : i.val < B.length := by rw [hBl]; exact i.isLt
  rw [lget_zipWith [] [] [] (List.zipWith (· + ·)) A B i.val hiA hiB]
  have hjA : j.val < (lget [] A i.val).length := by rw [hAr _ (lget_mem [] A i.val hiA)]; exact j.isLt
  have hjB : j.val < (lget [] B i.val).length := by rw [hBr _ (lget_mem [] B i.val hiB)]; exact j.isLt
  exact lget_zipWith 0 0 0 (· + ·) _ _ j.val hjA hjB

theorem toFinZ_sub {d : Nat} (A B : MatZList) (hA : isSqZ d A = true) (hB : isSqZ d B = true) :
    toFinZ d (matSubZ A B) = finMatSubZ (toFinZ d A) (toFinZ d B) := by
  obtain ⟨hAl, hAr⟩ := all_len_eq hA
  obtain ⟨hBl, hBr⟩ := all_len_eq hB
  funext i j
  unfold toFinZ finMatSubZ matSubZ
  have hiA : i.val < A.length := by rw [hAl]; exact i.isLt
  have hiB : i.val < B.length := by rw [hBl]; exact i.isLt
  rw [lget_zipWith [] [] [] (List.zipWith (· - ·)) A B i.val hiA hiB]
  have hjA : j.val < (lget [] A i.val).length := by rw [hAr _ (lget_mem [] A i.val hiA)]; exact j.isLt
  have hjB : j.val < (lget [] B i.val).length := by rw [hBr _ (lget_mem [] B i.val hiB)]; exact j.isLt
  exact lget_zipWith 0 0 0 (· - ·) _ _ j.val hjA hjB

theorem toFinZ_scale {d : Nat} (c : ZGauss) (A : MatZList) (hA : isSqZ d A = true) :
    toFinZ d (matScaleZ c A) = finMatScaleZ c (toFinZ d A) := by
  obtain ⟨hAl, hAr⟩ := all_len_eq hA
  funext i j
  unfold toFinZ finMatScaleZ matScaleZ
  have hiA : i.val < A.length := by rw [hAl]; exact i.isLt
  rw [lget_map [] [] (List.map (c * ·)) A i.val hiA]
  have hjA : j.val < (lget [] A i.val).length := by rw [hAr _ (lget_mem [] A i.val hiA)]; exact j.isLt
  exact lget_map 0 0 (c * ·) _ j.val hjA

private theorem dotZ_eq_sumFin_aux (xs ys : List ZGauss) (n : Nat)
    (hx : xs.length = n) (hy : ys.length = n) :
    dotZ xs ys = sumFin (0 : ZGauss) (fun k : Fin n => lget 0 xs k.val * lget 0 ys k.val) := by
  induction n generalizing xs ys with
  | zero =>
    cases xs <;> cases ys <;> simp_all [dotZ, sumFin]
  | succ n ih =>
    cases xs with
    | nil => simp at hx
    | cons x xs' =>
      cases ys with
      | nil => simp at hy
      | cons y ys' =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hx hy
        simp only [dotZ, sumFin]
        congr 1
        exact ih xs' ys' hx hy

private theorem dotConjZ_eq_sumFin_aux (xs ys : List ZGauss) (n : Nat)
    (hx : xs.length = n) (hy : ys.length = n) :
    dotConjZ xs ys = sumFin (0 : ZGauss) (fun k : Fin n => (lget 0 xs k.val).conj * lget 0 ys k.val) := by
  induction n generalizing xs ys with
  | zero =>
    cases xs <;> cases ys <;> simp_all [dotConjZ, sumFin]
  | succ n ih =>
    cases xs with
    | nil => simp at hx
    | cons x xs' =>
      cases ys with
      | nil => simp at hy
      | cons y ys' =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hx hy
        simp only [dotConjZ, sumFin]
        congr 1
        exact ih xs' ys' hx hy

theorem toFinZ_mul {d : Nat} (A B : MatZList) (hA : isSqZ d A = true) (hB : isSqZ d B = true) :
    toFinZ d (matMulZ d A B) = finMatMulZ (toFinZ d A) (toFinZ d B) := by
  obtain ⟨hAl, hAr⟩ := all_len_eq hA
  obtain ⟨hBl, _⟩ := all_len_eq hB
  funext i j
  unfold toFinZ finMatMulZ matMulZ
  have hiA : i.val < A.length := by rw [hAl]; exact i.isLt
  rw [lget_map [] [] _ A i.val hiA]
  have hjR : j.val < ((List.range d).map (fun j => B.map (fun r => lget 0 r j))).length := by
    rw [List.length_map, List.length_range]; exact j.isLt
  rw [lget_map [] 0 (dotZ (lget [] A i.val)) _ j.val hjR]
  have hjD : j.val < (List.range d).length := by rw [List.length_range]; exact j.isLt
  rw [lget_map 0 [] (fun j => B.map (fun r => lget 0 r j)) (List.range d) j.val hjD]
  rw [lget_range d j.val j.isLt]
  have hrow : (lget [] A i.val).length = d := hAr _ (lget_mem [] A i.val hiA)
  have hcol : (B.map (fun r => lget 0 r j.val)).length = d := by rw [List.length_map, hBl]
  rw [dotZ_eq_sumFin_aux _ _ d hrow hcol]
  congr 1
  funext k
  have hkB : k.val < B.length := by rw [hBl]; exact k.isLt
  rw [lget_map [] 0 (fun r => lget 0 r j.val) B k.val hkB]

theorem toFinZ_conjT {d : Nat} (A : MatZList) :
    toFinZ d (matConjTZ d A) = finMatConjTZ (toFinZ d A) := by
  funext i j
  unfold toFinZ finMatConjTZ matConjTZ
  have hiR : i.val < (List.range d).length := by rw [List.length_range]; exact i.isLt
  have hjR : j.val < (List.range d).length := by rw [List.length_range]; exact j.isLt
  rw [lget_map 0 [] _ (List.range d) i.val hiR, lget_range d i.val i.isLt]
  rw [lget_map 0 0 _ (List.range d) j.val hjR, lget_range d j.val j.isLt]

theorem toFinZ_comm {d : Nat} (A B : MatZList) (hA : isSqZ d A = true) (hB : isSqZ d B = true)
    (hAB : isSqZ d (matMulZ d A B) = true) (hBA : isSqZ d (matMulZ d B A) = true) :
    toFinZ d (matCommZ d A B) = finMatSubZ (finMatMulZ (toFinZ d A) (toFinZ d B))
                                            (finMatMulZ (toFinZ d B) (toFinZ d A)) := by
  unfold matCommZ
  rw [toFinZ_sub _ _ hAB hBA, toFinZ_mul A B hA hB, toFinZ_mul B A hB hA]

private theorem foldr_map_range_eq_sumFin (n start : Nat) (g : Nat → ZGauss) :
    ((List.range n).map (· + start)).foldr (fun k acc => g k + acc) 0 =
    sumFin (0 : ZGauss) (fun i : Fin n => g (i.val + start)) := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, List.foldr_cons, sumFin]
    have hfn : ((fun x => x + start) ∘ Nat.succ) = (fun x => x + (start + 1)) := by
      funext x; simp [Function.comp_def]; omega
    rw [hfn, ih (start + 1)]
    have heq : (fun i : Fin n => g (i.val + (start + 1))) = (fun i : Fin n => g (i.succ.val + start)) := by
      funext i; simp only [Fin.val_succ]; congr 1; omega
    rw [heq]
    simp [Nat.zero_add]

theorem matTraceZ_eq {d : Nat} (A : MatZList) :
    matTraceZ d A = finMatTraceZ (toFinZ d A) := by
  unfold matTraceZ finMatTraceZ toFinZ
  have h0 := foldr_map_range_eq_sumFin d 0 (fun i => lget 0 (lget [] A i) i)
  have hid : ((List.range d).map (· + 0)) = List.range d := by
    have h1 : (fun x : Nat => x + 0) = id := funext (fun x => Nat.add_zero x)
    rw [h1, List.map_id]
  rw [hid] at h0
  rw [h0]
  rfl

private theorem frobDotZ_aux (d n : Nat) (A B : MatZList)
    (hAl : A.length = n) (hAr : ∀ r, r ∈ A → r.length = d)
    (hBl : B.length = n) (hBr : ∀ r, r ∈ B → r.length = d) :
    (List.zipWith dotConjZ A B).foldr (· + ·) 0 =
    sumFin (0 : ZGauss) (fun i : Fin n =>
      sumFin (0 : ZGauss) (fun j : Fin d => (lget 0 (lget [] A i.val) j.val).conj * lget 0 (lget [] B i.val) j.val)) := by
  induction n generalizing A B with
  | zero =>
    cases A <;> cases B <;> simp_all [sumFin]
  | succ n ih =>
    cases A with
    | nil => simp at hAl
    | cons rA As =>
      cases B with
      | nil => simp at hBl
      | cons rB Bs =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hAl hBl
        simp only [List.zipWith_cons_cons, List.foldr_cons, sumFin]
        congr 1
        · exact dotConjZ_eq_sumFin_aux rA rB d (hAr rA (List.Mem.head _)) (hBr rB (List.Mem.head _))
        · exact ih As Bs hAl (fun r hr => hAr r (List.Mem.tail _ hr)) hBl (fun r hr => hBr r (List.Mem.tail _ hr))

theorem frobDotZ_eq {d : Nat} (A B : MatZList) (hA : isSqZ d A = true) (hB : isSqZ d B = true) :
    frobDotZ A B = finMatFrobDotZ (toFinZ d A) (toFinZ d B) := by
  obtain ⟨hAl, hAr⟩ := all_len_eq hA
  obtain ⟨hBl, hBr⟩ := all_len_eq hB
  exact frobDotZ_aux d d A B hAl hAr hBl hBr

/-! ### Kronecker Product Algebra & `kronZ` Bridge -/

def sumNat (n : Nat) (g : Nat → CQ) : CQ :=
  sumFin (0 : CQ) (fun i : Fin n => g i.val)

namespace SumNat

theorem zero (g : Nat → CQ) : sumNat 0 g = 0 := rfl

private theorem snoc_fin_aux :
    ∀ {n : Nat} (f : Fin (n + 1) → CQ),
    sumFin (0 : CQ) f = sumFin (0 : CQ) (fun i : Fin n => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) + f ⟨n, Nat.lt_succ_self n⟩
  | 0, f => by simp only [sumFin, CQ.zero_add, CQ.add_zero]; rfl
  | n + 1, f => by
    have ih := snoc_fin_aux (fun i : Fin (n + 1) => f i.succ)
    change f 0 + sumFin (0 : CQ) (fun i => f i.succ) = _
    rw [ih, ← CQ.add_assoc]
    rfl

theorem succ (n : Nat) (g : Nat → CQ) : sumNat (n + 1) g = sumNat n g + g n := by
  unfold sumNat
  exact snoc_fin_aux (fun i : Fin (n + 1) => g i.val)

theorem add (a b : Nat) (g : Nat → CQ) :
    sumNat (a + b) g = sumNat a g + sumNat b (fun j => g (a + j)) := by
  induction b with
  | zero => simp [zero, CQ.add_zero]
  | succ b ih =>
    rw [Nat.add_succ, succ, succ, ih, CQ.add_assoc]

theorem congr {n : Nat} {g1 g2 : Nat → CQ} (h : ∀ i, i < n → g1 i = g2 i) :
    sumNat n g1 = sumNat n g2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [succ, succ, ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h n (Nat.lt_succ_self n)]

theorem eq_sumFin {n : Nat} (f : Fin n → CQ) :
    sumFin (0 : CQ) f = sumNat n (fun i => if hi : i < n then f ⟨i, hi⟩ else 0) := by
  unfold sumNat
  congr 1
  funext i
  simp [i.isLt]

theorem mul_split (n m : Nat) (g : Nat → CQ) :
    sumNat (n * m) g = sumNat n (fun a => sumNat m (fun b => g (a * m + b))) := by
  induction n with
  | zero => simp [zero]
  | succ n ih =>
    rw [Nat.succ_mul, add, ih, succ]

theorem eq_sumFin_mul {n m : Nat} (hm : 0 < m) (f : Fin n → Fin m → CQ) :
    sumFin (0 : CQ) (fun k : Fin (n * m) =>
      f ⟨k.val / m, (Nat.div_lt_iff_lt_mul hm).2 k.isLt⟩ ⟨k.val % m, Nat.mod_lt k.val hm⟩) =
    sumFin (0 : CQ) (fun a : Fin n => sumFin (0 : CQ) (fun b : Fin m => f a b)) := by
  rw [eq_sumFin, mul_split]
  have hL :
      sumNat n (fun a => sumNat m (fun b =>
        if h : a * m + b < n * m then
          f ⟨(a * m + b) / m, (Nat.div_lt_iff_lt_mul hm).2 h⟩ ⟨(a * m + b) % m, Nat.mod_lt _ hm⟩
        else 0)) =
      sumNat n (fun a => sumNat m (fun b =>
        if ha : a < n then
          if hb : b < m then f ⟨a, ha⟩ ⟨b, hb⟩ else 0
        else 0)) := by
    apply congr
    intro a ha
    apply congr
    intro b hb
    have hlt : a * m + b < n * m := by
      have h1 : a * m + b < (a + 1) * m := by rw [Nat.succ_mul]; omega
      have h2 : (a + 1) * m ≤ n * m := Nat.mul_le_mul_right m ha
      exact Nat.lt_of_lt_of_le h1 h2
    have hdiv : (a * m + b) / m = a := by
      rw [Nat.mul_comm a m, Nat.mul_add_div hm, Nat.div_eq_of_lt hb, Nat.add_zero]
    have hmod : (a * m + b) % m = b := by
      rw [Nat.mul_comm a m, Nat.mul_add_mod, Nat.mod_eq_of_lt hb]
    simp [hlt, ha, hb, hdiv, hmod]
  rw [hL]
  rw [eq_sumFin]
  apply congr
  intro a ha
  simp [ha, eq_sumFin]

end SumNat

def finKronZ {d1 d2 : Nat} (hd2 : 0 < d2) (A : Mat d1 ZGauss) (B : Mat d2 ZGauss) : Mat (d1 * d2) ZGauss :=
  fun i j =>
    A ⟨i.val / d2, (Nat.div_lt_iff_lt_mul hd2).2 i.isLt⟩
      ⟨j.val / d2, (Nat.div_lt_iff_lt_mul hd2).2 j.isLt⟩ *
    B ⟨i.val % d2, Nat.mod_lt i.val hd2⟩
      ⟨j.val % d2, Nat.mod_lt j.val hd2⟩

def finKron {d1 d2 : Nat} (hd2 : 0 < d2) (A : Mat d1 CQ) (B : Mat d2 CQ) : Mat (d1 * d2) CQ :=
  fun i j =>
    A ⟨i.val / d2, (Nat.div_lt_iff_lt_mul hd2).2 i.isLt⟩
      ⟨j.val / d2, (Nat.div_lt_iff_lt_mul hd2).2 j.isLt⟩ *
    B ⟨i.val % d2, Nat.mod_lt i.val hd2⟩
      ⟨j.val % d2, Nat.mod_lt j.val hd2⟩

namespace Kron

theorem liftMat_finKron {d1 d2 : Nat} (hd2 : 0 < d2) (c1 c2 : Q) (A : Mat d1 ZGauss) (B : Mat d2 ZGauss) :
    liftMat (c1 * c2) (finKronZ hd2 A B) =
    finKron hd2 (liftMat c1 A) (liftMat c2 B) := by
  funext i j
  unfold liftMat finKronZ finKron
  rw [CQ.ofQ_mul, CQ.ofZGauss_mul]
  dsimp only
  ac_rfl

theorem add_left {d1 d2 : Nat} (hd2 : 0 < d2) (A1 A2 : Mat d1 CQ) (B : Mat d2 CQ) :
    finKron hd2 (MatCQ.add A1 A2) B = MatCQ.add (finKron hd2 A1 B) (finKron hd2 A2 B) := by
  funext i j; exact CQ.right_distrib _ _ _

theorem add_right {d1 d2 : Nat} (hd2 : 0 < d2) (A : Mat d1 CQ) (B1 B2 : Mat d2 CQ) :
    finKron hd2 A (MatCQ.add B1 B2) = MatCQ.add (finKron hd2 A B1) (finKron hd2 A B2) := by
  funext i j; exact CQ.left_distrib _ _ _

theorem sub_left {d1 d2 : Nat} (hd2 : 0 < d2) (A1 A2 : Mat d1 CQ) (B : Mat d2 CQ) :
    finKron hd2 (MatCQ.sub A1 A2) B = MatCQ.sub (finKron hd2 A1 B) (finKron hd2 A2 B) := by
  funext i j
  change (A1 _ _ + -(A2 _ _)) * B _ _ = A1 _ _ * B _ _ + -(A2 _ _ * B _ _)
  rw [CQ.right_distrib, CQ.neg_mul]

theorem sub_right {d1 d2 : Nat} (hd2 : 0 < d2) (A : Mat d1 CQ) (B1 B2 : Mat d2 CQ) :
    finKron hd2 A (MatCQ.sub B1 B2) = MatCQ.sub (finKron hd2 A B1) (finKron hd2 A B2) := by
  funext i j
  change A _ _ * (B1 _ _ + -(B2 _ _)) = A _ _ * B1 _ _ + -(A _ _ * B2 _ _)
  rw [CQ.left_distrib, CQ.mul_neg]

theorem scale_left {d1 d2 : Nat} (hd2 : 0 < d2) (c : CQ) (A : Mat d1 CQ) (B : Mat d2 CQ) :
    finKron hd2 (MatCQ.scale c A) B = MatCQ.scale c (finKron hd2 A B) := by
  funext i j; exact CQ.mul_assoc c _ _

theorem scale_right {d1 d2 : Nat} (hd2 : 0 < d2) (c : CQ) (A : Mat d1 CQ) (B : Mat d2 CQ) :
    finKron hd2 A (MatCQ.scale c B) = MatCQ.scale c (finKron hd2 A B) := by
  funext i j; unfold finKron MatCQ.scale; ac_rfl

theorem zero_left {d1 d2 : Nat} (hd2 : 0 < d2) (B : Mat d2 CQ) :
    finKron hd2 (MatCQ.zero : Mat d1 CQ) B = MatCQ.zero := by
  funext i j; exact CQ.zero_mul _

theorem zero_right {d1 d2 : Nat} (hd2 : 0 < d2) (A : Mat d1 CQ) :
    finKron hd2 A (MatCQ.zero : Mat d2 CQ) = MatCQ.zero := by
  funext i j; exact CQ.mul_zero _

theorem id_kron {d1 d2 : Nat} (hd2 : 0 < d2) :
    finKron hd2 (MatCQ.id : Mat d1 CQ) (MatCQ.id : Mat d2 CQ) = MatCQ.id := by
  funext i j
  unfold finKron MatCQ.id
  by_cases hij : i = j
  · subst hij; simp [CQ.one_mul]
  · have hpair : ¬ (i.val / d2 = j.val / d2 ∧ i.val % d2 = j.val % d2) := by
      intro ⟨hdiv, hmod⟩
      apply hij
      apply Fin.ext
      have hi := Nat.div_add_mod i.val d2
      have hj := Nat.div_add_mod j.val d2
      rw [← hi, ← hj, hdiv, hmod]
    by_cases h1 : (⟨i.val / d2, (Nat.div_lt_iff_lt_mul hd2).2 i.isLt⟩ : Fin d1) =
                  ⟨j.val / d2, (Nat.div_lt_iff_lt_mul hd2).2 j.isLt⟩
    · have h1v : i.val / d2 = j.val / d2 := congrArg Fin.val h1
      have h2 : (⟨i.val % d2, Nat.mod_lt i.val hd2⟩ : Fin d2) ≠
                ⟨j.val % d2, Nat.mod_lt j.val hd2⟩ := by
        intro heq
        exact hpair ⟨h1v, congrArg Fin.val heq⟩
      simp [hij, h1, h2, CQ.mul_zero]
    · simp [hij, h1, CQ.zero_mul]

theorem mul {d1 d2 : Nat} (hd2 : 0 < d2) (A1 A2 : Mat d1 CQ) (B1 B2 : Mat d2 CQ) :
    MatCQ.mul (finKron hd2 A1 B1) (finKron hd2 A2 B2) =
    finKron hd2 (MatCQ.mul A1 A2) (MatCQ.mul B1 B2) := by
  funext i j
  unfold MatCQ.mul finKron
  let i1 : Fin d1 := ⟨i.val / d2, (Nat.div_lt_iff_lt_mul hd2).2 i.isLt⟩
  let j1 : Fin d1 := ⟨j.val / d2, (Nat.div_lt_iff_lt_mul hd2).2 j.isLt⟩
  let i2 : Fin d2 := ⟨i.val % d2, Nat.mod_lt i.val hd2⟩
  let j2 : Fin d2 := ⟨j.val % d2, Nat.mod_lt j.val hd2⟩
  change sumFin (0 : CQ) (fun k : Fin (d1 * d2) =>
      (A1 ⟨k.val / d2, (Nat.div_lt_iff_lt_mul hd2).2 k.isLt⟩ j1 *
       B1 ⟨k.val % d2, Nat.mod_lt k.val hd2⟩ j2) |> fun _ =>
      (A1 i1 ⟨k.val / d2, (Nat.div_lt_iff_lt_mul hd2).2 k.isLt⟩ * B1 i2 ⟨k.val % d2, Nat.mod_lt k.val hd2⟩) *
      (A2 ⟨k.val / d2, (Nat.div_lt_iff_lt_mul hd2).2 k.isLt⟩ j1 * B2 ⟨k.val % d2, Nat.mod_lt k.val hd2⟩ j2)) =
    sumFin (0 : CQ) (fun a => A1 i1 a * A2 a j1) * sumFin (0 : CQ) (fun b => B1 i2 b * B2 b j2)
  rw [SumNat.eq_sumFin_mul hd2 (fun a b => (A1 i1 a * B1 i2 b) * (A2 a j1 * B2 b j2))]
  have hrew :
      (fun a => sumFin (0 : CQ) (fun b => (A1 i1 a * B1 i2 b) * (A2 a j1 * B2 b j2))) =
      (fun a => (A1 i1 a * A2 a j1) * sumFin (0 : CQ) (fun b => B1 i2 b * B2 b j2)) := by
    funext a
    have hb :
        (fun b => (A1 i1 a * B1 i2 b) * (A2 a j1 * B2 b j2)) =
        (fun b => (A1 i1 a * A2 a j1) * (B1 i2 b * B2 b j2)) := by
      funext b; ac_rfl
    rw [hb, SumFin.cq_mul_left]
  rw [hrew, SumFin.cq_mul_right]

theorem comm {d1 d2 : Nat} (hd2 : 0 < d2) (A1 A2 : Mat d1 CQ) (B1 B2 : Mat d2 CQ) :
    MatCQ.comm (finKron hd2 A1 B1) (finKron hd2 A2 B2) =
    MatCQ.sub (finKron hd2 (MatCQ.mul A1 A2) (MatCQ.mul B1 B2))
              (finKron hd2 (MatCQ.mul A2 A1) (MatCQ.mul B2 B1)) := by
  unfold MatCQ.comm
  rw [mul, mul]

theorem mul_id_id {d : Nat} (A : Mat d CQ) : MatCQ.mul A MatCQ.id = A := by
  funext i j
  unfold MatCQ.mul MatCQ.id
  have hf : (fun k => A i k * (if k = j then (1 : CQ) else 0)) =
            (fun k => if k = j then A i j else 0) := by
    funext k
    by_cases hk : k = j
    · subst hk; simp [CQ.mul_one]
    · simp [hk, CQ.mul_zero]
  rw [hf]
  clear hf
  suffices h : ∀ (m : Nat) (g : Fin m → CQ) (target : Fin m),
      sumFin (0 : CQ) (fun k => if k = target then g target else 0) = g target from h d (fun k => A i k) j
  intro m g target
  induction m with
  | zero => exact Fin.elim0 target
  | succ m ih =>
    simp only [sumFin]
    cases target using Fin.cases with
    | zero =>
      have hz : (fun k : Fin m => if k.succ = (0 : Fin (m + 1)) then g 0 else (0 : CQ)) = (fun _ => 0) := by
        funext k; simp [Fin.succ_ne_zero]
      rw [if_pos rfl, hz, SumFin.cq_eq_zero _ (fun _ => rfl), CQ.add_zero]
    | succ t =>
      have hne : (0 : Fin (m + 1)) ≠ t.succ := (Fin.succ_ne_zero t).symm
      rw [if_neg hne, CQ.zero_add]
      have hsucc : (fun k : Fin m => if k.succ = t.succ then g t.succ else (0 : CQ)) =
                   (fun k : Fin m => if k = t then g t.succ else (0 : CQ)) := by
        funext k
        by_cases hk : k = t
        · subst hk; simp
        · simp [hk, Fin.succ_inj]
      rw [hsucc]
      exact ih (fun k => g k.succ) t

theorem id_mul {d : Nat} (A : Mat d CQ) : MatCQ.mul MatCQ.id A = A := by
  funext i j
  unfold MatCQ.mul MatCQ.id
  have hf : (fun k => (if i = k then (1 : CQ) else 0) * A k j) =
            (fun k => if k = i then A i j else 0) := by
    funext k
    by_cases hk : k = i
    · subst hk; simp [CQ.one_mul]
    · have hki : i ≠ k := fun h => hk h.symm
      simp [hk, hki, CQ.zero_mul]
  rw [hf]
  clear hf
  suffices h : ∀ (m : Nat) (g : Fin m → CQ) (target : Fin m),
      sumFin (0 : CQ) (fun k => if k = target then g target else 0) = g target from h d (fun k => A k j) i
  intro m g target
  induction m with
  | zero => exact Fin.elim0 target
  | succ m ih =>
    simp only [sumFin]
    cases target using Fin.cases with
    | zero =>
      have hz : (fun k : Fin m => if k.succ = (0 : Fin (m + 1)) then g 0 else (0 : CQ)) = (fun _ => 0) := by
        funext k; simp [Fin.succ_ne_zero]
      rw [if_pos rfl, hz, SumFin.cq_eq_zero _ (fun _ => rfl), CQ.add_zero]
    | succ t =>
      have hne : (0 : Fin (m + 1)) ≠ t.succ := (Fin.succ_ne_zero t).symm
      rw [if_neg hne, CQ.zero_add]
      have hsucc : (fun k : Fin m => if k.succ = t.succ then g t.succ else (0 : CQ)) =
                   (fun k : Fin m => if k = t then g t.succ else (0 : CQ)) := by
        funext k
        by_cases hk : k = t
        · subst hk; simp
        · simp [hk, Fin.succ_inj]
      rw [hsucc]
      exact ih (fun k => g k.succ) t

theorem comm_id_right {d1 d2 : Nat} (hd2 : 0 < d2) (A1 A2 : Mat d1 CQ) (B : Mat d2 CQ) :
    MatCQ.comm (finKron hd2 A1 B) (finKron hd2 A2 MatCQ.id) =
    finKron hd2 (MatCQ.comm A1 A2) B := by
  rw [comm, mul_id_id, id_mul, ← sub_left]
  rfl

theorem comm_id_left {d1 d2 : Nat} (hd2 : 0 < d2) (A1 A2 : Mat d1 CQ) (B : Mat d2 CQ) :
    MatCQ.comm (finKron hd2 A1 MatCQ.id) (finKron hd2 A2 B) =
    finKron hd2 (MatCQ.comm A1 A2) B := by
  rw [comm, id_mul, mul_id_id, ← sub_left]
  rfl

theorem conjT {d1 d2 : Nat} (hd2 : 0 < d2) (A : Mat d1 CQ) (B : Mat d2 CQ) :
    MatCQ.conjT (finKron hd2 A B) = finKron hd2 (MatCQ.conjT A) (MatCQ.conjT B) := by
  funext i j
  unfold MatCQ.conjT finKron
  exact CQ.conj_mul _ _

theorem trace {d1 d2 : Nat} (hd2 : 0 < d2) (A : Mat d1 CQ) (B : Mat d2 CQ) :
    MatCQ.trace (finKron hd2 A B) = MatCQ.trace A * MatCQ.trace B := by
  unfold MatCQ.trace finKron
  rw [SumNat.eq_sumFin_mul hd2 (fun a b => A a a * B b b)]
  have h1 : (fun a : Fin d1 => sumFin (0 : CQ) (fun b : Fin d2 => A a a * B b b)) =
            (fun a : Fin d1 => A a a * sumFin (0 : CQ) (fun b : Fin d2 => B b b)) := by
    funext a; exact SumFin.cq_mul_left (A a a) _
  rw [h1, SumFin.cq_mul_right]

theorem frobInner {d1 d2 : Nat} (hd2 : 0 < d2) (A1 A2 : Mat d1 CQ) (B1 B2 : Mat d2 CQ) :
    MatCQ.frobInner (finKron hd2 A1 B1) (finKron hd2 A2 B2) =
    MatCQ.frobInner A1 A2 * MatCQ.frobInner B1 B2 := by
  unfold MatCQ.frobInner
  rw [conjT, mul, trace]

theorem mul_assoc {d : Nat} (A B C : Mat d CQ) :
    MatCQ.mul (MatCQ.mul A B) C = MatCQ.mul A (MatCQ.mul B C) := by
  funext i j
  unfold MatCQ.mul
  have hl : (fun k => sumFin (0 : CQ) (fun l => A i l * B l k) * C k j) =
            (fun k => sumFin (0 : CQ) (fun l => (A i l * B l k) * C k j)) := by
    funext k; exact (SumFin.cq_mul_right (C k j) _).symm
  have hr : (fun l => A i l * sumFin (0 : CQ) (fun k => B l k * C k j)) =
            (fun l => sumFin (0 : CQ) (fun k => A i l * (B l k * C k j))) := by
    funext l; exact (SumFin.cq_mul_left (A i l) _).symm
  rw [hl, hr, SumFin.cq_swap]
  congr 1; funext k; congr 1; funext l; exact CQ.mul_assoc _ _ _

theorem mul_sub {d : Nat} (A B C : Mat d CQ) :
    MatCQ.mul A (MatCQ.sub B C) = MatCQ.sub (MatCQ.mul A B) (MatCQ.mul A C) := by
  funext i j; unfold MatCQ.mul
  have hf : (fun k => A i k * MatCQ.sub B C k j) = (fun k => A i k * B k j - A i k * C k j) := by
    funext k; change A i k * (B k j + -C k j) = A i k * B k j + -(A i k * C k j); rw [CQ.left_distrib, CQ.mul_neg]
  rw [congrArg (sumFin (0 : CQ)) hf, SumFin.cq_sub]; rfl

theorem sub_mul {d : Nat} (A B C : Mat d CQ) :
    MatCQ.mul (MatCQ.sub A B) C = MatCQ.sub (MatCQ.mul A C) (MatCQ.mul B C) := by
  funext i j; unfold MatCQ.mul
  have hf : (fun k => MatCQ.sub A B i k * C k j) = (fun k => A i k * C k j - B i k * C k j) := by
    funext k; change (A i k + -B i k) * C k j = A i k * C k j + -(B i k * C k j); rw [CQ.right_distrib, CQ.neg_mul]
  rw [congrArg (sumFin (0 : CQ)) hf, SumFin.cq_sub]; rfl

theorem frobInner_sub_left {d : Nat} (A B C : Mat d CQ) :
    MatCQ.frobInner (MatCQ.sub A B) C = MatCQ.frobInner A C - MatCQ.frobInner B C := by
  rw [MatCQ.frobInner_eq_frobDot, MatCQ.frobInner_eq_frobDot, MatCQ.frobInner_eq_frobDot]
  unfold MatCQ.frobDot
  have hf : (fun i => sumFin (0 : CQ) (fun j => (MatCQ.sub A B i j).conj * C i j)) =
            (fun i => sumFin (0 : CQ) (fun j => (A i j).conj * C i j) -
                      sumFin (0 : CQ) (fun j => (B i j).conj * C i j)) := by
    funext i
    have hf' : (fun j => (MatCQ.sub A B i j).conj * C i j) =
               (fun j => (A i j).conj * C i j - (B i j).conj * C i j) := by
      funext j
      have hconj : (A i j + -B i j).conj = (A i j).conj + -(B i j).conj := by
        apply CQ.ext <;> simp [Q.neg_add, Q.neg_neg]
      change (A i j + -B i j).conj * C i j = (A i j).conj * C i j + -((B i j).conj * C i j)
      rw [hconj, CQ.right_distrib, CQ.neg_mul]
    rw [hf', SumFin.cq_sub]
  rw [hf, SumFin.cq_sub]

theorem frobInner_sub_right {d : Nat} (A B C : Mat d CQ) :
    MatCQ.frobInner A (MatCQ.sub B C) = MatCQ.frobInner A B - MatCQ.frobInner A C := by
  rw [MatCQ.frobInner_eq_frobDot, MatCQ.frobInner_eq_frobDot, MatCQ.frobInner_eq_frobDot]
  unfold MatCQ.frobDot
  have hf : (fun i => sumFin (0 : CQ) (fun j => (A i j).conj * MatCQ.sub B C i j)) =
            (fun i => sumFin (0 : CQ) (fun j => (A i j).conj * B i j) -
                      sumFin (0 : CQ) (fun j => (A i j).conj * C i j)) := by
    funext i
    have hf' : (fun j => (A i j).conj * MatCQ.sub B C i j) =
               (fun j => (A i j).conj * B i j - (A i j).conj * C i j) := by
      funext j
      change (A i j).conj * (B i j + -C i j) = (A i j).conj * B i j + -((A i j).conj * C i j)
      rw [CQ.left_distrib, CQ.mul_neg]
    rw [hf', SumFin.cq_sub]
  rw [hf, SumFin.cq_sub]

end Kron

private theorem lget_append_left {α : Type} (d : α) (xs ys : List α) (k : Nat) (hk : k < xs.length) :
    lget d (xs ++ ys) k = lget d xs k := by
  induction xs generalizing k with
  | nil => simp at hk
  | cons x xs ih =>
    cases k with
    | zero => rfl
    | succ k' =>
      simp only [List.length_cons] at hk
      exact ih k' (Nat.lt_of_succ_lt_succ hk)

private theorem lget_append_right {α : Type} (d : α) (xs ys : List α) (k : Nat) (hk : xs.length ≤ k) :
    lget d (xs ++ ys) k = lget d ys (k - xs.length) := by
  induction xs generalizing k with
  | nil => simp
  | cons x xs ih =>
    cases k with
    | zero => simp at hk
    | succ k' =>
      simp only [List.length_cons] at hk ⊢
      have hsub : k' + 1 - (xs.length + 1) = k' - xs.length := by omega
      rw [hsub]
      exact ih k' (Nat.le_of_succ_le_succ hk)

private theorem lget_flatMap_const {α β : Type} (a0 : α) (b0 : β) (f : α → List β) (xs : List α) (m k : Nat)
    (hm : 0 < m) (hf : ∀ x, x ∈ xs → (f x).length = m) (hk : k < xs.length * m) :
    lget b0 (xs.flatMap f) k = lget b0 (f (lget a0 xs (k / m))) (k % m) := by
  induction xs generalizing k with
  | nil => simp at hk
  | cons x xs ih =>
    have hxlen : (f x).length = m := hf x (List.Mem.head _)
    rw [List.flatMap_cons]
    by_cases hklt : k < m
    · rw [lget_append_left b0 (f x) (xs.flatMap f) k (by rw [hxlen]; exact hklt)]
      rw [Nat.div_eq_of_lt hklt, Nat.mod_eq_of_lt hklt]
      rfl
    · have hkge : m ≤ k := Nat.le_of_not_lt hklt
      rw [lget_append_right b0 (f x) (xs.flatMap f) k (by rw [hxlen]; exact hkge), hxlen]
      have hksub : k - m < xs.length * m := by
        simp only [List.length_cons, Nat.succ_mul] at hk
        omega
      rw [ih (k - m) (fun y hy => hf y (List.Mem.tail _ hy)) hksub]
      have h1 : k = (k - m) + m := by omega
      have hdiv0 : ((k - m) + m) / m = (k - m) / m + 1 := Nat.add_div_right (k - m) hm
      have hdiv : k / m = (k - m) / m + 1 := by rw [← h1] at hdiv0; exact hdiv0
      have hmod0 : ((k - m) + m) % m = (k - m) % m := Nat.add_mod_right (k - m) m
      have hmod : k % m = (k - m) % m := by rw [← h1] at hmod0; exact hmod0
      rw [hdiv, hmod]
      rfl

private theorem flatMap_map_len (rowA : List ZGauss) (rowB : List ZGauss) :
    (rowA.flatMap (fun a => rowB.map (fun b => a * b))).length = rowA.length * rowB.length := by
  induction rowA with
  | nil => simp
  | cons a rs ih =>
    simp [List.flatMap_cons, List.length_append, List.length_map, ih, Nat.succ_mul, Nat.add_comm]

theorem toFinZ_kronZ (d1 d2 : Nat) (hd2 : 0 < d2) (A B : MatZList)
    (hA : isSqZ d1 A = true) (hB : isSqZ d2 B = true) :
    toFinZ (d1 * d2) (kronZ A B) = finKronZ hd2 (toFinZ d1 A) (toFinZ d2 B) := by
  obtain ⟨hAl, hAr⟩ := all_len_eq hA
  obtain ⟨hBl, hBr⟩ := all_len_eq hB
  funext i j
  unfold toFinZ finKronZ kronZ
  have hrowLen : ∀ rA, rA ∈ A → (B.map (fun rowB => rA.flatMap (fun a => rowB.map (fun b => a * b)))).length = d2 := by
    intro rA _; rw [List.length_map, hBl]
  have hi : i.val < A.length * d2 := by rw [hAl]; exact i.isLt
  rw [lget_flatMap_const [] [] _ A d2 i.val hd2 hrowLen hi]
  have hrowB_lt : i.val % d2 < B.length := by rw [hBl]; exact Nat.mod_lt i.val hd2
  rw [lget_map [] [] _ B (i.val % d2) hrowB_lt]
  have hri : i.val / d2 < A.length := by rw [hAl]; exact (Nat.div_lt_iff_lt_mul hd2).2 i.isLt
  have hrowAlen : (lget [] A (i.val / d2)).length = d1 := hAr _ (lget_mem [] A (i.val / d2) hri)
  have hrowBlen : (lget [] B (i.val % d2)).length = d2 := hBr _ (lget_mem [] B (i.val % d2) hrowB_lt)
  have hinner : ∀ a, a ∈ lget [] A (i.val / d2) → ((lget [] B (i.val % d2)).map (fun b => a * b)).length = d2 := by
    intro a _; rw [List.length_map, hrowBlen]
  have hj : j.val < (lget [] A (i.val / d2)).length * d2 := by rw [hrowAlen]; exact j.isLt
  rw [lget_flatMap_const 0 0 _ (lget [] A (i.val / d2)) d2 j.val hd2 hinner hj]
  exact lget_map 0 0 _ (lget [] B (i.val % d2)) (j.val % d2) (by rw [hrowBlen]; exact Nat.mod_lt j.val hd2)

/-! ## 3. Exact 4x4, 8x8 (I=1/2), and 12x12 (I=1, 14N) Spin-Projector & Commutator Algebra -/

namespace SpinMatrices

private def z0 : ZGauss := 0
private def z1 : ZGauss := 1
private def zn1 : ZGauss := ⟨-1, 0⟩
private def z2 : ZGauss := ⟨2, 0⟩
private def zn2 : ZGauss := ⟨-2, 0⟩
private def z3 : ZGauss := ⟨3, 0⟩
private def z4 : ZGauss := ⟨4, 0⟩
private def zi : ZGauss := ⟨0, 1⟩
private def zni : ZGauss := ⟨0, -1⟩

def id2 : MatZList := [[z1, z0], [z0, z1]]
def sx2 : MatZList := [[z0, z1], [z1, z0]]
def sy2 : MatZList := [[z0, zni], [zi, z0]]
def sz2 : MatZList := [[z1, z0], [z0, zn1]]

theorem id2_sq : isSqZ 2 id2 = true := by decide
theorem sx2_sq : isSqZ 2 sx2 = true := by decide
theorem sy2_sq : isSqZ 2 sy2 = true := by decide
theorem sz2_sq : isSqZ 2 sz2 = true := by decide

theorem id2_frob : frobDotZ id2 id2 = z2 := by decide
theorem frob_2x2_table :
    ([sx2, sy2, sz2].map (fun a => [sx2, sy2, sz2].map (fun b => frobDotZ a b))) =
    [[z2, z0, z0], [z0, z2, z0], [z0, z0, z2]] := by decide
theorem symm_2x2_tr_zero :
    let nuc2 := [sx2, sy2, sz2]
    nuc2.all (fun a => nuc2.all (fun b => nuc2.all (fun c =>
      frobDotZ a (matAddZ (matMulZ 2 b c) (matMulZ 2 c b)) == z0))) = true := by decide

def id3 : MatZList := [[z1, z0, z0], [z0, z1, z0], [z0, z0, z1]]
def ix3 : MatZList := [[z0, z0, z0], [z0, z0, zni], [z0, zi, z0]]
def iy3 : MatZList := [[z0, z0, zi], [z0, z0, z0], [zni, z0, z0]]
def iz3 : MatZList := [[z0, zni, z0], [zi, z0, z0], [z0, z0, z0]]

theorem id3_sq : isSqZ 3 id3 = true := by decide
theorem ix3_sq : isSqZ 3 ix3 = true := by decide
theorem iy3_sq : isSqZ 3 iy3 = true := by decide
theorem iz3_sq : isSqZ 3 iz3 = true := by decide

theorem i1_comm_xy : matCommZ 3 ix3 iy3 = matScaleZ zi iz3 := by decide
theorem i1_comm_yz : matCommZ 3 iy3 iz3 = matScaleZ zi ix3 := by decide
theorem i1_comm_zx : matCommZ 3 iz3 ix3 = matScaleZ zi iy3 := by decide
theorem i1_casimir :
    matAddZ (matAddZ (matMulZ 3 ix3 ix3) (matMulZ 3 iy3 iy3)) (matMulZ 3 iz3 iz3) =
    matScaleZ z2 id3 := by decide
theorem id3_frob : frobDotZ id3 id3 = z3 := by decide
theorem frob_3x3_table :
    ([ix3, iy3, iz3].map (fun a => [ix3, iy3, iz3].map (fun b => frobDotZ a b))) =
    [[z2, z0, z0], [z0, z2, z0], [z0, z0, z2]] := by decide
theorem symm_3x3_tr_zero :
    let nuc3 := [ix3, iy3, iz3]
    nuc3.all (fun a => nuc3.all (fun b => nuc3.all (fun c =>
      frobDotZ a (matAddZ (matMulZ 3 b c) (matMulZ 3 c b)) == z0))) = true := by decide

/-! ### 4x4 Electronic Spin Operators (Fast Kernel Decisions) -/

def id4 : MatZList := kronZ id2 id2
def s1x4 : MatZList := kronZ sx2 id2
def s1y4 : MatZList := kronZ sy2 id2
def s1z4 : MatZList := kronZ sz2 id2
def s2x4 : MatZList := kronZ id2 sx2
def s2y4 : MatZList := kronZ id2 sy2
def s2z4 : MatZList := kronZ id2 sz2
def s1d2_4 : MatZList :=
  matAddZ (matAddZ (matMulZ 4 s1x4 s2x4) (matMulZ 4 s1y4 s2y4)) (matMulZ 4 s1z4 s2z4)
def fourPS4 : MatZList := [[z0, z0, z0, z0], [z0, z2, zn2, z0], [z0, zn2, z2, z0], [z0, z0, z0, z0]]
def fourPT4 : MatZList := [[z4, z0, z0, z0], [z0, z2, z2, z0], [z0, z2, z2, z0], [z0, z0, z0, z4]]
def z4x : MatZList := matAddZ s1x4 s2x4
def z4y : MatZList := matAddZ s1y4 s2y4
def z4z : MatZList := matAddZ s1z4 s2z4
def ex4 : MatZList := matAddZ s1d2_4 id4
def v4x : MatZList := [[z0, zn2, z2, z0], [z2, z0, z0, zn2], [zn2, z0, z0, z2], [z0, z2, zn2, z0]]
def v4y : MatZList := [[z0, ⟨0,2⟩, ⟨0,-2⟩, z0], [⟨0,2⟩, z0, z0, ⟨0,2⟩], [⟨0,-2⟩, z0, z0, ⟨0,-2⟩], [z0, ⟨0,2⟩, ⟨0,-2⟩, z0]]
def v4z : MatZList := [[z0, z0, z0, z0], [z0, z0, ⟨-4,0⟩, z0], [z0, ⟨4,0⟩, z0, z0], [z0, z0, z0, z0]]

theorem id4_sq : isSqZ 4 id4 = true := by decide
theorem s1x4_sq : isSqZ 4 s1x4 = true := by decide
theorem s1y4_sq : isSqZ 4 s1y4 = true := by decide
theorem s1z4_sq : isSqZ 4 s1z4 = true := by decide
theorem s2x4_sq : isSqZ 4 s2x4 = true := by decide
theorem s2y4_sq : isSqZ 4 s2y4 = true := by decide
theorem s2z4_sq : isSqZ 4 s2z4 = true := by decide
theorem fourPS4_sq : isSqZ 4 fourPS4 = true := by decide
theorem fourPT4_sq : isSqZ 4 fourPT4 = true := by decide
theorem z4x_sq : isSqZ 4 z4x = true := by decide
theorem z4y_sq : isSqZ 4 z4y = true := by decide
theorem z4z_sq : isSqZ 4 z4z = true := by decide
theorem ex4_sq : isSqZ 4 ex4 = true := by decide
theorem v4x_sq : isSqZ 4 v4x = true := by decide
theorem v4y_sq : isSqZ 4 v4y = true := by decide
theorem v4z_sq : isSqZ 4 v4z = true := by decide

theorem fourPS4_eq : fourPS4 = matSubZ id4 s1d2_4 := by decide
theorem fourPT4_eq : fourPT4 = matAddZ (matScaleZ z3 id4) s1d2_4 := by decide
theorem ps4_idem_Z : matMulZ 4 fourPS4 fourPS4 = matScaleZ z4 fourPS4 := by decide
theorem pt4_idem_Z : matMulZ 4 fourPT4 fourPT4 = matScaleZ z4 fourPT4 := by decide
theorem ps_pt4_ortho_Z : matMulZ 4 fourPS4 fourPT4 = matScaleZ z0 id4 := by decide
theorem ps_add_pt4_Z : matAddZ fourPS4 fourPT4 = matScaleZ z4 id4 := by decide
theorem ps4_herm_Z : matConjTZ 4 fourPS4 = fourPS4 := by decide
theorem pt4_herm_Z : matConjTZ 4 fourPT4 = fourPT4 := by decide
theorem ps4_trace_Z : matTraceZ 4 fourPS4 = z4 := by decide
theorem pt4_trace_Z : matTraceZ 4 fourPT4 = ⟨12, 0⟩ := by decide

theorem comm_z4x_Z : matCommZ 4 z4x fourPS4 = matScaleZ z0 id4 := by decide
theorem comm_z4y_Z : matCommZ 4 z4y fourPS4 = matScaleZ z0 id4 := by decide
theorem comm_z4z_Z : matCommZ 4 z4z fourPS4 = matScaleZ z0 id4 := by decide
theorem comm_ex4_Z : matCommZ 4 ex4 fourPS4 = matScaleZ z0 id4 := by decide

theorem v4x_eq : matCommZ 4 s1x4 fourPS4 = v4x := by decide
theorem v4y_eq : matCommZ 4 s1y4 fourPS4 = v4y := by decide
theorem v4z_eq : matCommZ 4 s1z4 fourPS4 = v4z := by decide

theorem gram4_v_exact :
    ([v4x, v4y, v4z].map (fun a => [v4x, v4y, v4z].map (fun b => frobDotZ a b))) =
    [[⟨32,0⟩, 0, 0], [0, ⟨32,0⟩, 0], [0, 0, ⟨32,0⟩]] := by decide

-- SU(2) covariance of [S_1a, P_S] under total electron spin Z_g = sigma_{1g} + sigma_{2g}:
theorem zv4_xx : matCommZ 4 z4x v4x = matScaleZ z0 id4 := by decide
theorem zv4_xy : matCommZ 4 z4x v4y = matScaleZ ⟨0,2⟩ v4z := by decide
theorem zv4_xz : matCommZ 4 z4x v4z = matScaleZ ⟨0,-2⟩ v4y := by decide
theorem zv4_yx : matCommZ 4 z4y v4x = matScaleZ ⟨0,-2⟩ v4z := by decide
theorem zv4_yy : matCommZ 4 z4y v4y = matScaleZ z0 id4 := by decide
theorem zv4_yz : matCommZ 4 z4y v4z = matScaleZ ⟨0,2⟩ v4x := by decide
theorem zv4_zx : matCommZ 4 z4z v4x = matScaleZ ⟨0,2⟩ v4y := by decide
theorem zv4_zy : matCommZ 4 z4z v4y = matScaleZ ⟨0,-2⟩ v4x := by decide
theorem zv4_zz : matCommZ 4 z4z v4z = matScaleZ z0 id4 := by decide

-- Exact 4x4 Pythagorean decoupling identities (checked across all 9 / 27 pairs):
theorem v4_orthog_ex4 :
    let vs := [v4x, v4y, v4z]
    vs.all (fun vd => vs.all (fun va =>
      frobDotZ vd (matCommZ 4 ex4 va) == z0)) = true := by decide

theorem v4_anticomm_s1_orthog :
    let vs := [v4x, v4y, v4z]
    let ss := [s1x4, s1y4, s1z4]
    vs.all (fun vd => ss.all (fun sg => vs.all (fun va =>
      (frobDotZ vd (matMulZ 4 sg va) + frobDotZ vd (matMulZ 4 va sg)) == z0))) = true := by decide

/-! ### 8x8 (I=1/2) & 12x12 (I=1, 14N) Operator Definitions -/

def id8 : MatZList := kronZ id4 id2
def fourPS8 : MatZList := kronZ fourPS4 id2
def fourPT8 : MatZList := kronZ fourPT4 id2
def sig1x8 : MatZList := kronZ s1x4 id2
def sig1y8 : MatZList := kronZ s1y4 id2
def sig1z8 : MatZList := kronZ s1z4 id2
def sig2x8 : MatZList := kronZ s2x4 id2
def sig2y8 : MatZList := kronZ s2y4 id2
def sig2z8 : MatZList := kronZ s2z4 id2
def sigIx8 : MatZList := kronZ id4 sx2
def sigIy8 : MatZList := kronZ id4 sy2
def sigIz8 : MatZList := kronZ id4 sz2
def sxTot8 : MatZList := kronZ z4x id2
def syTot8 : MatZList := kronZ z4y id2
def szTot8 : MatZList := kronZ z4z id2
def bex8 : MatZList := kronZ ex4 id2
def hfx8 : MatZList := kronZ s1x4 sx2
def hfy8 : MatZList := kronZ s1y4 sy2
def hfz8 : MatZList := kronZ s1z4 sz2

def id12 : MatZList := kronZ id4 id3
def fourPS12 : MatZList := kronZ fourPS4 id3
def fourPT12 : MatZList := kronZ fourPT4 id3
def sig1x12 : MatZList := kronZ s1x4 id3
def sig1y12 : MatZList := kronZ s1y4 id3
def sig1z12 : MatZList := kronZ s1z4 id3
def sig2x12 : MatZList := kronZ s2x4 id3
def sig2y12 : MatZList := kronZ s2y4 id3
def sig2z12 : MatZList := kronZ s2z4 id3
def i1x12 : MatZList := kronZ id4 ix3
def i1y12 : MatZList := kronZ id4 iy3
def i1z12 : MatZList := kronZ id4 iz3
def sxTot12 : MatZList := kronZ z4x id3
def syTot12 : MatZList := kronZ z4y id3
def szTot12 : MatZList := kronZ z4z id3
def bex12 : MatZList := kronZ ex4 id3
def hfx12 : MatZList := kronZ s1x4 ix3
def hfy12 : MatZList := kronZ s1y4 iy3
def hfz12 : MatZList := kronZ s1z4 iz3

theorem id2_entry : ∀ i j : Fin 2, toFinZ 2 id2 i j = if i = j then 1 else 0 := by decide
theorem id3_entry : ∀ i j : Fin 3, toFinZ 3 id3 i j = if i = j then 1 else 0 := by decide
theorem id4_entry : ∀ i j : Fin 4, toFinZ 4 id4 i j = if i = j then 1 else 0 := by decide

theorem symm_2x2_orthog (i j k : Fin 3) :
    let m := match i.val with | 0 => sx2 | 1 => sy2 | _ => sz2
    let p := match j.val with | 0 => sx2 | 1 => sy2 | _ => sz2
    let q := match k.val with | 0 => sx2 | 1 => sy2 | _ => sz2
    frobDotZ m (matAddZ (matMulZ 2 p q) (matMulZ 2 q p)) = z0 := by
  decide +revert

theorem symm_3x3_orthog (i j k : Fin 3) :
    let m := match i.val with | 0 => ix3 | 1 => iy3 | _ => iz3
    let p := match j.val with | 0 => ix3 | 1 => iy3 | _ => iz3
    let q := match k.val with | 0 => ix3 | 1 => iy3 | _ => iz3
    frobDotZ m (matAddZ (matMulZ 3 p q) (matMulZ 3 q p)) = z0 := by
  decide +revert

theorem v4_ex4_orthog_all (d a : Fin 3) :
    frobDotZ (match d.val with | 0 => v4x | 1 => v4y | _ => v4z)
             (matCommZ 4 ex4 (match a.val with | 0 => v4x | 1 => v4y | _ => v4z)) = z0 := by
  decide +revert

theorem v4_s1_anticomm_all (d g a : Fin 3) :
    frobDotZ (match d.val with | 0 => v4x | 1 => v4y | _ => v4z)
             (matMulZ 4 (match g.val with | 0 => s1x4 | 1 => s1y4 | _ => s1z4)
                        (match a.val with | 0 => v4x | 1 => v4y | _ => v4z)) +
    frobDotZ (match d.val with | 0 => v4x | 1 => v4y | _ => v4z)
             (matMulZ 4 (match a.val with | 0 => v4x | 1 => v4y | _ => v4z)
                        (match g.val with | 0 => s1x4 | 1 => s1y4 | _ => s1z4)) = z0 := by
  decide +revert

end SpinMatrices

/-! ## 4. Formal Radical-Pair Theory: Spin Projectors, M_0/M_2/M_4 Theorems & Asymptotics -/

section RadicalPair4A

open SpinMatrices

private theorem qrel_eq (a b : QRaw) (h : decide (a.num * b.den = b.num * a.den) = true) :
    Quotient.mk qSetoid a = Quotient.mk qSetoid b :=
  Quotient.sound (of_decide_eq_true h : a.num * b.den = b.num * a.den)

def q12 : Q := Q.frac 1 2
def q13 : Q := Q.frac 1 3
def q14 : Q := Q.frac 1 4
def q16 : Q := Q.frac 1 6
def q18 : Q := Q.frac 1 8
def q23 : Q := Q.frac 2 3

private theorem q14_sq_mul4 : q14 * q14 * Q.ofInt 4 = q14 := qrel_eq _ _ (by decide)
private theorem q14_sq_mul0 : q14 * q14 * Q.ofInt 0 = 0 := qrel_eq _ _ (by decide)
private theorem q14_mul4_eq1 : q14 * Q.ofInt 4 = 1 := qrel_eq _ _ (by decide)
private theorem q14_mul12_eq3 : q14 * Q.ofInt 12 = Q.ofInt 3 := qrel_eq _ _ (by decide)
private theorem q12_sq_eq14 : q12 * q12 = q14 := qrel_eq _ _ (by decide)
private theorem q14_mul_q12_eq_q18 : q14 * q12 = q18 := qrel_eq _ _ (by decide)
private theorem q12_mul_q14_eq_q18 : q12 * q14 = q18 := qrel_eq _ _ (by decide)
private theorem q18_sq_mul32_eq_q12 : q18 * q18 * Q.ofInt 32 = q12 := qrel_eq _ _ (by decide)
private theorem q12_sq_mul2_eq_q12 : q12 * q12 * Q.ofInt 2 = q12 := qrel_eq _ _ (by decide)
private theorem q12_div2_eq_q14 : q12 / Q.ofInt 2 = q14 := by
  change q12 * Q.inv (Q.ofInt 2) = q14
  have hinv : Q.inv (Q.ofInt 2) = q12 := qrel_eq _ _ (by decide)
  rw [hinv]; exact q12_sq_eq14
private theorem q2_div3_eq_q23 : Q.ofInt 2 / Q.ofInt 3 = q23 := by
  change Q.ofInt 2 * Q.inv (Q.ofInt 3) = q23
  have hinv : Q.inv (Q.ofInt 3) = q13 := qrel_eq _ _ (by decide)
  rw [hinv]; exact qrel_eq _ _ (by decide)
private theorem q12_mul_q14_mul_q12 : q12 * (q12 / Q.ofInt 2) = q18 := by
  rw [q12_div2_eq_q14]; exact q12_mul_q14_eq_q18
private theorem q12_mul_q23_eq_q13 : q12 * (Q.ofInt 2 / Q.ofInt 3) = q13 := by
  rw [q2_div3_eq_q23]; exact qrel_eq _ _ (by decide)
private theorem q12_mul3_eq_q32 : q12 * q14 = q18 := q12_mul_q14_eq_q18
private theorem qneg12_sq : (-q12) * q14 = -(q18) := by
  rw [Q.neg_mul, q12_mul_q14_eq_q18]

theorem liftMat_id2 : liftMat 1 (toFinZ 2 id2) = MatCQ.id := by
  funext i j; unfold liftMat MatCQ.id; rw [id2_entry i j]
  by_cases h : i = j
  · simp only [h, ↓reduceIte, CQ.ofZGauss]; change (1 : CQ) * 1 = 1; exact CQ.one_mul 1
  · simp only [h, ↓reduceIte, CQ.ofZGauss]; change (1 : CQ) * 0 = 0; exact CQ.mul_zero 1

theorem liftMat_id3 : liftMat 1 (toFinZ 3 id3) = MatCQ.id := by
  funext i j; unfold liftMat MatCQ.id; rw [id3_entry i j]
  by_cases h : i = j
  · simp only [h, ↓reduceIte, CQ.ofZGauss]; change (1 : CQ) * 1 = 1; exact CQ.one_mul 1
  · simp only [h, ↓reduceIte, CQ.ofZGauss]; change (1 : CQ) * 0 = 0; exact CQ.mul_zero 1

theorem liftMat_id4 : liftMat 1 (toFinZ 4 id4) = MatCQ.id := by
  funext i j; unfold liftMat MatCQ.id; rw [id4_entry i j]
  by_cases h : i = j
  · simp only [h, ↓reduceIte, CQ.ofZGauss]; change (1 : CQ) * 1 = 1; exact CQ.one_mul 1
  · simp only [h, ↓reduceIte, CQ.ofZGauss]; change (1 : CQ) * 0 = 0; exact CQ.mul_zero 1

/-! ### 4x4 Electronic Operators in `Mat 4 CQ` -/

def PS4 : Mat 4 CQ := liftMat q14 (toFinZ 4 fourPS4)
def PT4 : Mat 4 CQ := liftMat q14 (toFinZ 4 fourPT4)

def s1_4L : Fin 3 → MatZList | ⟨0, _⟩ => s1x4 | ⟨1, _⟩ => s1y4 | ⟨2, _⟩ => s1z4
def s2_4L : Fin 3 → MatZList | ⟨0, _⟩ => s2x4 | ⟨1, _⟩ => s2y4 | ⟨2, _⟩ => s2z4
def z4L   : Fin 3 → MatZList | ⟨0, _⟩ => z4x  | ⟨1, _⟩ => z4y  | ⟨2, _⟩ => z4z
def v4L   : Fin 3 → MatZList | ⟨0, _⟩ => v4x  | ⟨1, _⟩ => v4y  | ⟨2, _⟩ => v4z

private theorem s1_4L_sq (a : Fin 3) : isSqZ 4 (s1_4L a) = true := by
  rcases a with ⟨v, hv⟩; match v with | 0 => exact s1x4_sq | 1 => exact s1y4_sq | 2 => exact s1z4_sq | _+3 => omega
private theorem s2_4L_sq (a : Fin 3) : isSqZ 4 (s2_4L a) = true := by
  rcases a with ⟨v, hv⟩; match v with | 0 => exact s2x4_sq | 1 => exact s2y4_sq | 2 => exact s2z4_sq | _+3 => omega
private theorem z4L_sq (a : Fin 3) : isSqZ 4 (z4L a) = true := by
  rcases a with ⟨v, hv⟩; match v with | 0 => exact z4x_sq | 1 => exact z4y_sq | 2 => exact z4z_sq | _+3 => omega
private theorem v4L_sq (a : Fin 3) : isSqZ 4 (v4L a) = true := by
  rcases a with ⟨v, hv⟩; match v with | 0 => exact v4x_sq | 1 => exact v4y_sq | 2 => exact v4z_sq | _+3 => omega

def S1_4 (a : Fin 3) : Mat 4 CQ := liftMat q12 (toFinZ 4 (s1_4L a))
def S2_4 (a : Fin 3) : Mat 4 CQ := liftMat q12 (toFinZ 4 (s2_4L a))
def Z4   (a : Fin 3) : Mat 4 CQ := liftMat q12 (toFinZ 4 (z4L a))
def Hex4 : Mat 4 CQ := liftMat (-q12) (toFinZ 4 ex4)
def V4   (a : Fin 3) : Mat 4 CQ := liftMat q18 (toFinZ 4 (v4L a))

private theorem s1d2_4_sq : isSqZ 4 s1d2_4 = true := by decide
private theorem z0_mul_eq0 {d : Nat} (A : Mat d ZGauss) (c : Q) :
    liftMat c (finMatScaleZ (0 : ZGauss) A) = MatCQ.zero := by
  funext i j; simp only [liftMat, finMatScaleZ, MatCQ.zero]
  change CQ.ofQ c * CQ.ofZGauss (0 * A i j) = 0
  have hz : (0 : ZGauss) * A i j = 0 := by apply ZGauss.ext <;> simp
  rw [hz]; change CQ.ofQ c * 0 = 0; exact CQ.mul_zero _

theorem PS4_idem : MatCQ.mul PS4 PS4 = PS4 := by
  unfold PS4
  rw [Lift.liftMat_mul, ← toFinZ_mul fourPS4 fourPS4 fourPS4_sq fourPS4_sq, ps4_idem_Z,
      toFinZ_scale z4 fourPS4 fourPS4_sq, Lift.liftMat_scaleZ]
  have h4 : CQ.ofZGauss z4 = CQ.ofQ (Q.ofInt 4) := rfl
  rw [h4, Lift.liftMat_scale]
  change liftMat (Q.ofInt 4 * (q14 * q14)) (toFinZ 4 fourPS4) = liftMat q14 (toFinZ 4 fourPS4)
  rw [Q.mul_comm, q14_sq_mul4]

theorem PT4_idem : MatCQ.mul PT4 PT4 = PT4 := by
  unfold PT4
  rw [Lift.liftMat_mul, ← toFinZ_mul fourPT4 fourPT4 fourPT4_sq fourPT4_sq, pt4_idem_Z,
      toFinZ_scale z4 fourPT4 fourPT4_sq, Lift.liftMat_scaleZ]
  have h4 : CQ.ofZGauss z4 = CQ.ofQ (Q.ofInt 4) := rfl
  rw [h4, Lift.liftMat_scale]
  change liftMat (Q.ofInt 4 * (q14 * q14)) (toFinZ 4 fourPT4) = liftMat q14 (toFinZ 4 fourPT4)
  rw [Q.mul_comm, q14_sq_mul4]

theorem PS4_PT4_ortho : MatCQ.mul PS4 PT4 = MatCQ.zero := by
  unfold PS4 PT4
  rw [Lift.liftMat_mul, ← toFinZ_mul fourPS4 fourPT4 fourPS4_sq fourPT4_sq, ps_pt4_ortho_Z,
      show z0 = (0 : ZGauss) from rfl, toFinZ_scale 0 id4 id4_sq]
  exact z0_mul_eq0 _ _

theorem PS4_add_PT4 : MatCQ.add PS4 PT4 = MatCQ.id := by
  unfold PS4 PT4
  rw [Lift.liftMat_add, ← toFinZ_add fourPS4 fourPT4 fourPS4_sq fourPT4_sq, ps_add_pt4_Z,
      show z4 = ⟨4, 0⟩ from rfl, toFinZ_scale ⟨4, 0⟩ id4 id4_sq, Lift.liftMat_scaleZ]
  have h4 : CQ.ofZGauss ⟨4, 0⟩ = CQ.ofQ (Q.ofInt 4) := rfl
  rw [h4, Lift.liftMat_scale, Q.mul_comm, q14_mul4_eq1, liftMat_id4]

theorem PS4_herm : MatCQ.conjT PS4 = PS4 := by
  unfold PS4; rw [Lift.liftMat_conjT, ← toFinZ_conjT fourPS4, ps4_herm_Z]

theorem PT4_herm : MatCQ.conjT PT4 = PT4 := by
  unfold PT4; rw [Lift.liftMat_conjT, ← toFinZ_conjT fourPT4, pt4_herm_Z]

theorem PS4_trace : MatCQ.trace PS4 = 1 := by
  unfold PS4; rw [Lift.liftMat_trace, ← matTraceZ_eq, ps4_trace_Z]
  change CQ.ofQ q14 * CQ.ofQ (Q.ofInt 4) = 1
  rw [← CQ.ofQ_mul, q14_mul4_eq1]; rfl

theorem PT4_trace : MatCQ.trace PT4 = CQ.ofQ (Q.ofInt 3) := by
  unfold PT4; rw [Lift.liftMat_trace, ← matTraceZ_eq, pt4_trace_Z]
  change CQ.ofQ q14 * CQ.ofQ (Q.ofInt 12) = CQ.ofQ (Q.ofInt 3)
  rw [← CQ.ofQ_mul, q14_mul12_eq3]

theorem Z4_eq_add (a : Fin 3) : Z4 a = MatCQ.add (S1_4 a) (S2_4 a) := by
  unfold Z4 S1_4 S2_4
  rw [Lift.liftMat_add, ← toFinZ_add _ _ (s1_4L_sq a) (s2_4L_sq a)]
  rcases a with ⟨v, hv⟩
  match v with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | _+3 => omega

private theorem mul_z4L_sq1 (a : Fin 3) : isSqZ 4 (matMulZ 4 (z4L a) fourPS4) = true := by decide +revert
private theorem mul_z4L_sq2 (a : Fin 3) : isSqZ 4 (matMulZ 4 fourPS4 (z4L a)) = true := by decide +revert
private theorem mul_s1_sq1 (a : Fin 3) : isSqZ 4 (matMulZ 4 (s1_4L a) fourPS4) = true := by decide +revert
private theorem mul_s1_sq2 (a : Fin 3) : isSqZ 4 (matMulZ 4 fourPS4 (s1_4L a)) = true := by decide +revert

theorem comm_Z4_PS4 (a : Fin 3) : MatCQ.comm (Z4 a) PS4 = MatCQ.zero := by
  unfold Z4 PS4
  rw [Lift.liftMat_comm, ← toFinZ_comm (z4L a) fourPS4 (z4L_sq a) fourPS4_sq (mul_z4L_sq1 a) (mul_z4L_sq2 a)]
  have hcomm : matCommZ 4 (z4L a) fourPS4 = matScaleZ 0 id4 := by
    rcases a with ⟨v, hv⟩
    match v with
    | 0 => exact comm_z4x_Z
    | 1 => exact comm_z4y_Z
    | 2 => exact comm_z4z_Z
    | _+3 => omega
  rw [hcomm, toFinZ_scale 0 id4 id4_sq]
  exact z0_mul_eq0 _ _

theorem comm_Hex4_PS4 : MatCQ.comm Hex4 PS4 = MatCQ.zero := by
  unfold Hex4 PS4
  have h1 : isSqZ 4 (matMulZ 4 ex4 fourPS4) = true := by decide
  have h2 : isSqZ 4 (matMulZ 4 fourPS4 ex4) = true := by decide
  rw [Lift.liftMat_comm, ← toFinZ_comm ex4 fourPS4 ex4_sq fourPS4_sq h1 h2, comm_ex4_Z,
      show z0 = (0 : ZGauss) from rfl, toFinZ_scale 0 id4 id4_sq]
  exact z0_mul_eq0 _ _

theorem comm_S1_4_PS4 (a : Fin 3) : MatCQ.comm (S1_4 a) PS4 = V4 a := by
  unfold S1_4 PS4 V4
  rw [Lift.liftMat_comm, ← toFinZ_comm (s1_4L a) fourPS4 (s1_4L_sq a) fourPS4_sq (mul_s1_sq1 a) (mul_s1_sq2 a)]
  have hv : matCommZ 4 (s1_4L a) fourPS4 = v4L a := by
    rcases a with ⟨v, hv⟩
    match v with
    | 0 => exact v4x_eq
    | 1 => exact v4y_eq
    | 2 => exact v4z_eq
    | _+3 => omega
  rw [hv, q12_mul_q14_eq_q18]

theorem comm_S2_4_PS4 (a : Fin 3) : MatCQ.comm (S2_4 a) PS4 = MatCQ.neg (V4 a) := by
  have hZ := comm_Z4_PS4 a
  rw [Z4_eq_add a, MatCQ.comm_add_left, comm_S1_4_PS4 a] at hZ
  funext i j
  have hij := congrFun (congrFun hZ i) j
  unfold MatCQ.add MatCQ.zero at hij
  unfold MatCQ.neg
  have hadd := congrArg (fun x => -V4 a i j + x) hij
  dsimp only at hadd
  rw [CQ.add_zero, ← CQ.add_assoc, CQ.add_left_neg, CQ.zero_add] at hadd
  exact hadd

private theorem frob_v4L_exact (a b : Fin 3) :
    frobDotZ (v4L a) (v4L b) = if a = b then ⟨32, 0⟩ else 0 := by decide +revert

theorem frobInner_V4 (a b : Fin 3) :
    MatCQ.frobInner (V4 a) (V4 b) = if a = b then CQ.ofQ q12 else 0 := by
  unfold V4
  rw [Lift.liftMat_frobInner, ← frobDotZ_eq (v4L a) (v4L b) (v4L_sq a) (v4L_sq b), frob_v4L_exact]
  by_cases hab : a = b
  · simp only [hab, ↓reduceIte]
    change CQ.ofQ (q18 * q18) * CQ.ofQ (Q.ofInt 32) = CQ.ofQ q12
    rw [← CQ.ofQ_mul, q18_sq_mul32_eq_q12]
  · simp only [hab, ↓reduceIte, CQ.ofZGauss]; change _ * (0 : CQ) = 0; exact CQ.mul_zero _

private theorem liftMat_scaleZ_i2 (c : Q) (A : Mat 4 ZGauss) :
    liftMat c (finMatScaleZ ⟨0, 2⟩ A) = MatCQ.scale CQ.iUnit (liftMat (c * Q.ofInt 2) A) := by
  funext i j
  simp only [liftMat, finMatScaleZ, MatCQ.scale, CQ.ofZGauss_mul]
  have h2 : CQ.ofZGauss ⟨0, 2⟩ = CQ.iUnit * CQ.ofQ (Q.ofInt 2) := by
    apply CQ.ext <;> exact qrel_eq _ _ (by decide)
  rw [h2, CQ.ofQ_mul]
  ac_rfl

private theorem liftMat_scaleZ_ni2 (c : Q) (A : Mat 4 ZGauss) :
    liftMat c (finMatScaleZ ⟨0, -2⟩ A) = MatCQ.scale (-CQ.iUnit) (liftMat (c * Q.ofInt 2) A) := by
  funext i j
  simp only [liftMat, finMatScaleZ, MatCQ.scale, CQ.ofZGauss_mul]
  have h2 : CQ.ofZGauss ⟨0, -2⟩ = (-CQ.iUnit) * CQ.ofQ (Q.ofInt 2) := by
    apply CQ.ext <;> exact qrel_eq _ _ (by decide)
  rw [h2, CQ.ofQ_mul]
  ac_rfl

private theorem q12_mul_q18_mul2 : (q12 * q18) * Q.ofInt 2 = q18 := qrel_eq _ _ (by decide)

private theorem mul_z4_v4_sq1 (g a : Fin 3) : isSqZ 4 (matMulZ 4 (z4L g) (v4L a)) = true := by decide +revert
private theorem mul_z4_v4_sq2 (g a : Fin 3) : isSqZ 4 (matMulZ 4 (v4L a) (z4L g)) = true := by decide +revert

theorem comm_Z4_V4 (g a : Fin 3) :
    MatCQ.comm (Z4 g) (V4 a) =
      match g.val, a.val with
      | 0, 1 => MatCQ.scale CQ.iUnit (V4 ⟨2, by omega⟩)
      | 0, 2 => MatCQ.scale (-CQ.iUnit) (V4 ⟨1, by omega⟩)
      | 1, 0 => MatCQ.scale (-CQ.iUnit) (V4 ⟨2, by omega⟩)
      | 1, 2 => MatCQ.scale CQ.iUnit (V4 ⟨0, by omega⟩)
      | 2, 0 => MatCQ.scale CQ.iUnit (V4 ⟨1, by omega⟩)
      | 2, 1 => MatCQ.scale (-CQ.iUnit) (V4 ⟨0, by omega⟩)
      | _, _ => MatCQ.zero := by
  unfold Z4 V4
  rw [Lift.liftMat_comm, ← toFinZ_comm (z4L g) (v4L a) (z4L_sq g) (v4L_sq a) (mul_z4_v4_sq1 g a) (mul_z4_v4_sq2 g a)]
  rcases g with ⟨vg, hg⟩; rcases a with ⟨va, ha⟩
  match vg, va with
  | 0, 0 => rw [show z4L ⟨0, hg⟩ = z4x from rfl, show v4L ⟨0, ha⟩ = v4x from rfl, zv4_xx, show z0 = (0 : ZGauss) from rfl, toFinZ_scale 0 id4 id4_sq]; exact z0_mul_eq0 _ _
  | 0, 1 => rw [show z4L ⟨0, hg⟩ = z4x from rfl, show v4L ⟨1, ha⟩ = v4y from rfl, zv4_xy, toFinZ_scale ⟨0,2⟩ v4z v4z_sq, liftMat_scaleZ_i2, q12_mul_q18_mul2]; rfl
  | 0, 2 => rw [show z4L ⟨0, hg⟩ = z4x from rfl, show v4L ⟨2, ha⟩ = v4z from rfl, zv4_xz, toFinZ_scale ⟨0,-2⟩ v4y v4y_sq, liftMat_scaleZ_ni2, q12_mul_q18_mul2]; rfl
  | 1, 0 => rw [show z4L ⟨1, hg⟩ = z4y from rfl, show v4L ⟨0, ha⟩ = v4x from rfl, zv4_yx, toFinZ_scale ⟨0,-2⟩ v4z v4z_sq, liftMat_scaleZ_ni2, q12_mul_q18_mul2]; rfl
  | 1, 1 => rw [show z4L ⟨1, hg⟩ = z4y from rfl, show v4L ⟨1, ha⟩ = v4y from rfl, zv4_yy, show z0 = (0 : ZGauss) from rfl, toFinZ_scale 0 id4 id4_sq]; exact z0_mul_eq0 _ _
  | 1, 2 => rw [show z4L ⟨1, hg⟩ = z4y from rfl, show v4L ⟨2, ha⟩ = v4z from rfl, zv4_yz, toFinZ_scale ⟨0,2⟩ v4x v4x_sq, liftMat_scaleZ_i2, q12_mul_q18_mul2]; rfl
  | 2, 0 => rw [show z4L ⟨2, hg⟩ = z4z from rfl, show v4L ⟨0, ha⟩ = v4x from rfl, zv4_zx, toFinZ_scale ⟨0,2⟩ v4y v4y_sq, liftMat_scaleZ_i2, q12_mul_q18_mul2]; rfl
  | 2, 1 => rw [show z4L ⟨2, hg⟩ = z4z from rfl, show v4L ⟨1, ha⟩ = v4y from rfl, zv4_zy, toFinZ_scale ⟨0,-2⟩ v4x v4x_sq, liftMat_scaleZ_ni2, q12_mul_q18_mul2]; rfl
  | 2, 2 => rw [show z4L ⟨2, hg⟩ = z4z from rfl, show v4L ⟨2, ha⟩ = v4z from rfl, zv4_zz, show z0 = (0 : ZGauss) from rfl, toFinZ_scale 0 id4 id4_sq]; exact z0_mul_eq0 _ _
  | _+3, _ => omega
  | _, _+3 => omega

private theorem mul_ex4_v4_sq1 (a : Fin 3) : isSqZ 4 (matMulZ 4 ex4 (v4L a)) = true := by decide +revert
private theorem mul_ex4_v4_sq2 (a : Fin 3) : isSqZ 4 (matMulZ 4 (v4L a) ex4) = true := by decide +revert
private theorem comm_ex4_v4_sq (a : Fin 3) : isSqZ 4 (matCommZ 4 ex4 (v4L a)) = true := by decide +revert

theorem v4_orthog_Hex4 (d a : Fin 3) :
    MatCQ.frobInner (V4 d) (MatCQ.comm Hex4 (V4 a)) = 0 := by
  unfold Hex4 V4
  rw [Lift.liftMat_comm, ← toFinZ_comm ex4 (v4L a) ex4_sq (v4L_sq a) (mul_ex4_v4_sq1 a) (mul_ex4_v4_sq2 a),
      Lift.liftMat_frobInner, ← frobDotZ_eq (v4L d) (matCommZ 4 ex4 (v4L a)) (v4L_sq d) (comm_ex4_v4_sq a)]
  have hz : frobDotZ (v4L d) (matCommZ 4 ex4 (v4L a)) = z0 := by
    unfold v4L; decide +revert
  rw [hz]; change _ * (0 : CQ) = 0; exact CQ.mul_zero _

/-- Symmetrized integer two-electron dipolar basis `(2 S_{1a})(2 S_{2b}) + (2 S_{1b})(2 S_{2a})`. -/
def symDipZ (a b : Fin 3) : MatZList :=
  matAddZ (matMulZ 4 (s1_4L a) (s2_4L b)) (matMulZ 4 (s1_4L b) (s2_4L a))

/-- Symmetrized two-electron dipolar operator `1/2 (S_{1a} S_{2b} + S_{1b} S_{2a})`. -/
def SymDip4 (a b : Fin 3) : Mat 4 CQ :=
  liftMat q18 (toFinZ 4 (symDipZ a b))

private theorem symDipZ_sq (a b : Fin 3) : isSqZ 4 (symDipZ a b) = true := by
  unfold symDipZ s1_4L s2_4L; decide +revert
private theorem mul_symDip_ps_sq1 (a b : Fin 3) : isSqZ 4 (matMulZ 4 (symDipZ a b) fourPS4) = true := by
  unfold symDipZ s1_4L s2_4L; decide +revert
private theorem mul_symDip_ps_sq2 (a b : Fin 3) : isSqZ 4 (matMulZ 4 fourPS4 (symDipZ a b)) = true := by
  unfold symDipZ s1_4L s2_4L; decide +revert
private theorem comm_symDip_ps_Z (a b : Fin 3) : matCommZ 4 (symDipZ a b) fourPS4 = matScaleZ 0 id4 := by
  unfold symDipZ s1_4L s2_4L; decide +revert
private theorem mul_s1_s2_sq (a b : Fin 3) : isSqZ 4 (matMulZ 4 (s1_4L a) (s2_4L b)) = true := by
  unfold s1_4L s2_4L; decide +revert

theorem SymDip4_eq_half_sum (a b : Fin 3) :
    SymDip4 a b = MatCQ.scale (CQ.ofQ q12) (MatCQ.add (MatCQ.mul (S1_4 a) (S2_4 b)) (MatCQ.mul (S1_4 b) (S2_4 a))) := by
  unfold SymDip4 symDipZ S1_4 S2_4
  rw [Lift.liftMat_mul, Lift.liftMat_mul,
      ← toFinZ_mul (s1_4L a) (s2_4L b) (s1_4L_sq a) (s2_4L_sq b),
      ← toFinZ_mul (s1_4L b) (s2_4L a) (s1_4L_sq b) (s2_4L_sq a),
      Lift.liftMat_add, ← toFinZ_add _ _ (mul_s1_s2_sq a b) (mul_s1_s2_sq b a),
      Lift.liftMat_scale]
  have hq : q12 * (q12 * q12) = q18 := qrel_eq _ _ (by decide)
  rw [hq]

theorem comm_SymDip4_PS4 (a b : Fin 3) : MatCQ.comm (SymDip4 a b) PS4 = MatCQ.zero := by
  unfold SymDip4 PS4
  rw [Lift.liftMat_comm,
      ← toFinZ_comm (symDipZ a b) fourPS4 (symDipZ_sq a b) fourPS4_sq (mul_symDip_ps_sq1 a b) (mul_symDip_ps_sq2 a b),
      comm_symDip_ps_Z a b, toFinZ_scale 0 id4 id4_sq]
  exact z0_mul_eq0 _ _

private theorem mul_symDip_v4_sq1 (a b c : Fin 3) : isSqZ 4 (matMulZ 4 (symDipZ a b) (v4L c)) = true := by
  unfold symDipZ s1_4L s2_4L v4L; decide +revert
private theorem mul_symDip_v4_sq2 (a b c : Fin 3) : isSqZ 4 (matMulZ 4 (v4L c) (symDipZ a b)) = true := by
  unfold symDipZ s1_4L s2_4L v4L; decide +revert
private theorem comm_symDip_v4_sq (a b c : Fin 3) : isSqZ 4 (matCommZ 4 (symDipZ a b) (v4L c)) = true := by
  unfold symDipZ s1_4L s2_4L v4L; decide +revert

theorem v4_orthog_SymDip4 (d a b c : Fin 3) :
    MatCQ.frobInner (V4 d) (MatCQ.comm (SymDip4 a b) (V4 c)) = 0 := by
  unfold SymDip4 V4
  rw [Lift.liftMat_comm,
      ← toFinZ_comm (symDipZ a b) (v4L c) (symDipZ_sq a b) (v4L_sq c) (mul_symDip_v4_sq1 a b c) (mul_symDip_v4_sq2 a b c),
      Lift.liftMat_frobInner,
      ← frobDotZ_eq (v4L d) (matCommZ 4 (symDipZ a b) (v4L c)) (v4L_sq d) (comm_symDip_v4_sq a b c)]
  have hz : frobDotZ (v4L d) (matCommZ 4 (symDipZ a b) (v4L c)) = z0 := by
    unfold symDipZ s1_4L s2_4L v4L; decide +revert
  rw [hz]; change _ * (0 : CQ) = 0; exact CQ.mul_zero _

private theorem mul_s1_v4_sq1 (g a : Fin 3) : isSqZ 4 (matMulZ 4 (s1_4L g) (v4L a)) = true := by decide +revert
private theorem mul_s1_v4_sq2 (g a : Fin 3) : isSqZ 4 (matMulZ 4 (v4L a) (s1_4L g)) = true := by decide +revert

theorem v4_anticomm_S1_4 (d g a : Fin 3) :
    MatCQ.frobInner (V4 d) (MatCQ.add (MatCQ.mul (S1_4 g) (V4 a)) (MatCQ.mul (V4 a) (S1_4 g))) = 0 := by
  rw [MatCQ.frobInner_add_right]
  unfold V4 S1_4
  rw [Lift.liftMat_mul, Lift.liftMat_mul, Lift.liftMat_frobInner, Lift.liftMat_frobInner,
      ← toFinZ_mul (s1_4L g) (v4L a) (s1_4L_sq g) (v4L_sq a),
      ← toFinZ_mul (v4L a) (s1_4L g) (v4L_sq a) (s1_4L_sq g),
      ← frobDotZ_eq (v4L d) _ (v4L_sq d) (mul_s1_v4_sq1 g a),
      ← frobDotZ_eq (v4L d) _ (v4L_sq d) (mul_s1_v4_sq2 g a),
      Q.mul_comm q18 q12, ← CQ.left_distrib, ← CQ.ofZGauss_add]
  have hz : frobDotZ (v4L d) (matMulZ 4 (s1_4L g) (v4L a)) +
            frobDotZ (v4L d) (matMulZ 4 (v4L a) (s1_4L g)) = z0 := by
    unfold v4L s1_4L; decide +revert
  rw [hz]; change _ * (0 : CQ) = 0; exact CQ.mul_zero _

private theorem mul_s2_v4_sq1 (g a : Fin 3) : isSqZ 4 (matMulZ 4 (s2_4L g) (v4L a)) = true := by decide +revert
private theorem mul_s2_v4_sq2 (g a : Fin 3) : isSqZ 4 (matMulZ 4 (v4L a) (s2_4L g)) = true := by decide +revert

theorem v4_anticomm_S2_4 (d g a : Fin 3) :
    MatCQ.frobInner (V4 d) (MatCQ.add (MatCQ.mul (S2_4 g) (V4 a)) (MatCQ.mul (V4 a) (S2_4 g))) = 0 := by
  rw [MatCQ.frobInner_add_right]
  unfold V4 S2_4
  rw [Lift.liftMat_mul, Lift.liftMat_mul, Lift.liftMat_frobInner, Lift.liftMat_frobInner,
      ← toFinZ_mul (s2_4L g) (v4L a) (s2_4L_sq g) (v4L_sq a),
      ← toFinZ_mul (v4L a) (s2_4L g) (v4L_sq a) (s2_4L_sq g),
      ← frobDotZ_eq (v4L d) _ (v4L_sq d) (mul_s2_v4_sq1 g a),
      ← frobDotZ_eq (v4L d) _ (v4L_sq d) (mul_s2_v4_sq2 g a),
      Q.mul_comm q18 q12, ← CQ.left_distrib, ← CQ.ofZGauss_add]
  have hz : frobDotZ (v4L d) (matMulZ 4 (s2_4L g) (v4L a)) +
            frobDotZ (v4L d) (matMulZ 4 (v4L a) (s2_4L g)) = z0 := by
    unfold v4L s2_4L; decide +revert
  rw [hz]; change _ * (0 : CQ) = 0; exact CQ.mul_zero _

def Se_4 (b : Bool) (g : Fin 3) : Mat 4 CQ := if b then S1_4 g else S2_4 g
def σ_e (b : Bool) : Q := if b then 1 else -1

theorem σ_e_sq (b : Bool) : σ_e b * σ_e b = 1 := by
  cases b <;> exact qrel_eq _ _ (by decide)

theorem comm_Se_4_PS4 (b : Bool) (a : Fin 3) :
    MatCQ.comm (Se_4 b a) PS4 = MatCQ.scale (CQ.ofQ (σ_e b)) (V4 a) := by
  cases b
  · unfold Se_4 σ_e; rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, comm_S2_4_PS4 a]
    have hneg : CQ.ofQ (-1 : Q) = (-1 : CQ) := by apply CQ.ext <;> exact qrel_eq _ _ (by decide)
    funext i j; simp only [MatCQ.neg, MatCQ.scale]; rw [hneg, CQ.neg_mul, CQ.one_mul]
  · unfold Se_4 σ_e; rw [if_pos rfl, if_pos rfl, comm_S1_4_PS4 a]
    have hone : CQ.ofQ (1 : Q) = (1 : CQ) := rfl
    funext i j; simp only [MatCQ.scale]; rw [hone, CQ.one_mul]

theorem v4_anticomm_Se_4 (b : Bool) (d g a : Fin 3) :
    MatCQ.frobInner (V4 d) (MatCQ.add (MatCQ.mul (Se_4 b g) (V4 a)) (MatCQ.mul (V4 a) (Se_4 b g))) = 0 := by
  cases b
  · exact v4_anticomm_S2_4 d g a
  · exact v4_anticomm_S1_4 d g a

/-! ### Unified Spin-I Radical-Pair Model (`4*m` Dimensions) & Concrete `8x8` / `12x12` Models -/

def sum3M {d : Nat} (f : Fin 3 → Mat d CQ) : Mat d CQ :=
  MatCQ.add (f ⟨0, by omega⟩) (MatCQ.add (f ⟨1, by omega⟩) (f ⟨2, by omega⟩))

def sum3Q (f : Fin 3 → Q) : Q :=
  f ⟨0, by omega⟩ + (f ⟨1, by omega⟩ + f ⟨2, by omega⟩)

def sum3CQ (f : Fin 3 → CQ) : CQ :=
  f ⟨0, by omega⟩ + (f ⟨1, by omega⟩ + f ⟨2, by omega⟩)

theorem sum3M_comm_right {d : Nat} (f : Fin 3 → Mat d CQ) (B : Mat d CQ) :
    MatCQ.comm (sum3M f) B = sum3M (fun i => MatCQ.comm (f i) B) := by
  unfold sum3M; rw [MatCQ.comm_add_left, MatCQ.comm_add_left]

theorem sum3M_comm_left {d : Nat} (A : Mat d CQ) (f : Fin 3 → Mat d CQ) :
    MatCQ.comm A (sum3M f) = sum3M (fun i => MatCQ.comm A (f i)) := by
  unfold sum3M; rw [MatCQ.comm_add_right, MatCQ.comm_add_right]

theorem sum3M_frobInner_left {d : Nat} (f : Fin 3 → Mat d CQ) (B : Mat d CQ) :
    MatCQ.frobInner (sum3M f) B = sum3CQ (fun i => MatCQ.frobInner (f i) B) := by
  unfold sum3M sum3CQ; rw [MatCQ.frobInner_add_left, MatCQ.frobInner_add_left]

theorem sum3M_frobInner_right {d : Nat} (A : Mat d CQ) (f : Fin 3 → Mat d CQ) :
    MatCQ.frobInner A (sum3M f) = sum3CQ (fun i => MatCQ.frobInner A (f i)) := by
  unfold sum3M sum3CQ; rw [MatCQ.frobInner_add_right, MatCQ.frobInner_add_right]

theorem sum3M_zero {d : Nat} (f : Fin 3 → Mat d CQ) (h : ∀ i, f i = MatCQ.zero) :
    sum3M f = MatCQ.zero := by
  unfold sum3M; rw [h ⟨0, by omega⟩, h ⟨1, by omega⟩, h ⟨2, by omega⟩, MatCQ.zero_add, MatCQ.zero_add]

theorem sum3CQ_zero (f : Fin 3 → CQ) (h : ∀ i, f i = 0) : sum3CQ f = 0 := by
  unfold sum3CQ; rw [h ⟨0, by omega⟩, h ⟨1, by omega⟩, h ⟨2, by omega⟩, CQ.zero_add, CQ.zero_add]

theorem sum3CQ_ofQ (f : Fin 3 → Q) : sum3CQ (fun i => CQ.ofQ (f i)) = CQ.ofQ (sum3Q f) := by
  unfold sum3CQ sum3Q; simp only [CQ.ofQ_add]

structure NucSpec (m : Nat) where
  hm : 0 < m
  Iop : Fin 3 → Mat m CQ
  frobNuc : Q
  frob_exact : ∀ a b : Fin 3, MatCQ.frobInner (Iop a) (Iop b) = if a = b then CQ.ofQ frobNuc else 0
  anticomm_orthog : ∀ b r s : Fin 3,
    MatCQ.frobInner (Iop b) (MatCQ.add (MatCQ.mul (Iop r) (Iop s)) (MatCQ.mul (Iop s) (Iop r))) = 0

private theorem frob_2x2_f3 (a b : Fin 3) :
    frobDotZ (match a.val with | 0 => sx2 | 1 => sy2 | _ => sz2)
             (match b.val with | 0 => sx2 | 1 => sy2 | _ => sz2) =
    if a = b then ⟨2, 0⟩ else 0 := by decide +revert

private theorem mul_2x2_sq (r s : Fin 3) :
    isSqZ 2 (matMulZ 2 (match r.val with | 0 => sx2 | 1 => sy2 | _ => sz2)
                       (match s.val with | 0 => sx2 | 1 => sy2 | _ => sz2)) = true := by decide +revert

private theorem add_mul_2x2_sq (r s : Fin 3) :
    isSqZ 2 (matAddZ (matMulZ 2 (match r.val with | 0 => sx2 | 1 => sy2 | _ => sz2)
                                (match s.val with | 0 => sx2 | 1 => sy2 | _ => sz2))
                     (matMulZ 2 (match s.val with | 0 => sx2 | 1 => sy2 | _ => sz2)
                                (match r.val with | 0 => sx2 | 1 => sy2 | _ => sz2))) = true := by decide +revert

private theorem frob_3x3_f3 (a b : Fin 3) :
    frobDotZ (match a.val with | 0 => ix3 | 1 => iy3 | _ => iz3)
             (match b.val with | 0 => ix3 | 1 => iy3 | _ => iz3) =
    if a = b then ⟨2, 0⟩ else 0 := by decide +revert

private theorem mul_3x3_sq (r s : Fin 3) :
    isSqZ 3 (matMulZ 3 (match r.val with | 0 => ix3 | 1 => iy3 | _ => iz3)
                       (match s.val with | 0 => ix3 | 1 => iy3 | _ => iz3)) = true := by decide +revert

private theorem add_mul_3x3_sq (r s : Fin 3) :
    isSqZ 3 (matAddZ (matMulZ 3 (match r.val with | 0 => ix3 | 1 => iy3 | _ => iz3)
                                (match s.val with | 0 => ix3 | 1 => iy3 | _ => iz3))
                     (matMulZ 3 (match s.val with | 0 => ix3 | 1 => iy3 | _ => iz3)
                                (match r.val with | 0 => ix3 | 1 => iy3 | _ => iz3))) = true := by decide +revert

def nucHalf : NucSpec 2 where
  hm := by omega
  Iop := fun a => liftMat q12 (toFinZ 2 (match a.val with | 0 => sx2 | 1 => sy2 | _ => sz2))
  frobNuc := q12
  frob_exact := by
    intro a b
    have ha : isSqZ 2 (match a.val with | 0 => sx2 | 1 => sy2 | _ => sz2) = true := by
      rcases a with ⟨va, _⟩; match va with | 0 => exact sx2_sq | 1 => exact sy2_sq | 2 => exact sz2_sq | _+3 => omega
    have hb : isSqZ 2 (match b.val with | 0 => sx2 | 1 => sy2 | _ => sz2) = true := by
      rcases b with ⟨vb, _⟩; match vb with | 0 => exact sx2_sq | 1 => exact sy2_sq | 2 => exact sz2_sq | _+3 => omega
    rw [Lift.liftMat_frobInner, ← frobDotZ_eq _ _ ha hb, frob_2x2_f3 a b]
    by_cases h : a = b
    · simp only [h, ↓reduceIte]
      change CQ.ofQ (q12 * q12) * CQ.ofQ (Q.ofInt 2) = CQ.ofQ q12
      rw [← CQ.ofQ_mul, q12_sq_mul2_eq_q12]
    · simp only [h, ↓reduceIte, CQ.ofZGauss]; change _ * (0 : CQ) = 0; exact CQ.mul_zero _
  anticomm_orthog := by
    intro b r s
    have hb : isSqZ 2 (match b.val with | 0 => sx2 | 1 => sy2 | _ => sz2) = true := by
      rcases b with ⟨vb, _⟩; match vb with | 0 => exact sx2_sq | 1 => exact sy2_sq | 2 => exact sz2_sq | _+3 => omega
    have hr : isSqZ 2 (match r.val with | 0 => sx2 | 1 => sy2 | _ => sz2) = true := by
      rcases r with ⟨vr, _⟩; match vr with | 0 => exact sx2_sq | 1 => exact sy2_sq | 2 => exact sz2_sq | _+3 => omega
    have hs : isSqZ 2 (match s.val with | 0 => sx2 | 1 => sy2 | _ => sz2) = true := by
      rcases s with ⟨vs, _⟩; match vs with | 0 => exact sx2_sq | 1 => exact sy2_sq | 2 => exact sz2_sq | _+3 => omega
    rw [Lift.liftMat_mul, Lift.liftMat_mul, Lift.liftMat_add, Lift.liftMat_frobInner,
        ← toFinZ_mul _ _ hr hs, ← toFinZ_mul _ _ hs hr, ← toFinZ_add _ _ (mul_2x2_sq r s) (mul_2x2_sq s r),
        ← frobDotZ_eq _ _ hb (add_mul_2x2_sq r s), symm_2x2_orthog b r s]
    change _ * (0 : CQ) = 0; exact CQ.mul_zero _

def nucOne : NucSpec 3 where
  hm := by omega
  Iop := fun a => liftMat 1 (toFinZ 3 (match a.val with | 0 => ix3 | 1 => iy3 | _ => iz3))
  frobNuc := Q.ofInt 2
  frob_exact := by
    intro a b
    have ha : isSqZ 3 (match a.val with | 0 => ix3 | 1 => iy3 | _ => iz3) = true := by
      rcases a with ⟨va, _⟩; match va with | 0 => exact ix3_sq | 1 => exact iy3_sq | 2 => exact iz3_sq | _+3 => omega
    have hb : isSqZ 3 (match b.val with | 0 => ix3 | 1 => iy3 | _ => iz3) = true := by
      rcases b with ⟨vb, _⟩; match vb with | 0 => exact ix3_sq | 1 => exact iy3_sq | 2 => exact iz3_sq | _+3 => omega
    rw [Lift.liftMat_frobInner, ← frobDotZ_eq _ _ ha hb, frob_3x3_f3 a b]
    by_cases h : a = b
    · simp only [h, ↓reduceIte, CQ.ofZGauss, Q.one_mul]; rfl
    · simp only [h, ↓reduceIte, CQ.ofZGauss]; change _ * (0 : CQ) = 0; exact CQ.mul_zero _
  anticomm_orthog := by
    intro b r s
    have hb : isSqZ 3 (match b.val with | 0 => ix3 | 1 => iy3 | _ => iz3) = true := by
      rcases b with ⟨vb, _⟩; match vb with | 0 => exact ix3_sq | 1 => exact iy3_sq | 2 => exact iz3_sq | _+3 => omega
    have hr : isSqZ 3 (match r.val with | 0 => ix3 | 1 => iy3 | _ => iz3) = true := by
      rcases r with ⟨vr, _⟩; match vr with | 0 => exact ix3_sq | 1 => exact iy3_sq | 2 => exact iz3_sq | _+3 => omega
    have hs : isSqZ 3 (match s.val with | 0 => ix3 | 1 => iy3 | _ => iz3) = true := by
      rcases s with ⟨vs, _⟩; match vs with | 0 => exact ix3_sq | 1 => exact iy3_sq | 2 => exact iz3_sq | _+3 => omega
    rw [Lift.liftMat_mul, Lift.liftMat_mul, Lift.liftMat_add, Lift.liftMat_frobInner,
        ← toFinZ_mul _ _ hr hs, ← toFinZ_mul _ _ hs hr, ← toFinZ_add _ _ (mul_3x3_sq r s) (mul_3x3_sq s r),
        ← frobDotZ_eq _ _ hb (add_mul_3x3_sq r s), symm_3x3_orthog b r s]
    change _ * (0 : CQ) = 0; exact CQ.mul_zero _

section UnifiedRP

variable {m : Nat} (N : NucSpec m)

def PS : Mat (4 * m) CQ := finKron N.hm PS4 MatCQ.id
def PT : Mat (4 * m) CQ := finKron N.hm PT4 MatCQ.id

def H_Z (ωL : Q) (n : Fin 3 → Q) : Mat (4 * m) CQ :=
  sum3M (fun g => MatCQ.scale (CQ.ofQ (ωL * n g)) (finKron N.hm (Z4 g) MatCQ.id))

def H_ex (J : Q) : Mat (4 * m) CQ :=
  MatCQ.scale (CQ.ofQ J) (finKron N.hm Hex4 MatCQ.id)

def H_HF (A : Fin 3 → Fin 3 → Q) : Mat (4 * m) CQ :=
  sum3M (fun a => sum3M (fun b => MatCQ.scale (CQ.ofQ (A a b)) (finKron N.hm (S1_4 a) (N.Iop b))))

def H_RP (ωL : Q) (n : Fin 3 → Q) (A : Fin 3 → Fin 3 → Q) (J : Q) : Mat (4 * m) CQ :=
  MatCQ.add (H_Z N ωL n) (MatCQ.add (H_HF N A) (H_ex N J))

def C1_HF (A : Fin 3 → Fin 3 → Q) : Mat (4 * m) CQ :=
  sum3M (fun a => sum3M (fun b => MatCQ.scale (CQ.ofQ (A a b)) (finKron N.hm (V4 a) (N.Iop b))))

theorem PS_idem : MatCQ.mul (PS N) (PS N) = PS N := by
  unfold PS; rw [Kron.mul, PS4_idem, Kron.mul_id_id]

theorem PT_idem : MatCQ.mul (PT N) (PT N) = PT N := by
  unfold PT; rw [Kron.mul, PT4_idem, Kron.mul_id_id]

theorem PS_PT_ortho : MatCQ.mul (PS N) (PT N) = MatCQ.zero := by
  unfold PS PT; rw [Kron.mul, PS4_PT4_ortho, Kron.zero_left]

theorem PS_add_PT : MatCQ.add (PS N) (PT N) = MatCQ.id := by
  unfold PS PT; rw [← Kron.add_left, PS4_add_PT4, Kron.id_kron]

private theorem conjT_id {d : Nat} : MatCQ.conjT (MatCQ.id : Mat d CQ) = MatCQ.id := by
  funext i j; unfold MatCQ.conjT MatCQ.id
  by_cases hij : i = j
  · subst hij; simp; apply CQ.ext <;> simp [Q.neg_zero]
  · have hji : j ≠ i := fun h => hij h.symm
    simp [hij, hji]; apply CQ.ext <;> simp [Q.neg_zero]

theorem PS_herm : MatCQ.conjT (PS N) = PS N := by
  unfold PS; rw [Kron.conjT, PS4_herm, conjT_id]

theorem PT_herm : MatCQ.conjT (PT N) = PT N := by
  unfold PT; rw [Kron.conjT, PT4_herm, conjT_id]

private theorem trace_id {d : Nat} : MatCQ.trace (MatCQ.id : Mat d CQ) = CQ.ofQ (Q.ofInt d) := by
  unfold MatCQ.trace MatCQ.id
  induction d with
  | zero => rfl
  | succ d ih =>
    have hf : (fun i : Fin (d + 1) => if i = i then (1 : CQ) else 0) = fun _ => 1 := by
      funext i; simp
    rw [hf]
    change 1 + sumFin (0 : CQ) (fun i : Fin d => 1) = CQ.ofQ (Q.ofInt ↑(d + 1))
    have ih1 : sumFin (0 : CQ) (fun i : Fin d => (1 : CQ)) = CQ.ofQ (Q.ofInt d) := by
      have hf0 : (fun i : Fin d => if i = i then (1 : CQ) else 0) = fun _ => 1 := by
        funext i; simp
      rwa [hf0] at ih
    rw [ih1]
    have hint : Q.ofInt (d + 1 : Nat) = 1 + Q.ofInt (d : Nat) := by
      have hnat : ((d + 1 : Nat) : Int) = 1 + (d : Int) := by omega
      rw [hnat, Q.ofInt_add]; rfl
    rw [hint, CQ.ofQ_add]; rfl

theorem PS_trace : MatCQ.trace (PS N) = CQ.ofQ (Q.ofInt m) := by
  unfold PS; rw [Kron.trace, PS4_trace, trace_id, CQ.one_mul]

theorem PT_trace : MatCQ.trace (PT N) = CQ.ofQ (Q.ofInt (3 * m)) := by
  unfold PT; rw [Kron.trace, PT4_trace, trace_id, ← CQ.ofQ_mul]
  have hnat : Q.ofInt 3 * Q.ofInt (m : Int) = Q.ofInt (3 * (m : Int)) := by
    rw [← Q.ofInt_mul]
  rw [hnat]

theorem comm_H_Z_PS (ωL : Q) (n : Fin 3 → Q) :
    MatCQ.comm (H_Z N ωL n) (PS N) = MatCQ.zero := by
  unfold H_Z PS
  rw [sum3M_comm_right]
  apply sum3M_zero
  intro g
  rw [MatCQ.comm_scale_left, Kron.comm_id_left, comm_Z4_PS4 g, Kron.zero_left]
  funext i j; exact CQ.mul_zero _

theorem comm_H_ex_PS (J : Q) :
    MatCQ.comm (H_ex N J) (PS N) = MatCQ.zero := by
  unfold H_ex PS
  rw [MatCQ.comm_scale_left, Kron.comm_id_left, comm_Hex4_PS4, Kron.zero_left]
  funext i j; exact CQ.mul_zero _

theorem comm_H_HF_PS (A : Fin 3 → Fin 3 → Q) :
    MatCQ.comm (H_HF N A) (PS N) = C1_HF N A := by
  unfold H_HF C1_HF PS
  rw [sum3M_comm_right]
  apply congrArg sum3M; funext a
  rw [sum3M_comm_right]
  apply congrArg sum3M; funext b
  rw [MatCQ.comm_scale_left, Kron.comm_id_right, comm_S1_4_PS4 a]

theorem comm_H_RP_PS (ωL : Q) (n : Fin 3 → Q) (A : Fin 3 → Fin 3 → Q) (J : Q) :
    MatCQ.comm (H_RP N ωL n A J) (PS N) = C1_HF N A := by
  unfold H_RP
  rw [MatCQ.comm_add_left, MatCQ.comm_add_left, comm_H_Z_PS, comm_H_ex_PS,
      MatCQ.add_zero, MatCQ.zero_add, comm_H_HF_PS]

private theorem q_ofInt_ne_zero {k : Nat} (hk : 0 < k) : Q.ofInt k ≠ 0 := by
  intro h
  have hrel : QRel ⟨k, 0⟩ ⟨0, 0⟩ := Quotient.exact h
  simp [QRel, QRaw.den] at hrel
  omega

private theorem CQ_conj_ofQ (q : Q) : (CQ.ofQ q).conj = CQ.ofQ q := by
  apply CQ.ext <;> simp [CQ.ofQ, Q.neg_zero]

noncomputable def M0_val : Q :=
  (MatCQ.frobInner (PS N) (PS N)).re / Q.ofInt m

theorem M0_exact :
    (MatCQ.frobInner (PS N) (PS N)) = CQ.ofQ (Q.ofInt m) := by
  unfold MatCQ.frobInner
  rw [PS_herm, PS_idem, PS_trace]

theorem M0_norm_one : (MatCQ.frobInner (PS N) (PS N)).re / Q.ofInt m = 1 := by
  rw [M0_exact]
  exact Q.div_self (q_ofInt_ne_zero N.hm)

theorem frobInner_V4_Iop (a b a' b' : Fin 3) :
    MatCQ.frobInner (finKron N.hm (V4 a) (N.Iop b)) (finKron N.hm (V4 a') (N.Iop b')) =
    if a = a' ∧ b = b' then CQ.ofQ (q12 * N.frobNuc) else 0 := by
  rw [Kron.frobInner, frobInner_V4, N.frob_exact]
  by_cases ha : a = a' <;> by_cases hb : b = b'
  · simp [ha, hb, CQ.ofQ_mul]
  · simp [ha, hb, CQ.mul_zero]
  · simp [ha, hb, CQ.zero_mul]
  · simp [ha, hb, CQ.zero_mul]

private theorem sum3CQ_frob_VI (c : Fin 3 → Fin 3 → CQ) (d0 b0 : Fin 3) :
    MatCQ.frobInner (finKron N.hm (V4 d0) (N.Iop b0))
      (sum3M (fun a => sum3M (fun b => MatCQ.scale (c a b) (finKron N.hm (V4 a) (N.Iop b))))) =
    c d0 b0 * CQ.ofQ (q12 * N.frobNuc) := by
  rw [sum3M_frobInner_right]
  have inner_b : ∀ a : Fin 3,
      MatCQ.frobInner (finKron N.hm (V4 d0) (N.Iop b0))
        (sum3M (fun b => MatCQ.scale (c a b) (finKron N.hm (V4 a) (N.Iop b)))) =
      (if d0 = a then c a b0 * CQ.ofQ (q12 * N.frobNuc) else 0) := by
    intro a
    rw [sum3M_frobInner_right]
    simp only [MatCQ.frobInner_scale_right, frobInner_V4_Iop]
    rcases b0 with ⟨vb0, hb0⟩
    match vb0 with
    | 0 => unfold sum3CQ; by_cases hda : d0 = a <;> simp [hda, CQ.mul_zero, CQ.add_zero]
    | 1 => unfold sum3CQ; by_cases hda : d0 = a <;> simp [hda, CQ.mul_zero, CQ.zero_add, CQ.add_zero]
    | 2 => unfold sum3CQ; by_cases hda : d0 = a <;> simp [hda, CQ.mul_zero, CQ.zero_add]
    | _+3 => omega
  have hrewrite :
      (fun a : Fin 3 => MatCQ.frobInner (finKron N.hm (V4 d0) (N.Iop b0))
        (sum3M (fun b => MatCQ.scale (c a b) (finKron N.hm (V4 a) (N.Iop b))))) =
      (fun a : Fin 3 => if d0 = a then c a b0 * CQ.ofQ (q12 * N.frobNuc) else 0) := funext inner_b
  rw [hrewrite]
  rcases d0 with ⟨vd0, hd0⟩
  match vd0 with
  | 0 => unfold sum3CQ; simp [CQ.add_zero]
  | 1 => unfold sum3CQ; simp [CQ.zero_add, CQ.add_zero]
  | 2 => unfold sum3CQ; simp [CQ.zero_add]
  | _+3 => omega

private theorem sum3Q_mul_left (c : Q) (f : Fin 3 → Q) :
    c * sum3Q f = sum3Q (fun i => c * f i) := by
  unfold sum3Q; dsimp only; rw [Q.left_distrib, Q.left_distrib]

theorem M2_exact (ωL : Q) (n : Fin 3 → Q) (A : Fin 3 → Fin 3 → Q) (J : Q) :
    let C1 := MatCQ.comm (H_RP N ωL n A J) (PS N)
    MatCQ.frobInner C1 C1 =
      CQ.ofQ (q12 * N.frobNuc * sum3Q (fun a => sum3Q (fun b => A a b * A a b))) := by
  dsimp only
  rw [comm_H_RP_PS]
  unfold C1_HF
  rw [sum3M_frobInner_left]
  have hrow : ∀ a : Fin 3,
      MatCQ.frobInner (sum3M (fun b => MatCQ.scale (CQ.ofQ (A a b)) (finKron N.hm (V4 a) (N.Iop b))))
        (sum3M (fun a' => sum3M (fun b' => MatCQ.scale (CQ.ofQ (A a' b')) (finKron N.hm (V4 a') (N.Iop b'))))) =
      CQ.ofQ (q12 * N.frobNuc * sum3Q (fun b => A a b * A a b)) := by
    intro a
    rw [sum3M_frobInner_left]
    have hterm : ∀ b : Fin 3,
        MatCQ.frobInner (MatCQ.scale (CQ.ofQ (A a b)) (finKron N.hm (V4 a) (N.Iop b)))
          (sum3M (fun a' => sum3M (fun b' => MatCQ.scale (CQ.ofQ (A a' b')) (finKron N.hm (V4 a') (N.Iop b'))))) =
        CQ.ofQ (q12 * N.frobNuc * (A a b * A a b)) := by
      intro b
      rw [MatCQ.frobInner_scale_left, CQ_conj_ofQ, sum3CQ_frob_VI]
      rw [← CQ.ofQ_mul, ← CQ.ofQ_mul]; congr 1; ac_rfl
    have hr2 : (fun b : Fin 3 => MatCQ.frobInner (MatCQ.scale (CQ.ofQ (A a b)) (finKron N.hm (V4 a) (N.Iop b)))
                  (sum3M (fun a' => sum3M (fun b' => MatCQ.scale (CQ.ofQ (A a' b')) (finKron N.hm (V4 a') (N.Iop b')))))) =
               (fun b : Fin 3 => CQ.ofQ (q12 * N.frobNuc * (A a b * A a b))) := funext hterm
    rw [hr2, sum3CQ_ofQ, ← sum3Q_mul_left]
  have hr1 : (fun a : Fin 3 => MatCQ.frobInner (sum3M (fun b => MatCQ.scale (CQ.ofQ (A a b)) (finKron N.hm (V4 a) (N.Iop b))))
                (sum3M (fun a' => sum3M (fun b' => MatCQ.scale (CQ.ofQ (A a' b')) (finKron N.hm (V4 a') (N.Iop b')))))) =
             (fun a : Fin 3 => CQ.ofQ (q12 * N.frobNuc * sum3Q (fun b => A a b * A a b))) := funext hrow
  rw [hr1, sum3CQ_ofQ, ← sum3Q_mul_left]

theorem M2_norm_exact (ωL : Q) (n : Fin 3 → Q) (A : Fin 3 → Fin 3 → Q) (J : Q) :
    (MatCQ.frobInner (MatCQ.comm (H_RP N ωL n A J) (PS N))
                     (MatCQ.comm (H_RP N ωL n A J) (PS N))).re / Q.ofInt m =
    q12 * (N.frobNuc / Q.ofInt m) * sum3Q (fun a => sum3Q (fun b => A a b * A a b)) := by
  rw [M2_exact]
  change (q12 * N.frobNuc * sum3Q (fun a => sum3Q (fun b => A a b * A a b))) / Q.ofInt m = _
  change (q12 * N.frobNuc * sum3Q (fun a => sum3Q (fun b => A a b * A a b))) * Q.inv (Q.ofInt m) =
         q12 * (N.frobNuc * Q.inv (Q.ofInt m)) * sum3Q (fun a => sum3Q (fun b => A a b * A a b))
  ac_rfl

-- Cross product components of n with each column b of A: (n x A_{.,b})_d
def crossCol (n : Fin 3 → Q) (A : Fin 3 → Fin 3 → Q) (d b : Fin 3) : Q :=
  let x := ⟨0, by omega⟩; let y := ⟨1, by omega⟩; let z := ⟨2, by omega⟩
  match d.val with
  | 0 => n y * A z b - n z * A y b
  | 1 => n z * A x b - n x * A z b
  | _ => n x * A y b - n y * A x b

def C2_Z (ωL : Q) (n : Fin 3 → Q) (A : Fin 3 → Fin 3 → Q) : Mat (4 * m) CQ :=
  sum3M (fun d => sum3M (fun b =>
    MatCQ.scale (CQ.iUnit * CQ.ofQ (ωL * crossCol n A d b)) (finKron N.hm (V4 d) (N.Iop b))))

private theorem matCQ_scale_mul_scale {d : Nat} (a b : CQ) (M : Mat d CQ) :
    MatCQ.scale a (MatCQ.scale b M) = MatCQ.scale (a * b) M := by
  funext i j; unfold MatCQ.scale; exact (CQ.mul_assoc a b _).symm

private theorem matCQ_scale_add {d : Nat} (c : CQ) (M1 M2 : Mat d CQ) :
    MatCQ.scale c (MatCQ.add M1 M2) = MatCQ.add (MatCQ.scale c M1) (MatCQ.scale c M2) := by
  funext i j; unfold MatCQ.scale MatCQ.add; exact CQ.left_distrib c _ _

private theorem matCQ_scale_zero {d : Nat} (c : CQ) :
    MatCQ.scale c (MatCQ.zero : Mat d CQ) = MatCQ.zero := by
  funext i j; exact CQ.mul_zero c

private theorem cq_ofQ_neg (x : Q) : CQ.ofQ (-x) = -(CQ.ofQ x) := by
  apply CQ.ext
  · rfl
  · change (0 : Q) = -0
    exact qrel_eq _ _ (by decide)

private theorem sum3M_swap {d : Nat} (f : Fin 3 → Fin 3 → Mat d CQ) :
    sum3M (fun a => sum3M (fun b => f a b)) = sum3M (fun b => sum3M (fun a => f a b)) := by
  funext i j; unfold sum3M MatCQ.add; dsimp only; ac_rfl

private theorem regroup_cross_col_mat {d : Nat} (w n0 n1 n2 a0 a1 a2 : Q) (V0 V1 V2 : Mat d CQ) :
    MatCQ.add
      (MatCQ.add (MatCQ.scale (CQ.ofQ (w * n0 * a1) * CQ.iUnit) V2)
                 (MatCQ.scale (CQ.ofQ (w * n0 * a2) * (-CQ.iUnit)) V1))
      (MatCQ.add
        (MatCQ.add (MatCQ.scale (CQ.ofQ (w * n1 * a0) * (-CQ.iUnit)) V2)
                   (MatCQ.scale (CQ.ofQ (w * n1 * a2) * CQ.iUnit) V0))
        (MatCQ.add (MatCQ.scale (CQ.ofQ (w * n2 * a0) * CQ.iUnit) V1)
                   (MatCQ.scale (CQ.ofQ (w * n2 * a1) * (-CQ.iUnit)) V0))) =
    MatCQ.add
      (MatCQ.scale (CQ.iUnit * CQ.ofQ (w * (n1 * a2 - n2 * a1))) V0)
      (MatCQ.add
        (MatCQ.scale (CQ.iUnit * CQ.ofQ (w * (n2 * a0 - n0 * a2))) V1)
        (MatCQ.scale (CQ.iUnit * CQ.ofQ (w * (n0 * a1 - n1 * a0))) V2)) := by
  funext i j
  unfold MatCQ.add MatCQ.scale
  have hpair : ∀ (x y : Q) (v : CQ),
      CQ.ofQ (w * x) * CQ.iUnit * v + CQ.ofQ (w * y) * (-CQ.iUnit) * v =
      CQ.iUnit * CQ.ofQ (w * (x - y)) * v := by
    intro x y v
    have h1 : CQ.ofQ (w * y) * (-CQ.iUnit) * v = -(CQ.iUnit * CQ.ofQ (w * y) * v) := by
      rw [CQ.mul_neg, CQ.neg_mul]; congr 1; ac_rfl
    have h2 : CQ.ofQ (w * x) * CQ.iUnit * v = CQ.iUnit * CQ.ofQ (w * x) * v := by ac_rfl
    rw [h1, h2]
    have hsub : CQ.ofQ (w * (x - y)) = CQ.ofQ (w * x) + -(CQ.ofQ (w * y)) := by
      rw [Q.sub_eq_add_neg, Q.left_distrib, Q.mul_neg, CQ.ofQ_add, cq_ofQ_neg]
    rw [hsub, CQ.left_distrib, CQ.right_distrib, CQ.mul_neg]
    exact congrArg (CQ.iUnit * CQ.ofQ (w * x) * v + ·) (CQ.neg_mul (CQ.iUnit * CQ.ofQ (w * y)) v).symm
  simp only [Q.mul_assoc]
  rw [← hpair (n1 * a2) (n2 * a1) (V0 i j),
      ← hpair (n2 * a0) (n0 * a2) (V1 i j),
      ← hpair (n0 * a1) (n1 * a0) (V2 i j)]
  simp only [← Q.mul_assoc]
  ac_rfl

theorem comm_HZ_C1_eq (ωL : Q) (n : Fin 3 → Q) (A : Fin 3 → Fin 3 → Q) :
    MatCQ.comm (H_Z N ωL n) (C1_HF N A) = C2_Z N ωL n A := by
  unfold H_Z C1_HF C2_Z
  rw [sum3M_swap (fun a b => MatCQ.scale (CQ.ofQ (A a b)) (finKron N.hm (V4 a) (N.Iop b)))]
  rw [sum3M_comm_left]
  rw [sum3M_swap (fun d b => MatCQ.scale (CQ.iUnit * CQ.ofQ (ωL * crossCol n A d b)) (finKron N.hm (V4 d) (N.Iop b)))]
  apply congrArg sum3M; funext b
  rw [sum3M_comm_right]
  have expand_g : ∀ g : Fin 3,
      MatCQ.comm (MatCQ.scale (CQ.ofQ (ωL * n g)) (finKron N.hm (Z4 g) MatCQ.id))
        (sum3M (fun a => MatCQ.scale (CQ.ofQ (A a b)) (finKron N.hm (V4 a) (N.Iop b)))) =
      sum3M (fun a => MatCQ.scale (CQ.ofQ (ωL * n g * A a b)) (finKron N.hm (MatCQ.comm (Z4 g) (V4 a)) (N.Iop b))) := by
    intro g
    rw [sum3M_comm_left]
    apply congrArg sum3M; funext a
    rw [MatCQ.comm_scale_left, MatCQ.comm_scale_right, Kron.comm_id_left,
        matCQ_scale_mul_scale, ← CQ.ofQ_mul]
  have h1 : (fun g => MatCQ.comm (MatCQ.scale (CQ.ofQ (ωL * n g)) (finKron N.hm (Z4 g) MatCQ.id))
              (sum3M (fun a => MatCQ.scale (CQ.ofQ (A a b)) (finKron N.hm (V4 a) (N.Iop b))))) =
            (fun g => sum3M (fun a =>
              MatCQ.scale (CQ.ofQ (ωL * n g * A a b)) (finKron N.hm (MatCQ.comm (Z4 g) (V4 a)) (N.Iop b)))) :=
    funext expand_g
  rw [h1]
  unfold sum3M
  simp only [comm_Z4_V4, Kron.zero_left, Kron.scale_left, matCQ_scale_zero,
             MatCQ.zero_add, MatCQ.add_zero, matCQ_scale_mul_scale]
  unfold crossCol
  exact regroup_cross_col_mat ωL
    (n ⟨0, by omega⟩) (n ⟨1, by omega⟩) (n ⟨2, by omega⟩)
    (A ⟨0, by omega⟩ b) (A ⟨1, by omega⟩ b) (A ⟨2, by omega⟩ b)
    (finKron N.hm (V4 ⟨0, by omega⟩) (N.Iop b))
    (finKron N.hm (V4 ⟨1, by omega⟩) (N.Iop b))
    (finKron N.hm (V4 ⟨2, by omega⟩) (N.Iop b))

private theorem cq_neg_neg (a : CQ) : -(-a) = a := by
  apply CQ.ext <;> simp [CQ.neg, Q.neg_neg]

theorem C2_Z_orthog_int (ωL : Q) (n : Fin 3 → Q) (A : Fin 3 → Fin 3 → Q) (J : Q) :
    MatCQ.frobInner (C2_Z N ωL n A) (MatCQ.comm (MatCQ.add (H_HF N A) (H_ex N J)) (C1_HF N A)) = 0 := by
  rw [MatCQ.comm_add_left, MatCQ.frobInner_add_right]
  have step : ∀ d b : Fin 3,
      MatCQ.frobInner (finKron N.hm (V4 d) (N.Iop b)) (MatCQ.comm (H_HF N A) (C1_HF N A)) = 0 ∧
      MatCQ.frobInner (finKron N.hm (V4 d) (N.Iop b)) (MatCQ.comm (H_ex N J) (C1_HF N A)) = 0 := by
    intro d b
    constructor
    · unfold H_HF C1_HF
      rw [sum3M_comm_right, sum3M_frobInner_right]; apply sum3CQ_zero; intro g
      rw [sum3M_comm_right, sum3M_frobInner_right]; apply sum3CQ_zero; intro r
      rw [sum3M_comm_left, sum3M_frobInner_right]; apply sum3CQ_zero; intro a
      rw [sum3M_comm_left, sum3M_frobInner_right]; apply sum3CQ_zero; intro s
      rw [MatCQ.comm_scale_left, MatCQ.comm_scale_right, MatCQ.frobInner_scale_right,
          MatCQ.frobInner_scale_right, Kron.comm, Kron.frobInner_sub_right, Kron.frobInner, Kron.frobInner]
      have hV := v4_anticomm_S1_4 d g a
      rw [MatCQ.frobInner_add_right] at hV
      have hVneg : MatCQ.frobInner (V4 d) (MatCQ.mul (V4 a) (S1_4 g)) =
                   -MatCQ.frobInner (V4 d) (MatCQ.mul (S1_4 g) (V4 a)) := by
        have hadd := congrArg (fun x => -MatCQ.frobInner (V4 d) (MatCQ.mul (S1_4 g) (V4 a)) + x) hV
        dsimp only at hadd
        rw [CQ.add_zero, ← CQ.add_assoc, CQ.add_left_neg, CQ.zero_add] at hadd
        exact hadd
      rw [hVneg, CQ.neg_mul]
      change _ * (_ * (MatCQ.frobInner (V4 d) (MatCQ.mul (S1_4 g) (V4 a)) * MatCQ.frobInner (N.Iop b) (MatCQ.mul (N.Iop r) (N.Iop s)) +
                  -(-(MatCQ.frobInner (V4 d) (MatCQ.mul (S1_4 g) (V4 a)) * MatCQ.frobInner (N.Iop b) (MatCQ.mul (N.Iop s) (N.Iop r)))))) = 0
      rw [cq_neg_neg, ← CQ.left_distrib, ← MatCQ.frobInner_add_right, N.anticomm_orthog b r s, CQ.mul_zero, CQ.mul_zero, CQ.mul_zero]
    · unfold H_ex C1_HF
      rw [sum3M_comm_left, sum3M_frobInner_right]; apply sum3CQ_zero; intro a
      rw [sum3M_comm_left, sum3M_frobInner_right]; apply sum3CQ_zero; intro s
      rw [MatCQ.comm_scale_left, MatCQ.comm_scale_right, MatCQ.frobInner_scale_right,
          MatCQ.frobInner_scale_right, Kron.comm_id_left, Kron.frobInner, v4_orthog_Hex4 d a,
          CQ.zero_mul, CQ.mul_zero, CQ.mul_zero]
  unfold C2_Z
  have apply_sum : ∀ M : Mat (4 * m) CQ,
      (∀ d b : Fin 3, MatCQ.frobInner (finKron N.hm (V4 d) (N.Iop b)) M = 0) →
      MatCQ.frobInner (sum3M (fun d => sum3M (fun b =>
        MatCQ.scale (CQ.iUnit * CQ.ofQ (ωL * crossCol n A d b)) (finKron N.hm (V4 d) (N.Iop b))))) M = 0 := by
    intro M hM
    rw [sum3M_frobInner_left]; apply sum3CQ_zero; intro d
    rw [sum3M_frobInner_left]; apply sum3CQ_zero; intro b
    rw [MatCQ.frobInner_scale_left, hM d b, CQ.mul_zero]
  rw [apply_sum _ (fun d b => (step d b).1), apply_sum _ (fun d b => (step d b).2), CQ.zero_add]

private theorem cross_norm_sq_Q (nx ny nz vx vy vz : Q) :
    (ny * vz - nz * vy) * (ny * vz - nz * vy) +
    ((nz * vx - nx * vz) * (nz * vx - nx * vz) +
     (nx * vy - ny * vx) * (nx * vy - ny * vx)) =
    (nx * nx + (ny * ny + nz * nz)) * (vx * vx + (vy * vy + vz * vz)) -
    (nx * vx + (ny * vy + nz * vz)) * (nx * vx + (ny * vy + nz * vz)) := by
  have sq_sub : ∀ a b : Q, (a - b) * (a - b) = a * a + b * b + -(a * b + a * b) := by
    intro a b
    rw [Q.sub_eq_add_neg, Q.left_distrib, Q.right_distrib, Q.right_distrib, Q.mul_neg, Q.neg_mul]
    have hnb : (-b) * (-b) = b * b := by rw [Q.neg_mul, Q.mul_neg, Q.neg_neg]
    have hneg : -(b * a) = -(a * b) := by rw [Q.mul_comm]
    rw [hnb, hneg, Q.neg_add]
    ac_rfl
  have sq_sum3 : ∀ a b c : Q,
      (a + (b + c)) * (a + (b + c)) =
      a * a + b * b + c * c + ((a * b + a * b) + (b * c + b * c) + (c * a + c * a)) := by
    intro a b c
    simp only [Q.left_distrib, Q.right_distrib]
    have hc1 : b * a = a * b := Q.mul_comm _ _
    have hc2 : c * b = b * c := Q.mul_comm _ _
    have hc3 : a * c = c * a := Q.mul_comm _ _
    rw [hc1, hc2, hc3]
    ac_rfl
  rw [sq_sub (ny * vz) (nz * vy), sq_sub (nz * vx) (nx * vz), sq_sub (nx * vy) (ny * vx),
      sq_sum3 (nx * vx) (ny * vy) (nz * vz)]
  simp only [Q.left_distrib, Q.right_distrib, Q.sub_eq_add_neg, Q.neg_add, Q.mul_assoc]
  have m1 : ny * (vz * (nz * vy)) = ny * (vy * (nz * vz)) := by ac_rfl
  have m2 : nz * (vx * (nx * vz)) = nz * (vz * (nx * vx)) := by ac_rfl
  have m3 : nx * (vy * (ny * vx)) = nx * (vx * (ny * vy)) := by ac_rfl
  have d1 : nx * (nx * (vx * vx)) = nx * (vx * (nx * vx)) := by ac_rfl
  have d2 : ny * (ny * (vy * vy)) = ny * (vy * (ny * vy)) := by ac_rfl
  have d3 : nz * (nz * (vz * vz)) = nz * (vz * (nz * vz)) := by ac_rfl
  have e1 : nx * (nx * (vy * vy)) = nx * (vy * (nx * vy)) := by ac_rfl
  have e2 : nx * (nx * (vz * vz)) = nx * (vz * (nx * vz)) := by ac_rfl
  have e3 : ny * (ny * (vx * vx)) = ny * (vx * (ny * vx)) := by ac_rfl
  have e4 : ny * (ny * (vz * vz)) = ny * (vz * (ny * vz)) := by ac_rfl
  have e5 : nz * (nz * (vx * vx)) = nz * (vx * (nz * vx)) := by ac_rfl
  have e6 : nz * (nz * (vy * vy)) = nz * (vy * (nz * vy)) := by ac_rfl
  have k1 : nx * (vx * (nx * vx)) + -(nx * (vx * (nx * vx))) = 0 := Q.add_right_neg _
  have k2 : ny * (vy * (ny * vy)) + -(ny * (vy * (ny * vy))) = 0 := Q.add_right_neg _
  have k3 : nz * (vz * (nz * vz)) + -(nz * (vz * (nz * vz))) = 0 := Q.add_right_neg _
  rw [m1, m2, m3, d1, d2, d3, e1, e2, e3, e4, e5, e6]
  calc _ = (ny * (vz * (ny * vz)) + nz * (vy * (nz * vy)) + nz * (vx * (nz * vx)) +
            nx * (vz * (nx * vz)) + nx * (vy * (nx * vy)) + ny * (vx * (ny * vx))) +
           (-(ny * (vy * (nz * vz))) + -(ny * (vy * (nz * vz))) +
            -(nz * (vz * (nx * vx))) + -(nz * (vz * (nx * vx))) +
            -(nx * (vx * (ny * vy))) + -(nx * (vx * (ny * vy)))) := by ac_rfl
    _ = (ny * (vz * (ny * vz)) + nz * (vy * (nz * vy)) + nz * (vx * (nz * vx)) +
            nx * (vz * (nx * vz)) + nx * (vy * (nx * vy)) + ny * (vx * (ny * vx))) +
           ((nx * (vx * (nx * vx)) + -(nx * (vx * (nx * vx)))) +
            (ny * (vy * (ny * vy)) + -(ny * (vy * (ny * vy)))) +
            (nz * (vz * (nz * vz)) + -(nz * (vz * (nz * vz))))) +
           (-(ny * (vy * (nz * vz))) + -(ny * (vy * (nz * vz))) +
            -(nz * (vz * (nx * vx))) + -(nz * (vz * (nx * vx))) +
            -(nx * (vx * (ny * vy))) + -(nx * (vx * (ny * vy)))) := by
        rw [k1, k2, k3]; simp only [Q.add_zero]
    _ = _ := by ac_rfl

def frobSq3 (A : Fin 3 → Fin 3 → Q) : Q :=
  sum3Q (fun a => sum3Q (fun b => A a b * A a b))

def quadForm3 (A : Fin 3 → Fin 3 → Q) (n : Fin 3 → Q) : Q :=
  sum3Q (fun b =>
    let col := sum3Q (fun a => n a * A a b)
    col * col)

def normSq3 (n : Fin 3 → Q) : Q := sum3Q (fun a => n a * n a)

private theorem sum3Q_swap (f : Fin 3 → Fin 3 → Q) :
    sum3Q (fun a => sum3Q (fun b => f a b)) = sum3Q (fun b => sum3Q (fun a => f a b)) := by
  unfold sum3Q; dsimp only; ac_rfl

private theorem C2_Z_normSq (ωL : Q) (n : Fin 3 → Q) (A : Fin 3 → Fin 3 → Q) :
    MatCQ.frobInner (C2_Z N ωL n A) (C2_Z N ωL n A) =
    CQ.ofQ (q12 * N.frobNuc * ωL * ωL * (normSq3 n * frobSq3 A - quadForm3 A n)) := by
  have hi_conj : (CQ.iUnit).conj * CQ.iUnit = 1 := by
    apply CQ.ext <;> exact qrel_eq _ _ (by decide)
  have hnorm_cross : MatCQ.frobInner (C2_Z N ωL n A) (C2_Z N ωL n A) =
      CQ.ofQ (q12 * N.frobNuc * ωL * ωL *
        sum3Q (fun d => sum3Q (fun b => crossCol n A d b * crossCol n A d b))) := by
    unfold C2_Z
    rw [sum3M_frobInner_left]
    have hrow : ∀ d : Fin 3,
        MatCQ.frobInner (sum3M (fun b => MatCQ.scale (CQ.iUnit * CQ.ofQ (ωL * crossCol n A d b)) (finKron N.hm (V4 d) (N.Iop b))))
          (sum3M (fun d' => sum3M (fun b' => MatCQ.scale (CQ.iUnit * CQ.ofQ (ωL * crossCol n A d' b')) (finKron N.hm (V4 d') (N.Iop b'))))) =
        CQ.ofQ (q12 * N.frobNuc * ωL * ωL * sum3Q (fun b => crossCol n A d b * crossCol n A d b)) := by
      intro d
      rw [sum3M_frobInner_left]
      have hterm : ∀ b : Fin 3,
          MatCQ.frobInner (MatCQ.scale (CQ.iUnit * CQ.ofQ (ωL * crossCol n A d b)) (finKron N.hm (V4 d) (N.Iop b)))
            (sum3M (fun d' => sum3M (fun b' => MatCQ.scale (CQ.iUnit * CQ.ofQ (ωL * crossCol n A d' b')) (finKron N.hm (V4 d') (N.Iop b'))))) =
          CQ.ofQ (q12 * N.frobNuc * ωL * ωL * (crossCol n A d b * crossCol n A d b)) := by
        intro b
        rw [MatCQ.frobInner_scale_left, sum3CQ_frob_VI, CQ.conj_mul, CQ_conj_ofQ]
        have heq : (CQ.iUnit.conj * CQ.ofQ (ωL * crossCol n A d b)) *
                   (CQ.iUnit * CQ.ofQ (ωL * crossCol n A d b) * CQ.ofQ (q12 * N.frobNuc)) =
                   CQ.ofQ (q12 * N.frobNuc * ωL * ωL * (crossCol n A d b * crossCol n A d b)) := by
          calc (CQ.iUnit.conj * CQ.ofQ (ωL * crossCol n A d b)) * (CQ.iUnit * CQ.ofQ (ωL * crossCol n A d b) * CQ.ofQ (q12 * N.frobNuc))
              = (CQ.iUnit.conj * CQ.iUnit) * (CQ.ofQ (q12 * N.frobNuc) * CQ.ofQ (ωL * crossCol n A d b) * CQ.ofQ (ωL * crossCol n A d b)) := by ac_rfl
            _ = 1 * CQ.ofQ (q12 * N.frobNuc * (ωL * crossCol n A d b) * (ωL * crossCol n A d b)) := by rw [hi_conj, ← CQ.ofQ_mul, ← CQ.ofQ_mul]
            _ = CQ.ofQ (q12 * N.frobNuc * ωL * ωL * (crossCol n A d b * crossCol n A d b)) := by
                rw [CQ.one_mul]; congr 1; ac_rfl
        exact heq
      have hr2 : (fun b => MatCQ.frobInner (MatCQ.scale (CQ.iUnit * CQ.ofQ (ωL * crossCol n A d b)) (finKron N.hm (V4 d) (N.Iop b))) _) =
                 (fun b => CQ.ofQ (q12 * N.frobNuc * ωL * ωL * (crossCol n A d b * crossCol n A d b))) := funext hterm
      rw [hr2, sum3CQ_ofQ, ← sum3Q_mul_left]
    have hr1 : (fun d => MatCQ.frobInner (sum3M (fun b => MatCQ.scale (CQ.iUnit * CQ.ofQ (ωL * crossCol n A d b)) (finKron N.hm (V4 d) (N.Iop b)))) _) =
               (fun d => CQ.ofQ (q12 * N.frobNuc * ωL * ωL * sum3Q (fun b => crossCol n A d b * crossCol n A d b))) := funext hrow
    rw [hr1, sum3CQ_ofQ, ← sum3Q_mul_left]
  rw [hnorm_cross]
  congr 2
  rw [sum3Q_swap (fun d b => crossCol n A d b * crossCol n A d b)]
  have hfsq : frobSq3 A = sum3Q (fun b => sum3Q (fun a => A a b * A a b)) := sum3Q_swap _
  rw [hfsq]
  unfold crossCol quadForm3 normSq3
  unfold sum3Q
  dsimp only
  -- Rewrite columns directly without expanding q_b * q_b:
  have hc0 := cross_norm_sq_Q (n ⟨0, by omega⟩) (n ⟨1, by omega⟩) (n ⟨2, by omega⟩) (A ⟨0, by omega⟩ ⟨0, by omega⟩) (A ⟨1, by omega⟩ ⟨0, by omega⟩) (A ⟨2, by omega⟩ ⟨0, by omega⟩)
  have hc1 := cross_norm_sq_Q (n ⟨0, by omega⟩) (n ⟨1, by omega⟩) (n ⟨2, by omega⟩) (A ⟨0, by omega⟩ ⟨1, by omega⟩) (A ⟨1, by omega⟩ ⟨1, by omega⟩) (A ⟨2, by omega⟩ ⟨1, by omega⟩)
  have hc2 := cross_norm_sq_Q (n ⟨0, by omega⟩) (n ⟨1, by omega⟩) (n ⟨2, by omega⟩) (A ⟨0, by omega⟩ ⟨2, by omega⟩) (A ⟨1, by omega⟩ ⟨2, by omega⟩) (A ⟨2, by omega⟩ ⟨2, by omega⟩)
  have sum_diff3 : ∀ x0 x1 x2 y0 y1 y2 : Q,
      (x0 - y0) + ((x1 - y1) + (x2 - y2)) = (x0 + (x1 + x2)) - (y0 + (y1 + y2)) := by
    intro x0 x1 x2 y0 y1 y2
    simp only [Q.sub_eq_add_neg, Q.neg_add]; ac_rfl
  have fact : ∀ s v0 v1 v2 : Q, s * v0 + (s * v1 + s * v2) = s * (v0 + (v1 + v2)) := by
    intro s v0 v1 v2; rw [Q.left_distrib, Q.left_distrib]
  rw [hc0, hc1, hc2, sum_diff3, fact]

private theorem cq_conj_conj (a : CQ) : a.conj.conj = a := by
  apply CQ.ext <;> simp [CQ.conj, Q.neg_neg]

private theorem frobInner_add_orthog {d : Nat} (A B : Mat d CQ) (hAB : MatCQ.frobInner A B = 0) :
    MatCQ.frobInner (MatCQ.add A B) (MatCQ.add A B) =
    MatCQ.frobInner A A + MatCQ.frobInner B B := by
  have hBA : MatCQ.frobInner B A = 0 := by
    have hconj : (MatCQ.frobInner A B).conj = MatCQ.frobInner B A := by
      rw [MatCQ.frobInner_eq_frobDot, MatCQ.frobInner_eq_frobDot]
      unfold MatCQ.frobDot
      rw [SumFin.cq_conj]
      congr 1; funext i
      rw [SumFin.cq_conj]
      congr 1; funext j
      rw [CQ.conj_mul, cq_conj_conj, CQ.mul_comm]
    rw [← hconj, hAB]
    apply CQ.ext <;> simp [Q.neg_zero]
  rw [MatCQ.frobInner_add_left, MatCQ.frobInner_add_right, MatCQ.frobInner_add_right,
      hAB, hBA, CQ.add_zero, CQ.zero_add]

theorem M4_diff_unified (ωL : Q) (n n0 : Fin 3 → Q) (hn : normSq3 n = 1) (hn0 : normSq3 n0 = 1)
    (A : Fin 3 → Fin 3 → Q) (J : Q) :
    let C2 := fun dir => MatCQ.comm (H_RP N ωL dir A J) (MatCQ.comm (H_RP N ωL dir A J) (PS N))
    (MatCQ.frobInner (C2 n) (C2 n)).re / Q.ofInt m -
    (MatCQ.frobInner (C2 n0) (C2 n0)).re / Q.ofInt m =
    q12 * (N.frobNuc / Q.ofInt m) * ωL * ωL * (quadForm3 A n0 - quadForm3 A n) := by
  dsimp only
  let C1 := C1_HF N A
  have hC1 : ∀ dir, MatCQ.comm (H_RP N ωL dir A J) (PS N) = C1 := fun dir => comm_H_RP_PS N ωL dir A J
  have hC2 : ∀ dir, MatCQ.comm (H_RP N ωL dir A J) C1 =
      MatCQ.add (C2_Z N ωL dir A) (MatCQ.comm (MatCQ.add (H_HF N A) (H_ex N J)) C1) := by
    intro dir
    unfold H_RP
    rw [MatCQ.comm_add_left, comm_HZ_C1_eq N ωL dir A]
  have hpyth : ∀ dir,
      MatCQ.frobInner (MatCQ.comm (H_RP N ωL dir A J) (MatCQ.comm (H_RP N ωL dir A J) (PS N)))
                      (MatCQ.comm (H_RP N ωL dir A J) (MatCQ.comm (H_RP N ωL dir A J) (PS N))) =
      CQ.ofQ (q12 * N.frobNuc * ωL * ωL * (normSq3 dir * frobSq3 A - quadForm3 A dir)) +
      MatCQ.frobInner (MatCQ.comm (MatCQ.add (H_HF N A) (H_ex N J)) C1)
                      (MatCQ.comm (MatCQ.add (H_HF N A) (H_ex N J)) C1) := by
    intro dir
    rw [hC1 dir, hC2 dir, frobInner_add_orthog _ _ (C2_Z_orthog_int N ωL dir A J), C2_Z_normSq]
  rw [hpyth n, hpyth n0]
  simp only [CQ.add_re, CQ.ofQ_re, hn, hn0, Q.one_mul]
  rw [Q.add_div, Q.add_div]
  let Rint := (MatCQ.frobInner (MatCQ.comm (MatCQ.add (H_HF N A) (H_ex N J)) C1)
                               (MatCQ.comm (MatCQ.add (H_HF N A) (H_ex N J)) C1)).re / Q.ofInt m
  have hsub : ∀ u v : Q, (u + Rint) - (v + Rint) = u - v := by
    intro u v
    rw [Q.sub_eq_add_neg, Q.neg_add]
    calc (u + Rint) + (-v + -Rint) = (u + -v) + (Rint + -Rint) := by ac_rfl
      _ = u - v := by rw [Q.add_right_neg, Q.add_zero]; rfl
  change (_ + Rint) - (_ + Rint) = _
  rw [hsub]
  have hfactor : ∀ x y z : Q, (x - y) - (x - z) = z - y := by
    intro x y z; simp only [Q.sub_eq_add_neg, Q.neg_add, Q.neg_neg]
    calc x + -y + (-x + z) = (x + -x) + (z + -y) := by ac_rfl
      _ = z + -y := by rw [Q.add_right_neg, Q.zero_add]
  have hf :
      (q12 * N.frobNuc * ωL * ωL * (frobSq3 A - quadForm3 A n)) / Q.ofInt m -
      (q12 * N.frobNuc * ωL * ωL * (frobSq3 A - quadForm3 A n0)) / Q.ofInt m =
      (q12 * (N.frobNuc / Q.ofInt m) * ωL * ωL) * ((frobSq3 A - quadForm3 A n) - (frobSq3 A - quadForm3 A n0)) := by
    change (q12 * N.frobNuc * ωL * ωL * (frobSq3 A - quadForm3 A n)) * Q.inv (Q.ofInt m) -
           (q12 * N.frobNuc * ωL * ωL * (frobSq3 A - quadForm3 A n0)) * Q.inv (Q.ofInt m) = _
    have hc1 : (q12 * N.frobNuc * ωL * ωL * (frobSq3 A - quadForm3 A n)) * Q.inv (Q.ofInt m) =
               q12 * (N.frobNuc * Q.inv (Q.ofInt m)) * ωL * ωL * (frobSq3 A - quadForm3 A n) := by ac_rfl
    have hc2 : (q12 * N.frobNuc * ωL * ωL * (frobSq3 A - quadForm3 A n0)) * Q.inv (Q.ofInt m) =
               q12 * (N.frobNuc * Q.inv (Q.ofInt m)) * ωL * ωL * (frobSq3 A - quadForm3 A n0) := by ac_rfl
    rw [hc1, hc2, Q.sub_eq_add_neg, Q.sub_eq_add_neg]
    change q12 * (N.frobNuc / Q.ofInt m) * ωL * ωL * (frobSq3 A - quadForm3 A n) +
           -(q12 * (N.frobNuc / Q.ofInt m) * ωL * ωL * (frobSq3 A - quadForm3 A n0)) =
           q12 * (N.frobNuc / Q.ofInt m) * ωL * ωL *
             ((frobSq3 A - quadForm3 A n) + -(frobSq3 A - quadForm3 A n0))
    rw [← Q.mul_neg, ← Q.left_distrib]
  rw [hf, hfactor]

/-! ### Concrete 8x8 (I = 1/2) & 12x12 (I = 1, 14N) Connections & Axial Fourth-Moment Corollaries -/

def axialA (Ap Al : Q) : Fin 3 → Fin 3 → Q
  | ⟨0, _⟩, ⟨0, _⟩ => Ap
  | ⟨1, _⟩, ⟨1, _⟩ => Ap
  | ⟨2, _⟩, ⟨2, _⟩ => Al
  | _, _ => 0

def xzDir (s c : Q) : Fin 3 → Q
  | ⟨0, _⟩ => s
  | ⟨2, _⟩ => c
  | _ => 0

private theorem axial_quad_xz (Ap Al s c : Q) :
    quadForm3 (axialA Ap Al) (xzDir s c) = Ap * Ap * (s * s) + Al * Al * (c * c) := by
  unfold quadForm3 sum3Q axialA xzDir
  simp only [Q.zero_mul, Q.mul_zero, Q.add_zero, Q.zero_add]
  have h1 : (s * Ap) * (s * Ap) = Ap * Ap * (s * s) := by ac_rfl
  have h2 : (c * Al) * (c * Al) = Al * Al * (c * c) := by ac_rfl
  rw [h1, h2]

theorem axial_diff_quad (Ap Al s c : Q) (hsc : s * s + c * c = 1) :
    quadForm3 (axialA Ap Al) (xzDir 0 1) - quadForm3 (axialA Ap Al) (xzDir s c) =
    (Al * Al - Ap * Ap) * (s * s) := by
  rw [axial_quad_xz Ap Al 0 1, axial_quad_xz Ap Al s c]
  simp only [Q.zero_mul, Q.mul_zero, Q.one_mul, Q.zero_add]
  have hc2 : c * c = 1 - s * s := by
    have hadd := congrArg (fun x => x + -(s * s)) hsc
    dsimp only at hadd
    have hl : s * s + c * c + -(s * s) = c * c := by
      calc s * s + c * c + -(s * s) = c * c + (s * s + -(s * s)) := by ac_rfl
        _ = c * c := by rw [Q.add_right_neg, Q.add_zero]
    rw [hl] at hadd; exact hadd
  rw [hc2]
  simp only [Q.sub_eq_add_neg, Q.left_distrib, Q.right_distrib, Q.mul_one, Q.mul_neg, Q.neg_mul, Q.neg_add, Q.neg_neg]
  calc Al * Al + (-(Ap * Ap * (s * s)) + (-(Al * Al) + Al * Al * (s * s)))
      = (Al * Al + -(Al * Al)) + (Al * Al * (s * s) + -(Ap * Ap * (s * s))) := by ac_rfl
    _ = Al * Al * (s * s) + -(Ap * Ap * (s * s)) := by rw [Q.add_right_neg, Q.zero_add]

theorem PS_8_eq_explicit : PS nucHalf = liftMat q14 (toFinZ 8 fourPS8) := by
  unfold PS PS4 nucHalf fourPS8
  rw [toFinZ_kronZ 4 2 (by omega) fourPS4 id2 fourPS4_sq id2_sq,
      ← Q.mul_one q14,
      Kron.liftMat_finKron (by omega) q14 1 (toFinZ 4 fourPS4) (toFinZ 2 id2),
      liftMat_id2, Q.mul_one]

theorem PS_12_eq_explicit : PS nucOne = liftMat q14 (toFinZ 12 fourPS12) := by
  unfold PS PS4 nucOne fourPS12
  rw [toFinZ_kronZ 4 3 (by omega) fourPS4 id3 fourPS4_sq id3_sq,
      ← Q.mul_one q14,
      Kron.liftMat_finKron (by omega) q14 1 (toFinZ 4 fourPS4) (toFinZ 3 id3),
      liftMat_id3, Q.mul_one]

theorem M4_8_axial_diff (ωL s c Ap Al J : Q) (hsc : s * s + c * c = 1) :
    let C2 := fun dir => MatCQ.comm (H_RP nucHalf ωL dir (axialA Ap Al) J)
                                    (MatCQ.comm (H_RP nucHalf ωL dir (axialA Ap Al) J) (PS nucHalf))
    (MatCQ.frobInner (C2 (xzDir s c)) (C2 (xzDir s c))).re / Q.ofInt 2 -
    (MatCQ.frobInner (C2 (xzDir 0 1)) (C2 (xzDir 0 1))).re / Q.ofInt 2 =
    q18 * ωL * ωL * (Al * Al - Ap * Ap) * (s * s) := by
  dsimp only
  have hn : normSq3 (xzDir s c) = 1 := by
    unfold normSq3 sum3Q xzDir
    simp only [Q.zero_mul, Q.add_zero, Q.zero_add]; exact hsc
  have hn0 : normSq3 (xzDir 0 1) = 1 := by
    unfold normSq3 sum3Q xzDir
    simp only [Q.zero_mul, Q.one_mul, Q.add_zero, Q.zero_add]
  have hm := M4_diff_unified nucHalf ωL (xzDir s c) (xzDir 0 1) hn hn0 (axialA Ap Al) J
  dsimp only at hm
  rw [axial_diff_quad Ap Al s c hsc] at hm
  have hm2 : (MatCQ.frobInner (MatCQ.comm (H_RP nucHalf ωL (xzDir s c) (axialA Ap Al) J)
                                (MatCQ.comm (H_RP nucHalf ωL (xzDir s c) (axialA Ap Al) J) (PS nucHalf)))
                              (MatCQ.comm (H_RP nucHalf ωL (xzDir s c) (axialA Ap Al) J)
                                (MatCQ.comm (H_RP nucHalf ωL (xzDir s c) (axialA Ap Al) J) (PS nucHalf)))).re / Q.ofInt 2 -
             (MatCQ.frobInner (MatCQ.comm (H_RP nucHalf ωL (xzDir 0 1) (axialA Ap Al) J)
                                (MatCQ.comm (H_RP nucHalf ωL (xzDir 0 1) (axialA Ap Al) J) (PS nucHalf)))
                              (MatCQ.comm (H_RP nucHalf ωL (xzDir 0 1) (axialA Ap Al) J)
                                (MatCQ.comm (H_RP nucHalf ωL (xzDir 0 1) (axialA Ap Al) J) (PS nucHalf)))).re / Q.ofInt 2 =
             q12 * (q12 / Q.ofInt 2) * ωL * ωL * ((Al * Al - Ap * Ap) * (s * s)) := hm
  rw [hm2, q12_mul_q14_mul_q12]
  ac_rfl

theorem M4_12_axial_diff (ωL s c Ap Al J : Q) (hsc : s * s + c * c = 1) :
    let C2 := fun dir => MatCQ.comm (H_RP nucOne ωL dir (axialA Ap Al) J)
                                    (MatCQ.comm (H_RP nucOne ωL dir (axialA Ap Al) J) (PS nucOne))
    (MatCQ.frobInner (C2 (xzDir s c)) (C2 (xzDir s c))).re / Q.ofInt 3 -
    (MatCQ.frobInner (C2 (xzDir 0 1)) (C2 (xzDir 0 1))).re / Q.ofInt 3 =
    q13 * ωL * ωL * (Al * Al - Ap * Ap) * (s * s) := by
  dsimp only
  have hn : normSq3 (xzDir s c) = 1 := by
    unfold normSq3 sum3Q xzDir
    simp only [Q.zero_mul, Q.add_zero, Q.zero_add]; exact hsc
  have hn0 : normSq3 (xzDir 0 1) = 1 := by
    unfold normSq3 sum3Q xzDir
    simp only [Q.zero_mul, Q.one_mul, Q.add_zero, Q.zero_add]
  have hm := M4_diff_unified nucOne ωL (xzDir s c) (xzDir 0 1) hn hn0 (axialA Ap Al) J
  dsimp only at hm
  rw [axial_diff_quad Ap Al s c hsc] at hm
  have hm2 : (MatCQ.frobInner (MatCQ.comm (H_RP nucOne ωL (xzDir s c) (axialA Ap Al) J)
                                (MatCQ.comm (H_RP nucOne ωL (xzDir s c) (axialA Ap Al) J) (PS nucOne)))
                              (MatCQ.comm (H_RP nucOne ωL (xzDir s c) (axialA Ap Al) J)
                                (MatCQ.comm (H_RP nucOne ωL (xzDir s c) (axialA Ap Al) J) (PS nucOne)))).re / Q.ofInt 3 -
             (MatCQ.frobInner (MatCQ.comm (H_RP nucOne ωL (xzDir 0 1) (axialA Ap Al) J)
                                (MatCQ.comm (H_RP nucOne ωL (xzDir 0 1) (axialA Ap Al) J) (PS nucOne)))
                              (MatCQ.comm (H_RP nucOne ωL (xzDir 0 1) (axialA Ap Al) J)
                                (MatCQ.comm (H_RP nucOne ωL (xzDir 0 1) (axialA Ap Al) J) (PS nucOne)))).re / Q.ofInt 3 =
             q12 * (Q.ofInt 2 / Q.ofInt 3) * ωL * ωL * ((Al * Al - Ap * Ap) * (s * s)) := hm
  rw [hm2, q12_mul_q23_eq_q13]
  ac_rfl

theorem M2_8_canonical :
    let C1 := MatCQ.comm (H_RP nucHalf (Q.frac 7 5) (xzDir 1 0) (axialA q12 (Q.ofInt 5)) (Q.frac 3 20)) (PS nucHalf)
    (MatCQ.frobInner C1 C1).re / Q.ofInt 2 = Q.frac 51 16 := by
  dsimp only
  have hm := M2_norm_exact nucHalf (Q.frac 7 5) (xzDir 1 0) (axialA q12 (Q.ofInt 5)) (Q.frac 3 20)
  have hm2 : (MatCQ.frobInner (MatCQ.comm (H_RP nucHalf (Q.frac 7 5) (xzDir 1 0) (axialA q12 (Q.ofInt 5)) (Q.frac 3 20)) (PS nucHalf))
                              (MatCQ.comm (H_RP nucHalf (Q.frac 7 5) (xzDir 1 0) (axialA q12 (Q.ofInt 5)) (Q.frac 3 20)) (PS nucHalf))).re / Q.ofInt 2 =
             q12 * (q12 / Q.ofInt 2) * sum3Q (fun a => sum3Q (fun b => axialA q12 (Q.ofInt 5) a b * axialA q12 (Q.ofInt 5) a b)) := hm
  rw [hm2, q12_mul_q14_mul_q12]
  unfold sum3Q axialA
  simp only [Q.zero_mul, Q.add_zero, Q.zero_add]
  exact qrel_eq _ _ (by decide)

theorem M4_8_canonical_90deg :
    let ωL := Q.frac 7 5
    let Ap := q12
    let Al := Q.ofInt 5
    let J := Q.frac 3 20
    let C2 := fun dir => MatCQ.comm (H_RP nucHalf ωL dir (axialA Ap Al) J)
                                    (MatCQ.comm (H_RP nucHalf ωL dir (axialA Ap Al) J) (PS nucHalf))
    (MatCQ.frobInner (C2 (xzDir 1 0)) (C2 (xzDir 1 0))).re / Q.ofInt 2 -
    (MatCQ.frobInner (C2 (xzDir 0 1)) (C2 (xzDir 0 1))).re / Q.ofInt 2 = Q.frac 4851 800 := by
  dsimp only
  have hsc : (1 : Q) * 1 + 0 * 0 = 1 := by simp [Q.zero_mul, Q.one_mul, Q.add_zero]
  rw [M4_8_axial_diff (Q.frac 7 5) 1 0 q12 (Q.ofInt 5) (Q.frac 3 20) hsc]
  exact qrel_eq _ _ (by decide)

theorem M4_12_canonical_90deg :
    let ωL := Q.frac 7 5
    let Ap := q12
    let Al := Q.ofInt 5
    let J := Q.frac 3 20
    let C2 := fun dir => MatCQ.comm (H_RP nucOne ωL dir (axialA Ap Al) J)
                                    (MatCQ.comm (H_RP nucOne ωL dir (axialA Ap Al) J) (PS nucOne))
    (MatCQ.frobInner (C2 (xzDir 1 0)) (C2 (xzDir 1 0))).re / Q.ofInt 3 -
    (MatCQ.frobInner (C2 (xzDir 0 1)) (C2 (xzDir 0 1))).re / Q.ofInt 3 = Q.frac 1617 100 := by
  dsimp only
  have hsc : (1 : Q) * 1 + 0 * 0 = 1 := by simp [Q.zero_mul, Q.one_mul, Q.add_zero]
  rw [M4_12_axial_diff (Q.frac 7 5) 1 0 q12 (Q.ofInt 5) (Q.frac 3 20) hsc]
  exact qrel_eq _ _ (by decide)

end UnifiedRP

end RadicalPair4A

/-! ### Section 4B: Multi-Nucleus Tensor-Product Spin Models & 36x36 FAD^(.-) Theory -/

section MultiNucleus4B

open SpinMatrices

private theorem cq_conj_one : (1 : CQ).conj = 1 := by
  apply CQ.ext <;> exact qrel_eq _ _ (by decide)

private theorem cq_conj_zero : (0 : CQ).conj = 0 := by
  apply CQ.ext <;> exact qrel_eq _ _ (by decide)

private theorem frobInner_id_right {d : Nat} (A : Mat d CQ) :
    MatCQ.frobInner A MatCQ.id = (MatCQ.trace A).conj := by
  unfold MatCQ.frobInner
  rw [Kron.mul_id_id]
  unfold MatCQ.trace MatCQ.conjT
  rw [SumFin.cq_conj]

private theorem frobInner_id_left {d : Nat} (A : Mat d CQ) :
    MatCQ.frobInner MatCQ.id A = MatCQ.trace A := by
  have hid : MatCQ.conjT (MatCQ.id : Mat d CQ) = MatCQ.id := by
    funext i j
    unfold MatCQ.conjT MatCQ.id
    by_cases hij : j = i
    · subst hij; simp [cq_conj_one]
    · have hne : i ≠ j := fun h => hij h.symm
      simp [hij, hne, cq_conj_zero]
  unfold MatCQ.frobInner
  rw [hid, Kron.id_mul]

private theorem trace_kron_eq {d1 d2 : Nat} (hd2 : 0 < d2) (A : Mat d1 CQ) (B : Mat d2 CQ) :
    MatCQ.trace (finKron hd2 A B) = MatCQ.trace A * MatCQ.trace B := Kron.trace hd2 A B

private theorem finKron_add_left {d1 d2 : Nat} (hd2 : 0 < d2) (A1 A2 : Mat d1 CQ) (B : Mat d2 CQ) :
    finKron hd2 (MatCQ.add A1 A2) B = MatCQ.add (finKron hd2 A1 B) (finKron hd2 A2 B) := by
  funext i j; unfold finKron MatCQ.add; exact CQ.right_distrib _ _ _

private theorem finKron_add_right {d1 d2 : Nat} (hd2 : 0 < d2) (A : Mat d1 CQ) (B1 B2 : Mat d2 CQ) :
    finKron hd2 A (MatCQ.add B1 B2) = MatCQ.add (finKron hd2 A B1) (finKron hd2 A B2) := by
  funext i j; unfold finKron MatCQ.add; exact CQ.left_distrib _ _ _

private theorem ofInt_pos_nat {n : Nat} (hn : 0 < n) : (0 : Q) < Q.ofInt n := by
  constructor
  · change (0 : Int) * QRaw.den ⟨n, 0⟩ ≤ (n : Int) * QRaw.den ⟨0, 0⟩
    simp [QRaw.den]; omega
  · intro heq
    have hr : QRel ⟨0, 0⟩ ⟨n, 0⟩ := Quotient.exact heq
    simp [QRel, QRaw.den] at hr
    omega

structure ZeroTraceNuc (m : Nat) where
  nuc : NucSpec m
  trace_zero : ∀ a : Fin 3, MatCQ.trace (nuc.Iop a) = 0

def nucHalfZT : ZeroTraceNuc 2 where
  nuc := nucHalf
  trace_zero := by
    intro a
    change MatCQ.trace (liftMat q12 (toFinZ 2 (match a.val with | 0 => sx2 | 1 => sy2 | _ => sz2))) = 0
    rw [Lift.liftMat_trace, ← matTraceZ_eq]
    have htr : matTraceZ 2 (match a.val with | 0 => sx2 | 1 => sy2 | _ => sz2) = z0 := by
      decide +revert
    rw [htr]
    change CQ.ofQ q12 * (0 : CQ) = 0
    exact CQ.mul_zero _

def nucOneZT : ZeroTraceNuc 3 where
  nuc := nucOne
  trace_zero := by
    intro a
    change MatCQ.trace (liftMat 1 (toFinZ 3 (match a.val with | 0 => ix3 | 1 => iy3 | _ => iz3))) = 0
    rw [Lift.liftMat_trace, ← matTraceZ_eq]
    have htr : matTraceZ 3 (match a.val with | 0 => ix3 | 1 => iy3 | _ => iz3) = z0 := by
      decide +revert
    rw [htr]
    change CQ.ofQ 1 * (0 : CQ) = 0
    exact CQ.mul_zero _

private theorem matCQ_mul_zero {d : Nat} (A : Mat d CQ) : MatCQ.mul A MatCQ.zero = MatCQ.zero := by
  funext i j; simp only [MatCQ.mul, MatCQ.zero, CQ.mul_zero]; exact SumFin.cq_eq_zero _ (fun _ => rfl)

private theorem matCQ_zero_mul {d : Nat} (B : Mat d CQ) : MatCQ.mul MatCQ.zero B = MatCQ.zero := by
  funext i j; simp only [MatCQ.mul, MatCQ.zero, CQ.zero_mul]; exact SumFin.cq_eq_zero _ (fun _ => rfl)

private theorem matCQ_comm_zero_left {d : Nat} (B : Mat d CQ) : MatCQ.comm MatCQ.zero B = MatCQ.zero := by
  unfold MatCQ.comm; rw [matCQ_zero_mul, matCQ_mul_zero]
  funext i j; simp [MatCQ.sub, CQ.sub, CQ.zero_add]; apply CQ.ext <;> exact qrel_eq _ _ (by decide)

private theorem matCQ_comm_zero_right {d : Nat} (A : Mat d CQ) : MatCQ.comm A MatCQ.zero = MatCQ.zero := by
  unfold MatCQ.comm; rw [matCQ_mul_zero, matCQ_zero_mul]
  funext i j; simp [MatCQ.sub, CQ.sub, CQ.zero_add]; apply CQ.ext <;> exact qrel_eq _ _ (by decide)

private theorem matCQ_frobInner_zero_left {d : Nat} (B : Mat d CQ) : MatCQ.frobInner MatCQ.zero B = 0 := by
  rw [MatCQ.frobInner_eq_frobDot]; unfold MatCQ.frobDot MatCQ.zero
  simp only [cq_conj_zero, CQ.zero_mul]; exact SumFin.cq_eq_zero _ (fun _ => SumFin.cq_eq_zero _ (fun _ => rfl))

private theorem matCQ_frobInner_zero_right {d : Nat} (A : Mat d CQ) : MatCQ.frobInner A MatCQ.zero = 0 := by
  rw [MatCQ.frobInner_eq_frobDot]; unfold MatCQ.frobDot MatCQ.zero
  simp only [CQ.mul_zero]; exact SumFin.cq_eq_zero _ (fun _ => SumFin.cq_eq_zero _ (fun _ => rfl))

def sumFinM {K d : Nat} (f : Fin K → Mat d CQ) : Mat d CQ :=
  match K with
  | 0 => MatCQ.zero
  | K' + 1 => MatCQ.add (f 0) (sumFinM (fun k : Fin K' => f k.succ))

def sumFinQ (K : Nat) (f : Fin K → Q) : Q :=
  match K with
  | 0 => 0
  | K' + 1 => f 0 + sumFinQ K' (fun k : Fin K' => f k.succ)

def sumFinCQ (K : Nat) (f : Fin K → CQ) : CQ :=
  match K with
  | 0 => 0
  | K' + 1 => f 0 + sumFinCQ K' (fun k : Fin K' => f k.succ)

theorem sumFinM_comm_right {K d : Nat} (f : Fin K → Mat d CQ) (B : Mat d CQ) :
    MatCQ.comm (sumFinM f) B = sumFinM (fun k => MatCQ.comm (f k) B) := by
  induction K with
  | zero => exact matCQ_comm_zero_left B
  | succ K' ih =>
    simp only [sumFinM, MatCQ.comm_add_left, ih (fun k => f k.succ)]

theorem sumFinM_comm_left {K d : Nat} (A : Mat d CQ) (f : Fin K → Mat d CQ) :
    MatCQ.comm A (sumFinM f) = sumFinM (fun k => MatCQ.comm A (f k)) := by
  induction K with
  | zero => exact matCQ_comm_zero_right A
  | succ K' ih =>
    simp only [sumFinM, MatCQ.comm_add_right, ih (fun k => f k.succ)]

theorem sumFinM_frobInner_left {K d : Nat} (f : Fin K → Mat d CQ) (B : Mat d CQ) :
    MatCQ.frobInner (sumFinM f) B = sumFinCQ K (fun k => MatCQ.frobInner (f k) B) := by
  induction K with
  | zero => exact matCQ_frobInner_zero_left B
  | succ K' ih =>
    simp only [sumFinM, sumFinCQ, MatCQ.frobInner_add_left, ih (fun k => f k.succ)]

theorem sumFinM_frobInner_right {K d : Nat} (A : Mat d CQ) (f : Fin K → Mat d CQ) :
    MatCQ.frobInner A (sumFinM f) = sumFinCQ K (fun k => MatCQ.frobInner A (f k)) := by
  induction K with
  | zero => exact matCQ_frobInner_zero_right A
  | succ K' ih =>
    simp only [sumFinM, sumFinCQ, MatCQ.frobInner_add_right, ih (fun k => f k.succ)]

theorem sumFinM_zero {K d : Nat} (f : Fin K → Mat d CQ) (h : ∀ k, f k = MatCQ.zero) :
    sumFinM f = MatCQ.zero := by
  induction K with
  | zero => rfl
  | succ K' ih =>
    simp only [sumFinM, h 0, ih (fun k => f k.succ) (fun k => h k.succ), MatCQ.zero_add]

theorem sumFinCQ_zero (K : Nat) (f : Fin K → CQ) (h : ∀ k, f k = 0) : sumFinCQ K f = 0 := by
  induction K with
  | zero => rfl
  | succ K' ih =>
    simp only [sumFinCQ, h 0, ih (fun k => f k.succ) (fun k => h k.succ), CQ.zero_add]

theorem sumFinCQ_ofQ (K : Nat) (f : Fin K → Q) :
    sumFinCQ K (fun k => CQ.ofQ (f k)) = CQ.ofQ (sumFinQ K f) := by
  induction K with
  | zero => rfl
  | succ K' ih =>
    simp only [sumFinCQ, sumFinQ, CQ.ofQ_add, ih (fun k => f k.succ)]

theorem sumFinQ_mul_left (c : Q) (K : Nat) (f : Fin K → Q) :
    sumFinQ K (fun k => c * f k) = c * sumFinQ K f := by
  induction K with
  | zero => exact (Q.mul_zero c).symm
  | succ K' ih =>
    simp only [sumFinQ, Q.left_distrib, ih (fun k => f k.succ)]

theorem sumFinQ_sub (K : Nat) (f g : Fin K → Q) :
    sumFinQ K f - sumFinQ K g = sumFinQ K (fun k => f k - g k) := by
  induction K with
  | zero => exact qrel_eq _ _ (by decide)
  | succ K' ih =>
    simp only [sumFinQ]
    have hsub := ih (fun k => f k.succ) (fun k => g k.succ)
    rw [Q.sub_eq_add_neg, Q.neg_add, ← Q.sub_eq_add_neg, Q.sub_eq_add_neg (f 0),
        Q.sub_eq_add_neg (sumFinQ K' _)] at *
    rw [← hsub, Q.sub_eq_add_neg]
    ac_rfl

theorem sumFinQ_zero (K : Nat) (f : Fin K → Q) (h : ∀ k, f k = 0) : sumFinQ K f = 0 := by
  induction K with
  | zero => rfl
  | succ K' ih =>
    simp only [sumFinQ, h 0, ih (fun k => f k.succ) (fun k => h k.succ), Q.zero_add]

theorem sumFinQ_add (K : Nat) (f g : Fin K → Q) :
    sumFinQ K (fun k => f k + g k) = sumFinQ K f + sumFinQ K g := by
  induction K with
  | zero => exact (Q.zero_add 0).symm
  | succ K' ih =>
    simp only [sumFinQ, ih (fun k => f k.succ) (fun k => g k.succ)]
    ac_rfl

theorem sumFinM_frobInner_self_orthog {K d : Nat} (f : Fin K → Mat d CQ)
    (horth : ∀ k k' : Fin K, k ≠ k' → MatCQ.frobInner (f k) (f k') = 0) :
    MatCQ.frobInner (sumFinM f) (sumFinM f) = sumFinCQ K (fun k => MatCQ.frobInner (f k) (f k)) := by
  induction K with
  | zero => exact matCQ_frobInner_zero_left MatCQ.zero
  | succ K' ih =>
    simp only [sumFinM, sumFinCQ, MatCQ.frobInner_add_left, MatCQ.frobInner_add_right]
    have hcross1 : MatCQ.frobInner (f 0) (sumFinM (fun k : Fin K' => f k.succ)) = 0 := by
      rw [sumFinM_frobInner_right]
      exact sumFinCQ_zero K' _ (fun k => horth 0 k.succ (Fin.succ_ne_zero k).symm)
    have hcross2 : MatCQ.frobInner (sumFinM (fun k : Fin K' => f k.succ)) (f 0) = 0 := by
      rw [sumFinM_frobInner_left]
      exact sumFinCQ_zero K' _ (fun k => horth k.succ 0 (Fin.succ_ne_zero k))
    have htail := ih (fun k => f k.succ) (fun j j' hne => horth j.succ j'.succ (fun heq => hne (Fin.succ_inj.mp heq)))
    rw [hcross1, hcross2, htail, CQ.add_zero, CQ.zero_add]

structure MultiNucSpec (K dNuc : Nat) where
  hd : 0 < dNuc
  Iop : Fin K → Fin 3 → Mat dNuc CQ
  weight : Fin K → Q
  trace_zero : ∀ k : Fin K, ∀ a : Fin 3, MatCQ.trace (Iop k a) = 0
  frob_orthog : ∀ k k' : Fin K, ∀ a b : Fin 3,
    MatCQ.frobInner (Iop k a) (Iop k' b) =
      if k = k' ∧ a = b then CQ.ofQ (weight k * Q.ofInt dNuc) else 0
  comm_cross : ∀ k k' k'' : Fin K, k' ≠ k'' → ∀ b r s : Fin 3,
    MatCQ.mul (Iop k' r) (Iop k'' s) = MatCQ.mul (Iop k'' s) (Iop k' r) ∧
    MatCQ.frobInner (Iop k b) (MatCQ.mul (Iop k' r) (Iop k'' s)) = 0
  same_other_orthog : ∀ k k' : Fin K, k ≠ k' → ∀ b r s : Fin 3,
    MatCQ.frobInner (Iop k b) (MatCQ.mul (Iop k' r) (Iop k' s)) = 0
  same_anticomm_orthog : ∀ k : Fin K, ∀ b r s : Fin 3,
    MatCQ.frobInner (Iop k b) (MatCQ.add (MatCQ.mul (Iop k r) (Iop k s)) (MatCQ.mul (Iop k s) (Iop k r))) = 0

def MultiNucSpec.empty : MultiNucSpec 0 1 where
  hd := by omega
  Iop := fun k => Fin.elim0 k
  weight := fun k => Fin.elim0 k
  trace_zero := fun k => Fin.elim0 k
  frob_orthog := fun k => Fin.elim0 k
  comm_cross := fun _ k' => Fin.elim0 k'
  same_other_orthog := fun k => Fin.elim0 k
  same_anticomm_orthog := fun k => Fin.elim0 k

def MultiNucSpec.cons {m K d : Nat} (zn : ZeroTraceNuc m) (M : MultiNucSpec K d) :
    MultiNucSpec (K + 1) (m * d) where
  hd := Nat.mul_pos zn.nuc.hm M.hd
  Iop := Fin.cases (fun a => finKron M.hd (zn.nuc.Iop a) MatCQ.id)
                   (fun j a => finKron M.hd MatCQ.id (M.Iop j a))
  weight := Fin.cases (zn.nuc.frobNuc / Q.ofInt m) M.weight
  trace_zero := by
    intro k a
    cases k using Fin.cases with
    | zero =>
      simp only [Fin.cases_zero]
      rw [trace_kron_eq M.hd, zn.trace_zero a, CQ.zero_mul]
    | succ j =>
      simp only [Fin.cases_succ]
      rw [trace_kron_eq M.hd, M.trace_zero j a, CQ.mul_zero]
  frob_orthog := by
    intro k k' a b
    cases k using Fin.cases with
    | zero =>
      cases k' using Fin.cases with
      | zero =>
        simp only [Fin.cases_zero]
        rw [Kron.frobInner, zn.nuc.frob_exact a b, frobInner_id_left, trace_id]
        by_cases hab : a = b
        · simp only [hab, and_self, ↓reduceIte, ← CQ.ofQ_mul]
          congr 1
          have hmd : Q.ofInt (m * d : Nat) = Q.ofInt m * Q.ofInt d := by
            have hnat : ((m * d : Nat) : Int) = (m : Int) * (d : Int) := Int.natCast_mul m d
            rw [hnat, Q.ofInt_mul]
          have hmne : Q.ofInt m ≠ 0 := Q.ne_zero_of_pos (ofInt_pos_nat zn.nuc.hm)
          rw [hmd, ← Q.mul_assoc, Q.div_mul_cancel hmne]
        · simp [hab, CQ.zero_mul]
      | succ j' =>
        simp only [Fin.cases_zero, Fin.cases_succ]
        rw [Kron.frobInner, frobInner_id_right, zn.trace_zero a, cq_conj_zero, CQ.zero_mul]
        have hne : (0 : Fin (K + 1)) ≠ j'.succ := (Fin.succ_ne_zero j').symm
        simp [hne]
    | succ j =>
      cases k' using Fin.cases with
      | zero =>
        simp only [Fin.cases_zero, Fin.cases_succ]
        rw [Kron.frobInner, frobInner_id_left, zn.trace_zero b, CQ.zero_mul]
        simp [Fin.succ_ne_zero]
      | succ j' =>
        simp only [Fin.cases_succ]
        rw [Kron.frobInner, frobInner_id_left, trace_id, M.frob_orthog j j' a b]
        by_cases hjj : j = j' <;> by_cases hab : a = b
        · subst hjj; subst hab
          simp only [and_self, ↓reduceIte, ← CQ.ofQ_mul]
          congr 1
          have hmd : Q.ofInt (m * d : Nat) = Q.ofInt m * Q.ofInt d := by
            have hnat : ((m * d : Nat) : Int) = (m : Int) * (d : Int) := Int.natCast_mul m d
            rw [hnat, Q.ofInt_mul]
          rw [hmd]; ac_rfl
        · simp [hjj, hab, Fin.succ_inj, CQ.mul_zero]
        · simp [hjj, hab, Fin.succ_inj, CQ.mul_zero]
        · simp [hjj, hab, Fin.succ_inj, CQ.mul_zero]
  comm_cross := by
    intro k k' k'' hne b r s
    cases k' using Fin.cases with
    | zero =>
      cases k'' using Fin.cases with
      | zero => exact False.elim (hne rfl)
      | succ j'' =>
        simp only [Fin.cases_zero, Fin.cases_succ]
        rw [Kron.mul, Kron.mul, Kron.mul_id_id, Kron.id_mul, Kron.id_mul, Kron.mul_id_id]
        refine ⟨rfl, ?_⟩
        cases k using Fin.cases with
        | zero =>
          simp only [Fin.cases_zero]
          rw [Kron.frobInner, frobInner_id_left, M.trace_zero j'' s, CQ.mul_zero]
        | succ j =>
          simp only [Fin.cases_succ]
          rw [Kron.frobInner, frobInner_id_left, zn.trace_zero r, CQ.zero_mul]
    | succ j' =>
      cases k'' using Fin.cases with
      | zero =>
        simp only [Fin.cases_zero, Fin.cases_succ]
        rw [Kron.mul, Kron.mul, Kron.id_mul, Kron.mul_id_id, Kron.mul_id_id, Kron.id_mul]
        refine ⟨rfl, ?_⟩
        cases k using Fin.cases with
        | zero =>
          simp only [Fin.cases_zero]
          rw [Kron.frobInner, frobInner_id_left, M.trace_zero j' r, CQ.mul_zero]
        | succ j =>
          simp only [Fin.cases_succ]
          rw [Kron.frobInner, frobInner_id_left, zn.trace_zero s, CQ.zero_mul]
      | succ j'' =>
        have hne' : j' ≠ j'' := fun h => hne (congrArg Fin.succ h)
        simp only [Fin.cases_succ]
        rw [Kron.mul, Kron.mul, Kron.id_mul]
        cases k using Fin.cases with
        | zero =>
          simp only [Fin.cases_zero]
          refine ⟨congrArg (finKron M.hd MatCQ.id) (M.comm_cross j' j' j'' hne' b r s).1, ?_⟩
          rw [Kron.frobInner, frobInner_id_right, zn.trace_zero b, cq_conj_zero, CQ.zero_mul]
        | succ j =>
          simp only [Fin.cases_succ]
          have hmc := M.comm_cross j j' j'' hne' b r s
          refine ⟨congrArg (finKron M.hd MatCQ.id) hmc.1, ?_⟩
          rw [Kron.frobInner, hmc.2, CQ.mul_zero]
  same_other_orthog := by
    intro k k' hne b r s
    cases k using Fin.cases with
    | zero =>
      cases k' using Fin.cases with
      | zero => exact False.elim (hne rfl)
      | succ j' =>
        simp only [Fin.cases_zero, Fin.cases_succ]
        rw [Kron.mul, Kron.id_mul, Kron.frobInner, frobInner_id_right, zn.trace_zero b, cq_conj_zero, CQ.zero_mul]
    | succ j =>
      cases k' using Fin.cases with
      | zero =>
        simp only [Fin.cases_zero, Fin.cases_succ]
        rw [Kron.mul, Kron.mul_id_id, Kron.frobInner, frobInner_id_right, M.trace_zero j b, cq_conj_zero, CQ.mul_zero]
      | succ j' =>
        have hne' : j ≠ j' := fun h => hne (congrArg Fin.succ h)
        simp only [Fin.cases_succ]
        rw [Kron.mul, Kron.id_mul, Kron.frobInner, M.same_other_orthog j j' hne' b r s, CQ.mul_zero]
  same_anticomm_orthog := by
    intro k b r s
    cases k using Fin.cases with
    | zero =>
      simp only [Fin.cases_zero]
      rw [Kron.mul, Kron.mul, Kron.mul_id_id, ← finKron_add_left M.hd, Kron.frobInner,
          zn.nuc.anticomm_orthog b r s, CQ.zero_mul]
    | succ j =>
      simp only [Fin.cases_succ]
      rw [Kron.mul, Kron.mul, Kron.id_mul, ← finKron_add_right M.hd, Kron.frobInner,
          M.same_anticomm_orthog j b r s, CQ.mul_zero]

def fadTwo14N : MultiNucSpec 2 9 :=
  MultiNucSpec.cons nucOneZT (MultiNucSpec.cons nucOneZT MultiNucSpec.empty)

namespace MultiRP

variable {K dNuc : Nat} (M : MultiNucSpec K dNuc)

def PS : Mat (4 * dNuc) CQ := finKron M.hd PS4 MatCQ.id
def PT : Mat (4 * dNuc) CQ := finKron M.hd PT4 MatCQ.id

def H_Z (ωL : Q) (n : Fin 3 → Q) : Mat (4 * dNuc) CQ :=
  sum3M (fun g => MatCQ.scale (CQ.ofQ (ωL * n g)) (finKron M.hd (Z4 g) MatCQ.id))

def H_ex (J : Q) : Mat (4 * dNuc) CQ :=
  MatCQ.scale (CQ.ofQ J) (finKron M.hd Hex4 MatCQ.id)

def H_HF (A : Fin K → Fin 3 → Fin 3 → Q) : Mat (4 * dNuc) CQ :=
  sumFinM (fun k => sum3M (fun g => sum3M (fun r =>
    MatCQ.scale (CQ.ofQ (A k g r)) (finKron M.hd (S1_4 g) (M.Iop k r)))))

def H_RP (ωL : Q) (n : Fin 3 → Q) (A : Fin K → Fin 3 → Fin 3 → Q) (J : Q) : Mat (4 * dNuc) CQ :=
  MatCQ.add (H_Z M ωL n) (MatCQ.add (H_HF M A) (H_ex M J))

def C1_HF (A : Fin K → Fin 3 → Fin 3 → Q) : Mat (4 * dNuc) CQ :=
  sumFinM (fun k => sum3M (fun a => sum3M (fun b =>
    MatCQ.scale (CQ.ofQ (A k a b)) (finKron M.hd (V4 a) (M.Iop k b)))))

def C2_Z (ωL : Q) (n : Fin 3 → Q) (A : Fin K → Fin 3 → Fin 3 → Q) : Mat (4 * dNuc) CQ :=
  sumFinM (fun k => sum3M (fun d => sum3M (fun b =>
    MatCQ.scale (CQ.iUnit * CQ.ofQ (ωL * crossCol n (A k) d b)) (finKron M.hd (V4 d) (M.Iop k b)))))

theorem M0_multi : (MatCQ.frobInner (PS M) (PS M)).re / Q.ofInt dNuc = 1 := by
  unfold PS
  have hps4 : MatCQ.frobInner PS4 PS4 = 1 := by
    unfold MatCQ.frobInner
    rw [PS4_herm, PS4_idem, PS4_trace]
  rw [Kron.frobInner, hps4, frobInner_id_left, trace_id, CQ.one_mul, CQ.ofQ_re]
  exact Q.div_self (Q.ne_zero_of_pos (ofInt_pos_nat M.hd))

theorem comm_H_Z_PS_multi (ωL : Q) (n : Fin 3 → Q) :
    MatCQ.comm (H_Z M ωL n) (PS M) = MatCQ.zero := by
  unfold H_Z PS
  rw [sum3M_comm_right]; apply sum3M_zero; intro g
  rw [MatCQ.comm_scale_left, Kron.comm_id_left, comm_Z4_PS4 g, Kron.zero_left]
  funext i j; exact CQ.mul_zero _

theorem comm_H_ex_PS_multi (J : Q) :
    MatCQ.comm (H_ex M J) (PS M) = MatCQ.zero := by
  unfold H_ex PS
  rw [MatCQ.comm_scale_left, Kron.comm_id_left, comm_Hex4_PS4, Kron.zero_left]
  funext i j; exact CQ.mul_zero _

theorem comm_H_RP_PS_multi (ωL : Q) (n : Fin 3 → Q) (A : Fin K → Fin 3 → Fin 3 → Q) (J : Q) :
    MatCQ.comm (H_RP M ωL n A J) (PS M) = C1_HF M A := by
  unfold H_RP
  rw [MatCQ.comm_add_left, MatCQ.comm_add_left, comm_H_Z_PS_multi, comm_H_ex_PS_multi,
      MatCQ.zero_add, MatCQ.add_zero]
  unfold H_HF C1_HF PS
  rw [sumFinM_comm_right]
  apply congrArg sumFinM; funext k
  rw [sum3M_comm_right]; apply congrArg sum3M; funext a
  rw [sum3M_comm_right]; apply congrArg sum3M; funext b
  rw [MatCQ.comm_scale_left, Kron.comm_id_right, comm_S1_4_PS4 a]

private theorem nuc_k_block_frob (A : Fin K → Fin 3 → Fin 3 → Q) (k k' : Fin K) :
    k ≠ k' →
    MatCQ.frobInner
      (sum3M (fun a => sum3M (fun b => MatCQ.scale (CQ.ofQ (A k a b)) (finKron M.hd (V4 a) (M.Iop k b)))))
      (sum3M (fun a' => sum3M (fun b' => MatCQ.scale (CQ.ofQ (A k' a' b')) (finKron M.hd (V4 a') (M.Iop k' b'))))) = 0 := by
  intro hne
  rw [sum3M_frobInner_left]; apply sum3CQ_zero; intro a
  rw [sum3M_frobInner_left]; apply sum3CQ_zero; intro b
  rw [MatCQ.frobInner_scale_left, CQ_conj_ofQ, sum3M_frobInner_right]
  have hzero : sum3CQ (fun a' => MatCQ.frobInner (finKron M.hd (V4 a) (M.Iop k b))
      (sum3M (fun b' => MatCQ.scale (CQ.ofQ (A k' a' b')) (finKron M.hd (V4 a') (M.Iop k' b'))))) = 0 := by
    apply sum3CQ_zero; intro a'
    rw [sum3M_frobInner_right]; apply sum3CQ_zero; intro b'
    rw [MatCQ.frobInner_scale_right, Kron.frobInner, M.frob_orthog k k' b b']
    simp [hne, CQ.mul_zero]
  rw [hzero, CQ.mul_zero]

private theorem frob_C1_block_self (A : Fin K → Fin 3 → Fin 3 → Q) (k : Fin K) :
    MatCQ.frobInner
      (sum3M (fun a => sum3M (fun b => MatCQ.scale (CQ.ofQ (A k a b)) (finKron M.hd (V4 a) (M.Iop k b)))))
      (sum3M (fun a' => sum3M (fun b' => MatCQ.scale (CQ.ofQ (A k a' b')) (finKron M.hd (V4 a') (M.Iop k b'))))) =
    CQ.ofQ (q12 * M.weight k * Q.ofInt dNuc * frobSq3 (A k)) := by
  have hsum : ∀ (a b : Fin 3),
      MatCQ.frobInner (finKron M.hd (V4 a) (M.Iop k b))
        (sum3M (fun a' => sum3M (fun b' => MatCQ.scale (CQ.ofQ (A k a' b')) (finKron M.hd (V4 a') (M.Iop k b'))))) =
      CQ.ofQ (A k a b * (q12 * (M.weight k * Q.ofInt dNuc))) := by
    intro a b
    rw [sum3M_frobInner_right]
    have ha : ∀ a' : Fin 3,
        MatCQ.frobInner (finKron M.hd (V4 a) (M.Iop k b))
          (sum3M (fun b' => MatCQ.scale (CQ.ofQ (A k a' b')) (finKron M.hd (V4 a') (M.Iop k b')))) =
        if a' = a then CQ.ofQ (A k a b * (q12 * (M.weight k * Q.ofInt dNuc))) else 0 := by
      intro a'
      rw [sum3M_frobInner_right]
      have hb : ∀ b' : Fin 3,
          MatCQ.frobInner (finKron M.hd (V4 a) (M.Iop k b))
            (MatCQ.scale (CQ.ofQ (A k a' b')) (finKron M.hd (V4 a') (M.Iop k b'))) =
          if a' = a ∧ b' = b then CQ.ofQ (A k a b * (q12 * (M.weight k * Q.ofInt dNuc))) else 0 := by
        intro b'
        rw [MatCQ.frobInner_scale_right, Kron.frobInner, frobInner_V4 a a', M.frob_orthog k k b b']
        by_cases haa : a' = a <;> by_cases hbb : b' = b
        · subst haa; subst hbb; simp only [and_self, if_true, ← CQ.ofQ_mul]
        · have hne : b ≠ b' := fun h => hbb h.symm
          simp [haa, hbb, hne, CQ.zero_mul, CQ.mul_zero]
        · have hne : a ≠ a' := fun h => haa h.symm
          simp [haa, hbb, hne, CQ.zero_mul, CQ.mul_zero]
        · have hne : a ≠ a' := fun h => haa h.symm
          simp [haa, hbb, hne, CQ.zero_mul, CQ.mul_zero]
      have hf : (fun b' => MatCQ.frobInner (finKron M.hd (V4 a) (M.Iop k b))
                    (MatCQ.scale (CQ.ofQ (A k a' b')) (finKron M.hd (V4 a') (M.Iop k b')))) =
                (fun b' => if a' = a ∧ b' = b then CQ.ofQ (A k a b * (q12 * (M.weight k * Q.ofInt dNuc))) else 0) :=
        funext hb
      rw [hf]; unfold sum3CQ
      by_cases haa : a' = a
      · subst haa
        rcases b with ⟨vb, hvb⟩; match vb with
        | 0 => simp [CQ.zero_add, CQ.add_zero]
        | 1 => simp [CQ.zero_add, CQ.add_zero]
        | 2 => simp [CQ.zero_add, CQ.add_zero]
        | _ + 3 => omega
      · simp [haa, CQ.zero_add]
    have hfa : (fun a' => MatCQ.frobInner (finKron M.hd (V4 a) (M.Iop k b))
                   (sum3M (fun b' => MatCQ.scale (CQ.ofQ (A k a' b')) (finKron M.hd (V4 a') (M.Iop k b'))))) =
               (fun a' => if a' = a then CQ.ofQ (A k a b * (q12 * (M.weight k * Q.ofInt dNuc))) else 0) :=
      funext ha
    rw [hfa]; unfold sum3CQ
    rcases a with ⟨va, hva⟩; match va with
    | 0 => simp [CQ.zero_add, CQ.add_zero]
    | 1 => simp [CQ.zero_add, CQ.add_zero]
    | 2 => simp [CQ.zero_add, CQ.add_zero]
    | _ + 3 => omega
  rw [sum3M_frobInner_left]
  have hrow : ∀ a : Fin 3,
      MatCQ.frobInner (sum3M (fun b => MatCQ.scale (CQ.ofQ (A k a b)) (finKron M.hd (V4 a) (M.Iop k b))))
        (sum3M (fun a' => sum3M (fun b' => MatCQ.scale (CQ.ofQ (A k a' b')) (finKron M.hd (V4 a') (M.Iop k b'))))) =
      CQ.ofQ (q12 * M.weight k * Q.ofInt dNuc * sum3Q (fun b => A k a b * A k a b)) := by
    intro a
    rw [sum3M_frobInner_left]
    have ht : ∀ b : Fin 3,
        MatCQ.frobInner (MatCQ.scale (CQ.ofQ (A k a b)) (finKron M.hd (V4 a) (M.Iop k b)))
          (sum3M (fun a' => sum3M (fun b' => MatCQ.scale (CQ.ofQ (A k a' b')) (finKron M.hd (V4 a') (M.Iop k b'))))) =
        CQ.ofQ (q12 * M.weight k * Q.ofInt dNuc * (A k a b * A k a b)) := by
      intro b
      rw [MatCQ.frobInner_scale_left, CQ_conj_ofQ, hsum a b, ← CQ.ofQ_mul]
      congr 1; ac_rfl
    have hft : (fun b => MatCQ.frobInner (MatCQ.scale (CQ.ofQ (A k a b)) (finKron M.hd (V4 a) (M.Iop k b))) _) =
               (fun b => CQ.ofQ (q12 * M.weight k * Q.ofInt dNuc * (A k a b * A k a b))) := funext ht
    rw [hft, sum3CQ_ofQ, ← sum3Q_mul_left]
  have hfr : (fun a => MatCQ.frobInner (sum3M (fun b => MatCQ.scale (CQ.ofQ (A k a b)) (finKron M.hd (V4 a) (M.Iop k b)))) _) =
             (fun a => CQ.ofQ (q12 * M.weight k * Q.ofInt dNuc * sum3Q (fun b => A k a b * A k a b))) := funext hrow
  rw [hfr, sum3CQ_ofQ, ← sum3Q_mul_left]
  rfl

theorem M2_multi_exact (ωL : Q) (n : Fin 3 → Q) (A : Fin K → Fin 3 → Fin 3 → Q) (J : Q) :
    (MatCQ.frobInner (MatCQ.comm (H_RP M ωL n A J) (PS M))
                     (MatCQ.comm (H_RP M ωL n A J) (PS M))).re / Q.ofInt dNuc =
    sumFinQ K (fun k => q12 * M.weight k * frobSq3 (A k)) := by
  rw [comm_H_RP_PS_multi]
  unfold C1_HF
  rw [sumFinM_frobInner_self_orthog _ (nuc_k_block_frob M A)]
  have hf : (fun k => MatCQ.frobInner
      (sum3M (fun a => sum3M (fun b => MatCQ.scale (CQ.ofQ (A k a b)) (finKron M.hd (V4 a) (M.Iop k b)))))
      (sum3M (fun a => sum3M (fun b => MatCQ.scale (CQ.ofQ (A k a b)) (finKron M.hd (V4 a) (M.Iop k b)))))) =
            (fun k => CQ.ofQ (q12 * M.weight k * Q.ofInt dNuc * frobSq3 (A k))) :=
    funext (frob_C1_block_self M A)
  rw [hf, sumFinCQ_ofQ, CQ.ofQ_re]
  have hdne : Q.ofInt dNuc ≠ 0 := Q.ne_zero_of_pos (ofInt_pos_nat M.hd)
  have hfact : sumFinQ K (fun k => q12 * M.weight k * Q.ofInt dNuc * frobSq3 (A k)) =
              Q.ofInt dNuc * sumFinQ K (fun k => q12 * M.weight k * frobSq3 (A k)) := by
    rw [← sumFinQ_mul_left]
    congr 1; funext k; ac_rfl
  rw [hfact, Q.mul_comm (Q.ofInt dNuc), Q.mul_div_cancel hdne]

theorem comm_HZ_C1_multi (ωL : Q) (n : Fin 3 → Q) (A : Fin K → Fin 3 → Fin 3 → Q) :
    MatCQ.comm (H_Z M ωL n) (C1_HF M A) = C2_Z M ωL n A := by
  unfold C1_HF C2_Z
  rw [sumFinM_comm_left]
  apply congrArg sumFinM; funext k
  unfold H_Z
  rw [sum3M_swap (fun a b => MatCQ.scale (CQ.ofQ (A k a b)) (finKron M.hd (V4 a) (M.Iop k b)))]
  rw [sum3M_comm_left]
  rw [sum3M_swap (fun d b => MatCQ.scale (CQ.iUnit * CQ.ofQ (ωL * crossCol n (A k) d b)) (finKron M.hd (V4 d) (M.Iop k b)))]
  apply congrArg sum3M; funext b
  rw [sum3M_comm_right]
  have expand_g : ∀ g : Fin 3,
      MatCQ.comm (MatCQ.scale (CQ.ofQ (ωL * n g)) (finKron M.hd (Z4 g) MatCQ.id))
        (sum3M (fun a => MatCQ.scale (CQ.ofQ (A k a b)) (finKron M.hd (V4 a) (M.Iop k b)))) =
      sum3M (fun a => MatCQ.scale (CQ.ofQ (ωL * n g * A k a b)) (finKron M.hd (MatCQ.comm (Z4 g) (V4 a)) (M.Iop k b))) := by
    intro g
    rw [sum3M_comm_left]; apply congrArg sum3M; funext a
    rw [MatCQ.comm_scale_left, MatCQ.comm_scale_right, Kron.comm_id_left, matCQ_scale_mul_scale, ← CQ.ofQ_mul]
  have h1 : (fun g => MatCQ.comm (MatCQ.scale (CQ.ofQ (ωL * n g)) (finKron M.hd (Z4 g) MatCQ.id))
              (sum3M (fun a => MatCQ.scale (CQ.ofQ (A k a b)) (finKron M.hd (V4 a) (M.Iop k b))))) =
            (fun g => sum3M (fun a =>
              MatCQ.scale (CQ.ofQ (ωL * n g * A k a b)) (finKron M.hd (MatCQ.comm (Z4 g) (V4 a)) (M.Iop k b)))) :=
    funext expand_g
  rw [h1]
  unfold sum3M
  simp only [comm_Z4_V4, Kron.zero_left, Kron.scale_left, matCQ_scale_zero,
             MatCQ.zero_add, MatCQ.add_zero, matCQ_scale_mul_scale]
  unfold crossCol
  exact regroup_cross_col_mat ωL
    (n ⟨0, by omega⟩) (n ⟨1, by omega⟩) (n ⟨2, by omega⟩)
    (A k ⟨0, by omega⟩ b) (A k ⟨1, by omega⟩ b) (A k ⟨2, by omega⟩ b)
    (finKron M.hd (V4 ⟨0, by omega⟩) (M.Iop k b))
    (finKron M.hd (V4 ⟨1, by omega⟩) (M.Iop k b))
    (finKron M.hd (V4 ⟨2, by omega⟩) (M.Iop k b))

theorem C2_Z_orthog_int_multi (ωL : Q) (n : Fin 3 → Q) (A : Fin K → Fin 3 → Fin 3 → Q) (J : Q) :
    MatCQ.frobInner (C2_Z M ωL n A) (MatCQ.comm (MatCQ.add (H_HF M A) (H_ex M J)) (C1_HF M A)) = 0 := by
  rw [MatCQ.comm_add_left, MatCQ.frobInner_add_right]
  have step : ∀ k : Fin K, ∀ d b : Fin 3,
      MatCQ.frobInner (finKron M.hd (V4 d) (M.Iop k b)) (MatCQ.comm (H_HF M A) (C1_HF M A)) = 0 ∧
      MatCQ.frobInner (finKron M.hd (V4 d) (M.Iop k b)) (MatCQ.comm (H_ex M J) (C1_HF M A)) = 0 := by
    intro k d b
    constructor
    · unfold H_HF C1_HF
      rw [sumFinM_comm_right, sumFinM_frobInner_right]; apply sumFinCQ_zero; intro k'
      rw [sum3M_comm_right, sum3M_frobInner_right]; apply sum3CQ_zero; intro g
      rw [sum3M_comm_right, sum3M_frobInner_right]; apply sum3CQ_zero; intro r
      rw [sumFinM_comm_left, sumFinM_frobInner_right]; apply sumFinCQ_zero; intro k''
      rw [sum3M_comm_left, sum3M_frobInner_right]; apply sum3CQ_zero; intro a
      rw [sum3M_comm_left, sum3M_frobInner_right]; apply sum3CQ_zero; intro s
      rw [MatCQ.comm_scale_left, MatCQ.comm_scale_right, MatCQ.frobInner_scale_right,
          MatCQ.frobInner_scale_right, Kron.comm, Kron.frobInner_sub_right, Kron.frobInner, Kron.frobInner]
      by_cases hk : k' = k''
      · subst hk
        by_cases hkk : k = k'
        · subst hkk
          have hV := v4_anticomm_S1_4 d g a
          rw [MatCQ.frobInner_add_right] at hV
          have hVneg : MatCQ.frobInner (V4 d) (MatCQ.mul (V4 a) (S1_4 g)) =
                       -MatCQ.frobInner (V4 d) (MatCQ.mul (S1_4 g) (V4 a)) := by
            have hadd := congrArg (fun x => -MatCQ.frobInner (V4 d) (MatCQ.mul (S1_4 g) (V4 a)) + x) hV
            dsimp only at hadd
            rw [CQ.add_zero, ← CQ.add_assoc, CQ.add_left_neg, CQ.zero_add] at hadd
            exact hadd
          rw [hVneg, CQ.neg_mul]
          change _ * (_ * (MatCQ.frobInner (V4 d) (MatCQ.mul (S1_4 g) (V4 a)) * MatCQ.frobInner (M.Iop k b) (MatCQ.mul (M.Iop k r) (M.Iop k s)) +
                      -(-(MatCQ.frobInner (V4 d) (MatCQ.mul (S1_4 g) (V4 a)) * MatCQ.frobInner (M.Iop k b) (MatCQ.mul (M.Iop k s) (M.Iop k r)))))) = 0
          rw [cq_neg_neg, ← CQ.left_distrib, ← MatCQ.frobInner_add_right, M.same_anticomm_orthog k b r s, CQ.mul_zero, CQ.mul_zero, CQ.mul_zero]
        · rw [M.same_other_orthog k k' hkk b r s, M.same_other_orthog k k' hkk b s r,
              CQ.mul_zero, CQ.mul_zero]
          change _ * (_ * ((0 : CQ) + -(0 : CQ))) = 0
          have hz : (0 : CQ) + -(0 : CQ) = 0 := by apply CQ.ext <;> exact qrel_eq _ _ (by decide)
          rw [hz, CQ.mul_zero, CQ.mul_zero]
      · have hc1 := (M.comm_cross k k' k'' hk b r s).2
        have hc2 := (M.comm_cross k k'' k' (fun h => hk h.symm) b s r).2
        rw [hc1, hc2, CQ.mul_zero, CQ.mul_zero]
        change _ * (_ * ((0 : CQ) + -(0 : CQ))) = 0
        have hz : (0 : CQ) + -(0 : CQ) = 0 := by apply CQ.ext <;> exact qrel_eq _ _ (by decide)
        rw [hz, CQ.mul_zero, CQ.mul_zero]
    · unfold H_ex C1_HF
      rw [sumFinM_comm_left, sumFinM_frobInner_right]; apply sumFinCQ_zero; intro k''
      rw [sum3M_comm_left, sum3M_frobInner_right]; apply sum3CQ_zero; intro a
      rw [sum3M_comm_left, sum3M_frobInner_right]; apply sum3CQ_zero; intro s
      rw [MatCQ.comm_scale_left, MatCQ.comm_scale_right, MatCQ.frobInner_scale_right,
          MatCQ.frobInner_scale_right, Kron.comm_id_left, Kron.frobInner, v4_orthog_Hex4 d a,
          CQ.zero_mul, CQ.mul_zero, CQ.mul_zero]
  unfold C2_Z
  have apply_sum : ∀ Mmat : Mat (4 * dNuc) CQ,
      (∀ k : Fin K, ∀ d b : Fin 3, MatCQ.frobInner (finKron M.hd (V4 d) (M.Iop k b)) Mmat = 0) →
      MatCQ.frobInner (sumFinM (fun k => sum3M (fun d => sum3M (fun b =>
        MatCQ.scale (CQ.iUnit * CQ.ofQ (ωL * crossCol n (A k) d b)) (finKron M.hd (V4 d) (M.Iop k b)))))) Mmat = 0 := by
    intro Mmat hM
    rw [sumFinM_frobInner_left]; apply sumFinCQ_zero; intro k
    rw [sum3M_frobInner_left]; apply sum3CQ_zero; intro d
    rw [sum3M_frobInner_left]; apply sum3CQ_zero; intro b
    rw [MatCQ.frobInner_scale_left, hM k d b, CQ.mul_zero]
  rw [apply_sum _ (fun k d b => (step k d b).1), apply_sum _ (fun k d b => (step k d b).2), CQ.zero_add]

private theorem frob_C2_block_self (ωL : Q) (n : Fin 3 → Q) (A : Fin K → Fin 3 → Fin 3 → Q) (k : Fin K) :
    MatCQ.frobInner
      (sum3M (fun d => sum3M (fun b => MatCQ.scale (CQ.iUnit * CQ.ofQ (ωL * crossCol n (A k) d b)) (finKron M.hd (V4 d) (M.Iop k b)))))
      (sum3M (fun d' => sum3M (fun b' => MatCQ.scale (CQ.iUnit * CQ.ofQ (ωL * crossCol n (A k) d' b')) (finKron M.hd (V4 d') (M.Iop k b'))))) =
    CQ.ofQ (q12 * M.weight k * Q.ofInt dNuc * ωL * ωL * (normSq3 n * frobSq3 (A k) - quadForm3 (A k) n)) := by
  have hi_conj : (CQ.iUnit).conj * CQ.iUnit = 1 := by
    apply CQ.ext <;> exact qrel_eq _ _ (by decide)
  have hsum : ∀ d b : Fin 3,
      MatCQ.frobInner (finKron M.hd (V4 d) (M.Iop k b))
        (sum3M (fun d' => sum3M (fun b' => MatCQ.scale (CQ.iUnit * CQ.ofQ (ωL * crossCol n (A k) d' b')) (finKron M.hd (V4 d') (M.Iop k b'))))) =
      CQ.iUnit * CQ.ofQ (ωL * crossCol n (A k) d b) * CQ.ofQ (q12 * (M.weight k * Q.ofInt dNuc)) := by
    intro d b
    rw [sum3M_frobInner_right]
    have hd' : ∀ d' : Fin 3,
        MatCQ.frobInner (finKron M.hd (V4 d) (M.Iop k b))
          (sum3M (fun b' => MatCQ.scale (CQ.iUnit * CQ.ofQ (ωL * crossCol n (A k) d' b')) (finKron M.hd (V4 d') (M.Iop k b')))) =
        if d' = d then CQ.iUnit * CQ.ofQ (ωL * crossCol n (A k) d b) * CQ.ofQ (q12 * (M.weight k * Q.ofInt dNuc)) else 0 := by
      intro d'
      rw [sum3M_frobInner_right]
      have hb' : ∀ b' : Fin 3,
          MatCQ.frobInner (finKron M.hd (V4 d) (M.Iop k b))
            (MatCQ.scale (CQ.iUnit * CQ.ofQ (ωL * crossCol n (A k) d' b')) (finKron M.hd (V4 d') (M.Iop k b'))) =
          if d' = d ∧ b' = b then CQ.iUnit * CQ.ofQ (ωL * crossCol n (A k) d b) * CQ.ofQ (q12 * (M.weight k * Q.ofInt dNuc)) else 0 := by
        intro b'
        rw [MatCQ.frobInner_scale_right, Kron.frobInner, frobInner_V4 d d', M.frob_orthog k k b b']
        by_cases hdd : d' = d <;> by_cases hbb : b' = b
        · subst hdd; subst hbb; simp only [and_self, if_true, ← CQ.ofQ_mul]
        · have hne : b ≠ b' := fun h => hbb h.symm
          simp [hdd, hbb, hne, CQ.zero_mul, CQ.mul_zero]
        · have hne : d ≠ d' := fun h => hdd h.symm
          simp [hdd, hbb, hne, CQ.zero_mul, CQ.mul_zero]
        · have hne : d ≠ d' := fun h => hdd h.symm
          simp [hdd, hbb, hne, CQ.zero_mul, CQ.mul_zero]
      have hfb := funext hb'
      rw [hfb]; unfold sum3CQ
      by_cases hdd : d' = d
      · subst hdd
        rcases b with ⟨vb, hvb⟩; match vb with
        | 0 => simp [CQ.zero_add, CQ.add_zero]
        | 1 => simp [CQ.zero_add, CQ.add_zero]
        | 2 => simp [CQ.zero_add, CQ.add_zero]
        | _ + 3 => omega
      · simp [hdd, CQ.zero_add]
    have hfd := funext hd'
    rw [hfd]; unfold sum3CQ
    rcases d with ⟨vd, hvd⟩; match vd with
    | 0 => simp [CQ.zero_add, CQ.add_zero]
    | 1 => simp [CQ.zero_add, CQ.add_zero]
    | 2 => simp [CQ.zero_add, CQ.add_zero]
    | _ + 3 => omega
  have hnorm_cross : MatCQ.frobInner
      (sum3M (fun d => sum3M (fun b => MatCQ.scale (CQ.iUnit * CQ.ofQ (ωL * crossCol n (A k) d b)) (finKron M.hd (V4 d) (M.Iop k b)))))
      (sum3M (fun d' => sum3M (fun b' => MatCQ.scale (CQ.iUnit * CQ.ofQ (ωL * crossCol n (A k) d' b')) (finKron M.hd (V4 d') (M.Iop k b'))))) =
      CQ.ofQ (q12 * M.weight k * Q.ofInt dNuc * ωL * ωL *
        sum3Q (fun d => sum3Q (fun b => crossCol n (A k) d b * crossCol n (A k) d b))) := by
    rw [sum3M_frobInner_left]
    have hrow : ∀ d : Fin 3,
        MatCQ.frobInner (sum3M (fun b => MatCQ.scale (CQ.iUnit * CQ.ofQ (ωL * crossCol n (A k) d b)) (finKron M.hd (V4 d) (M.Iop k b))))
          (sum3M (fun d' => sum3M (fun b' => MatCQ.scale (CQ.iUnit * CQ.ofQ (ωL * crossCol n (A k) d' b')) (finKron M.hd (V4 d') (M.Iop k b'))))) =
        CQ.ofQ (q12 * M.weight k * Q.ofInt dNuc * ωL * ωL * sum3Q (fun b => crossCol n (A k) d b * crossCol n (A k) d b)) := by
      intro d
      rw [sum3M_frobInner_left]
      have ht : ∀ b : Fin 3,
          MatCQ.frobInner (MatCQ.scale (CQ.iUnit * CQ.ofQ (ωL * crossCol n (A k) d b)) (finKron M.hd (V4 d) (M.Iop k b)))
            (sum3M (fun d' => sum3M (fun b' => MatCQ.scale (CQ.iUnit * CQ.ofQ (ωL * crossCol n (A k) d' b')) (finKron M.hd (V4 d') (M.Iop k b'))))) =
          CQ.ofQ (q12 * M.weight k * Q.ofInt dNuc * ωL * ωL * (crossCol n (A k) d b * crossCol n (A k) d b)) := by
        intro b
        rw [MatCQ.frobInner_scale_left, hsum d b, CQ.conj_mul, CQ_conj_ofQ]
        calc (CQ.iUnit.conj * CQ.ofQ (ωL * crossCol n (A k) d b)) *
               (CQ.iUnit * CQ.ofQ (ωL * crossCol n (A k) d b) * CQ.ofQ (q12 * (M.weight k * Q.ofInt dNuc)))
            = (CQ.iUnit.conj * CQ.iUnit) * (CQ.ofQ (q12 * (M.weight k * Q.ofInt dNuc)) * CQ.ofQ (ωL * crossCol n (A k) d b) * CQ.ofQ (ωL * crossCol n (A k) d b)) := by ac_rfl
          _ = 1 * CQ.ofQ (q12 * (M.weight k * Q.ofInt dNuc) * (ωL * crossCol n (A k) d b) * (ωL * crossCol n (A k) d b)) := by rw [hi_conj, ← CQ.ofQ_mul, ← CQ.ofQ_mul]
          _ = CQ.ofQ (q12 * M.weight k * Q.ofInt dNuc * ωL * ωL * (crossCol n (A k) d b * crossCol n (A k) d b)) := by
              rw [CQ.one_mul]; congr 1; ac_rfl
      have hft := funext ht
      rw [hft, sum3CQ_ofQ, ← sum3Q_mul_left]
    have hfr := funext hrow
    rw [hfr, sum3CQ_ofQ, ← sum3Q_mul_left]
  rw [hnorm_cross]
  congr 2
  rw [sum3Q_swap (fun d b => crossCol n (A k) d b * crossCol n (A k) d b)]
  have hfsq : frobSq3 (A k) = sum3Q (fun b => sum3Q (fun a => A k a b * A k a b)) := sum3Q_swap _
  rw [hfsq]
  unfold crossCol quadForm3 normSq3
  unfold sum3Q
  dsimp only
  have hc0 := cross_norm_sq_Q (n ⟨0, by omega⟩) (n ⟨1, by omega⟩) (n ⟨2, by omega⟩) (A k ⟨0, by omega⟩ ⟨0, by omega⟩) (A k ⟨1, by omega⟩ ⟨0, by omega⟩) (A k ⟨2, by omega⟩ ⟨0, by omega⟩)
  have hc1 := cross_norm_sq_Q (n ⟨0, by omega⟩) (n ⟨1, by omega⟩) (n ⟨2, by omega⟩) (A k ⟨0, by omega⟩ ⟨1, by omega⟩) (A k ⟨1, by omega⟩ ⟨1, by omega⟩) (A k ⟨2, by omega⟩ ⟨1, by omega⟩)
  have hc2 := cross_norm_sq_Q (n ⟨0, by omega⟩) (n ⟨1, by omega⟩) (n ⟨2, by omega⟩) (A k ⟨0, by omega⟩ ⟨2, by omega⟩) (A k ⟨1, by omega⟩ ⟨2, by omega⟩) (A k ⟨2, by omega⟩ ⟨2, by omega⟩)
  have sum_diff3 : ∀ x0 x1 x2 y0 y1 y2 : Q,
      (x0 - y0) + ((x1 - y1) + (x2 - y2)) = (x0 + (x1 + x2)) - (y0 + (y1 + y2)) := by
    intro x0 x1 x2 y0 y1 y2
    simp only [Q.sub_eq_add_neg, Q.neg_add]; ac_rfl
  have fact : ∀ s v0 v1 v2 : Q, s * v0 + (s * v1 + s * v2) = s * (v0 + (v1 + v2)) := by
    intro s v0 v1 v2; rw [Q.left_distrib, Q.left_distrib]
  rw [hc0, hc1, hc2, sum_diff3, fact]

private theorem C2_Z_normSq_multi (ωL : Q) (n : Fin 3 → Q) (A : Fin K → Fin 3 → Fin 3 → Q) :
    MatCQ.frobInner (C2_Z M ωL n A) (C2_Z M ωL n A) =
    CQ.ofQ (sumFinQ K (fun k => q12 * M.weight k * Q.ofInt dNuc * ωL * ωL * (normSq3 n * frobSq3 (A k) - quadForm3 (A k) n))) := by
  unfold C2_Z
  have horth : ∀ k k' : Fin K, k ≠ k' →
      MatCQ.frobInner
        (sum3M (fun d => sum3M (fun b => MatCQ.scale (CQ.iUnit * CQ.ofQ (ωL * crossCol n (A k) d b)) (finKron M.hd (V4 d) (M.Iop k b)))))
        (sum3M (fun d' => sum3M (fun b' => MatCQ.scale (CQ.iUnit * CQ.ofQ (ωL * crossCol n (A k') d' b')) (finKron M.hd (V4 d') (M.Iop k' b'))))) = 0 := by
    intro k k' hne
    rw [sum3M_frobInner_left]; apply sum3CQ_zero; intro d
    rw [sum3M_frobInner_left]; apply sum3CQ_zero; intro b
    rw [MatCQ.frobInner_scale_left, sum3M_frobInner_right]
    have hzero : sum3CQ (fun d' => MatCQ.frobInner (finKron M.hd (V4 d) (M.Iop k b))
        (sum3M (fun b' => MatCQ.scale (CQ.iUnit * CQ.ofQ (ωL * crossCol n (A k') d' b')) (finKron M.hd (V4 d') (M.Iop k' b'))))) = 0 := by
      apply sum3CQ_zero; intro d'
      rw [sum3M_frobInner_right]; apply sum3CQ_zero; intro b'
      rw [MatCQ.frobInner_scale_right, Kron.frobInner, M.frob_orthog k k' b b']
      simp [hne, CQ.mul_zero]
    rw [hzero, CQ.mul_zero]
  rw [sumFinM_frobInner_self_orthog _ horth]
  have hf := funext (frob_C2_block_self M ωL n A)
  rw [hf, sumFinCQ_ofQ]

theorem M4_multi_diff (ωL : Q) (n n0 : Fin 3 → Q) (hn : normSq3 n = 1) (hn0 : normSq3 n0 = 1)
    (A : Fin K → Fin 3 → Fin 3 → Q) (J : Q) :
    let C2 := fun dir => MatCQ.comm (H_RP M ωL dir A J) (MatCQ.comm (H_RP M ωL dir A J) (PS M))
    (MatCQ.frobInner (C2 n) (C2 n)).re / Q.ofInt dNuc -
    (MatCQ.frobInner (C2 n0) (C2 n0)).re / Q.ofInt dNuc =
    sumFinQ K (fun k => q12 * M.weight k * ωL * ωL * (quadForm3 (A k) n0 - quadForm3 (A k) n)) := by
  dsimp only
  let C1 := C1_HF M A
  have hC1 : ∀ dir, MatCQ.comm (H_RP M ωL dir A J) (PS M) = C1 := fun dir => comm_H_RP_PS_multi M ωL dir A J
  have hC2 : ∀ dir, MatCQ.comm (H_RP M ωL dir A J) C1 =
      MatCQ.add (C2_Z M ωL dir A) (MatCQ.comm (MatCQ.add (H_HF M A) (H_ex M J)) C1) := by
    intro dir; unfold H_RP
    rw [MatCQ.comm_add_left, comm_HZ_C1_multi M ωL dir A]
  have hpyth : ∀ dir,
      MatCQ.frobInner (MatCQ.comm (H_RP M ωL dir A J) (MatCQ.comm (H_RP M ωL dir A J) (PS M)))
                      (MatCQ.comm (H_RP M ωL dir A J) (MatCQ.comm (H_RP M ωL dir A J) (PS M))) =
      CQ.ofQ (sumFinQ K (fun k => q12 * M.weight k * Q.ofInt dNuc * ωL * ωL * (normSq3 dir * frobSq3 (A k) - quadForm3 (A k) dir))) +
      MatCQ.frobInner (MatCQ.comm (MatCQ.add (H_HF M A) (H_ex M J)) C1)
                      (MatCQ.comm (MatCQ.add (H_HF M A) (H_ex M J)) C1) := by
    intro dir
    rw [hC1 dir, hC2 dir, frobInner_add_orthog _ _ (C2_Z_orthog_int_multi M ωL dir A J), C2_Z_normSq_multi]
  rw [hpyth n, hpyth n0]
  simp only [CQ.add_re, CQ.ofQ_re, hn, hn0, Q.one_mul]
  rw [Q.add_div, Q.add_div]
  let Rint := (MatCQ.frobInner (MatCQ.comm (MatCQ.add (H_HF M A) (H_ex M J)) C1)
                               (MatCQ.comm (MatCQ.add (H_HF M A) (H_ex M J)) C1)).re / Q.ofInt dNuc
  have hsub : ∀ u v : Q, (u + Rint) - (v + Rint) = u - v := by
    intro u v
    rw [Q.sub_eq_add_neg, Q.neg_add]
    calc (u + Rint) + (-v + -Rint) = (u + -v) + (Rint + -Rint) := by ac_rfl
      _ = u - v := by rw [Q.add_right_neg, Q.add_zero]; rfl
  change (_ + Rint) - (_ + Rint) = _
  rw [hsub]
  have hdne : Q.ofInt dNuc ≠ 0 := Q.ne_zero_of_pos (ofInt_pos_nat M.hd)
  have hdiv : ∀ dirFun : (Fin K → Q),
      sumFinQ K (fun k => q12 * M.weight k * Q.ofInt dNuc * ωL * ωL * dirFun k) / Q.ofInt dNuc =
      sumFinQ K (fun k => q12 * M.weight k * ωL * ωL * dirFun k) := by
    intro dirFun
    have hf : sumFinQ K (fun k => q12 * M.weight k * Q.ofInt dNuc * ωL * ωL * dirFun k) =
              Q.ofInt dNuc * sumFinQ K (fun k => q12 * M.weight k * ωL * ωL * dirFun k) := by
      rw [← sumFinQ_mul_left]; congr 1; funext k; ac_rfl
    rw [hf, Q.mul_comm (Q.ofInt dNuc), Q.mul_div_cancel hdne]
  rw [hdiv (fun k => frobSq3 (A k) - quadForm3 (A k) n),
      hdiv (fun k => frobSq3 (A k) - quadForm3 (A k) n0),
      sumFinQ_sub]
  congr 1; funext k
  rw [Q.sub_eq_add_neg, ← Q.mul_neg, ← Q.left_distrib, ← Q.sub_eq_add_neg]
  congr 1
  simp only [Q.sub_eq_add_neg, Q.neg_add, Q.neg_neg]
  calc frobSq3 (A k) + -quadForm3 (A k) n + (-frobSq3 (A k) + quadForm3 (A k) n0)
      = (frobSq3 (A k) + -frobSq3 (A k)) + (quadForm3 (A k) n0 + -quadForm3 (A k) n) := by ac_rfl
    _ = quadForm3 (A k) n0 + -quadForm3 (A k) n := by rw [Q.add_right_neg, Q.zero_add]

theorem M4_multi_isotropic_blindness (ωL : Q) (n n0 : Fin 3 → Q) (hn : normSq3 n = 1) (hn0 : normSq3 n0 = 1)
    (iso : Fin K → Q) (J : Q) :
    let A := fun k => axialA (iso k) (iso k)
    let C2 := fun dir => MatCQ.comm (H_RP M ωL dir A J) (MatCQ.comm (H_RP M ωL dir A J) (PS M))
    (MatCQ.frobInner (C2 n) (C2 n)).re / Q.ofInt dNuc -
    (MatCQ.frobInner (C2 n0) (C2 n0)).re / Q.ofInt dNuc = 0 := by
  dsimp only
  rw [M4_multi_diff M ωL n n0 hn hn0]
  apply sumFinQ_zero; intro k
  have hiso : ∀ dir : Fin 3 → Q, normSq3 dir = 1 → quadForm3 (axialA (iso k) (iso k)) dir = iso k * iso k := by
    intro dir hdir
    unfold quadForm3 sum3Q axialA
    simp only [Q.zero_mul, Q.mul_zero, Q.add_zero, Q.zero_add]
    have hs1 : (dir ⟨0, by omega⟩ * iso k) * (dir ⟨0, by omega⟩ * iso k) =
               (iso k * iso k) * (dir ⟨0, by omega⟩ * dir ⟨0, by omega⟩) := by ac_rfl
    have hs2 : (dir ⟨1, by omega⟩ * iso k) * (dir ⟨1, by omega⟩ * iso k) =
               (iso k * iso k) * (dir ⟨1, by omega⟩ * dir ⟨1, by omega⟩) := by ac_rfl
    have hs3 : (dir ⟨2, by omega⟩ * iso k) * (dir ⟨2, by omega⟩ * iso k) =
               (iso k * iso k) * (dir ⟨2, by omega⟩ * dir ⟨2, by omega⟩) := by ac_rfl
    rw [hs1, hs2, hs3, ← Q.left_distrib, ← Q.left_distrib]
    have hnorm : dir ⟨0, by omega⟩ * dir ⟨0, by omega⟩ +
                 (dir ⟨1, by omega⟩ * dir ⟨1, by omega⟩ + dir ⟨2, by omega⟩ * dir ⟨2, by omega⟩) = 1 := hdir
    rw [hnorm, Q.mul_one]
  rw [hiso n0 hn0, hiso n hn, Q.sub_self, Q.mul_zero]

theorem FAD_36x36_twoN14_M2 (ωL : Q) (n : Fin 3 → Q) (A1 A2 : Fin 3 → Fin 3 → Q) (J : Q) :
    (MatCQ.frobInner (MatCQ.comm (H_RP fadTwo14N ωL n (Fin.cases A1 (fun _ => A2)) J) (PS fadTwo14N))
                     (MatCQ.comm (H_RP fadTwo14N ωL n (Fin.cases A1 (fun _ => A2)) J) (PS fadTwo14N))).re / Q.ofInt 9 =
    q13 * (frobSq3 A1 + frobSq3 A2) := by
  have hm := M2_multi_exact fadTwo14N ωL n (Fin.cases A1 (fun _ => A2)) J
  change _ / Q.ofInt 9 = _ at hm
  rw [hm]
  simp only [sumFinQ, Q.add_zero]
  have hw0 : q12 * fadTwo14N.weight 0 = q13 := qrel_eq _ _ (by decide)
  have hw1 : q12 * fadTwo14N.weight 1 = q13 := qrel_eq _ _ (by decide)
  change q12 * fadTwo14N.weight 0 * frobSq3 A1 + q12 * fadTwo14N.weight (Fin.succ 0) * frobSq3 A2 = _
  rw [hw0, show (Fin.succ 0 : Fin 2) = 1 from rfl, hw1, Q.left_distrib]

theorem FAD_36x36_twoN14_M4_axial_diff (ωL s c Ap1 Al1 Ap2 Al2 J : Q) (hsc : s * s + c * c = 1) :
    let A : Fin 2 → Fin 3 → Fin 3 → Q := Fin.cases (axialA Ap1 Al1) (fun _ => axialA Ap2 Al2)
    let C2 := fun dir => MatCQ.comm (H_RP fadTwo14N ωL dir A J)
                                    (MatCQ.comm (H_RP fadTwo14N ωL dir A J) (PS fadTwo14N))
    (MatCQ.frobInner (C2 (xzDir s c)) (C2 (xzDir s c))).re / Q.ofInt 9 -
    (MatCQ.frobInner (C2 (xzDir 0 1)) (C2 (xzDir 0 1))).re / Q.ofInt 9 =
    q13 * ωL * ωL * ((Al1 * Al1 - Ap1 * Ap1) + (Al2 * Al2 - Ap2 * Ap2)) * (s * s) := by
  have hn : normSq3 (xzDir s c) = 1 := by
    unfold normSq3 sum3Q xzDir; simp only [Q.zero_mul, Q.add_zero, Q.zero_add]; exact hsc
  have hn0 : normSq3 (xzDir 0 1) = 1 := by
    unfold normSq3 sum3Q xzDir; simp only [Q.zero_mul, Q.one_mul, Q.add_zero, Q.zero_add]
  have hm := M4_multi_diff fadTwo14N ωL (xzDir s c) (xzDir 0 1) hn hn0
               (Fin.cases (axialA Ap1 Al1) (fun _ => axialA Ap2 Al2)) J
  change _ / Q.ofInt 9 - _ / Q.ofInt 9 = _ at hm
  dsimp only
  rw [hm]
  simp only [sumFinQ, Q.add_zero]
  have hw0 : q12 * fadTwo14N.weight 0 = q13 := qrel_eq _ _ (by decide)
  have hw1 : q12 * fadTwo14N.weight 1 = q13 := qrel_eq _ _ (by decide)
  change q12 * fadTwo14N.weight 0 * ωL * ωL * (quadForm3 (axialA Ap1 Al1) (xzDir 0 1) - quadForm3 (axialA Ap1 Al1) (xzDir s c)) +
         q12 * fadTwo14N.weight (Fin.succ 0) * ωL * ωL * (quadForm3 (axialA Ap2 Al2) (xzDir 0 1) - quadForm3 (axialA Ap2 Al2) (xzDir s c)) = _
  rw [hw0, show (Fin.succ 0 : Fin 2) = 1 from rfl, hw1,
      axial_diff_quad Ap1 Al1 s c hsc, axial_diff_quad Ap2 Al2 s c hsc]
  simp only [Q.left_distrib, Q.right_distrib]
  ac_rfl

/-! #### Arbitrary Electron Attachment `e : Fin K -> Bool` (`e_k in {1, 2}`) for Multi-Nucleus Systems -/

def H_HF_gen (e : Fin K → Bool) (A : Fin K → Fin 3 → Fin 3 → Q) : Mat (4 * dNuc) CQ :=
  sumFinM (fun k => sum3M (fun g => sum3M (fun r =>
    MatCQ.scale (CQ.ofQ (A k g r)) (finKron M.hd (Se_4 (e k) g) (M.Iop k r)))))

def H_RP_gen (ωL : Q) (n : Fin 3 → Q) (e : Fin K → Bool)
    (A : Fin K → Fin 3 → Fin 3 → Q) (J : Q) : Mat (4 * dNuc) CQ :=
  MatCQ.add (H_Z M ωL n) (MatCQ.add (H_HF_gen M e A) (H_ex M J))

def sgnA (e : Fin K → Bool) (A : Fin K → Fin 3 → Fin 3 → Q) : Fin K → Fin 3 → Fin 3 → Q :=
  fun k a b => σ_e (e k) * A k a b

private theorem frobSq3_sgnA (e : Fin K → Bool) (A : Fin K → Fin 3 → Fin 3 → Q) (k : Fin K) :
    frobSq3 (sgnA e A k) = frobSq3 (A k) := by
  unfold frobSq3 sum3Q sgnA
  have hterm : ∀ a b : Fin 3, (σ_e (e k) * A k a b) * (σ_e (e k) * A k a b) = A k a b * A k a b := by
    intro a b
    calc (σ_e (e k) * A k a b) * (σ_e (e k) * A k a b)
        = (σ_e (e k) * σ_e (e k)) * (A k a b * A k a b) := by ac_rfl
      _ = 1 * (A k a b * A k a b) := by rw [σ_e_sq]
      _ = A k a b * A k a b := Q.one_mul _
  simp only [hterm]

private theorem quadForm3_sgnA (e : Fin K → Bool) (A : Fin K → Fin 3 → Fin 3 → Q)
    (dir : Fin 3 → Q) (k : Fin K) :
    quadForm3 (sgnA e A k) dir = quadForm3 (A k) dir := by
  unfold quadForm3 sum3Q sgnA
  have hcol : ∀ b : Fin 3,
      (dir ⟨0, by omega⟩ * (σ_e (e k) * A k ⟨0, by omega⟩ b) +
       (dir ⟨1, by omega⟩ * (σ_e (e k) * A k ⟨1, by omega⟩ b) +
        dir ⟨2, by omega⟩ * (σ_e (e k) * A k ⟨2, by omega⟩ b))) *
      (dir ⟨0, by omega⟩ * (σ_e (e k) * A k ⟨0, by omega⟩ b) +
       (dir ⟨1, by omega⟩ * (σ_e (e k) * A k ⟨1, by omega⟩ b) +
        dir ⟨2, by omega⟩ * (σ_e (e k) * A k ⟨2, by omega⟩ b))) =
      (dir ⟨0, by omega⟩ * A k ⟨0, by omega⟩ b +
       (dir ⟨1, by omega⟩ * A k ⟨1, by omega⟩ b +
        dir ⟨2, by omega⟩ * A k ⟨2, by omega⟩ b)) *
      (dir ⟨0, by omega⟩ * A k ⟨0, by omega⟩ b +
       (dir ⟨1, by omega⟩ * A k ⟨1, by omega⟩ b +
        dir ⟨2, by omega⟩ * A k ⟨2, by omega⟩ b)) := by
    intro b
    let x := dir ⟨0, by omega⟩ * A k ⟨0, by omega⟩ b +
             (dir ⟨1, by omega⟩ * A k ⟨1, by omega⟩ b +
              dir ⟨2, by omega⟩ * A k ⟨2, by omega⟩ b)
    have hfac : dir ⟨0, by omega⟩ * (σ_e (e k) * A k ⟨0, by omega⟩ b) +
                (dir ⟨1, by omega⟩ * (σ_e (e k) * A k ⟨1, by omega⟩ b) +
                 dir ⟨2, by omega⟩ * (σ_e (e k) * A k ⟨2, by omega⟩ b)) = σ_e (e k) * x := by
      dsimp only [x]
      have h0 : dir ⟨0, by omega⟩ * (σ_e (e k) * A k ⟨0, by omega⟩ b) = σ_e (e k) * (dir ⟨0, by omega⟩ * A k ⟨0, by omega⟩ b) := by ac_rfl
      have h1 : dir ⟨1, by omega⟩ * (σ_e (e k) * A k ⟨1, by omega⟩ b) = σ_e (e k) * (dir ⟨1, by omega⟩ * A k ⟨1, by omega⟩ b) := by ac_rfl
      have h2 : dir ⟨2, by omega⟩ * (σ_e (e k) * A k ⟨2, by omega⟩ b) = σ_e (e k) * (dir ⟨2, by omega⟩ * A k ⟨2, by omega⟩ b) := by ac_rfl
      rw [h0, h1, h2, ← Q.left_distrib, ← Q.left_distrib]
    rw [hfac]
    calc (σ_e (e k) * x) * (σ_e (e k) * x) = (σ_e (e k) * σ_e (e k)) * (x * x) := by ac_rfl
      _ = 1 * (x * x) := by rw [σ_e_sq]
      _ = x * x := Q.one_mul _
  simp only [hcol]

theorem comm_H_RP_PS_multi_gen (ωL : Q) (n : Fin 3 → Q) (e : Fin K → Bool)
    (A : Fin K → Fin 3 → Fin 3 → Q) (J : Q) :
    MatCQ.comm (H_RP_gen M ωL n e A J) (PS M) = C1_HF M (sgnA e A) := by
  unfold H_RP_gen
  rw [MatCQ.comm_add_left, MatCQ.comm_add_left, comm_H_Z_PS_multi, comm_H_ex_PS_multi,
      MatCQ.zero_add, MatCQ.add_zero]
  unfold H_HF_gen C1_HF sgnA PS
  rw [sumFinM_comm_right]
  apply congrArg sumFinM; funext k
  rw [sum3M_comm_right]; apply congrArg sum3M; funext a
  rw [sum3M_comm_right]; apply congrArg sum3M; funext b
  rw [MatCQ.comm_scale_left, Kron.comm_id_right, comm_Se_4_PS4 (e k) a, Kron.scale_left,
      matCQ_scale_mul_scale, ← CQ.ofQ_mul, Q.mul_comm (A k a b) (σ_e (e k))]

theorem M2_multi_gen (ωL : Q) (n : Fin 3 → Q) (e : Fin K → Bool)
    (A : Fin K → Fin 3 → Fin 3 → Q) (J : Q) :
    (MatCQ.frobInner (MatCQ.comm (H_RP_gen M ωL n e A J) (PS M))
                     (MatCQ.comm (H_RP_gen M ωL n e A J) (PS M))).re / Q.ofInt dNuc =
    sumFinQ K (fun k => q12 * M.weight k * frobSq3 (A k)) := by
  rw [comm_H_RP_PS_multi_gen]
  have hf := M2_multi_exact M ωL n (sgnA e A) J
  rw [comm_H_RP_PS_multi] at hf
  rw [hf]
  congr 1; funext k; rw [frobSq3_sgnA]

theorem C2_Z_orthog_int_multi_gen (ωL : Q) (n : Fin 3 → Q) (e : Fin K → Bool)
    (A : Fin K → Fin 3 → Fin 3 → Q) (J : Q) :
    MatCQ.frobInner (C2_Z M ωL n (sgnA e A))
      (MatCQ.comm (MatCQ.add (H_HF_gen M e A) (H_ex M J)) (C1_HF M (sgnA e A))) = 0 := by
  rw [MatCQ.comm_add_left, MatCQ.frobInner_add_right]
  have step : ∀ k : Fin K, ∀ d b : Fin 3,
      MatCQ.frobInner (finKron M.hd (V4 d) (M.Iop k b)) (MatCQ.comm (H_HF_gen M e A) (C1_HF M (sgnA e A))) = 0 ∧
      MatCQ.frobInner (finKron M.hd (V4 d) (M.Iop k b)) (MatCQ.comm (H_ex M J) (C1_HF M (sgnA e A))) = 0 := by
    intro k d b
    constructor
    · unfold H_HF_gen C1_HF
      rw [sumFinM_comm_right, sumFinM_frobInner_right]; apply sumFinCQ_zero; intro k'
      rw [sum3M_comm_right, sum3M_frobInner_right]; apply sum3CQ_zero; intro g
      rw [sum3M_comm_right, sum3M_frobInner_right]; apply sum3CQ_zero; intro r
      rw [sumFinM_comm_left, sumFinM_frobInner_right]; apply sumFinCQ_zero; intro k''
      rw [sum3M_comm_left, sum3M_frobInner_right]; apply sum3CQ_zero; intro a
      rw [sum3M_comm_left, sum3M_frobInner_right]; apply sum3CQ_zero; intro s
      rw [MatCQ.comm_scale_left, MatCQ.comm_scale_right, MatCQ.frobInner_scale_right,
          MatCQ.frobInner_scale_right, Kron.comm, Kron.frobInner_sub_right, Kron.frobInner, Kron.frobInner]
      by_cases hk : k' = k''
      · subst hk
        by_cases hkk : k = k'
        · subst hkk
          have hV := v4_anticomm_Se_4 (e k) d g a
          rw [MatCQ.frobInner_add_right] at hV
          have hVneg : MatCQ.frobInner (V4 d) (MatCQ.mul (V4 a) (Se_4 (e k) g)) =
                       -MatCQ.frobInner (V4 d) (MatCQ.mul (Se_4 (e k) g) (V4 a)) := by
            have hadd := congrArg (fun x => -MatCQ.frobInner (V4 d) (MatCQ.mul (Se_4 (e k) g) (V4 a)) + x) hV
            dsimp only at hadd
            rw [CQ.add_zero, ← CQ.add_assoc, CQ.add_left_neg, CQ.zero_add] at hadd
            exact hadd
          rw [hVneg, CQ.neg_mul]
          change _ * (_ * (MatCQ.frobInner (V4 d) (MatCQ.mul (Se_4 (e k) g) (V4 a)) * MatCQ.frobInner (M.Iop k b) (MatCQ.mul (M.Iop k r) (M.Iop k s)) +
                      -(-(MatCQ.frobInner (V4 d) (MatCQ.mul (Se_4 (e k) g) (V4 a)) * MatCQ.frobInner (M.Iop k b) (MatCQ.mul (M.Iop k s) (M.Iop k r)))))) = 0
          rw [cq_neg_neg, ← CQ.left_distrib, ← MatCQ.frobInner_add_right, M.same_anticomm_orthog k b r s, CQ.mul_zero, CQ.mul_zero, CQ.mul_zero]
        · rw [M.same_other_orthog k k' hkk b r s, M.same_other_orthog k k' hkk b s r,
              CQ.mul_zero, CQ.mul_zero]
          change _ * (_ * ((0 : CQ) + -(0 : CQ))) = 0
          have hz : (0 : CQ) + -(0 : CQ) = 0 := by apply CQ.ext <;> exact qrel_eq _ _ (by decide)
          rw [hz, CQ.mul_zero, CQ.mul_zero]
      · have hc1 := (M.comm_cross k k' k'' hk b r s).2
        have hc2 := (M.comm_cross k k'' k' (fun h => hk h.symm) b s r).2
        rw [hc1, hc2, CQ.mul_zero, CQ.mul_zero]
        change _ * (_ * ((0 : CQ) + -(0 : CQ))) = 0
        have hz : (0 : CQ) + -(0 : CQ) = 0 := by apply CQ.ext <;> exact qrel_eq _ _ (by decide)
        rw [hz, CQ.mul_zero, CQ.mul_zero]
    · unfold H_ex C1_HF
      rw [sumFinM_comm_left, sumFinM_frobInner_right]; apply sumFinCQ_zero; intro k''
      rw [sum3M_comm_left, sum3M_frobInner_right]; apply sum3CQ_zero; intro a
      rw [sum3M_comm_left, sum3M_frobInner_right]; apply sum3CQ_zero; intro s
      rw [MatCQ.comm_scale_left, MatCQ.comm_scale_right, MatCQ.frobInner_scale_right,
          MatCQ.frobInner_scale_right, Kron.comm_id_left, Kron.frobInner, v4_orthog_Hex4 d a,
          CQ.zero_mul, CQ.mul_zero, CQ.mul_zero]
  unfold C2_Z
  have apply_sum : ∀ Mmat : Mat (4 * dNuc) CQ,
      (∀ k : Fin K, ∀ d b : Fin 3, MatCQ.frobInner (finKron M.hd (V4 d) (M.Iop k b)) Mmat = 0) →
      MatCQ.frobInner (sumFinM (fun k => sum3M (fun d => sum3M (fun b =>
        MatCQ.scale (CQ.iUnit * CQ.ofQ (ωL * crossCol n (sgnA e A k) d b)) (finKron M.hd (V4 d) (M.Iop k b)))))) Mmat = 0 := by
    intro Mmat hM
    rw [sumFinM_frobInner_left]; apply sumFinCQ_zero; intro k
    rw [sum3M_frobInner_left]; apply sum3CQ_zero; intro d
    rw [sum3M_frobInner_left]; apply sum3CQ_zero; intro b
    rw [MatCQ.frobInner_scale_left, hM k d b, CQ.mul_zero]
  rw [apply_sum _ (fun k d b => (step k d b).1), apply_sum _ (fun k d b => (step k d b).2), CQ.zero_add]

theorem M4_multi_diff_gen (ωL : Q) (n n0 : Fin 3 → Q) (hn : normSq3 n = 1) (hn0 : normSq3 n0 = 1)
    (e : Fin K → Bool) (A : Fin K → Fin 3 → Fin 3 → Q) (J : Q) :
    let C2 := fun dir => MatCQ.comm (H_RP_gen M ωL dir e A J) (MatCQ.comm (H_RP_gen M ωL dir e A J) (PS M))
    (MatCQ.frobInner (C2 n) (C2 n)).re / Q.ofInt dNuc -
    (MatCQ.frobInner (C2 n0) (C2 n0)).re / Q.ofInt dNuc =
    sumFinQ K (fun k => q12 * M.weight k * ωL * ωL * (quadForm3 (A k) n0 - quadForm3 (A k) n)) := by
  dsimp only
  let sA := sgnA e A
  let C1 := C1_HF M sA
  have hC1 : ∀ dir, MatCQ.comm (H_RP_gen M ωL dir e A J) (PS M) = C1 := fun dir =>
    comm_H_RP_PS_multi_gen M ωL dir e A J
  have hC2 : ∀ dir, MatCQ.comm (H_RP_gen M ωL dir e A J) C1 =
      MatCQ.add (C2_Z M ωL dir sA) (MatCQ.comm (MatCQ.add (H_HF_gen M e A) (H_ex M J)) C1) := by
    intro dir; unfold H_RP_gen
    rw [MatCQ.comm_add_left, comm_HZ_C1_multi M ωL dir sA]
  have hpyth : ∀ dir,
      MatCQ.frobInner (MatCQ.comm (H_RP_gen M ωL dir e A J) (MatCQ.comm (H_RP_gen M ωL dir e A J) (PS M)))
                      (MatCQ.comm (H_RP_gen M ωL dir e A J) (MatCQ.comm (H_RP_gen M ωL dir e A J) (PS M))) =
      CQ.ofQ (sumFinQ K (fun k => q12 * M.weight k * Q.ofInt dNuc * ωL * ωL * (normSq3 dir * frobSq3 (sA k) - quadForm3 (sA k) dir))) +
      MatCQ.frobInner (MatCQ.comm (MatCQ.add (H_HF_gen M e A) (H_ex M J)) C1)
                      (MatCQ.comm (MatCQ.add (H_HF_gen M e A) (H_ex M J)) C1) := by
    intro dir
    rw [hC1 dir, hC2 dir, frobInner_add_orthog _ _ (C2_Z_orthog_int_multi_gen M ωL dir e A J), C2_Z_normSq_multi]
  rw [hpyth n, hpyth n0]
  simp only [CQ.add_re, CQ.ofQ_re, hn, hn0, Q.one_mul]
  rw [Q.add_div, Q.add_div]
  let Rint := (MatCQ.frobInner (MatCQ.comm (MatCQ.add (H_HF_gen M e A) (H_ex M J)) C1)
                               (MatCQ.comm (MatCQ.add (H_HF_gen M e A) (H_ex M J)) C1)).re / Q.ofInt dNuc
  have hsub : ∀ u v : Q, (u + Rint) - (v + Rint) = u - v := by
    intro u v
    rw [Q.sub_eq_add_neg, Q.neg_add]
    calc (u + Rint) + (-v + -Rint) = (u + -v) + (Rint + -Rint) := by ac_rfl
      _ = u - v := by rw [Q.add_right_neg, Q.add_zero]; rfl
  change (_ + Rint) - (_ + Rint) = _
  rw [hsub]
  have hdne : Q.ofInt dNuc ≠ 0 := Q.ne_zero_of_pos (ofInt_pos_nat M.hd)
  have hdiv : ∀ dirFun : (Fin K → Q),
      sumFinQ K (fun k => q12 * M.weight k * Q.ofInt dNuc * ωL * ωL * dirFun k) / Q.ofInt dNuc =
      sumFinQ K (fun k => q12 * M.weight k * ωL * ωL * dirFun k) := by
    intro dirFun
    have hf : sumFinQ K (fun k => q12 * M.weight k * Q.ofInt dNuc * ωL * ωL * dirFun k) =
              Q.ofInt dNuc * sumFinQ K (fun k => q12 * M.weight k * ωL * ωL * dirFun k) := by
      rw [← sumFinQ_mul_left]; congr 1; funext k; ac_rfl
    rw [hf, Q.mul_comm (Q.ofInt dNuc), Q.mul_div_cancel hdne]
  rw [hdiv (fun k => frobSq3 (sA k) - quadForm3 (sA k) n),
      hdiv (fun k => frobSq3 (sA k) - quadForm3 (sA k) n0),
      sumFinQ_sub]
  congr 1; funext k
  rw [frobSq3_sgnA, quadForm3_sgnA, quadForm3_sgnA]
  rw [Q.sub_eq_add_neg, ← Q.mul_neg, ← Q.left_distrib, ← Q.sub_eq_add_neg]
  congr 1
  simp only [Q.sub_eq_add_neg, Q.neg_add, Q.neg_neg]
  calc frobSq3 (A k) + -quadForm3 (A k) n + (-frobSq3 (A k) + quadForm3 (A k) n0)
      = (frobSq3 (A k) + -frobSq3 (A k)) + (quadForm3 (A k) n0 + -quadForm3 (A k) n) := by ac_rfl
    _ = quadForm3 (A k) n0 + -quadForm3 (A k) n := by rw [Q.add_right_neg, Q.zero_add]

theorem FAD_36x36_twoN14_e1e2_M4_diff (ωL : Q) (n n0 : Fin 3 → Q)
    (hn : normSq3 n = 1) (hn0 : normSq3 n0 = 1) (A1 A2 : Fin 3 → Fin 3 → Q) (J : Q) :
    let e : Fin 2 → Bool := Fin.cases true (fun _ => false)
    let A : Fin 2 → Fin 3 → Fin 3 → Q := Fin.cases A1 (fun _ => A2)
    let C2 := fun dir => MatCQ.comm (H_RP_gen fadTwo14N ωL dir e A J)
                                    (MatCQ.comm (H_RP_gen fadTwo14N ωL dir e A J) (PS fadTwo14N))
    (MatCQ.frobInner (C2 n) (C2 n)).re / Q.ofInt 9 -
    (MatCQ.frobInner (C2 n0) (C2 n0)).re / Q.ofInt 9 =
    q13 * ωL * ωL * ((quadForm3 A1 n0 - quadForm3 A1 n) + (quadForm3 A2 n0 - quadForm3 A2 n)) := by
  have hm := M4_multi_diff_gen fadTwo14N ωL n n0 hn hn0 (Fin.cases true (fun _ => false)) (Fin.cases A1 (fun _ => A2)) J
  change _ / Q.ofInt 9 - _ / Q.ofInt 9 = _ at hm
  dsimp only
  rw [hm]
  simp only [sumFinQ, Q.add_zero]
  have hw0 : q12 * fadTwo14N.weight 0 = q13 := qrel_eq _ _ (by decide)
  have hw1 : q12 * fadTwo14N.weight 1 = q13 := qrel_eq _ _ (by decide)
  change q12 * fadTwo14N.weight 0 * ωL * ωL * (quadForm3 A1 n0 - quadForm3 A1 n) +
         q12 * fadTwo14N.weight (Fin.succ 0) * ωL * ωL * (quadForm3 A2 n0 - quadForm3 A2 n) = _
  rw [hw0, show (Fin.succ 0 : Fin 2) = 1 from rfl, hw1]
  simp only [Q.left_distrib, Q.right_distrib]

/-! #### Arbitrary Symmetric Electron–Electron Dipolar Tensor `H_dip = S_1 · D · S_2` (`D = D^T`) -/

def H_dip (D : Fin 3 → Fin 3 → Q) : Mat (4 * dNuc) CQ :=
  sum3M (fun a => sum3M (fun b =>
    MatCQ.scale (CQ.ofQ (D a b)) (finKron M.hd (MatCQ.mul (S1_4 a) (S2_4 b)) MatCQ.id)))

def H_dip_sym (D : Fin 3 → Fin 3 → Q) : Mat (4 * dNuc) CQ :=
  sum3M (fun a => sum3M (fun b =>
    MatCQ.scale (CQ.ofQ (D a b)) (finKron M.hd (SymDip4 a b) MatCQ.id)))

def H_RP_gen_dip (ωL : Q) (n : Fin 3 → Q) (e : Fin K → Bool)
    (A : Fin K → Fin 3 → Fin 3 → Q) (J : Q) (D : Fin 3 → Fin 3 → Q) : Mat (4 * dNuc) CQ :=
  MatCQ.add (H_Z M ωL n) (MatCQ.add (H_HF_gen M e A) (MatCQ.add (H_ex M J) (H_dip M D)))

theorem H_dip_eq_sym (D : Fin 3 → Fin 3 → Q) (hD : ∀ a b : Fin 3, D a b = D b a) :
    H_dip M D = H_dip_sym M D := by
  have h1 : ∀ f g : Fin 3 → Fin 3 → Mat (4 * dNuc) CQ,
      sum3M (fun a => sum3M (fun b => MatCQ.add (f a b) (g a b))) =
      MatCQ.add (sum3M (fun a => sum3M (fun b => f a b))) (sum3M (fun a => sum3M (fun b => g a b))) := by
    intro f g; funext i j; unfold sum3M MatCQ.add; dsimp only; ac_rfl
  have hscale : ∀ (c : CQ) (f : Fin 3 → Fin 3 → Mat (4 * dNuc) CQ),
      sum3M (fun a => sum3M (fun b => MatCQ.scale c (f a b))) =
      MatCQ.scale c (sum3M (fun a => sum3M (fun b => f a b))) := by
    intro c f; funext i j; unfold sum3M MatCQ.scale MatCQ.add; dsimp only
    simp only [CQ.left_distrib]
  have hhalf_self : ∀ X : Mat (4 * dNuc) CQ,
      MatCQ.scale (CQ.ofQ q12) (MatCQ.add X X) = X := by
    intro X; funext i j; unfold MatCQ.scale MatCQ.add
    have hq2 : CQ.ofQ q12 + CQ.ofQ q12 = 1 := by
      rw [← CQ.ofQ_add]
      have hq : q12 + q12 = 1 := qrel_eq _ _ (by decide)
      rw [hq]; rfl
    rw [CQ.left_distrib, ← CQ.right_distrib, hq2, CQ.one_mul]
  have hsym_expand : H_dip_sym M D =
      MatCQ.scale (CQ.ofQ q12) (MatCQ.add
        (sum3M (fun a => sum3M (fun b => MatCQ.scale (CQ.ofQ (D a b)) (finKron M.hd (MatCQ.mul (S1_4 a) (S2_4 b)) MatCQ.id))))
        (sum3M (fun a => sum3M (fun b => MatCQ.scale (CQ.ofQ (D a b)) (finKron M.hd (MatCQ.mul (S1_4 b) (S2_4 a)) MatCQ.id))))) := by
    unfold H_dip_sym
    rw [← h1, ← hscale]
    apply congrArg sum3M; funext a
    apply congrArg sum3M; funext b
    rw [SymDip4_eq_half_sum, Kron.scale_left, finKron_add_left, matCQ_scale_mul_scale,
        CQ.mul_comm (CQ.ofQ (D a b)) (CQ.ofQ q12), ← matCQ_scale_mul_scale, matCQ_scale_add]
  have hswap :
      sum3M (fun a => sum3M (fun b => MatCQ.scale (CQ.ofQ (D a b)) (finKron M.hd (MatCQ.mul (S1_4 b) (S2_4 a)) MatCQ.id))) =
      H_dip M D := by
    rw [sum3M_swap]
    unfold H_dip
    apply congrArg sum3M; funext b
    apply congrArg sum3M; funext a
    rw [hD a b]
  rw [hsym_expand, hswap, show sum3M (fun a => sum3M (fun b =>
      MatCQ.scale (CQ.ofQ (D a b)) (finKron M.hd (MatCQ.mul (S1_4 a) (S2_4 b)) MatCQ.id))) = H_dip M D from rfl,
      hhalf_self]

theorem comm_H_dip_PS_multi (D : Fin 3 → Fin 3 → Q) (hD : ∀ a b : Fin 3, D a b = D b a) :
    MatCQ.comm (H_dip M D) (PS M) = MatCQ.zero := by
  rw [H_dip_eq_sym M D hD]
  unfold H_dip_sym PS
  rw [sum3M_comm_right]; apply sum3M_zero; intro a
  rw [sum3M_comm_right]; apply sum3M_zero; intro b
  rw [MatCQ.comm_scale_left, Kron.comm_id_left, comm_SymDip4_PS4 a b, Kron.zero_left]
  funext i j; exact CQ.mul_zero _

theorem comm_H_RP_PS_multi_gen_dip (ωL : Q) (n : Fin 3 → Q) (e : Fin K → Bool)
    (A : Fin K → Fin 3 → Fin 3 → Q) (J : Q) (D : Fin 3 → Fin 3 → Q) (hD : ∀ a b : Fin 3, D a b = D b a) :
    MatCQ.comm (H_RP_gen_dip M ωL n e A J D) (PS M) = C1_HF M (sgnA e A) := by
  unfold H_RP_gen_dip
  rw [MatCQ.comm_add_left, MatCQ.comm_add_left, MatCQ.comm_add_left,
      comm_H_Z_PS_multi, comm_H_ex_PS_multi, comm_H_dip_PS_multi M D hD,
      MatCQ.zero_add, MatCQ.add_zero, MatCQ.add_zero]
  have h0 := comm_H_RP_PS_multi_gen M ωL n e A J
  unfold H_RP_gen at h0
  rw [MatCQ.comm_add_left, MatCQ.comm_add_left, comm_H_Z_PS_multi, comm_H_ex_PS_multi,
      MatCQ.zero_add, MatCQ.add_zero] at h0
  exact h0

theorem M2_multi_gen_dip (ωL : Q) (n : Fin 3 → Q) (e : Fin K → Bool)
    (A : Fin K → Fin 3 → Fin 3 → Q) (J : Q) (D : Fin 3 → Fin 3 → Q) (hD : ∀ a b : Fin 3, D a b = D b a) :
    (MatCQ.frobInner (MatCQ.comm (H_RP_gen_dip M ωL n e A J D) (PS M))
                     (MatCQ.comm (H_RP_gen_dip M ωL n e A J D) (PS M))).re / Q.ofInt dNuc =
    sumFinQ K (fun k => q12 * M.weight k * frobSq3 (A k)) := by
  rw [comm_H_RP_PS_multi_gen_dip M ωL n e A J D hD]
  have hf := M2_multi_gen M ωL n e A J
  rw [comm_H_RP_PS_multi_gen] at hf
  exact hf

theorem C2_Z_orthog_int_multi_gen_dip (ωL : Q) (n : Fin 3 → Q) (e : Fin K → Bool)
    (A : Fin K → Fin 3 → Fin 3 → Q) (J : Q) (D : Fin 3 → Fin 3 → Q) (hD : ∀ a b : Fin 3, D a b = D b a) :
    MatCQ.frobInner (C2_Z M ωL n (sgnA e A))
      (MatCQ.comm (MatCQ.add (H_HF_gen M e A) (MatCQ.add (H_ex M J) (H_dip M D))) (C1_HF M (sgnA e A))) = 0 := by
  have hassoc : MatCQ.add (H_HF_gen M e A) (MatCQ.add (H_ex M J) (H_dip M D)) =
      MatCQ.add (MatCQ.add (H_HF_gen M e A) (H_ex M J)) (H_dip M D) := by
    funext i j; unfold MatCQ.add; exact (CQ.add_assoc _ _ _).symm
  rw [hassoc, MatCQ.comm_add_left, MatCQ.frobInner_add_right,
      C2_Z_orthog_int_multi_gen M ωL n e A J, CQ.zero_add, H_dip_eq_sym M D hD]
  have hdip_step : ∀ k : Fin K, ∀ d b : Fin 3,
      MatCQ.frobInner (finKron M.hd (V4 d) (M.Iop k b))
        (MatCQ.comm (H_dip_sym M D) (C1_HF M (sgnA e A))) = 0 := by
    intro k d b
    unfold H_dip_sym C1_HF
    rw [sum3M_comm_right, sum3M_frobInner_right]; apply sum3CQ_zero; intro a1
    rw [sum3M_comm_right, sum3M_frobInner_right]; apply sum3CQ_zero; intro b1
    rw [sumFinM_comm_left, sumFinM_frobInner_right]; apply sumFinCQ_zero; intro k''
    rw [sum3M_comm_left, sum3M_frobInner_right]; apply sum3CQ_zero; intro c
    rw [sum3M_comm_left, sum3M_frobInner_right]; apply sum3CQ_zero; intro s
    rw [MatCQ.comm_scale_left, MatCQ.comm_scale_right, MatCQ.frobInner_scale_right,
        MatCQ.frobInner_scale_right, Kron.comm_id_left, Kron.frobInner, v4_orthog_SymDip4 d a1 b1 c,
        CQ.zero_mul, CQ.mul_zero, CQ.mul_zero]
  unfold C2_Z
  rw [sumFinM_frobInner_left]; apply sumFinCQ_zero; intro k
  rw [sum3M_frobInner_left]; apply sum3CQ_zero; intro d
  rw [sum3M_frobInner_left]; apply sum3CQ_zero; intro b
  rw [MatCQ.frobInner_scale_left, hdip_step k d b, CQ.mul_zero]

theorem M4_multi_diff_gen_dip (ωL : Q) (n n0 : Fin 3 → Q) (hn : normSq3 n = 1) (hn0 : normSq3 n0 = 1)
    (e : Fin K → Bool) (A : Fin K → Fin 3 → Fin 3 → Q) (J : Q)
    (D : Fin 3 → Fin 3 → Q) (hD : ∀ a b : Fin 3, D a b = D b a) :
    let C2 := fun dir => MatCQ.comm (H_RP_gen_dip M ωL dir e A J D)
                                    (MatCQ.comm (H_RP_gen_dip M ωL dir e A J D) (PS M))
    (MatCQ.frobInner (C2 n) (C2 n)).re / Q.ofInt dNuc -
    (MatCQ.frobInner (C2 n0) (C2 n0)).re / Q.ofInt dNuc =
    sumFinQ K (fun k => q12 * M.weight k * ωL * ωL * (quadForm3 (A k) n0 - quadForm3 (A k) n)) := by
  dsimp only
  let sA := sgnA e A
  let C1 := C1_HF M sA
  let Hint := MatCQ.add (H_HF_gen M e A) (MatCQ.add (H_ex M J) (H_dip M D))
  have hC1 : ∀ dir, MatCQ.comm (H_RP_gen_dip M ωL dir e A J D) (PS M) = C1 := fun dir =>
    comm_H_RP_PS_multi_gen_dip M ωL dir e A J D hD
  have hC2 : ∀ dir, MatCQ.comm (H_RP_gen_dip M ωL dir e A J D) C1 =
      MatCQ.add (C2_Z M ωL dir sA) (MatCQ.comm Hint C1) := by
    intro dir; unfold H_RP_gen_dip
    rw [MatCQ.comm_add_left, comm_HZ_C1_multi M ωL dir sA]
  have hpyth : ∀ dir,
      MatCQ.frobInner (MatCQ.comm (H_RP_gen_dip M ωL dir e A J D) (MatCQ.comm (H_RP_gen_dip M ωL dir e A J D) (PS M)))
                      (MatCQ.comm (H_RP_gen_dip M ωL dir e A J D) (MatCQ.comm (H_RP_gen_dip M ωL dir e A J D) (PS M))) =
      CQ.ofQ (sumFinQ K (fun k => q12 * M.weight k * Q.ofInt dNuc * ωL * ωL * (normSq3 dir * frobSq3 (sA k) - quadForm3 (sA k) dir))) +
      MatCQ.frobInner (MatCQ.comm Hint C1) (MatCQ.comm Hint C1) := by
    intro dir
    rw [hC1 dir, hC2 dir, frobInner_add_orthog _ _ (C2_Z_orthog_int_multi_gen_dip M ωL dir e A J D hD), C2_Z_normSq_multi]
  rw [hpyth n, hpyth n0]
  simp only [CQ.add_re, CQ.ofQ_re, hn, hn0, Q.one_mul]
  rw [Q.add_div, Q.add_div]
  let Rint := (MatCQ.frobInner (MatCQ.comm Hint C1) (MatCQ.comm Hint C1)).re / Q.ofInt dNuc
  have hsub : ∀ u v : Q, (u + Rint) - (v + Rint) = u - v := by
    intro u v
    rw [Q.sub_eq_add_neg, Q.neg_add]
    calc (u + Rint) + (-v + -Rint) = (u + -v) + (Rint + -Rint) := by ac_rfl
      _ = u - v := by rw [Q.add_right_neg, Q.add_zero]; rfl
  change (_ + Rint) - (_ + Rint) = _
  rw [hsub]
  have hdne : Q.ofInt dNuc ≠ 0 := Q.ne_zero_of_pos (ofInt_pos_nat M.hd)
  have hdiv : ∀ dirFun : (Fin K → Q),
      sumFinQ K (fun k => q12 * M.weight k * Q.ofInt dNuc * ωL * ωL * dirFun k) / Q.ofInt dNuc =
      sumFinQ K (fun k => q12 * M.weight k * ωL * ωL * dirFun k) := by
    intro dirFun
    have hf : sumFinQ K (fun k => q12 * M.weight k * Q.ofInt dNuc * ωL * ωL * dirFun k) =
              Q.ofInt dNuc * sumFinQ K (fun k => q12 * M.weight k * ωL * ωL * dirFun k) := by
      rw [← sumFinQ_mul_left]; congr 1; funext k; ac_rfl
    rw [hf, Q.mul_comm (Q.ofInt dNuc), Q.mul_div_cancel hdne]
  rw [hdiv (fun k => frobSq3 (sA k) - quadForm3 (sA k) n),
      hdiv (fun k => frobSq3 (sA k) - quadForm3 (sA k) n0),
      sumFinQ_sub]
  congr 1; funext k
  rw [frobSq3_sgnA, quadForm3_sgnA, quadForm3_sgnA]
  rw [Q.sub_eq_add_neg, ← Q.mul_neg, ← Q.left_distrib, ← Q.sub_eq_add_neg]
  congr 1
  simp only [Q.sub_eq_add_neg, Q.neg_add, Q.neg_neg]
  calc frobSq3 (A k) + -quadForm3 (A k) n + (-frobSq3 (A k) + quadForm3 (A k) n0)
      = (frobSq3 (A k) + -frobSq3 (A k)) + (quadForm3 (A k) n0 + -quadForm3 (A k) n) := by ac_rfl
    _ = quadForm3 (A k) n0 + -quadForm3 (A k) n := by rw [Q.add_right_neg, Q.zero_add]

theorem FAD_36x36_twoN14_dipolar_M4_diff (ωL : Q) (n n0 : Fin 3 → Q)
    (hn : normSq3 n = 1) (hn0 : normSq3 n0 = 1) (e : Fin 2 → Bool)
    (A1 A2 : Fin 3 → Fin 3 → Q) (J : Q) (D : Fin 3 → Fin 3 → Q) (hD : ∀ a b : Fin 3, D a b = D b a) :
    let A : Fin 2 → Fin 3 → Fin 3 → Q := Fin.cases A1 (fun _ => A2)
    let C2 := fun dir => MatCQ.comm (H_RP_gen_dip fadTwo14N ωL dir e A J D)
                                    (MatCQ.comm (H_RP_gen_dip fadTwo14N ωL dir e A J D) (PS fadTwo14N))
    (MatCQ.frobInner (C2 n) (C2 n)).re / Q.ofInt 9 -
    (MatCQ.frobInner (C2 n0) (C2 n0)).re / Q.ofInt 9 =
    q13 * ωL * ωL * ((quadForm3 A1 n0 - quadForm3 A1 n) + (quadForm3 A2 n0 - quadForm3 A2 n)) := by
  have hm := M4_multi_diff_gen_dip fadTwo14N ωL n n0 hn hn0 e (Fin.cases A1 (fun _ => A2)) J D hD
  change _ / Q.ofInt 9 - _ / Q.ofInt 9 = _ at hm
  dsimp only
  rw [hm]
  simp only [sumFinQ, Q.add_zero]
  have hw0 : q12 * fadTwo14N.weight 0 = q13 := qrel_eq _ _ (by decide)
  have hw1 : q12 * fadTwo14N.weight 1 = q13 := qrel_eq _ _ (by decide)
  change q12 * fadTwo14N.weight 0 * ωL * ωL * (quadForm3 A1 n0 - quadForm3 A1 n) +
         q12 * fadTwo14N.weight (Fin.succ 0) * ωL * ωL * (quadForm3 A2 n0 - quadForm3 A2 n) = _
  rw [hw0, show (Fin.succ 0 : Fin 2) = 1 from rfl, hw1]
  simp only [Q.left_distrib, Q.right_distrib]

end MultiRP

end MultiNucleus4B

/-! ### Section 4C: Strong-Noise Resolvent Asymptotics, Blind Spot, ML Separation & Schur Manifolds -/

section StrongNoiseAsymptotics4C

private theorem q_mul_ne_zero {a b : Q} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  intro h
  have h1 : (a * b) * Q.inv b = 0 * Q.inv b := by rw [h]
  rw [Q.zero_mul, Q.mul_assoc, Q.mul_inv_cancel hb, Q.mul_one] at h1
  exact ha h1

private theorem q_eq_div_iff {a b c : Q} (hb : b ≠ 0) : a = c / b ↔ a * b = c := by
  constructor
  · intro h; rw [h, Q.div_mul_cancel hb]
  · intro h; rw [← h, Q.mul_div_cancel hb]

private theorem q_div_eq_iff {a b c : Q} (hb : b ≠ 0) : c / b = a ↔ c = a * b := by
  constructor
  · intro h; exact ((q_eq_div_iff hb).mp h.symm).symm
  · intro h; exact ((q_eq_div_iff hb).mpr h.symm).symm

private theorem q_eq_of_mul_eq_right {a b c : Q} (hc : c ≠ 0) (h : a * c = b * c) : a = b := by
  have h1 := congrArg (· * Q.inv c) h
  dsimp only at h1
  rwa [Q.mul_assoc, Q.mul_assoc, Q.mul_inv_cancel hc, Q.mul_one, Q.mul_one] at h1

private theorem q_add_nonneg {a b : Q} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b := by
  have h1 := Q.add_le_add_right ha b
  rw [Q.zero_add] at h1
  exact Q.le_trans hb h1

private theorem q_add_pos_of_pos_of_nonneg {a b : Q} (ha : 0 < a) (hb : 0 ≤ b) : 0 < a + b := by
  have h1 := Q.add_le_add_left hb a
  rw [Q.add_zero] at h1
  exact Q.lt_of_lt_of_le ha h1

private theorem q_div_pos {a b : Q} (ha : 0 < a) (hb : 0 < b) : 0 < a / b :=
  Q.mul_pos ha (Q.inv_pos hb)

private theorem q_div_nonneg {a b : Q} (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a / b :=
  Q.mul_nonneg ha (Q.le_of_lt (Q.inv_pos hb))

private theorem q_inv_le_inv {a b : Q} (ha : 0 < a) (hab : a ≤ b) : Q.inv b ≤ Q.inv a := by
  have hb : 0 < b := Q.lt_of_lt_of_le ha hab
  have h1 : a * Q.inv a ≤ b * Q.inv a := Q.mul_le_mul_of_nonneg_right hab (Q.le_of_lt (Q.inv_pos ha))
  rw [Q.mul_inv_cancel (Q.ne_zero_of_pos ha)] at h1
  have h2 := Q.mul_le_mul_of_nonneg_left h1 (Q.le_of_lt (Q.inv_pos hb))
  rw [Q.mul_one, ← Q.mul_assoc, Q.mul_comm (Q.inv b) b, Q.mul_inv_cancel (Q.ne_zero_of_pos hb), Q.one_mul] at h2
  exact h2

private theorem q_div_le_div_of_nonneg_left {c a b : Q} (hc : 0 ≤ c) (ha : 0 < a) (hab : a ≤ b) :
    c / b ≤ c / a :=
  Q.mul_le_mul_of_nonneg_left (q_inv_le_inv ha hab) hc

private theorem q_le_of_mul_le_mul_pos_right {a b c : Q} (hc : 0 < c) (h : a * c ≤ b * c) : a ≤ b := by
  have h1 := Q.mul_le_mul_of_nonneg_right h (Q.le_of_lt (Q.inv_pos hc))
  rwa [Q.mul_assoc, Q.mul_assoc, Q.mul_inv_cancel (Q.ne_zero_of_pos hc), Q.mul_one, Q.mul_one] at h1

private theorem q_neg_le_neg {a b : Q} (h : a ≤ b) : -b ≤ -a := by
  have h1 := Q.add_le_add_right h (-a + -b)
  have hL : a + (-a + -b) = -b := by
    calc a + (-a + -b) = (a + -a) + -b := (Q.add_assoc a (-a) (-b)).symm
      _ = -b := by rw [Q.add_right_neg, Q.zero_add]
  have hR : b + (-a + -b) = -a := by
    calc b + (-a + -b) = (b + -b) + -a := by ac_rfl
      _ = -a := by rw [Q.add_right_neg, Q.zero_add]
  rwa [hL, hR] at h1

private theorem q_add_le_add {a b c d : Q} (hab : a ≤ b) (hcd : c ≤ d) : a + c ≤ b + d :=
  Q.le_trans (Q.add_le_add_right hab c) (Q.add_le_add_left hcd b)

private theorem q_sub_le_sub {a b c d : Q} (hab : a ≤ b) (hcd : c ≤ d) : a - d ≤ b - c :=
  q_add_le_add hab (q_neg_le_neg hcd)

private theorem q_sub_div (a b c : Q) : (a - b) / c = a / c - b / c := by
  change (a + -b) * Q.inv c = a * Q.inv c + -(b * Q.inv c)
  rw [Q.right_distrib, Q.neg_mul]

private theorem q_div_div {a b c : Q} (hb : b ≠ 0) (hc : c ≠ 0) : (a / b) / c = a / (b * c) := by
  rw [q_eq_div_iff (q_mul_ne_zero hb hc)]
  calc ((a / b) / c) * (b * c)
      = (((a / b) / c) * c) * b := by ac_rfl
    _ = (a / b) * b := by rw [Q.div_mul_cancel hc]
    _ = a := Q.div_mul_cancel hb

private theorem q_div_mul_cancel_num {a b c : Q} (hb : b ≠ 0) (hc : c ≠ 0) : (a * b) / (c * b) = a / c := by
  rw [q_div_eq_iff (q_mul_ne_zero hc hb)]
  calc a * b = ((a / c) * c) * b := by rw [Q.div_mul_cancel hc]
    _ = (a / c) * (c * b) := by ac_rfl

private theorem q_pos_of_lt_zero_neg {a : Q} (ha : a < 0) : 0 < -a := by
  refine ⟨?_, ?_⟩
  · have h := q_neg_le_neg ha.1
    rwa [Q.neg_zero] at h
  · intro hz; apply ha.2
    have h1 := congrArg (fun x : Q => -x) hz
    dsimp only at h1
    rw [Q.neg_neg, Q.neg_zero] at h1
    exact h1.symm

private theorem q_neg_lt_zero_of_pos {a : Q} (ha : 0 < a) : -a < 0 := by
  refine ⟨?_, ?_⟩
  · have h := q_neg_le_neg ha.1
    rwa [Q.neg_zero] at h
  · intro hz; apply ha.2
    have h1 := congrArg (fun x : Q => -x) hz
    dsimp only at h1
    rw [Q.neg_neg, Q.neg_zero] at h1
    exact h1.symm

/-! #### 1. Exact Lorentzian Resolvent Expansion & Markov `xi^{-5}` Two-Sided Bounds -/

theorem lorentz_resolvent_identity (s lam : Q) (hs : s ≠ 0) (hd : s * s + lam ≠ 0) :
    s / (s * s + lam) =
    1 / s - lam / (s * s * s) + (lam * lam) / (s * s * s * s * s) -
    (lam * lam * lam) / ((s * s * s * s * s) * (s * s + lam)) := by
  have hs2 : s * s ≠ 0 := q_mul_ne_zero hs hs
  have hs3 : s * s * s ≠ 0 := q_mul_ne_zero hs2 hs
  have hs5 : s * s * s * s * s ≠ 0 := q_mul_ne_zero (q_mul_ne_zero hs3 hs) hs
  have hden : (s * s * s * s * s) * (s * s + lam) ≠ 0 := q_mul_ne_zero hs5 hd
  apply q_eq_of_mul_eq_right hden
  have hL : (s / (s * s + lam)) * (s * s * s * s * s * (s * s + lam)) = s * s * s * s * s * s := by
    calc (s * Q.inv (s * s + lam)) * (s * s * s * s * s * (s * s + lam))
        = (s * s * s * s * s * s) * ((s * s + lam) * Q.inv (s * s + lam)) := by ac_rfl
      _ = s * s * s * s * s * s := by rw [Q.mul_inv_cancel hd, Q.mul_one]
  have t1 : (1 / s) * (s * s * s * s * s * (s * s + lam)) = s * s * s * s * (s * s + lam) := by
    change (1 * Q.inv s) * (s * s * s * s * s * (s * s + lam)) = _
    rw [Q.one_mul]
    calc Q.inv s * (s * s * s * s * s * (s * s + lam))
        = s * s * s * s * (s * s + lam) * (s * Q.inv s) := by ac_rfl
      _ = s * s * s * s * (s * s + lam) := by rw [Q.mul_inv_cancel hs, Q.mul_one]
  have t2 : (lam / (s * s * s)) * (s * s * s * s * s * (s * s + lam)) = lam * s * s * (s * s + lam) := by
    calc (lam * Q.inv (s * s * s)) * (s * s * s * s * s * (s * s + lam))
        = lam * s * s * (s * s + lam) * ((s * s * s) * Q.inv (s * s * s)) := by ac_rfl
      _ = lam * s * s * (s * s + lam) := by rw [Q.mul_inv_cancel hs3, Q.mul_one]
  have t3 : ((lam * lam) / (s * s * s * s * s)) * (s * s * s * s * s * (s * s + lam)) = lam * lam * (s * s + lam) := by
    calc ((lam * lam) * Q.inv (s * s * s * s * s)) * (s * s * s * s * s * (s * s + lam))
        = lam * lam * (s * s + lam) * ((s * s * s * s * s) * Q.inv (s * s * s * s * s)) := by ac_rfl
      _ = lam * lam * (s * s + lam) := by rw [Q.mul_inv_cancel hs5, Q.mul_one]
  have t4 : ((lam * lam * lam) / ((s * s * s * s * s) * (s * s + lam))) * (s * s * s * s * s * (s * s + lam)) = lam * lam * lam :=
    Q.div_mul_cancel hden
  rw [hL, Q.sub_eq_add_neg, Q.sub_eq_add_neg, Q.right_distrib, Q.right_distrib, Q.right_distrib,
      Q.neg_mul, Q.neg_mul, t1, t2, t3, t4]
  simp only [Q.left_distrib, Q.neg_add, Q.mul_assoc]
  have k1 : s * (s * (s * (s * lam))) + -(lam * (s * (s * (s * s)))) = 0 := by
    rw [show lam * (s * (s * (s * s))) = s * (s * (s * (s * lam))) from by ac_rfl, Q.add_right_neg]
  have k2 : -(lam * (s * (s * lam))) + lam * (lam * (s * s)) = 0 := by
    rw [show lam * (s * (s * lam)) = lam * (lam * (s * s)) from by ac_rfl, Q.add_left_neg]
  have k3 : lam * (lam * lam) + -(lam * (lam * lam)) = 0 := Q.add_right_neg _
  rw [show (s * (s * (s * (s * (s * s)))) + s * (s * (s * (s * lam))) +
            (-(lam * (s * (s * (s * s)))) + -(lam * (s * (s * lam)))) +
            (lam * (lam * (s * s)) + lam * (lam * lam)) + -(lam * (lam * lam))) =
            s * (s * (s * (s * (s * s)))) +
            ((s * (s * (s * (s * lam))) + -(lam * (s * (s * (s * s))))) +
             (-(lam * (s * (s * lam))) + lam * (lam * (s * s))) +
             (lam * (lam * lam) + -(lam * (lam * lam)))) from by ac_rfl,
      k1, k2, k3, Q.add_zero, Q.add_zero, Q.add_zero]

structure SpectralMode where
  w : Q
  lam : Q
  hw : 0 ≤ w
  hlam : 0 ≤ lam

def specM0 (N : Nat) (m : Fin N → SpectralMode) : Q := sumFinQ N (fun j => (m j).w)
def specM2 (N : Nat) (m : Fin N → SpectralMode) : Q := sumFinQ N (fun j => (m j).w * (m j).lam)
def specM4 (N : Nat) (m : Fin N → SpectralMode) : Q := sumFinQ N (fun j => (m j).w * (m j).lam * (m j).lam)
def specM6 (N : Nat) (m : Fin N → SpectralMode) : Q := sumFinQ N (fun j => (m j).w * ((m j).lam * (m j).lam * (m j).lam))

def laplacePS (s : Q) (N : Nat) (m : Fin N → SpectralMode) : Q :=
  sumFinQ N (fun j => (m j).w * s / (s * s + (m j).lam))

def laplaceRem (s : Q) (N : Nat) (m : Fin N → SpectralMode) : Q :=
  sumFinQ N (fun j => (m j).w * ((m j).lam * (m j).lam * (m j).lam) / (s * s + (m j).lam))

private theorem sumFinQ_div_right (N : Nat) (f : Fin N → Q) (c : Q) :
    sumFinQ N (fun j => f j / c) = sumFinQ N f / c := by
  change sumFinQ N (fun j => f j * Q.inv c) = sumFinQ N f * Q.inv c
  have hf : (fun j => f j * Q.inv c) = (fun j => Q.inv c * f j) := funext (fun j => Q.mul_comm _ _)
  rw [hf, sumFinQ_mul_left, Q.mul_comm]

theorem laplacePS_expansion (s : Q) (hs : 0 < s) (N : Nat) (m : Fin N → SpectralMode)
    (hM0 : specM0 N m = 1) :
    laplacePS s N m =
    1 / s - specM2 N m / (s * s * s) + specM4 N m / (s * s * s * s * s) -
    laplaceRem s N m / (s * s * s * s * s) := by
  have hsne : s ≠ 0 := Q.ne_zero_of_pos hs
  have hs2 : 0 < s * s := Q.mul_pos hs hs
  have hs5 : s * s * s * s * s ≠ 0 := q_mul_ne_zero (q_mul_ne_zero (q_mul_ne_zero (q_mul_ne_zero hsne hsne) hsne) hsne) hsne
  have hterm : (fun j : Fin N => (m j).w * s / (s * s + (m j).lam)) =
      (fun j : Fin N =>
        ((m j).w / s - (m j).w * (m j).lam / (s * s * s) + (m j).w * (m j).lam * (m j).lam / (s * s * s * s * s)) -
        ((m j).w * ((m j).lam * (m j).lam * (m j).lam) / (s * s + (m j).lam)) / (s * s * s * s * s)) := by
    funext j
    have hd : s * s + (m j).lam ≠ 0 := Q.ne_zero_of_pos (q_add_pos_of_pos_of_nonneg hs2 (m j).hlam)
    rw [show (m j).w * s / (s * s + (m j).lam) = (m j).w * (s / (s * s + (m j).lam)) from Q.mul_assoc _ _ _,
        lorentz_resolvent_identity s (m j).lam hsne hd]
    have e1 : (m j).w * (1 / s) = (m j).w / s := by
      change (m j).w * (1 * Q.inv s) = (m j).w * Q.inv s; rw [Q.one_mul]
    have e2 : (m j).w * ((m j).lam / (s * s * s)) = (m j).w * (m j).lam / (s * s * s) :=
      (Q.mul_assoc _ _ _).symm
    have e3 : (m j).w * (((m j).lam * (m j).lam) / (s * s * s * s * s)) = (m j).w * (m j).lam * (m j).lam / (s * s * s * s * s) := by
      change (m j).w * (((m j).lam * (m j).lam) * Q.inv _) = ((m j).w * (m j).lam * (m j).lam) * Q.inv _
      rw [← Q.mul_assoc, ← Q.mul_assoc]
    have e4 : (m j).w * (((m j).lam * (m j).lam * (m j).lam) / ((s * s * s * s * s) * (s * s + (m j).lam))) =
        ((m j).w * ((m j).lam * (m j).lam * (m j).lam) / (s * s + (m j).lam)) / (s * s * s * s * s) := by
      rw [q_div_div hd hs5, Q.mul_comm (s * s + (m j).lam) (s * s * s * s * s)]
      exact (Q.mul_assoc _ _ _).symm
    rw [Q.sub_eq_add_neg, Q.sub_eq_add_neg, Q.left_distrib, Q.left_distrib, Q.left_distrib,
        Q.mul_neg, Q.mul_neg, e1, e2, e3, e4]
    simp only [Q.sub_eq_add_neg]
  unfold laplacePS
  rw [hterm, ← sumFinQ_sub, sumFinQ_add, ← sumFinQ_sub,
      sumFinQ_div_right, sumFinQ_div_right, sumFinQ_div_right, sumFinQ_div_right]
  change specM0 N m / s - specM2 N m / (s * s * s) + specM4 N m / (s * s * s * s * s) -
         laplaceRem s N m / (s * s * s * s * s) = _
  rw [hM0]

theorem laplaceRem_bounds (s : Q) (hs : 0 < s) (N : Nat) (m : Fin N → SpectralMode) :
    0 ≤ laplaceRem s N m ∧ laplaceRem s N m ≤ specM6 N m / (s * s) := by
  have hs2 : 0 < s * s := Q.mul_pos hs hs
  induction N with
  | zero =>
    unfold laplaceRem specM6 sumFinQ
    exact ⟨Q.le_refl 0, by change 0 ≤ 0 * Q.inv (s * s); rw [Q.zero_mul]; exact Q.le_refl 0⟩
  | succ N' ih =>
    have htail := ih (fun j => m j.succ)
    have h0num : 0 ≤ (m 0).w * ((m 0).lam * (m 0).lam * (m 0).lam) :=
      Q.mul_nonneg (m 0).hw (Q.mul_nonneg (Q.mul_nonneg (m 0).hlam (m 0).hlam) (m 0).hlam)
    have h0den_pos : 0 < s * s + (m 0).lam := q_add_pos_of_pos_of_nonneg hs2 (m 0).hlam
    have h0den_ge : s * s ≤ s * s + (m 0).lam := by
      have := Q.add_le_add_left (m 0).hlam (s * s)
      rwa [Q.add_zero] at this
    have h0_nn : 0 ≤ (m 0).w * ((m 0).lam * (m 0).lam * (m 0).lam) / (s * s + (m 0).lam) :=
      q_div_nonneg h0num h0den_pos
    have h0_ub : (m 0).w * ((m 0).lam * (m 0).lam * (m 0).lam) / (s * s + (m 0).lam) ≤
                 (m 0).w * ((m 0).lam * (m 0).lam * (m 0).lam) / (s * s) :=
      q_div_le_div_of_nonneg_left h0num hs2 h0den_ge
    unfold laplaceRem specM6 sumFinQ
    constructor
    · exact q_add_nonneg h0_nn htail.1
    · rw [Q.add_div]
      exact q_add_le_add h0_ub htail.2

private theorem q_diff4_cancel (a b c1 d1 c2 d2 : Q) :
    (a - b + c1 - d1) - (a - b + c2 - d2) = (c1 - c2) - (d1 - d2) := by
  simp only [Q.sub_eq_add_neg, Q.neg_add, Q.neg_neg]
  have ca : a + -a = 0 := Q.add_right_neg a
  have cb : -b + b = 0 := Q.add_left_neg b
  calc a + -b + c1 + -d1 + (-a + b + -c2 + d2)
      = (a + -a) + (-b + b) + (c1 + -c2 + (-d1 + d2)) := by ac_rfl
    _ = c1 + -c2 + (-d1 + d2) := by rw [ca, cb, Q.zero_add, Q.zero_add]

private theorem q_sub_half (x : Q) : x - x / Q.ofInt 2 = x / Q.ofInt 2 := by
  have h2pos : (0 : Q) < Q.ofInt 2 := ofInt_pos_nat (n := 2) (by decide)
  have h2ne : Q.ofInt 2 ≠ 0 := Q.ne_zero_of_pos h2pos
  have h21 : Q.ofInt 2 = 1 + 1 := qrel_eq _ _ (by decide)
  have htwo : x = x / Q.ofInt 2 + x / Q.ofInt 2 := by
    calc x = (x * Q.ofInt 2) / Q.ofInt 2 := (Q.mul_div_cancel h2ne).symm
      _ = (x * (1 + 1)) / Q.ofInt 2 := by rw [h21]
      _ = (x + x) / Q.ofInt 2 := by rw [Q.left_distrib, Q.mul_one]
      _ = x / Q.ofInt 2 + x / Q.ofInt 2 := Q.add_div x x (Q.ofInt 2)
  calc x - x / Q.ofInt 2
      = (x / Q.ofInt 2 + x / Q.ofInt 2) - x / Q.ofInt 2 := by rw [← htwo]
    _ = x / Q.ofInt 2 := by rw [Q.sub_eq_add_neg, Q.add_assoc, Q.add_right_neg, Q.add_zero]

private theorem q_add_half (x : Q) : x + x / Q.ofInt 2 = Q.ofInt 3 * x / Q.ofInt 2 := by
  have h2pos : (0 : Q) < Q.ofInt 2 := ofInt_pos_nat (n := 2) (by decide)
  have h2ne : Q.ofInt 2 ≠ 0 := Q.ne_zero_of_pos h2pos
  have h3def : Q.ofInt 3 = Q.ofInt 2 + 1 := qrel_eq _ _ (by decide)
  calc x + x / Q.ofInt 2
      = (Q.ofInt 2 * x) / Q.ofInt 2 + x / Q.ofInt 2 := by rw [Q.mul_comm, Q.mul_div_cancel h2ne]
    _ = (Q.ofInt 2 * x + x) / Q.ofInt 2 := (Q.add_div _ _ _).symm
    _ = (Q.ofInt 2 * x + 1 * x) / Q.ofInt 2 := by rw [Q.one_mul]
    _ = ((Q.ofInt 2 + 1) * x) / Q.ofInt 2 := by rw [← Q.right_distrib]
    _ = Q.ofInt 3 * x / Q.ofInt 2 := by rw [← h3def]

private theorem q_sub_le_add_of_neg_le (x : Q) {y z : Q} (h : -z ≤ y) : x - y ≤ x + z := by
  have h1 := q_sub_le_sub (Q.le_refl x) h
  rwa [Q.sub_eq_add_neg (b := -z), Q.neg_neg] at h1

theorem markov_contrast_two_sided {N1 N0 : Nat} (mθ : Fin N1 → SpectralMode) (m0 : Fin N0 → SpectralMode)
    (hM0_θ : specM0 N1 mθ = 1) (hM0_0 : specM0 N0 m0 = 1)
    (hM2 : specM2 N1 mθ = specM2 N0 m0)
    (B6 k s : Q) (hM6θ : specM6 N1 mθ ≤ B6) (hM6_0 : specM6 N0 m0 ≤ B6)
    (hk : 0 < k) (hs : 0 < s)
    (hΔpos : 0 < specM4 N1 mθ - specM4 N0 m0)
    (hthresh : Q.ofInt 2 * B6 ≤ (specM4 N1 mθ - specM4 N0 m0) * (s * s)) :
    let ΔM4 := specM4 N1 mθ - specM4 N0 m0
    let s5 := s * s * s * s * s
    let diff := k * (laplacePS s N1 mθ - laplacePS s N0 m0)
    (k * ΔM4) / (Q.ofInt 2 * s5) ≤ diff ∧ diff ≤ (Q.ofInt 3 * k * ΔM4) / (Q.ofInt 2 * s5) := by
  let _ := hΔpos
  dsimp only
  let ΔM4 := specM4 N1 mθ - specM4 N0 m0
  let s5 := s * s * s * s * s
  have hs2 : 0 < s * s := Q.mul_pos hs hs
  have hs5 : 0 < s5 := Q.mul_pos (Q.mul_pos (Q.mul_pos hs2 hs) hs) hs
  have h2pos : (0 : Q) < Q.ofInt 2 := ofInt_pos_nat (n := 2) (by decide)
  have hks5_pos : 0 < k / s5 := q_div_pos hk hs5
  have hexpθ := laplacePS_expansion s hs N1 mθ hM0_θ
  have hexp0 := laplacePS_expansion s hs N0 m0 hM0_0
  have hdiff : laplacePS s N1 mθ - laplacePS s N0 m0 =
      (ΔM4 - (laplaceRem s N1 mθ - laplaceRem s N0 m0)) / s5 := by
    rw [hexpθ, hexp0, hM2, q_diff4_cancel, q_sub_div, q_sub_div, q_sub_div]
  have hremθ := laplaceRem_bounds s hs N1 mθ
  have hrem0 := laplaceRem_bounds s hs N0 m0
  have hrem_ub : laplaceRem s N1 mθ - laplaceRem s N0 m0 ≤ B6 / (s * s) := by
    have h1 := Q.le_trans hremθ.2 (Q.div_le_div_of_nonneg_right hM6θ hs2)
    have h2 : laplaceRem s N1 mθ - laplaceRem s N0 m0 ≤ laplaceRem s N1 mθ := by
      have := Q.add_le_add_left (q_neg_le_neg hrem0.1) (laplaceRem s N1 mθ)
      rwa [Q.neg_zero, Q.add_zero] at this
    exact Q.le_trans h2 h1
  have hrem_lb : -(B6 / (s * s)) ≤ laplaceRem s N1 mθ - laplaceRem s N0 m0 := by
    have h1 : -(B6 / (s * s)) ≤ -laplaceRem s N0 m0 :=
      q_neg_le_neg (Q.le_trans hrem0.2 (Q.div_le_div_of_nonneg_right hM6_0 hs2))
    have h2 : -laplaceRem s N0 m0 ≤ laplaceRem s N1 mθ - laplaceRem s N0 m0 := by
      have := Q.add_le_add_right hremθ.1 (-laplaceRem s N0 m0)
      rwa [Q.zero_add] at this
    exact Q.le_trans h1 h2
  have hB6_half : B6 / (s * s) ≤ ΔM4 / Q.ofInt 2 := by
    have hs2_pos := hs2
    have h1 : B6 * Q.ofInt 2 ≤ ΔM4 * (s * s) := by rwa [Q.mul_comm]
    have h2 := Q.div_le_div_of_nonneg_right h1 (Q.mul_pos hs2_pos h2pos)
    have hL : (B6 * Q.ofInt 2) / ((s * s) * Q.ofInt 2) = B6 / (s * s) :=
      q_div_mul_cancel_num (Q.ne_zero_of_pos h2pos) (Q.ne_zero_of_pos hs2_pos)
    have hR : (ΔM4 * (s * s)) / ((s * s) * Q.ofInt 2) = ΔM4 / Q.ofInt 2 := by
      rw [Q.mul_comm (s * s) (Q.ofInt 2)]
      exact q_div_mul_cancel_num (Q.ne_zero_of_pos hs2_pos) (Q.ne_zero_of_pos h2pos)
    rwa [hL, hR] at h2
  have hcore_lb : ΔM4 / Q.ofInt 2 ≤ ΔM4 - (laplaceRem s N1 mθ - laplaceRem s N0 m0) := by
    have h1 : ΔM4 - B6 / (s * s) ≤ ΔM4 - (laplaceRem s N1 mθ - laplaceRem s N0 m0) :=
      q_sub_le_sub (Q.le_refl ΔM4) hrem_ub
    have h2 : ΔM4 - ΔM4 / Q.ofInt 2 ≤ ΔM4 - B6 / (s * s) :=
      q_sub_le_sub (Q.le_refl ΔM4) hB6_half
    rw [q_sub_half] at h2
    exact Q.le_trans h2 h1
  have hcore_ub : ΔM4 - (laplaceRem s N1 mθ - laplaceRem s N0 m0) ≤ Q.ofInt 3 * ΔM4 / Q.ofInt 2 := by
    have h1 := q_sub_le_add_of_neg_le ΔM4 hrem_lb
    have h2 : ΔM4 + B6 / (s * s) ≤ ΔM4 + ΔM4 / Q.ofInt 2 := Q.add_le_add_left hB6_half ΔM4
    rw [q_add_half] at h2
    exact Q.le_trans h1 h2
  have hmul_k : k * (laplacePS s N1 mθ - laplacePS s N0 m0) =
      (k / s5) * (ΔM4 - (laplaceRem s N1 mθ - laplaceRem s N0 m0)) := by
    rw [hdiff]; change k * (_ * Q.inv s5) = (k * Q.inv s5) * _; ac_rfl
  rw [hmul_k]
  constructor
  · have hm := Q.mul_le_mul_of_nonneg_left hcore_lb (Q.le_of_lt hks5_pos)
    have hl : (k / s5) * (ΔM4 / Q.ofInt 2) = (k * ΔM4) / (Q.ofInt 2 * s5) := by
      rw [← q_div_div (Q.ne_zero_of_pos h2pos) (Q.ne_zero_of_pos hs5)]
      change (k * Q.inv s5) * (ΔM4 * Q.inv (Q.ofInt 2)) = ((k * ΔM4) * Q.inv (Q.ofInt 2)) * Q.inv s5
      ac_rfl
    rwa [hl] at hm
  · have hm := Q.mul_le_mul_of_nonneg_left hcore_ub (Q.le_of_lt hks5_pos)
    have hr : (k / s5) * (Q.ofInt 3 * ΔM4 / Q.ofInt 2) = (Q.ofInt 3 * k * ΔM4) / (Q.ofInt 2 * s5) := by
      rw [← q_div_div (Q.ne_zero_of_pos h2pos) (Q.ne_zero_of_pos hs5)]
      change (k * Q.inv s5) * ((Q.ofInt 3 * ΔM4) * Q.inv (Q.ofInt 2)) =
             ((Q.ofInt 3 * k * ΔM4) * Q.inv (Q.ofInt 2)) * Q.inv s5
      ac_rfl
    rwa [hr] at hm

theorem markov_xi5_envelope {N1 N0 : Nat} (mθ : Fin N1 → SpectralMode) (m0 : Fin N0 → SpectralMode)
    (hM0_θ : specM0 N1 mθ = 1) (hM0_0 : specM0 N0 m0 = 1)
    (hM2 : specM2 N1 mθ = specM2 N0 m0)
    (B6 k ξ : Q) (hM6θ : specM6 N1 mθ ≤ B6) (hM6_0 : specM6 N0 m0 ≤ B6)
    (hk : 0 < k) (hξ : 1 ≤ ξ)
    (hΔpos : 0 < specM4 N1 mθ - specM4 N0 m0)
    (hthresh : Q.ofInt 2 * B6 ≤ (specM4 N1 mθ - specM4 N0 m0) * (((1 + ξ) * k) * ((1 + ξ) * k))) :
    let ΔM4 := specM4 N1 mθ - specM4 N0 m0
    let k4 := k * k * k * k
    let ξ5 := ξ * ξ * ξ * ξ * ξ
    let diff := k * (laplacePS ((1 + ξ) * k) N1 mθ - laplacePS ((1 + ξ) * k) N0 m0)
    ΔM4 / (Q.ofInt 64 * k4 * ξ5) ≤ diff ∧ diff ≤ (Q.ofInt 3 * ΔM4) / (Q.ofInt 2 * k4 * ξ5) := by
  dsimp only
  let s := (1 + ξ) * k
  let ΔM4 := specM4 N1 mθ - specM4 N0 m0
  let s5 := s * s * s * s * s
  let k4 := k * k * k * k
  let ξ5 := ξ * ξ * ξ * ξ * ξ
  have hξ_pos : 0 < ξ := Q.lt_of_lt_of_le Q.zero_lt_one hξ
  have hs_pos : 0 < s := Q.mul_pos (q_add_pos_of_pos_of_nonneg Q.zero_lt_one (Q.le_of_lt hξ_pos)) hk
  have htwo_band := markov_contrast_two_sided mθ m0 hM0_θ hM0_0 hM2 B6 k s hM6θ hM6_0 hk hs_pos hΔpos hthresh
  dsimp only at htwo_band
  have hxik_le_s : ξ * k ≤ s := by
    have h1 : ξ ≤ 1 + ξ := by
      have := Q.add_le_add_right (Q.le_of_lt Q.zero_lt_one) ξ
      rwa [Q.zero_add] at this
    exact Q.mul_le_mul_of_nonneg_right h1 (Q.le_of_lt hk)
  have hs_le_2xik : s ≤ Q.ofInt 2 * ξ * k := by
    have h1 : 1 + ξ ≤ Q.ofInt 2 * ξ := by
      have h2x : Q.ofInt 2 * ξ = ξ + ξ := by
        have h21 : Q.ofInt 2 = 1 + 1 := qrel_eq _ _ (by decide)
        rw [h21, Q.right_distrib, Q.one_mul]
      rw [h2x]; exact Q.add_le_add_right hξ ξ
    exact Q.mul_le_mul_of_nonneg_right h1 (Q.le_of_lt hk)
  have hxik_pos : 0 < ξ * k := Q.mul_pos hξ_pos hk
  have hpow5_le : ∀ {a b : Q}, 0 < a → a ≤ b → a * a * a * a * a ≤ b * b * b * b * b := by
    intro a b ha hab
    have hb := Q.le_trans (Q.le_of_lt ha) hab
    have ha0 := Q.le_of_lt ha
    have h2 : a * a ≤ b * b := Q.le_trans (Q.mul_le_mul_of_nonneg_right hab ha0) (Q.mul_le_mul_of_nonneg_left hab hb)
    have ha2 : 0 ≤ a * a := Q.mul_nonneg ha0 ha0
    have hb2 : 0 ≤ b * b := Q.mul_nonneg hb hb
    have h4 : (a * a) * (a * a) ≤ (b * b) * (b * b) :=
      Q.le_trans (Q.mul_le_mul_of_nonneg_right h2 ha2) (Q.mul_le_mul_of_nonneg_left h2 hb2)
    have h4' : a * a * a * a ≤ b * b * b * b := by
      calc a * a * a * a = (a * a) * (a * a) := by ac_rfl
        _ ≤ (b * b) * (b * b) := h4
        _ = b * b * b * b := by ac_rfl
    have hb4 : 0 ≤ b * b * b * b := Q.mul_nonneg (Q.mul_nonneg hb2 hb) hb
    exact Q.le_trans (Q.mul_le_mul_of_nonneg_right h4' ha0) (Q.mul_le_mul_of_nonneg_left hab hb4)
  have hs5_lb : (ξ * k) * (ξ * k) * (ξ * k) * (ξ * k) * (ξ * k) ≤ s5 := hpow5_le hxik_pos hxik_le_s
  have hs5_ub : s5 ≤ (Q.ofInt 2 * ξ * k) * (Q.ofInt 2 * ξ * k) * (Q.ofInt 2 * ξ * k) * (Q.ofInt 2 * ξ * k) * (Q.ofInt 2 * ξ * k) :=
    hpow5_le hs_pos hs_le_2xik
  have hxik5_eq : (ξ * k) * (ξ * k) * (ξ * k) * (ξ * k) * (ξ * k) = k4 * k * ξ5 := by
    dsimp only [k4, ξ5]; ac_rfl
  have h32_eq : (Q.ofInt 2 * ξ * k) * (Q.ofInt 2 * ξ * k) * (Q.ofInt 2 * ξ * k) * (Q.ofInt 2 * ξ * k) * (Q.ofInt 2 * ξ * k) =
      Q.ofInt 32 * k4 * k * ξ5 := by
    dsimp only [k4, ξ5]
    have h32 : Q.ofInt 2 * Q.ofInt 2 * Q.ofInt 2 * Q.ofInt 2 * Q.ofInt 2 = Q.ofInt 32 := qrel_eq _ _ (by decide)
    calc (Q.ofInt 2 * ξ * k) * (Q.ofInt 2 * ξ * k) * (Q.ofInt 2 * ξ * k) * (Q.ofInt 2 * ξ * k) * (Q.ofInt 2 * ξ * k)
        = (Q.ofInt 2 * Q.ofInt 2 * Q.ofInt 2 * Q.ofInt 2 * Q.ofInt 2) * (k * k * k * k) * k * (ξ * ξ * ξ * ξ * ξ) := by ac_rfl
      _ = Q.ofInt 32 * (k * k * k * k) * k * (ξ * ξ * ξ * ξ * ξ) := by rw [h32]
  have hs5_pos : 0 < s5 := Q.mul_pos (Q.mul_pos (Q.mul_pos (Q.mul_pos hs_pos hs_pos) hs_pos) hs_pos) hs_pos
  have hk_ne : k ≠ 0 := Q.ne_zero_of_pos hk
  have h2_pos : (0 : Q) < Q.ofInt 2 := ofInt_pos_nat (n := 2) (by decide)
  have h3_pos : (0 : Q) < Q.ofInt 3 := ofInt_pos_nat (n := 3) (by decide)
  have h64_pos : (0 : Q) < Q.ofInt 64 := ofInt_pos_nat (n := 64) (by decide)
  have hk4_pos : 0 < k4 := Q.mul_pos (Q.mul_pos (Q.mul_pos hk hk) hk) hk
  have hξ5_pos : 0 < ξ5 := Q.mul_pos (Q.mul_pos (Q.mul_pos (Q.mul_pos hξ_pos hξ_pos) hξ_pos) hξ_pos) hξ_pos
  have hxik5_pos : 0 < k4 * k * ξ5 := Q.mul_pos (Q.mul_pos hk4_pos hk) hξ5_pos
  constructor
  · have hs5_ub' : Q.ofInt 2 * s5 ≤ Q.ofInt 64 * k4 * k * ξ5 := by
      have h64 : Q.ofInt 2 * Q.ofInt 32 = Q.ofInt 64 := qrel_eq _ _ (by decide)
      have h := Q.mul_le_mul_of_nonneg_left (by rwa [h32_eq] at hs5_ub) (Q.le_of_lt h2_pos)
      calc Q.ofInt 2 * s5 ≤ Q.ofInt 2 * (Q.ofInt 32 * k4 * k * ξ5) := h
        _ = (Q.ofInt 2 * Q.ofInt 32) * k4 * k * ξ5 := by ac_rfl
        _ = Q.ofInt 64 * k4 * k * ξ5 := by rw [h64]
    have hdiv := q_div_le_div_of_nonneg_left (Q.mul_nonneg (Q.le_of_lt hk) (Q.le_of_lt hΔpos))
      (Q.mul_pos h2_pos hs5_pos) hs5_ub'
    have hL : (k * ΔM4) / (Q.ofInt 64 * k4 * k * ξ5) = ΔM4 / (Q.ofInt 64 * k4 * ξ5) := by
      rw [show Q.ofInt 64 * k4 * k * ξ5 = (Q.ofInt 64 * k4 * ξ5) * k from by ac_rfl,
          Q.mul_comm k ΔM4]
      exact q_div_mul_cancel_num hk_ne (Q.ne_zero_of_pos (Q.mul_pos (Q.mul_pos h64_pos hk4_pos) hξ5_pos))
    rw [hL] at hdiv
    exact Q.le_trans hdiv htwo_band.1
  · have hs5_lb' : Q.ofInt 2 * (k4 * k * ξ5) ≤ Q.ofInt 2 * s5 := by
      rw [hxik5_eq] at hs5_lb
      exact Q.mul_le_mul_of_nonneg_left hs5_lb (Q.le_of_lt h2_pos)
    have hdiv := q_div_le_div_of_nonneg_left
      (Q.mul_nonneg (Q.mul_nonneg (Q.le_of_lt h3_pos) (Q.le_of_lt hk)) (Q.le_of_lt hΔpos))
      (Q.mul_pos h2_pos hxik5_pos) hs5_lb'
    have hR : (Q.ofInt 3 * k * ΔM4) / (Q.ofInt 2 * (k4 * k * ξ5)) = (Q.ofInt 3 * ΔM4) / (Q.ofInt 2 * k4 * ξ5) := by
      rw [show Q.ofInt 3 * k * ΔM4 = (Q.ofInt 3 * ΔM4) * k from by ac_rfl,
          show Q.ofInt 2 * (k4 * k * ξ5) = (Q.ofInt 2 * k4 * ξ5) * k from by ac_rfl]
      exact q_div_mul_cancel_num hk_ne (Q.ne_zero_of_pos (Q.mul_pos (Q.mul_pos h2_pos hk4_pos) hξ5_pos))
    rw [hR] at hdiv
    exact Q.le_trans htwo_band.2 hdiv

/-! #### 2. Sign-Flip Blind Spot (`xi_flip` Witness & General Reversal Guarantee) -/

theorem markov_sign_flip_guarantee {N1 N0 : Nat} (mθ : Fin N1 → SpectralMode) (m0 : Fin N0 → SpectralMode)
    (hM0_θ : specM0 N1 mθ = 1) (hM0_0 : specM0 N0 m0 = 1)
    (hM2 : specM2 N1 mθ = specM2 N0 m0)
    (B6 k s : Q) (hM6θ : specM6 N1 mθ ≤ B6) (hM6_0 : specM6 N0 m0 ≤ B6)
    (hk : 0 < k) (hs : 0 < s)
    (hΔpos : 0 < specM4 N1 mθ - specM4 N0 m0)
    (hthresh : Q.ofInt 2 * B6 ≤ (specM4 N1 mθ - specM4 N0 m0) * (s * s)) :
    k * (laplacePS s N0 m0 - laplacePS s N1 mθ) < 0 := by
  have htwo := markov_contrast_two_sided mθ m0 hM0_θ hM0_0 hM2 B6 k s hM6θ hM6_0 hk hs hΔpos hthresh
  dsimp only at htwo
  have hs5 : 0 < s * s * s * s * s := Q.mul_pos (Q.mul_pos (Q.mul_pos (Q.mul_pos hs hs) hs) hs) hs
  have hpos : 0 < (k * (specM4 N1 mθ - specM4 N0 m0)) / (Q.ofInt 2 * (s * s * s * s * s)) :=
    q_div_pos (Q.mul_pos hk hΔpos) (Q.mul_pos (ofInt_pos_nat (n := 2) (by decide)) hs5)
  have hpos2 : 0 < k * (laplacePS s N1 mθ - laplacePS s N0 m0) := Q.lt_of_lt_of_le hpos htwo.1
  have hneg : -(k * (laplacePS s N1 mθ - laplacePS s N0 m0)) = k * (laplacePS s N0 m0 - laplacePS s N1 mθ) := by
    rw [← Q.mul_neg, Q.sub_eq_add_neg, Q.neg_add, Q.neg_neg, Q.add_comm]; rfl
  rw [← hneg]
  exact q_neg_lt_zero_of_pos hpos2

private theorem q_pos_frac (n : Int) (d : Nat) (hn : 0 < n) : (0 : Q) < Q.frac n (d + 1) := by
  refine ⟨?_, ?_⟩
  · change (0 : Int) * QRaw.den ⟨n, d⟩ ≤ n * QRaw.den ⟨0, 0⟩
    simp [QRaw.den]; omega
  · intro h
    have hr := Quotient.exact h
    change QRel ⟨0, 0⟩ ⟨n, d⟩ at hr
    simp [QRel, QRaw.den] at hr
    omega

private def witnessModes0 : Fin 2 → SpectralMode
  | ⟨0, _⟩ => ⟨q12, 0, Q.le_of_lt (q_pos_frac 1 1 (by decide)), Q.le_refl 0⟩
  | ⟨1, _⟩ => ⟨q12, Q.ofInt 4, Q.le_of_lt (q_pos_frac 1 1 (by decide)), Q.le_of_lt (ofInt_pos_nat (n := 4) (by decide))⟩

private def witnessModes90 : Fin 2 → SpectralMode
  | ⟨0, _⟩ => ⟨Q.frac 9 10, Q.frac 8 9, Q.le_of_lt (q_pos_frac 9 9 (by decide)), Q.le_of_lt (q_pos_frac 8 8 (by decide))⟩
  | ⟨1, _⟩ => ⟨Q.frac 1 10, Q.ofInt 12, Q.le_of_lt (q_pos_frac 1 9 (by decide)), Q.le_of_lt (ofInt_pos_nat (n := 12) (by decide))⟩

theorem sign_flip_blind_spot_witness :
    specM0 2 witnessModes0 = 1 ∧
    specM0 2 witnessModes90 = 1 ∧
    specM2 2 witnessModes0 = specM2 2 witnessModes90 ∧
    specM4 2 witnessModes90 - specM4 2 witnessModes0 = Q.frac 64 9 ∧
    0 < laplacePS 1 2 witnessModes0 - laplacePS 1 2 witnessModes90 ∧
    laplacePS (Q.ofInt 10) 2 witnessModes0 - laplacePS (Q.ofInt 10) 2 witnessModes90 < 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold specM0 sumFinQ witnessModes0; exact qrel_eq _ _ (by decide)
  · unfold specM0 sumFinQ witnessModes90; exact qrel_eq _ _ (by decide)
  · unfold specM2 sumFinQ witnessModes0 witnessModes90; exact qrel_eq _ _ (by decide)
  · unfold specM4 sumFinQ witnessModes0 witnessModes90; exact qrel_eq _ _ (by decide)
  · have heq : laplacePS 1 2 witnessModes0 - laplacePS 1 2 witnessModes90 = Q.frac 128 1105 := by
      unfold laplacePS sumFinQ witnessModes0 witnessModes90; exact qrel_eq _ _ (by decide)
    rw [heq]; exact q_pos_frac 128 1104 (by decide)
  · have heq : laplacePS (Q.ofInt 10) 2 witnessModes0 - laplacePS (Q.ofInt 10) 2 witnessModes90 = -(Q.frac 97 1652560) := by
      unfold laplacePS sumFinQ witnessModes0 witnessModes90; exact qrel_eq _ _ (by decide)
    rw [heq]
    exact q_neg_lt_zero_of_pos (q_pos_frac 97 1652559 (by decide))

/-! #### 3. Mittag-Leffler `xi^{5-mu}` Separation (`mu = 1/2` over `Q` & General `PosPowModel`) -/

theorem ml_half_vs_markov_xi9_2 {N1 N0 : Nat} (mθ : Fin N1 → SpectralMode) (m0 : Fin N0 → SpectralMode)
    (hM0_θ : specM0 N1 mθ = 1) (hM0_0 : specM0 N0 m0 = 1)
    (hM2 : specM2 N1 mθ = specM2 N0 m0)
    (B6 k t cML ΔΦ_ML : Q)
    (hM6θ : specM6 N1 mθ ≤ B6) (hM6_0 : specM6 N0 m0 ≤ B6)
    (hk : 0 < k) (ht : 1 ≤ t) (hcML : 0 < cML)
    (hΔpos : 0 < specM4 N1 mθ - specM4 N0 m0)
    (hML : cML / t ≤ ΔΦ_ML)
    (hthresh : Q.ofInt 2 * B6 ≤ (specM4 N1 mθ - specM4 N0 m0) * (((1 + t * t) * k) * ((1 + t * t) * k))) :
    let ΔM4 := specM4 N1 mθ - specM4 N0 m0
    let k4 := k * k * k * k
    let t9 := t * t * t * t * t * t * t * t * t
    let ΔΦ_M := k * (laplacePS ((1 + t * t) * k) N1 mθ - laplacePS ((1 + t * t) * k) N0 m0)
    (Q.frac 2 3 * (cML * k4 / ΔM4)) * t9 ≤ ΔΦ_ML / ΔΦ_M := by
  dsimp only
  let ξ := t * t
  have ht_pos : 0 < t := Q.lt_of_lt_of_le Q.zero_lt_one ht
  have hξ : 1 ≤ ξ := by
    have h1 := Q.mul_le_mul_of_nonneg_right ht (Q.le_of_lt ht_pos)
    rw [Q.one_mul] at h1
    exact Q.le_trans ht h1
  have henv := markov_xi5_envelope mθ m0 hM0_θ hM0_0 hM2 B6 k ξ hM6θ hM6_0 hk hξ hΔpos hthresh
  dsimp only at henv
  let ΔM4 := specM4 N1 mθ - specM4 N0 m0
  let k4 := k * k * k * k
  let t9 := t * t * t * t * t * t * t * t * t
  let ξ5 := ξ * ξ * ξ * ξ * ξ
  let ΔΦ_M := k * (laplacePS ((1 + ξ) * k) N1 mθ - laplacePS ((1 + ξ) * k) N0 m0)
  have hξ_pos : 0 < ξ := Q.mul_pos ht_pos ht_pos
  have hk4_pos : 0 < k4 := Q.mul_pos (Q.mul_pos (Q.mul_pos hk hk) hk) hk
  have hξ5_pos : 0 < ξ5 := Q.mul_pos (Q.mul_pos (Q.mul_pos (Q.mul_pos hξ_pos hξ_pos) hξ_pos) hξ_pos) hξ_pos
  have h2_pos : (0 : Q) < Q.ofInt 2 := ofInt_pos_nat (n := 2) (by decide)
  have h3_pos : (0 : Q) < Q.ofInt 3 := ofInt_pos_nat (n := 3) (by decide)
  have h64_pos : (0 : Q) < Q.ofInt 64 := ofInt_pos_nat (n := 64) (by decide)
  have hM_pos : 0 < ΔΦ_M :=
    Q.lt_of_lt_of_le (q_div_pos hΔpos (Q.mul_pos (Q.mul_pos h64_pos hk4_pos) hξ5_pos)) henv.1
  have hupper_pos : 0 < (Q.ofInt 3 * ΔM4) / (Q.ofInt 2 * k4 * ξ5) :=
    q_div_pos (Q.mul_pos h3_pos hΔpos) (Q.mul_pos (Q.mul_pos h2_pos hk4_pos) hξ5_pos)
  have hinv_le : Q.inv ((Q.ofInt 3 * ΔM4) / (Q.ofInt 2 * k4 * ξ5)) ≤ Q.inv ΔΦ_M :=
    q_inv_le_inv hM_pos henv.2
  have hml_nonneg : 0 ≤ cML / t := Q.le_of_lt (q_div_pos hcML ht_pos)
  have hprod1 : (cML / t) * Q.inv ((Q.ofInt 3 * ΔM4) / (Q.ofInt 2 * k4 * ξ5)) ≤ (cML / t) * Q.inv ΔΦ_M :=
    Q.mul_le_mul_of_nonneg_left hinv_le hml_nonneg
  have hprod2 : (cML / t) * Q.inv ΔΦ_M ≤ ΔΦ_ML * Q.inv ΔΦ_M :=
    Q.mul_le_mul_of_nonneg_right hML (Q.le_of_lt (Q.inv_pos hM_pos))
  have hleft_eq : (cML / t) * Q.inv ((Q.ofInt 3 * ΔM4) / (Q.ofInt 2 * k4 * ξ5)) =
      (Q.frac 2 3 * (cML * k4 / ΔM4)) * t9 := by
    have hξ5_t10 : ξ5 = t9 * t := by dsimp only [ξ5, t9, ξ]; ac_rfl
    have ht_ne : t ≠ 0 := Q.ne_zero_of_pos ht_pos
    have hΔ_ne : ΔM4 ≠ 0 := Q.ne_zero_of_pos hΔpos
    have h32_ne : (Q.ofInt 3 * ΔM4) / (Q.ofInt 2 * k4 * ξ5) ≠ 0 := Q.ne_zero_of_pos hupper_pos
    have hmul_eq : ((cML / t) * Q.inv ((Q.ofInt 3 * ΔM4) / (Q.ofInt 2 * k4 * ξ5))) * ((Q.ofInt 3 * ΔM4) / (Q.ofInt 2 * k4 * ξ5)) =
                   ((Q.frac 2 3 * (cML * k4 / ΔM4)) * t9) * ((Q.ofInt 3 * ΔM4) / (Q.ofInt 2 * k4 * ξ5)) := by
      rw [Q.mul_assoc, Q.mul_comm (Q.inv _) _, Q.mul_inv_cancel h32_ne, Q.mul_one]
      have ht9_pos : 0 < t9 :=
        Q.mul_pos (Q.mul_pos (Q.mul_pos (Q.mul_pos (Q.mul_pos (Q.mul_pos (Q.mul_pos (Q.mul_pos ht_pos ht_pos) ht_pos) ht_pos) ht_pos) ht_pos) ht_pos) ht_pos) ht_pos
      have ha : Q.ofInt 2 ≠ 0 := Q.ne_zero_of_pos h2_pos
      have hb : k4 ≠ 0 := Q.ne_zero_of_pos hk4_pos
      have hc : t9 ≠ 0 := Q.ne_zero_of_pos ht9_pos
      have hk2t_ne : (Q.ofInt 2 * k4 * (t9 * t)) ≠ 0 := q_mul_ne_zero (q_mul_ne_zero ha hb) (q_mul_ne_zero hc ht_ne)
      have hq2 : Q.inv (Q.ofInt 2 * k4 * (t9 * t)) = Q.inv (Q.ofInt 2) * Q.inv k4 * Q.inv t9 * Q.inv t := by
        have h1 : (Q.ofInt 2 * k4 * (t9 * t)) * (Q.inv (Q.ofInt 2) * Q.inv k4 * Q.inv t9 * Q.inv t) = 1 := by
          calc (Q.ofInt 2 * k4 * (t9 * t)) * (Q.inv (Q.ofInt 2) * Q.inv k4 * Q.inv t9 * Q.inv t)
              = (Q.ofInt 2 * Q.inv (Q.ofInt 2)) * (k4 * Q.inv k4) * (t9 * Q.inv t9) * (t * Q.inv t) := by ac_rfl
            _ = 1 := by rw [Q.mul_inv_cancel ha, Q.mul_inv_cancel hb, Q.mul_inv_cancel hc, Q.mul_inv_cancel ht_ne, Q.one_mul, Q.one_mul, Q.one_mul]
        calc Q.inv (Q.ofInt 2 * k4 * (t9 * t))
            = Q.inv (Q.ofInt 2 * k4 * (t9 * t)) * 1 := (Q.mul_one _).symm
          _ = Q.inv (Q.ofInt 2 * k4 * (t9 * t)) * ((Q.ofInt 2 * k4 * (t9 * t)) * (Q.inv (Q.ofInt 2) * Q.inv k4 * Q.inv t9 * Q.inv t)) := by rw [h1]
          _ = (Q.inv (Q.ofInt 2 * k4 * (t9 * t)) * (Q.ofInt 2 * k4 * (t9 * t))) * (Q.inv (Q.ofInt 2) * Q.inv k4 * Q.inv t9 * Q.inv t) := (Q.mul_assoc _ _ _).symm
          _ = Q.inv (Q.ofInt 2) * Q.inv k4 * Q.inv t9 * Q.inv t := by rw [Q.mul_comm (Q.inv _), Q.mul_inv_cancel hk2t_ne, Q.one_mul]
      have hq1 : Q.frac 2 3 * Q.ofInt 3 / Q.ofInt 2 = 1 := qrel_eq _ _ (by decide)
      calc cML / t
          = cML * Q.inv t := rfl
        _ = cML * Q.inv t * ((Q.frac 2 3 * Q.ofInt 3 / Q.ofInt 2) * (k4 / k4) * (ΔM4 / ΔM4) * (t9 / t9)) := by
            rw [hq1, Q.div_self hb, Q.div_self hΔ_ne, Q.div_self hc, Q.mul_one, Q.mul_one, Q.mul_one, Q.mul_one]
        _ = Q.frac 2 3 * ((cML * k4) * Q.inv ΔM4) * t9 * ((Q.ofInt 3 * ΔM4) * (Q.inv (Q.ofInt 2) * Q.inv k4 * Q.inv t9 * Q.inv t)) := by
            change cML * Q.inv t * ((Q.frac 2 3 * Q.ofInt 3 * Q.inv (Q.ofInt 2)) * (k4 * Q.inv k4) * (ΔM4 * Q.inv ΔM4) * (t9 * Q.inv t9)) = _
            ac_rfl
        _ = ((Q.frac 2 3 * (cML * k4 / ΔM4)) * t9) * ((Q.ofInt 3 * ΔM4) / (Q.ofInt 2 * k4 * ξ5)) := by
            change _ = Q.frac 2 3 * ((cML * k4) * Q.inv ΔM4) * t9 * ((Q.ofInt 3 * ΔM4) * Q.inv (Q.ofInt 2 * k4 * ξ5))
            rw [hξ5_t10, hq2]
    exact q_eq_of_mul_eq_right h32_ne hmul_eq
  rw [← hleft_eq]
  exact Q.le_trans hprod1 hprod2

structure PosPowModel (F : Type) where
  zero : F
  one : F
  add : F → F → F
  neg : F → F
  mul : F → F → F
  inv : F → F
  le : F → F → Prop
  lt : F → F → Prop
  rpow : F → Q → F
  add_comm : ∀ a b, add a b = add b a
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  zero_add : ∀ a, add zero a = a
  add_right_neg : ∀ a, add a (neg a) = zero
  mul_comm : ∀ a b, mul a b = mul b a
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a, mul one a = a
  mul_inv_cancel : ∀ a, a ≠ zero → mul a (inv a) = one
  zero_lt_one : lt zero one
  le_trans : ∀ {a b c}, le a b → le b c → le a c
  le_of_lt : ∀ {a b}, lt a b → le a b
  lt_of_lt_of_le : ∀ {a b c}, lt a b → le b c → lt a c
  lt_of_le_of_lt : ∀ {a b c}, le a b → lt b c → lt a c
  ne_zero_of_pos : ∀ {a}, lt zero a → a ≠ zero
  mul_le_mul_of_nonneg_left : ∀ {a b c}, le a b → le zero c → le (mul c a) (mul c b)
  mul_le_mul_of_nonneg_right : ∀ {a b c}, le a b → le zero c → le (mul a c) (mul b c)
  mul_lt_mul_of_pos_left : ∀ {a b c}, lt a b → lt zero c → lt (mul c a) (mul c b)
  mul_pos : ∀ {a b}, lt zero a → lt zero b → lt zero (mul a b)
  inv_pos : ∀ {a}, lt zero a → lt zero (inv a)
  inv_anti : ∀ {a b}, lt zero a → le a b → le (inv b) (inv a)
  rpow_pos : ∀ x q, lt zero x → lt zero (rpow x q)
  rpow_add : ∀ x a b, lt zero x → mul (rpow x a) (rpow x b) = rpow x (a + b)
  rpow_neg : ∀ x a, lt zero x → rpow x (-a) = inv (rpow x a)
  rpow_mono_exp : ∀ x a b, lt one x → a < b → lt (rpow x a) (rpow x b)

theorem ml_separation_general {F : Type} (M : PosPowModel F)
    (μ : Q) (hμ_lt : μ < 1) (ξ cML cM ΔΦ_ML ΔΦ_M : F)
    (hξ : M.lt M.one ξ) (hcML : M.lt M.zero cML) (hcM : M.lt M.zero cM)
    (hΔM_pos : M.lt M.zero ΔΦ_M)
    (hML : M.le (M.mul cML (M.inv (M.rpow ξ μ))) ΔΦ_ML)
    (hMk : M.le ΔΦ_M (M.mul cM (M.inv (M.rpow ξ (Q.ofInt 5))))) :
    M.le (M.mul (M.mul cML (M.inv cM)) (M.rpow ξ (Q.ofInt 5 - μ))) (M.mul ΔΦ_ML (M.inv ΔΦ_M)) ∧
    M.lt (M.mul (M.mul cML (M.inv cM)) (M.rpow ξ (Q.ofInt 4))) (M.mul ΔΦ_ML (M.inv ΔΦ_M)) := by
  have hξ_pos : M.lt M.zero ξ := M.lt_of_lt_of_le M.zero_lt_one (M.le_of_lt hξ)
  have h5_pos := M.rpow_pos ξ (Q.ofInt 5) hξ_pos
  have hμ_pos := M.rpow_pos ξ μ hξ_pos
  have hup_pos : M.lt M.zero (M.mul cM (M.inv (M.rpow ξ (Q.ofInt 5)))) := M.mul_pos hcM (M.inv_pos h5_pos)
  have hinv_le : M.le (M.inv (M.mul cM (M.inv (M.rpow ξ (Q.ofInt 5))))) (M.inv ΔΦ_M) :=
    M.inv_anti hΔM_pos hMk
  have hml_lb_pos : M.lt M.zero (M.mul cML (M.inv (M.rpow ξ μ))) := M.mul_pos hcML (M.inv_pos hμ_pos)
  have h1 : M.le (M.mul (M.mul cML (M.inv (M.rpow ξ μ))) (M.inv (M.mul cM (M.inv (M.rpow ξ (Q.ofInt 5))))))
                 (M.mul (M.mul cML (M.inv (M.rpow ξ μ))) (M.inv ΔΦ_M)) :=
    M.mul_le_mul_of_nonneg_left hinv_le (M.le_of_lt hml_lb_pos)
  have h2 : M.le (M.mul (M.mul cML (M.inv (M.rpow ξ μ))) (M.inv ΔΦ_M)) (M.mul ΔΦ_ML (M.inv ΔΦ_M)) :=
    M.mul_le_mul_of_nonneg_right hML (M.le_of_lt (M.inv_pos hΔM_pos))
  have hcomb : M.le (M.mul (M.mul cML (M.inv (M.rpow ξ μ))) (M.inv (M.mul cM (M.inv (M.rpow ξ (Q.ofInt 5))))))
                    (M.mul ΔΦ_ML (M.inv ΔΦ_M)) := M.le_trans h1 h2
  have hinv_prod : M.inv (M.mul cM (M.inv (M.rpow ξ (Q.ofInt 5)))) = M.mul (M.inv cM) (M.rpow ξ (Q.ofInt 5)) := by
    have hcM_ne : cM ≠ M.zero := M.ne_zero_of_pos hcM
    have h5_ne : M.rpow ξ (Q.ofInt 5) ≠ M.zero := M.ne_zero_of_pos h5_pos
    have hmul_ne : M.mul cM (M.inv (M.rpow ξ (Q.ofInt 5))) ≠ M.zero := M.ne_zero_of_pos hup_pos
    have hswap4 : ∀ a b c d : F, M.mul (M.mul a b) (M.mul c d) = M.mul (M.mul a c) (M.mul d b) := by
      intro a b c d
      calc M.mul (M.mul a b) (M.mul c d)
          = M.mul a (M.mul b (M.mul c d)) := M.mul_assoc a b _
        _ = M.mul a (M.mul (M.mul c d) b) := by rw [M.mul_comm b (M.mul c d)]
        _ = M.mul a (M.mul c (M.mul d b)) := by rw [M.mul_assoc c d b]
        _ = M.mul (M.mul a c) (M.mul d b) := (M.mul_assoc a c _).symm
    have hprod1 : M.mul (M.mul cM (M.inv (M.rpow ξ (Q.ofInt 5)))) (M.mul (M.inv cM) (M.rpow ξ (Q.ofInt 5))) = M.one := by
      rw [hswap4]
      calc M.mul (M.mul cM (M.inv cM)) (M.mul (M.rpow ξ (Q.ofInt 5)) (M.inv (M.rpow ξ (Q.ofInt 5))))
          = M.mul M.one M.one := by rw [M.mul_inv_cancel cM hcM_ne, M.mul_inv_cancel (M.rpow ξ (Q.ofInt 5)) h5_ne]
        _ = M.one := M.one_mul M.one
    have hid : M.inv (M.mul cM (M.inv (M.rpow ξ (Q.ofInt 5)))) =
        M.mul (M.inv (M.mul cM (M.inv (M.rpow ξ (Q.ofInt 5))))) M.one := by
      rw [M.mul_comm _ M.one, M.one_mul]
    calc M.inv (M.mul cM (M.inv (M.rpow ξ (Q.ofInt 5))))
        = M.mul (M.inv (M.mul cM (M.inv (M.rpow ξ (Q.ofInt 5))))) M.one := hid
      _ = M.mul (M.inv (M.mul cM (M.inv (M.rpow ξ (Q.ofInt 5)))))
                (M.mul (M.mul cM (M.inv (M.rpow ξ (Q.ofInt 5)))) (M.mul (M.inv cM) (M.rpow ξ (Q.ofInt 5)))) := by rw [hprod1]
      _ = M.mul (M.mul (M.inv (M.mul cM (M.inv (M.rpow ξ (Q.ofInt 5))))) (M.mul cM (M.inv (M.rpow ξ (Q.ofInt 5)))))
                (M.mul (M.inv cM) (M.rpow ξ (Q.ofInt 5))) := (M.mul_assoc _ _ _).symm
      _ = M.mul (M.inv cM) (M.rpow ξ (Q.ofInt 5)) := by
          rw [M.mul_comm (M.inv _), M.mul_inv_cancel _ hmul_ne, M.one_mul]
  have hrhs_eq : M.mul (M.mul cML (M.inv (M.rpow ξ μ))) (M.inv (M.mul cM (M.inv (M.rpow ξ (Q.ofInt 5))))) =
      M.mul (M.mul cML (M.inv cM)) (M.rpow ξ (Q.ofInt 5 - μ)) := by
    rw [hinv_prod, ← M.rpow_neg ξ μ hξ_pos]
    have hexp : M.mul (M.rpow ξ (Q.ofInt 5)) (M.rpow ξ (-μ)) = M.rpow ξ (Q.ofInt 5 - μ) := by
      rw [M.rpow_add ξ (Q.ofInt 5) (-μ) hξ_pos]; rfl
    rw [← hexp]
    calc M.mul (M.mul cML (M.rpow ξ (-μ))) (M.mul (M.inv cM) (M.rpow ξ (Q.ofInt 5)))
        = M.mul cML (M.mul (M.rpow ξ (-μ)) (M.mul (M.inv cM) (M.rpow ξ (Q.ofInt 5)))) := M.mul_assoc cML _ _
      _ = M.mul cML (M.mul (M.mul (M.inv cM) (M.rpow ξ (Q.ofInt 5))) (M.rpow ξ (-μ))) := by
          rw [M.mul_comm (M.rpow ξ (-μ))]
      _ = M.mul cML (M.mul (M.inv cM) (M.mul (M.rpow ξ (Q.ofInt 5)) (M.rpow ξ (-μ)))) := by
          rw [M.mul_assoc (M.inv cM)]
      _ = M.mul (M.mul cML (M.inv cM)) (M.mul (M.rpow ξ (Q.ofInt 5)) (M.rpow ξ (-μ))) := (M.mul_assoc cML _ _).symm
  rw [hrhs_eq] at hcomb
  refine ⟨hcomb, ?_⟩
  have hexp_lt : Q.ofInt 4 < Q.ofInt 5 - μ := by
    have h45 : Q.ofInt 4 = Q.ofInt 5 - 1 := qrel_eq _ _ (by decide)
    rw [h45]
    refine ⟨?_, ?_⟩
    · have h1 : -1 ≤ -μ := q_neg_le_neg (Q.le_of_lt hμ_lt)
      exact Q.add_le_add_left h1 (Q.ofInt 5)
    · intro heq
      have h1 := congrArg (fun x => x + (-Q.ofInt 5)) heq
      dsimp only at h1
      rw [Q.sub_eq_add_neg, Q.sub_eq_add_neg, Q.add_comm (Q.ofInt 5) (-1), Q.add_assoc, Q.add_right_neg, Q.add_zero,
          Q.add_comm (Q.ofInt 5) (-μ), Q.add_assoc, Q.add_right_neg, Q.add_zero] at h1
      have h2 := congrArg (fun x => -x) h1
      dsimp only at h2
      rw [Q.neg_neg, Q.neg_neg] at h2
      exact hμ_lt.2 h2.symm
  have hr_lt := M.rpow_mono_exp ξ (Q.ofInt 4) (Q.ofInt 5 - μ) hξ hexp_lt
  have hcoef_pos : M.lt M.zero (M.mul cML (M.inv cM)) := M.mul_pos hcML (M.inv_pos hcM)
  exact M.lt_of_lt_of_le (M.mul_lt_mul_of_pos_left hr_lt hcoef_pos) hcomb

/-! #### 4. Feshbach-Schur Dark-Manifold Resolvent & Five-Channel Exponent Taxonomy -/

theorem schur_complement_2x2 (d v w r x y a b : Q)
    (h1 : d * x - v * y = a) (h2 : w * x + r * y = b)
    (hr : r ≠ 0) (hs : d + (v * w) / r ≠ 0) :
    x = (a + (v / r) * b) / (d + (v * w) / r) := by
  have hy : v * y = (v / r) * (r * y) := by
    symm
    change (v * Q.inv r) * (r * y) = v * y
    calc (v * Q.inv r) * (r * y) = (v * y) * (r * Q.inv r) := by ac_rfl
      _ = v * y := by rw [Q.mul_inv_cancel hr, Q.mul_one]
  have h2s := congrArg (fun z => (v / r) * z) h2
  dsimp only at h2s
  rw [Q.left_distrib, ← hy] at h2s
  have hsum : (d * x - v * y) + ((v / r) * (w * x) + v * y) = a + (v / r) * b := by
    rw [h1, h2s]
  have hcancel : (d * x - v * y) + ((v / r) * (w * x) + v * y) = (d + (v * w) / r) * x := by
    rw [Q.sub_eq_add_neg, Q.right_distrib]
    have hcoeff : (v / r) * (w * x) = ((v * w) / r) * x := by
      change (v * Q.inv r) * (w * x) = ((v * w) * Q.inv r) * x; ac_rfl
    rw [hcoeff]
    calc d * x + -(v * y) + (((v * w) / r) * x + v * y)
        = (d * x + ((v * w) / r) * x) + (v * y + -(v * y)) := by ac_rfl
      _ = d * x + ((v * w) / r) * x := by rw [Q.add_right_neg, Q.add_zero]
  rw [hcancel, Q.mul_comm (d + (v * w) / r) x] at hsum
  exact (q_eq_div_iff hs).mpr hsum

private theorem single_zeno_expand (r k u : Q) (hr : r ≠ 0) (hkr : k * r + u ≠ 0) :
    (k * u) / (k * r + u) = u / r - (u * u) / (r * (k * r + u)) := by
  have hden := q_mul_ne_zero hr hkr
  apply q_eq_of_mul_eq_right hden
  rw [Q.sub_eq_add_neg, Q.right_distrib, Q.neg_mul]
  have hL : ((k * u) / (k * r + u)) * (r * (k * r + u)) = k * r * u := by
    calc ((k * u) * Q.inv (k * r + u)) * (r * (k * r + u))
        = (k * r * u) * ((k * r + u) * Q.inv (k * r + u)) := by ac_rfl
      _ = k * r * u := by rw [Q.mul_inv_cancel hkr, Q.mul_one]
  have hR1 : (u / r) * (r * (k * r + u)) = u * (k * r + u) := by
    calc (u * Q.inv r) * (r * (k * r + u))
        = u * (k * r + u) * (r * Q.inv r) := by ac_rfl
      _ = u * (k * r + u) := by rw [Q.mul_inv_cancel hr, Q.mul_one]
  have hR2 : ((u * u) / (r * (k * r + u))) * (r * (k * r + u)) = u * u := by
    exact Q.div_mul_cancel hden
  rw [hL, hR1, hR2, Q.left_distrib]
  have hcu : u * u + -(u * u) = 0 := Q.add_right_neg _
  calc k * r * u = u * (k * r) + (u * u + -(u * u)) := by rw [hcu, Q.add_zero]; ac_rfl
    _ = u * (k * r) + u * u + -(u * u) := by ac_rfl

private theorem single_zeno_second_order (r k u : Q) (hr : r ≠ 0) (hk : k ≠ 0) (hkr : k * r + u ≠ 0) :
    (u * u) / (r * (k * r + u)) =
    (u * u) / (k * r * r) - (u * u * u) / ((k * r * r) * (k * r + u)) := by
  have hkrr : k * r * r ≠ 0 := q_mul_ne_zero (q_mul_ne_zero hk hr) hr
  have hden : (k * r * r) * (k * r + u) ≠ 0 := q_mul_ne_zero hkrr hkr
  apply q_eq_of_mul_eq_right hden
  rw [Q.sub_eq_add_neg, Q.right_distrib, Q.neg_mul]
  have hL : ((u * u) / (r * (k * r + u))) * ((k * r * r) * (k * r + u)) = k * r * (u * u) := by
    calc ((u * u) * Q.inv (r * (k * r + u))) * ((k * r * r) * (k * r + u))
        = (k * r * (u * u)) * ((r * (k * r + u)) * Q.inv (r * (k * r + u))) := by ac_rfl
      _ = k * r * (u * u) := by rw [Q.mul_inv_cancel (q_mul_ne_zero hr hkr), Q.mul_one]
  have hR1 : ((u * u) / (k * r * r)) * ((k * r * r) * (k * r + u)) = (u * u) * (k * r + u) := by
    calc ((u * u) * Q.inv (k * r * r)) * ((k * r * r) * (k * r + u))
        = (u * u) * (k * r + u) * ((k * r * r) * Q.inv (k * r * r)) := by ac_rfl
      _ = (u * u) * (k * r + u) := by rw [Q.mul_inv_cancel hkrr, Q.mul_one]
  have hR2 : ((u * u * u) / ((k * r * r) * (k * r + u))) * ((k * r * r) * (k * r + u)) = u * u * u :=
    Q.div_mul_cancel hden
  rw [hL, hR1, hR2, Q.left_distrib]
  have hcu : (u * u) * u + -((u * u) * u) = 0 := Q.add_right_neg _
  calc k * r * (u * u) = (u * u) * (k * r) + ((u * u) * u + -((u * u) * u)) := by rw [hcu, Q.add_zero]; ac_rfl
    _ = (u * u) * (k * r) + (u * u) * u + -(u * u * u) := by ac_rfl

theorem std_zeno_M2_cancel (r k u1 u2 : Q) (hr : r ≠ 0) (h1 : k * r + u1 ≠ 0) (h2 : k * r + u2 ≠ 0) :
    (k * u1) / (k * r + u1) + (k * u2) / (k * r + u2) =
    (u1 + u2) / r - (u1 * u1 / (r * (k * r + u1)) + u2 * u2 / (r * (k * r + u2))) := by
  rw [single_zeno_expand r k u1 hr h1, single_zeno_expand r k u2 hr h2, Q.add_div]
  simp only [Q.sub_eq_add_neg, Q.neg_add]; ac_rfl

theorem std_zeno_two_sided_xi2 (k ξ u1 u2 v1 v2 B6 : Q)
    (hk : 0 < k) (hξ : 1 ≤ ξ)
    (hu1 : 0 ≤ u1) (hu2 : 0 ≤ u2) (hv1 : 0 ≤ v1) (hv2 : 0 ≤ v2)
    (hM2 : u1 + u2 = v1 + v2)
    (hΔpos : 0 < (u1 * u1 + u2 * u2) - (v1 * v1 + v2 * v2))
    (hBu : u1 * u1 * u1 + u2 * u2 * u2 ≤ B6)
    (hBv : v1 * v1 * v1 + v2 * v2 * v2 ≤ B6)
    (hthresh : Q.ofInt 2 * B6 ≤ ((u1 * u1 + u2 * u2) - (v1 * v1 + v2 * v2)) * (k * ((1 + ξ) * k))) :
    let r := (1 + ξ) * k
    let Z2 := fun a b => (k * a) / (k * r + a) + (k * b) / (k * r + b)
    let Δ4 := (u1 * u1 + u2 * u2) - (v1 * v1 + v2 * v2)
    Δ4 / (Q.ofInt 8 * k * k * k * (ξ * ξ)) ≤ Z2 v1 v2 - Z2 u1 u2 ∧
    Z2 v1 v2 - Z2 u1 u2 ≤ (Q.ofInt 3 * Δ4) / (Q.ofInt 2 * k * k * k * (ξ * ξ)) := by
  dsimp only
  let r := (1 + ξ) * k
  let Δ4 := (u1 * u1 + u2 * u2) - (v1 * v1 + v2 * v2)
  have hξ_pos : 0 < ξ := Q.lt_of_lt_of_le Q.zero_lt_one hξ
  have hr_pos : 0 < r := Q.mul_pos (q_add_pos_of_pos_of_nonneg Q.zero_lt_one (Q.le_of_lt hξ_pos)) hk
  have hkr_pos : 0 < k * r := Q.mul_pos hk hr_pos
  have hkrr_pos : 0 < k * r * r := Q.mul_pos hkr_pos hr_pos
  have hr_ne : r ≠ 0 := Q.ne_zero_of_pos hr_pos
  have hk_ne : k ≠ 0 := Q.ne_zero_of_pos hk
  have h2_pos : (0 : Q) < Q.ofInt 2 := ofInt_pos_nat (n := 2) (by decide)
  have h3_pos : (0 : Q) < Q.ofInt 3 := ofInt_pos_nat (n := 3) (by decide)
  have h8_pos : (0 : Q) < Q.ofInt 8 := ofInt_pos_nat (n := 8) (by decide)
  have hdu1 : k * r + u1 ≠ 0 := Q.ne_zero_of_pos (q_add_pos_of_pos_of_nonneg hkr_pos hu1)
  have hdu2 : k * r + u2 ≠ 0 := Q.ne_zero_of_pos (q_add_pos_of_pos_of_nonneg hkr_pos hu2)
  have hdv1 : k * r + v1 ≠ 0 := Q.ne_zero_of_pos (q_add_pos_of_pos_of_nonneg hkr_pos hv1)
  have hdv2 : k * r + v2 ≠ 0 := Q.ne_zero_of_pos (q_add_pos_of_pos_of_nonneg hkr_pos hv2)
  let rem_u := (u1 * u1 * u1) / (k * r + u1) + (u2 * u2 * u2) / (k * r + u2)
  let rem_v := (v1 * v1 * v1) / (k * r + v1) + (v2 * v2 * v2) / (k * r + v2)
  have hdiff : ((k * v1) / (k * r + v1) + (k * v2) / (k * r + v2)) -
               ((k * u1) / (k * r + u1) + (k * u2) / (k * r + u2)) =
               (Δ4 - (rem_u - rem_v)) / (k * r * r) := by
    rw [std_zeno_M2_cancel r k v1 v2 hr_ne hdv1 hdv2,
        std_zeno_M2_cancel r k u1 u2 hr_ne hdu1 hdu2, ← hM2]
    have hxy : ∀ X Y1 Y2 : Q, (X - Y1) - (X - Y2) = Y2 - Y1 := by
      intro X Y1 Y2
      simp only [Q.sub_eq_add_neg, Q.neg_add, Q.neg_neg]
      calc X + -Y1 + (-X + Y2) = (X + -X) + (Y2 + -Y1) := by ac_rfl
        _ = Y2 + -Y1 := by rw [Q.add_right_neg, Q.zero_add]
    rw [hxy]
    rw [single_zeno_second_order r k u1 hr_ne hk_ne hdu1,
        single_zeno_second_order r k u2 hr_ne hk_ne hdu2,
        single_zeno_second_order r k v1 hr_ne hk_ne hdv1,
        single_zeno_second_order r k v2 hr_ne hk_ne hdv2]
    have hrem_u_div : (u1 * u1 * u1) / ((k * r * r) * (k * r + u1)) = ((u1 * u1 * u1) / (k * r + u1)) / (k * r * r) := by
      rw [q_div_div hdu1 (Q.ne_zero_of_pos hkrr_pos), Q.mul_comm (k * r + u1)]
    have hrem_u_div2 : (u2 * u2 * u2) / ((k * r * r) * (k * r + u2)) = ((u2 * u2 * u2) / (k * r + u2)) / (k * r * r) := by
      rw [q_div_div hdu2 (Q.ne_zero_of_pos hkrr_pos), Q.mul_comm (k * r + u2)]
    have hrem_v_div : (v1 * v1 * v1) / ((k * r * r) * (k * r + v1)) = ((v1 * v1 * v1) / (k * r + v1)) / (k * r * r) := by
      rw [q_div_div hdv1 (Q.ne_zero_of_pos hkrr_pos), Q.mul_comm (k * r + v1)]
    have hrem_v_div2 : (v2 * v2 * v2) / ((k * r * r) * (k * r + v2)) = ((v2 * v2 * v2) / (k * r + v2)) / (k * r * r) := by
      rw [q_div_div hdv2 (Q.ne_zero_of_pos hkrr_pos), Q.mul_comm (k * r + v2)]
    rw [hrem_u_div, hrem_u_div2, hrem_v_div, hrem_v_div2,
        ← q_sub_div, ← q_sub_div, ← Q.add_div,
        ← q_sub_div, ← q_sub_div, ← Q.add_div, ← q_sub_div]
    congr 1
    dsimp only [Δ4, rem_u, rem_v]
    simp only [Q.sub_eq_add_neg, Q.neg_add, Q.neg_neg]
    ac_rfl
  have hrem_bnds : ∀ a b : Q, 0 ≤ a → 0 ≤ b → a * a * a + b * b * b ≤ B6 →
      0 ≤ (a * a * a) / (k * r + a) + (b * b * b) / (k * r + b) ∧
      (a * a * a) / (k * r + a) + (b * b * b) / (k * r + b) ≤ B6 / (k * r) := by
    intro a b ha hb hB
    have hda_pos : 0 < k * r + a := q_add_pos_of_pos_of_nonneg hkr_pos ha
    have hdb_pos : 0 < k * r + b := q_add_pos_of_pos_of_nonneg hkr_pos hb
    have hda_ge : k * r ≤ k * r + a := by have := Q.add_le_add_left ha (k * r); rwa [Q.add_zero] at this
    have hdb_ge : k * r ≤ k * r + b := by have := Q.add_le_add_left hb (k * r); rwa [Q.add_zero] at this
    have ha3 : 0 ≤ a * a * a := Q.mul_nonneg (Q.mul_nonneg ha ha) ha
    have hb3 : 0 ≤ b * b * b := Q.mul_nonneg (Q.mul_nonneg hb hb) hb
    constructor
    · exact q_add_nonneg (q_div_nonneg ha3 hda_pos) (q_div_nonneg hb3 hdb_pos)
    · have hu1 := q_div_le_div_of_nonneg_left ha3 hkr_pos hda_ge
      have hu2 := q_div_le_div_of_nonneg_left hb3 hkr_pos hdb_ge
      have hsum := q_add_le_add hu1 hu2
      rw [← Q.add_div] at hsum
      exact Q.le_trans hsum (Q.div_le_div_of_nonneg_right hB hkr_pos)
  have hru := hrem_bnds u1 u2 hu1 hu2 hBu
  have hrv := hrem_bnds v1 v2 hv1 hv2 hBv
  have hB6_half : B6 / (k * r) ≤ Δ4 / Q.ofInt 2 := by
    have h1 : B6 * Q.ofInt 2 ≤ Δ4 * (k * r) := by rwa [Q.mul_comm]
    have h2 := Q.div_le_div_of_nonneg_right h1 (Q.mul_pos hkr_pos h2_pos)
    have hL : (B6 * Q.ofInt 2) / ((k * r) * Q.ofInt 2) = B6 / (k * r) :=
      q_div_mul_cancel_num (Q.ne_zero_of_pos h2_pos) (Q.ne_zero_of_pos hkr_pos)
    have hR : (Δ4 * (k * r)) / ((k * r) * Q.ofInt 2) = Δ4 / Q.ofInt 2 := by
      rw [Q.mul_comm (k * r) (Q.ofInt 2)]
      exact q_div_mul_cancel_num (Q.ne_zero_of_pos hkr_pos) (Q.ne_zero_of_pos h2_pos)
    rwa [hL, hR] at h2
  have hcore_lb : Δ4 / Q.ofInt 2 ≤ Δ4 - (rem_u - rem_v) := by
    have h1 : rem_u - rem_v ≤ rem_u := by
      have := Q.add_le_add_left (q_neg_le_neg hrv.1) rem_u; rwa [Q.neg_zero, Q.add_zero] at this
    have h2 := Q.le_trans h1 (Q.le_trans hru.2 hB6_half)
    have h3 := q_sub_le_sub (Q.le_refl Δ4) h2
    rw [q_sub_half] at h3
    exact h3
  have hcore_ub : Δ4 - (rem_u - rem_v) ≤ Q.ofInt 3 * Δ4 / Q.ofInt 2 := by
    have h1 : -(Δ4 / Q.ofInt 2) ≤ -rem_v := q_neg_le_neg (Q.le_trans hrv.2 hB6_half)
    have h2 : -rem_v ≤ rem_u - rem_v := by
      have := Q.add_le_add_right hru.1 (-rem_v); rwa [Q.zero_add] at this
    have h3 := q_sub_le_add_of_neg_le Δ4 (Q.le_trans h1 h2)
    rw [q_add_half] at h3
    exact h3
  have hxik_le_r : ξ * k ≤ r := by
    have h1 : ξ ≤ 1 + ξ := by have := Q.add_le_add_right (Q.le_of_lt Q.zero_lt_one) ξ; rwa [Q.zero_add] at this
    exact Q.mul_le_mul_of_nonneg_right h1 (Q.le_of_lt hk)
  have hr_le_2xik : r ≤ Q.ofInt 2 * ξ * k := by
    have h1 : 1 + ξ ≤ Q.ofInt 2 * ξ := by
      have h21 : Q.ofInt 2 = 1 + 1 := qrel_eq _ _ (by decide)
      rw [h21, Q.right_distrib, Q.one_mul]; exact Q.add_le_add_right hξ ξ
    exact Q.mul_le_mul_of_nonneg_right h1 (Q.le_of_lt hk)
  have hxik_pos : 0 < ξ * k := Q.mul_pos hξ_pos hk
  have hr2_lb : (ξ * k) * (ξ * k) ≤ r * r :=
    Q.le_trans (Q.mul_le_mul_of_nonneg_right hxik_le_r (Q.le_of_lt hxik_pos)) (Q.mul_le_mul_of_nonneg_left hxik_le_r (Q.le_of_lt hr_pos))
  have hr2_ub : r * r ≤ (Q.ofInt 2 * ξ * k) * (Q.ofInt 2 * ξ * k) :=
    Q.le_trans (Q.mul_le_mul_of_nonneg_right hr_le_2xik (Q.le_of_lt hr_pos))
      (Q.mul_le_mul_of_nonneg_left hr_le_2xik (Q.mul_nonneg (Q.mul_nonneg (Q.le_of_lt h2_pos) (Q.le_of_lt hξ_pos)) (Q.le_of_lt hk)))
  have hmid_lb := Q.div_le_div_of_nonneg_right hcore_lb hkrr_pos
  have hmid_ub := Q.div_le_div_of_nonneg_right hcore_ub hkrr_pos
  rw [← hdiff] at hmid_lb hmid_ub
  constructor
  · have hk8_pos : 0 < Q.ofInt 8 * k * k * k * (ξ * ξ) :=
      Q.mul_pos (Q.mul_pos (Q.mul_pos (Q.mul_pos h8_pos hk) hk) hk) (Q.mul_pos hξ_pos hξ_pos)
    have hden_ub : Q.ofInt 2 * (k * r * r) ≤ Q.ofInt 8 * k * k * k * (ξ * ξ) := by
      have h4_eq : (Q.ofInt 2 * ξ * k) * (Q.ofInt 2 * ξ * k) = Q.ofInt 4 * k * k * (ξ * ξ) := by
        have h4 : Q.ofInt 2 * Q.ofInt 2 = Q.ofInt 4 := qrel_eq _ _ (by decide)
        rw [← h4]; ac_rfl
      have h8_eq : Q.ofInt 2 * (k * (Q.ofInt 4 * k * k * (ξ * ξ))) = Q.ofInt 8 * k * k * k * (ξ * ξ) := by
        have h8 : Q.ofInt 2 * Q.ofInt 4 = Q.ofInt 8 := qrel_eq _ _ (by decide)
        rw [← h8]; ac_rfl
      rw [h4_eq] at hr2_ub
      calc Q.ofInt 2 * (k * r * r)
          = Q.ofInt 2 * (k * (r * r)) := by ac_rfl
        _ ≤ Q.ofInt 2 * (k * (Q.ofInt 4 * k * k * (ξ * ξ))) :=
            Q.mul_le_mul_of_nonneg_left (Q.mul_le_mul_of_nonneg_left hr2_ub (Q.le_of_lt hk)) (Q.le_of_lt h2_pos)
        _ = Q.ofInt 8 * k * k * k * (ξ * ξ) := h8_eq
    have hdiv := q_div_le_div_of_nonneg_left (Q.le_of_lt hΔpos) (Q.mul_pos h2_pos hkrr_pos) hden_ub
    rw [q_div_div (Q.ne_zero_of_pos h2_pos) (Q.ne_zero_of_pos hkrr_pos)] at hmid_lb
    exact Q.le_trans hdiv hmid_lb
  · have hk2_pos : 0 < Q.ofInt 2 * k * k * k * (ξ * ξ) :=
      Q.mul_pos (Q.mul_pos (Q.mul_pos (Q.mul_pos h2_pos hk) hk) hk) (Q.mul_pos hξ_pos hξ_pos)
    have hden_lb : Q.ofInt 2 * k * k * k * (ξ * ξ) ≤ Q.ofInt 2 * (k * r * r) := by
      calc Q.ofInt 2 * k * k * k * (ξ * ξ)
          = Q.ofInt 2 * (k * ((ξ * k) * (ξ * k))) := by ac_rfl
        _ ≤ Q.ofInt 2 * (k * (r * r)) :=
            Q.mul_le_mul_of_nonneg_left (Q.mul_le_mul_of_nonneg_left hr2_lb (Q.le_of_lt hk)) (Q.le_of_lt h2_pos)
        _ = Q.ofInt 2 * (k * r * r) := by ac_rfl
    have hdiv := q_div_le_div_of_nonneg_left (Q.mul_nonneg (Q.le_of_lt h3_pos) (Q.le_of_lt hΔpos)) hk2_pos hden_lb
    rw [q_div_div (Q.ne_zero_of_pos h2_pos) (Q.ne_zero_of_pos hkrr_pos)] at hmid_ub
    exact Q.le_trans hmid_ub hdiv

theorem local_iso_dark_xi4 (k ξ cθ c0 dθ d0 B : Q)
    (hk : 0 < k) (hξ : 1 ≤ ξ)
    (hcθ : 0 ≤ cθ) (hc0 : 0 ≤ c0) (hdθ : 0 ≤ dθ) (hd0 : 0 ≤ d0)
    (hΔpos : 0 < cθ - c0) (hBθ : cθ * dθ ≤ B) (hB0 : c0 * d0 ≤ B)
    (hthresh : Q.ofInt 2 * B ≤ (cθ - c0) * (k * (((1 + ξ) * k) * ((1 + ξ) * k)))) :
    let r := (1 + ξ) * k
    let W := fun c d => c / ((r * r) * (k * (r * r) + d))
    let Δ := cθ - c0
    Δ / (Q.ofInt 32 * k * k * k * k * k * (ξ * ξ * ξ * ξ)) ≤ W cθ dθ - W c0 d0 ∧
    W cθ dθ - W c0 d0 ≤ (Q.ofInt 3 * Δ) / (Q.ofInt 2 * k * k * k * k * k * (ξ * ξ * ξ * ξ)) := by
  dsimp only
  let r := (1 + ξ) * k
  let r2 := r * r
  let Δ := cθ - c0
  have hξ_pos : 0 < ξ := Q.lt_of_lt_of_le Q.zero_lt_one hξ
  have hr_pos : 0 < r := Q.mul_pos (q_add_pos_of_pos_of_nonneg Q.zero_lt_one (Q.le_of_lt hξ_pos)) hk
  have hr2_pos : 0 < r2 := Q.mul_pos hr_pos hr_pos
  have hkr2_pos : 0 < k * r2 := Q.mul_pos hk hr2_pos
  have hkr4_pos : 0 < k * (r2 * r2) := Q.mul_pos hk (Q.mul_pos hr2_pos hr2_pos)
  have h2_pos : (0 : Q) < Q.ofInt 2 := ofInt_pos_nat (n := 2) (by decide)
  have h3_pos : (0 : Q) < Q.ofInt 3 := ofInt_pos_nat (n := 3) (by decide)
  have h32_pos : (0 : Q) < Q.ofInt 32 := ofInt_pos_nat (n := 32) (by decide)
  have hw_exp : ∀ c d : Q, 0 ≤ d →
      c / (r2 * (k * r2 + d)) = c / (k * (r2 * r2)) - ((c * d) / (k * r2 + d)) / (k * (r2 * r2)) := by
    intro c d hd
    have hdk : k * r2 + d ≠ 0 := Q.ne_zero_of_pos (q_add_pos_of_pos_of_nonneg hkr2_pos hd)
    have hkr4_ne : k * (r2 * r2) ≠ 0 := Q.ne_zero_of_pos hkr4_pos
    have hden : r2 * (k * r2 + d) ≠ 0 := q_mul_ne_zero (Q.ne_zero_of_pos hr2_pos) hdk
    have hbig : (k * (r2 * r2)) * (k * r2 + d) ≠ 0 := q_mul_ne_zero hkr4_ne hdk
    rw [q_div_div hdk hkr4_ne]
    apply q_eq_of_mul_eq_right hbig
    rw [Q.sub_eq_add_neg, Q.right_distrib, Q.neg_mul]
    have hL : (c / (r2 * (k * r2 + d))) * ((k * (r2 * r2)) * (k * r2 + d)) = c * (k * r2) := by
      calc (c * Q.inv (r2 * (k * r2 + d))) * ((k * (r2 * r2)) * (k * r2 + d))
          = (c * (k * r2)) * ((r2 * (k * r2 + d)) * Q.inv (r2 * (k * r2 + d))) := by ac_rfl
        _ = c * (k * r2) := by rw [Q.mul_inv_cancel hden, Q.mul_one]
    have hR1 : (c / (k * (r2 * r2))) * ((k * (r2 * r2)) * (k * r2 + d)) = c * (k * r2 + d) := by
      calc (c * Q.inv (k * (r2 * r2))) * ((k * (r2 * r2)) * (k * r2 + d))
          = c * (k * r2 + d) * ((k * (r2 * r2)) * Q.inv (k * (r2 * r2))) := by ac_rfl
        _ = c * (k * r2 + d) := by rw [Q.mul_inv_cancel hkr4_ne, Q.mul_one]
    have hR2 : ((c * d) / ((k * r2 + d) * (k * (r2 * r2)))) * ((k * (r2 * r2)) * (k * r2 + d)) = c * d := by
      rw [Q.mul_comm (k * r2 + d) (k * (r2 * r2))]; exact Q.div_mul_cancel hbig
    rw [hL, hR1, hR2, Q.left_distrib]
    have hcd : c * d + -(c * d) = 0 := Q.add_right_neg _
    calc c * (k * r2) = c * (k * r2) + (c * d + -(c * d)) := by rw [hcd, Q.add_zero]
      _ = c * (k * r2) + c * d + -(c * d) := by ac_rfl
  let remθ := (cθ * dθ) / (k * r2 + dθ)
  let rem0 := (c0 * d0) / (k * r2 + d0)
  have hdiff : cθ / (r2 * (k * r2 + dθ)) - c0 / (r2 * (k * r2 + d0)) =
      (Δ - (remθ - rem0)) / (k * (r2 * r2)) := by
    rw [hw_exp cθ dθ hdθ, hw_exp c0 d0 hd0, ← q_sub_div, ← q_sub_div, ← q_sub_div]
    congr 1
    dsimp only [Δ, remθ, rem0]
    simp only [Q.sub_eq_add_neg, Q.neg_add, Q.neg_neg]
    ac_rfl
  have hrb : ∀ c d : Q, 0 ≤ c → 0 ≤ d → c * d ≤ B →
      0 ≤ (c * d) / (k * r2 + d) ∧ (c * d) / (k * r2 + d) ≤ B / (k * r2) := by
    intro c d hc hd hcd
    have hd_pos : 0 < k * r2 + d := q_add_pos_of_pos_of_nonneg hkr2_pos hd
    have hd_ge : k * r2 ≤ k * r2 + d := by have := Q.add_le_add_left hd (k * r2); rwa [Q.add_zero] at this
    constructor
    · exact q_div_nonneg (Q.mul_nonneg hc hd) hd_pos
    · exact Q.le_trans (q_div_le_div_of_nonneg_left (Q.mul_nonneg hc hd) hkr2_pos hd_ge)
        (Q.div_le_div_of_nonneg_right hcd hkr2_pos)
  have hrθ := hrb cθ dθ hcθ hdθ hBθ
  have hr0 := hrb c0 d0 hc0 hd0 hB0
  have hB_half : B / (k * r2) ≤ Δ / Q.ofInt 2 := by
    have h1 : B * Q.ofInt 2 ≤ Δ * (k * r2) := by rwa [Q.mul_comm]
    have h2 := Q.div_le_div_of_nonneg_right h1 (Q.mul_pos hkr2_pos h2_pos)
    have hL : (B * Q.ofInt 2) / ((k * r2) * Q.ofInt 2) = B / (k * r2) :=
      q_div_mul_cancel_num (Q.ne_zero_of_pos h2_pos) (Q.ne_zero_of_pos hkr2_pos)
    have hR : (Δ * (k * r2)) / ((k * r2) * Q.ofInt 2) = Δ / Q.ofInt 2 := by
      rw [Q.mul_comm (k * r2) (Q.ofInt 2)]
      exact q_div_mul_cancel_num (Q.ne_zero_of_pos hkr2_pos) (Q.ne_zero_of_pos h2_pos)
    rwa [hL, hR] at h2
  have hcore_lb : Δ / Q.ofInt 2 ≤ Δ - (remθ - rem0) := by
    have h1 : remθ - rem0 ≤ remθ := by
      have := Q.add_le_add_left (q_neg_le_neg hr0.1) remθ; rwa [Q.neg_zero, Q.add_zero] at this
    have h2 := q_sub_le_sub (Q.le_refl Δ) (Q.le_trans h1 (Q.le_trans hrθ.2 hB_half))
    rw [q_sub_half] at h2
    exact h2
  have hcore_ub : Δ - (remθ - rem0) ≤ Q.ofInt 3 * Δ / Q.ofInt 2 := by
    have h1 : -(Δ / Q.ofInt 2) ≤ -rem0 := q_neg_le_neg (Q.le_trans hr0.2 hB_half)
    have h2 : -rem0 ≤ remθ - rem0 := by
      have := Q.add_le_add_right hrθ.1 (-rem0); rwa [Q.zero_add] at this
    have h3 := q_sub_le_add_of_neg_le Δ (Q.le_trans h1 h2)
    rw [q_add_half] at h3
    exact h3
  have hxik_le_r : ξ * k ≤ r := by
    have h1 : ξ ≤ 1 + ξ := by have := Q.add_le_add_right (Q.le_of_lt Q.zero_lt_one) ξ; rwa [Q.zero_add] at this
    exact Q.mul_le_mul_of_nonneg_right h1 (Q.le_of_lt hk)
  have hr_le_2xik : r ≤ Q.ofInt 2 * ξ * k := by
    have h1 : 1 + ξ ≤ Q.ofInt 2 * ξ := by
      have h21 : Q.ofInt 2 = 1 + 1 := qrel_eq _ _ (by decide)
      rw [h21, Q.right_distrib, Q.one_mul]; exact Q.add_le_add_right hξ ξ
    exact Q.mul_le_mul_of_nonneg_right h1 (Q.le_of_lt hk)
  have hxik_pos : 0 < ξ * k := Q.mul_pos hξ_pos hk
  have hr2_lb : (ξ * k) * (ξ * k) ≤ r2 :=
    Q.le_trans (Q.mul_le_mul_of_nonneg_right hxik_le_r (Q.le_of_lt hxik_pos)) (Q.mul_le_mul_of_nonneg_left hxik_le_r (Q.le_of_lt hr_pos))
  have hr2_ub : r2 ≤ (Q.ofInt 2 * ξ * k) * (Q.ofInt 2 * ξ * k) :=
    Q.le_trans (Q.mul_le_mul_of_nonneg_right hr_le_2xik (Q.le_of_lt hr_pos))
      (Q.mul_le_mul_of_nonneg_left hr_le_2xik (Q.mul_nonneg (Q.mul_nonneg (Q.le_of_lt h2_pos) (Q.le_of_lt hξ_pos)) (Q.le_of_lt hk)))
  have hr4_lb : ((ξ * k) * (ξ * k)) * ((ξ * k) * (ξ * k)) ≤ r2 * r2 :=
    Q.le_trans (Q.mul_le_mul_of_nonneg_right hr2_lb (Q.le_of_lt (Q.mul_pos hxik_pos hxik_pos)))
      (Q.mul_le_mul_of_nonneg_left hr2_lb (Q.le_of_lt hr2_pos))
  have hr4_ub : r2 * r2 ≤ ((Q.ofInt 2 * ξ * k) * (Q.ofInt 2 * ξ * k)) * ((Q.ofInt 2 * ξ * k) * (Q.ofInt 2 * ξ * k)) :=
    Q.le_trans (Q.mul_le_mul_of_nonneg_right hr2_ub (Q.le_of_lt hr2_pos))
      (Q.mul_le_mul_of_nonneg_left hr2_ub (Q.le_of_lt (Q.mul_pos (Q.mul_pos (Q.mul_pos h2_pos hξ_pos) hk)
        (Q.mul_pos (Q.mul_pos h2_pos hξ_pos) hk))))
  have hmid_lb := Q.div_le_div_of_nonneg_right hcore_lb hkr4_pos
  have hmid_ub := Q.div_le_div_of_nonneg_right hcore_ub hkr4_pos
  rw [← hdiff] at hmid_lb hmid_ub
  constructor
  · have hk32_pos : 0 < Q.ofInt 32 * k * k * k * k * k * (ξ * ξ * ξ * ξ) :=
      Q.mul_pos (Q.mul_pos (Q.mul_pos (Q.mul_pos (Q.mul_pos (Q.mul_pos h32_pos hk) hk) hk) hk) hk)
        (Q.mul_pos (Q.mul_pos (Q.mul_pos hξ_pos hξ_pos) hξ_pos) hξ_pos)
    have hden_ub : Q.ofInt 2 * (k * (r2 * r2)) ≤ Q.ofInt 32 * k * k * k * k * k * (ξ * ξ * ξ * ξ) := by
      have h16_eq : ((Q.ofInt 2 * ξ * k) * (Q.ofInt 2 * ξ * k)) * ((Q.ofInt 2 * ξ * k) * (Q.ofInt 2 * ξ * k)) =
          Q.ofInt 16 * k * k * k * k * (ξ * ξ * ξ * ξ) := by
        have h16 : Q.ofInt 2 * Q.ofInt 2 * Q.ofInt 2 * Q.ofInt 2 = Q.ofInt 16 := qrel_eq _ _ (by decide)
        rw [← h16]; ac_rfl
      have h32_eq : Q.ofInt 2 * (k * (Q.ofInt 16 * k * k * k * k * (ξ * ξ * ξ * ξ))) =
          Q.ofInt 32 * k * k * k * k * k * (ξ * ξ * ξ * ξ) := by
        have h32 : Q.ofInt 2 * Q.ofInt 16 = Q.ofInt 32 := qrel_eq _ _ (by decide)
        rw [← h32]; ac_rfl
      rw [h16_eq] at hr4_ub
      have := Q.mul_le_mul_of_nonneg_left (Q.mul_le_mul_of_nonneg_left hr4_ub (Q.le_of_lt hk)) (Q.le_of_lt h2_pos)
      rwa [h32_eq] at this
    have hdiv := q_div_le_div_of_nonneg_left (Q.le_of_lt hΔpos) (Q.mul_pos h2_pos hkr4_pos) hden_ub
    rw [q_div_div (Q.ne_zero_of_pos h2_pos) (Q.ne_zero_of_pos hkr4_pos)] at hmid_lb
    exact Q.le_trans hdiv hmid_lb
  · have hk2_pos : 0 < Q.ofInt 2 * k * k * k * k * k * (ξ * ξ * ξ * ξ) :=
      Q.mul_pos (Q.mul_pos (Q.mul_pos (Q.mul_pos (Q.mul_pos (Q.mul_pos h2_pos hk) hk) hk) hk) hk)
        (Q.mul_pos (Q.mul_pos (Q.mul_pos hξ_pos hξ_pos) hξ_pos) hξ_pos)
    have hden_lb : Q.ofInt 2 * k * k * k * k * k * (ξ * ξ * ξ * ξ) ≤ Q.ofInt 2 * (k * (r2 * r2)) := by
      have h_eq : Q.ofInt 2 * (k * (((ξ * k) * (ξ * k)) * ((ξ * k) * (ξ * k)))) =
          Q.ofInt 2 * k * k * k * k * k * (ξ * ξ * ξ * ξ) := by ac_rfl
      have := Q.mul_le_mul_of_nonneg_left (Q.mul_le_mul_of_nonneg_left hr4_lb (Q.le_of_lt hk)) (Q.le_of_lt h2_pos)
      rwa [h_eq] at this
    have hdiv := q_div_le_div_of_nonneg_left (Q.mul_nonneg (Q.le_of_lt h3_pos) (Q.le_of_lt hΔpos)) hk2_pos hden_lb
    rw [q_div_div (Q.ne_zero_of_pos h2_pos) (Q.ne_zero_of_pos hkr4_pos)] at hmid_ub
    exact Q.le_trans hmid_ub hdiv

theorem local_z_leak_xi1 (k ξ v y Φ_leak : Q)
    (hk : 0 < k) (hξ : 1 ≤ ξ) (hv : 0 ≤ v)
    (h1 : k * Φ_leak - v * y = k)
    (h2 : v * Φ_leak + ((1 + ξ) * k) * y = 0)
    (hleak : v * v ≤ k * k * ξ) :
    (v * v) / (Q.ofInt 3 * k * k * ξ) ≤ 1 - Φ_leak ∧ 1 - Φ_leak ≤ (v * v) / (k * k * ξ) := by
  let r := (1 + ξ) * k
  have hξ_pos : 0 < ξ := Q.lt_of_lt_of_le Q.zero_lt_one hξ
  have hr_pos : 0 < r := Q.mul_pos (q_add_pos_of_pos_of_nonneg Q.zero_lt_one (Q.le_of_lt hξ_pos)) hk
  have hs_pos : 0 < k + (v * v) / r :=
    q_add_pos_of_pos_of_nonneg hk (q_div_nonneg (Q.mul_nonneg hv hv) hr_pos)
  have hsch := schur_complement_2x2 k v v r Φ_leak y k 0 h1 h2 (Q.ne_zero_of_pos hr_pos) (Q.ne_zero_of_pos hs_pos)
  rw [Q.mul_zero, Q.add_zero] at hsch
  have hcontrast : 1 - Φ_leak = (v * v) / (k * r + v * v) := by
    rw [hsch]
    have hd_pos : 0 < k * r + v * v := q_add_pos_of_pos_of_nonneg (Q.mul_pos hk hr_pos) (Q.mul_nonneg hv hv)
    have hr_ne := Q.ne_zero_of_pos hr_pos
    have hkr_ne := Q.ne_zero_of_pos hd_pos
    have hdiv_r : k / (k + (v * v) / r) = (k * r) / (k * r + v * v) := by
      rw [q_div_eq_iff (Q.ne_zero_of_pos hs_pos)]
      have h_eq : ((k * r) / (k * r + v * v)) * (k + (v * v) / r) = k := by
        have hk_id : k + (v * v) / r = (k * r + v * v) / r := by
          rw [Q.add_div, Q.mul_div_cancel hr_ne]
        rw [hk_id]
        calc ((k * r) / (k * r + v * v)) * ((k * r + v * v) / r)
            = (((k * r) / (k * r + v * v)) * (k * r + v * v)) / r := by
                change ((k * r * Q.inv (k * r + v * v)) * ((k * r + v * v) * Q.inv r)) =
                       ((k * r * Q.inv (k * r + v * v)) * (k * r + v * v)) * Q.inv r
                ac_rfl
          _ = (k * r) / r := by rw [Q.div_mul_cancel hkr_ne]
          _ = k := Q.mul_div_cancel hr_ne
      exact h_eq.symm
    rw [hdiv_r, ← Q.div_self hkr_ne, ← Q.sub_div]
    congr 1
    rw [Q.sub_eq_add_neg, Q.add_comm (k * r) (v * v), Q.add_assoc, Q.add_right_neg, Q.add_zero]
  rw [hcontrast]
  have hxik_le_r : ξ * k ≤ r := by
    have h1 : ξ ≤ 1 + ξ := by have := Q.add_le_add_right (Q.le_of_lt Q.zero_lt_one) ξ; rwa [Q.zero_add] at this
    exact Q.mul_le_mul_of_nonneg_right h1 (Q.le_of_lt hk)
  have hr_le_2xik : r ≤ Q.ofInt 2 * ξ * k := by
    have h1 : 1 + ξ ≤ Q.ofInt 2 * ξ := by
      have h21 : Q.ofInt 2 = 1 + 1 := qrel_eq _ _ (by decide)
      rw [h21, Q.right_distrib, Q.one_mul]; exact Q.add_le_add_right hξ ξ
    exact Q.mul_le_mul_of_nonneg_right h1 (Q.le_of_lt hk)
  have hkkx_pos : 0 < k * k * ξ := Q.mul_pos (Q.mul_pos hk hk) hξ_pos
  constructor
  · have hden_ub : k * r + v * v ≤ Q.ofInt 3 * k * k * ξ := by
      have hkr_ub : k * r ≤ Q.ofInt 2 * k * k * ξ := by
        have h := Q.mul_le_mul_of_nonneg_left hr_le_2xik (Q.le_of_lt hk)
        rwa [show k * (Q.ofInt 2 * ξ * k) = Q.ofInt 2 * k * k * ξ from by ac_rfl] at h
      have hsum := q_add_le_add hkr_ub hleak
      have h32 : Q.ofInt 2 * k * k * ξ + k * k * ξ = Q.ofInt 3 * k * k * ξ := by
        have h3def : Q.ofInt 3 = Q.ofInt 2 + 1 := qrel_eq _ _ (by decide)
        rw [h3def, Q.right_distrib, Q.right_distrib, Q.right_distrib, Q.one_mul]
      rwa [h32] at hsum
    exact q_div_le_div_of_nonneg_left (Q.mul_nonneg hv hv)
      (q_add_pos_of_pos_of_nonneg (Q.mul_pos hk hr_pos) (Q.mul_nonneg hv hv)) hden_ub
  · have hden_lb : k * k * ξ ≤ k * r + v * v := by
      have hkr_lb : k * k * ξ ≤ k * r := by
        have h := Q.mul_le_mul_of_nonneg_left hxik_le_r (Q.le_of_lt hk)
        rwa [show k * (ξ * k) = k * k * ξ from by ac_rfl] at h
      have := q_add_le_add hkr_lb (Q.mul_nonneg hv hv)
      rwa [Q.add_zero] at this
    exact q_div_le_div_of_nonneg_left (Q.mul_nonneg hv hv) hkkx_pos hden_lb

theorem local_z_single_sat_xi0 (k ωL y Φ_sat : Q)
    (hk : 0 < k)
    (h1 : k * Φ_sat - ωL * y = k)
    (h2 : ωL * Φ_sat + k * y = 0) :
    1 - Φ_sat = (ωL * ωL) / (k * k + ωL * ωL) := by
  have hs_pos : 0 < k + (ωL * ωL) / k :=
    q_add_pos_of_pos_of_nonneg hk (q_div_nonneg (Q.sq_nonneg ωL) hk)
  have hsch := schur_complement_2x2 k ωL ωL k Φ_sat y k 0 h1 h2 (Q.ne_zero_of_pos hk) (Q.ne_zero_of_pos hs_pos)
  rw [Q.mul_zero, Q.add_zero] at hsch
  rw [hsch]
  have hk_ne := Q.ne_zero_of_pos hk
  have hd_pos : 0 < k * k + ωL * ωL := q_add_pos_of_pos_of_nonneg (Q.mul_pos hk hk) (Q.sq_nonneg ωL)
  have hkd_ne := Q.ne_zero_of_pos hd_pos
  have hdiv : k / (k + (ωL * ωL) / k) = (k * k) / (k * k + ωL * ωL) := by
    rw [q_div_eq_iff (Q.ne_zero_of_pos hs_pos)]
    have h_eq : ((k * k) / (k * k + ωL * ωL)) * (k + (ωL * ωL) / k) = k := by
      have hk_id : k + (ωL * ωL) / k = (k * k + ωL * ωL) / k := by
        rw [Q.add_div, Q.mul_div_cancel hk_ne]
      rw [hk_id]
      calc ((k * k) / (k * k + ωL * ωL)) * ((k * k + ωL * ωL) / k)
          = (((k * k) / (k * k + ωL * ωL)) * (k * k + ωL * ωL)) / k := by
              change ((k * k * Q.inv (k * k + ωL * ωL)) * ((k * k + ωL * ωL) * Q.inv k)) =
                     ((k * k * Q.inv (k * k + ωL * ωL)) * (k * k + ωL * ωL)) * Q.inv k
              ac_rfl
        _ = (k * k) / k := by rw [Q.div_mul_cancel hkd_ne]
        _ = k := Q.mul_div_cancel hk_ne
    exact h_eq.symm
  rw [hdiv, ← Q.div_self hkd_ne, ← Q.sub_div]
  congr 1
  rw [Q.sub_eq_add_neg, Q.add_comm (k * k) (ωL * ωL), Q.add_assoc, Q.add_right_neg, Q.add_zero]

end StrongNoiseAsymptotics4C

end DiamondProofs.Paper1



