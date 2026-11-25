import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17126

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def hcsGateVal (bank : List (BitVec 32768)) (g : Gate) : BitVec 32768 :=
  let args := g.inputs.map fun i => bank.getD i 0
  match g.op with
  | .and => args.foldr (· &&& ·) (BitVec.allOnes 32768)
  | .or => args.foldr (· ||| ·) 0
  | .not => ~~~(args.headD 0)
  | _ => 0

def hcsStep (bank : List (BitVec 32768)) (g : Gate) : List (BitVec 32768) :=
  bank ++ [hcsGateVal bank g]

theorem hcsGetDBit (bank : List (BitVec 32768)) (i : Nat) (k : Nat) :
    (bank.getD k 0).getLsbD i = (bank.map fun w => w.getLsbD i).getD k false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases bank[k]? <;> simp

theorem hcsAndBit (xs : List (BitVec 32768)) (i : Fin 32768) :
    (xs.foldr (· &&& ·) (BitVec.allOnes 32768)).getLsbD i.val = (xs.map fun w => w.getLsbD i.val).all id := by
  induction xs with
  | nil => simp only [List.foldr_nil, BitVec.getLsbD_allOnes, i.isLt, decide_true, List.map_nil, List.all_nil]
  | cons a t ih => simp only [List.foldr_cons, BitVec.getLsbD_and, List.map_cons, List.all_cons, id_eq, ih]

theorem hcsOrBit (xs : List (BitVec 32768)) (i : Fin 32768) :
    (xs.foldr (· ||| ·) 0).getLsbD i.val = (xs.map fun w => w.getLsbD i.val).any id := by
  induction xs with
  | nil => simp
  | cons a t ih => simp only [List.foldr_cons, BitVec.getLsbD_or, List.map_cons, List.any_cons, id_eq, ih]

theorem hcsGateBit (bank : List (BitVec 32768)) (i : Fin 32768) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    (hcsGateVal bank g).getLsbD i.val =
      g.op.eval (g.inputs.map fun k => (bank.map fun w => w.getLsbD i.val).getD k false) := by
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · simp only [hcsGateVal, GateOp.eval, hcsAndBit, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    exact hcsGetDBit bank i.val k
  · simp only [hcsGateVal, GateOp.eval, hcsOrBit, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    exact hcsGetDBit bank i.val k
  · simp only [hcsGateVal, GateOp.eval, BitVec.getLsbD_not, i.isLt, decide_true, Bool.true_and]
    cases ins with
    | nil => simp
    | cons k _ => simp only [List.map_cons, List.headD_cons, hcsGetDBit]

theorem hcsFoldBits (bank : List (BitVec 32768)) (i : Fin 32768) (gs : List Gate)
    (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (gs.foldl hcsStep bank).map (fun w => w.getLsbD i.val) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)])
        (bank.map fun w => w.getLsbD i.val) := by
  induction gs generalizing bank with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hstep : (hcsStep bank g).map (fun w => w.getLsbD i.val) =
        (bank.map fun w => w.getLsbD i.val) ++
          [g.op.eval (g.inputs.map fun k => (bank.map fun w => w.getLsbD i.val).getD k false)] := by
      simp only [hcsStep, List.map_append, List.map_cons, List.map_nil,
        hcsGateBit bank i g (hfan g List.mem_cons_self).1]
    rw [ih (hcsStep bank g) (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg')), hstep]

def hcsBitsNat : {k : Nat} → (Fin k → Bool) → Nat
  | 0, _ => 0
  | k + 1, x => (if x 0 then 1 else 0) + 2 * hcsBitsNat (fun i : Fin k => x i.succ)

theorem hcsBitsNat_lt : ∀ {k : Nat} (x : Fin k → Bool), hcsBitsNat x < 2 ^ k
  | 0, _ => by simp [hcsBitsNat]
  | k + 1, x => by
    have ih := hcsBitsNat_lt (fun i : Fin k => x i.succ)
    simp only [hcsBitsNat, Nat.pow_succ]
    cases x 0
    · simp; omega
    · simp; omega

theorem hcsBitsNat_testBit : ∀ {k : Nat} (x : Fin k → Bool) (i : Fin k),
    (hcsBitsNat x).testBit i.val = x i
  | 0, _, i => Fin.elim0 i
  | k + 1, x, i => by
    refine Fin.cases ?_ ?_ i
    · simp only [hcsBitsNat, Fin.val_zero]
      cases x 0
      · simp [Nat.testBit_zero]
      · have hmod : (1 + 2 * hcsBitsNat (fun m : Fin k => x m.succ)) % 2 = 1 := by omega
        simp [Nat.testBit_zero, hmod]
    · intro j
      have ih := hcsBitsNat_testBit (fun m : Fin k => x m.succ) j
      have hdiv : ((if x 0 then 1 else 0) + 2 * hcsBitsNat (fun m : Fin k => x m.succ)) / 2 =
          hcsBitsNat (fun m : Fin k => x m.succ) := by
        cases x 0
        · simp
        · simp; omega
      simpa only [hcsBitsNat, Fin.val_succ, Nat.testBit_succ, hdiv] using ih

def fanInTwoBool (C : Circuit) : Bool :=
  C.gates.all fun g =>
    (match g.op with
     | .and => true
     | .or => true
     | .not => true
     | _ => false) && decide (g.inputs.length ≤ 2)

theorem fanInTwo_of_bool (C : Circuit) (h : fanInTwoBool C = true) : FanInTwo C := by
  intro g hg
  have hall := List.all_eq_true.mp h g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hall
  refine ⟨?_, hall.2⟩
  cases hop : g.op <;> simp [hop] at hall ⊢

def repNat (a p : Nat) : Nat → Nat
  | 0 => a
  | k + 1 =>
    let x := repNat a p k
    x ||| (x <<< (p * 2 ^ k))

theorem repNat_hi (a p : Nat) (ha : ∀ r, p ≤ r → a.testBit r = false) :
    ∀ k r, p * 2 ^ k ≤ r → (repNat a p k).testBit r = false
  | 0, r, hr => ha r (by simpa using hr)
  | k + 1, r, hr => by
    simp only [repNat, Nat.testBit_or, Nat.testBit_shiftLeft]
    have h1 : p * 2 ^ k ≤ r := by
      have : p * 2 ^ k ≤ p * 2 ^ (k + 1) := Nat.mul_le_mul_left p (Nat.pow_le_pow_right (by omega) (by omega))
      omega
    have h2 : p * 2 ^ k ≤ r - p * 2 ^ k := by
      have : p * 2 ^ (k + 1) = p * 2 ^ k + p * 2 ^ k := by
        rw [Nat.pow_succ, Nat.mul_two, Nat.mul_add]
      omega
    rw [repNat_hi a p ha k r h1, repNat_hi a p ha k (r - p * 2 ^ k) h2]
    simp

theorem repNat_testBit (a p : Nat) (hp : 0 < p) (ha : ∀ r, p ≤ r → a.testBit r = false) :
    ∀ k r, r < p * 2 ^ k → (repNat a p k).testBit r = a.testBit (r % p)
  | 0, r, hr => by
    have hlt : r < p := by simpa using hr
    simp [repNat, Nat.mod_eq_of_lt hlt]
  | k + 1, r, hr => by
    simp only [repNat, Nat.testBit_or, Nat.testBit_shiftLeft]
    by_cases hlt : r < p * 2 ^ k
    · have hnot : ¬ (p * 2 ^ k ≤ r) := by omega
      simp [hnot, repNat_testBit a p hp ha k r hlt]
    · have hle : p * 2 ^ k ≤ r := by omega
      have hsub : r - p * 2 ^ k < p * 2 ^ k := by
        have : p * 2 ^ (k + 1) = p * 2 ^ k + p * 2 ^ k := by
          rw [Nat.pow_succ, Nat.mul_two, Nat.mul_add]
        omega
      have hmod : (r - p * 2 ^ k) % p = r % p := by
        have hd : r = (r - p * 2 ^ k) + p * 2 ^ k := by omega
        conv_rhs => rw [hd]
        rw [Nat.add_mul_mod_self_left]
      rw [repNat_hi a p ha k r hle, decide_eq_true hle, Bool.true_and, Bool.false_or,
        repNat_testBit a p hp ha k (r - p * 2 ^ k) hsub, hmod]

def varNat (j : Fin 15) : Nat :=
  repNat ((2 ^ (2 ^ j.val) - 1) <<< (2 ^ j.val)) (2 ^ (j.val + 1)) (14 - j.val)

theorem varNat_testBit (j : Fin 15) (r : Nat) (hr : r < 32768) :
    (varNat j).testBit r = r.testBit j.val := by
  have hp : 0 < 2 ^ (j.val + 1) := Nat.two_pow_pos _
  have ha : ∀ t, 2 ^ (j.val + 1) ≤ t → ((2 ^ (2 ^ j.val) - 1) <<< (2 ^ j.val)).testBit t = false := by
    intro t ht
    rw [Nat.testBit_shiftLeft]
    by_cases hle : 2 ^ j.val ≤ t
    · have hge : 2 ^ j.val ≤ t - 2 ^ j.val := by
        have : 2 ^ (j.val + 1) = 2 ^ j.val + 2 ^ j.val := by rw [Nat.pow_succ, Nat.mul_two]
        omega
      have hlt2 : 2 ^ (2 ^ j.val) - 1 < 2 ^ (t - 2 ^ j.val) := by
        have hpow : 2 ^ (2 ^ j.val) ≤ 2 ^ (t - 2 ^ j.val) := Nat.pow_le_pow_right (by omega) hge
        have hpos : 0 < 2 ^ (2 ^ j.val) := Nat.two_pow_pos _
        omega
      simp [Nat.testBit_lt_two_pow hlt2]
    · simp [hle]
  have hbound : r < 2 ^ (j.val + 1) * 2 ^ (14 - j.val) := by
    rw [← Nat.pow_add]
    have hexp : j.val + 1 + (14 - j.val) = 15 := by omega
    rw [hexp]
    exact hr
  rw [varNat, repNat_testBit _ _ hp ha (14 - j.val) r hbound]
  rw [Nat.testBit_shiftLeft]
  have hmod_lt : r % 2 ^ (j.val + 1) < 2 ^ (j.val + 1) := Nat.mod_lt r hp
  have hpow2 : 2 ^ (j.val + 1) = 2 ^ j.val + 2 ^ j.val := by rw [Nat.pow_succ, Nat.mul_two]
  have hbit : r.testBit j.val = decide (2 ^ j.val ≤ r % 2 ^ (j.val + 1)) := by
    rw [Nat.testBit_eq_decide_div_mod_eq]
    have hdiv : r % 2 ^ (j.val + 1) = r % 2 ^ j.val + 2 ^ j.val * (r / 2 ^ j.val % 2) := by
      have h1 : 2 ^ (j.val + 1) = 2 ^ j.val * 2 := by rw [Nat.pow_succ]
      rw [h1, Nat.mod_mul]
    have hrem : r % 2 ^ j.val < 2 ^ j.val := Nat.mod_lt r (Nat.two_pow_pos _)
    have hmod2 : r / 2 ^ j.val % 2 = 0 ∨ r / 2 ^ j.val % 2 = 1 := by omega
    rcases hmod2 with h0 | h1
    · rw [hdiv, h0]; simp [Nat.not_le.mpr hrem]
    · rw [hdiv, h1]; simp
  rw [hbit]
  by_cases hle : 2 ^ j.val ≤ r % 2 ^ (j.val + 1)
  · have hsub : r % 2 ^ (j.val + 1) - 2 ^ j.val < 2 ^ j.val := by omega
    simp [hle, Nat.testBit_two_pow_sub_one, hsub]
  · simp [hle]

def rawInputs : List (BitVec 32768) :=
  List.ofFn fun j : Fin 15 => BitVec.ofNat 32768 (varNat j)

theorem rawInputs_map (x : Fin 15 → Bool) :
    rawInputs.map (fun v => v.getLsbD (hcsBitsNat x)) = List.ofFn x := by
  have hr : hcsBitsNat x < 32768 := hcsBitsNat_lt x
  simp only [rawInputs, List.map_ofFn]
  congr 1
  funext j
  simp only [Function.comp_apply, BitVec.getLsbD_ofNat, hr, decide_true, Bool.true_and,
    varNat_testBit j (hcsBitsNat x) hr, hcsBitsNat_testBit x j]

def grpB0 (x : Fin 15 → Bool) : Bool :=
  (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 7 && x 9 && x 13 && x 14) || (x 0 && x 2 && x 4 && x 6 && x 8 && x 13) || (x 2 && x 3 && x 4 && x 5 && x 6 && x 7 && x 9 && x 11 && x 12 && x 13) || (x 0 && x 3 && x 4 && x 5 && x 7 && x 9 && x 10 && x 12 && x 13 && x 14) || (x 1 && x 2 && x 4 && x 5 && x 6 && x 7 && x 9 && x 10 && x 11 && x 14) || (x 0 && x 1 && x 2 && x 6 && x 7 && x 9 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 3 && x 7 && x 8 && x 9 && x 10 && x 12 && x 13 && x 14) || (x 1 && x 3 && x 4 && x 5 && x 6 && x 7 && x 9 && x 10 && x 11 && x 13) || (x 0 && x 3 && x 4 && x 6 && x 7 && x 9 && x 10 && x 11 && x 12 && x 14) || (x 0 && x 1 && x 3 && x 5 && x 6 && x 9 && x 10 && x 11 && x 13 && x 14)

def grpV0 (b0 : BitVec 32768) (b1 : BitVec 32768) (b2 : BitVec 32768) (b3 : BitVec 32768) (b4 : BitVec 32768) (b5 : BitVec 32768) (b6 : BitVec 32768) (b7 : BitVec 32768) (b8 : BitVec 32768) (b9 : BitVec 32768) (b10 : BitVec 32768) (b11 : BitVec 32768) (b12 : BitVec 32768) (b13 : BitVec 32768) (b14 : BitVec 32768) : BitVec 32768 :=
  (b0 &&& b1 &&& b2 &&& b3 &&& b4 &&& b5 &&& b7 &&& b9 &&& b13 &&& b14) ||| (b0 &&& b2 &&& b4 &&& b6 &&& b8 &&& b13) ||| (b2 &&& b3 &&& b4 &&& b5 &&& b6 &&& b7 &&& b9 &&& b11 &&& b12 &&& b13) ||| (b0 &&& b3 &&& b4 &&& b5 &&& b7 &&& b9 &&& b10 &&& b12 &&& b13 &&& b14) ||| (b1 &&& b2 &&& b4 &&& b5 &&& b6 &&& b7 &&& b9 &&& b10 &&& b11 &&& b14) ||| (b0 &&& b1 &&& b2 &&& b6 &&& b7 &&& b9 &&& b11 &&& b12 &&& b13 &&& b14) ||| (b0 &&& b1 &&& b3 &&& b7 &&& b8 &&& b9 &&& b10 &&& b12 &&& b13 &&& b14) ||| (b1 &&& b3 &&& b4 &&& b5 &&& b6 &&& b7 &&& b9 &&& b10 &&& b11 &&& b13) ||| (b0 &&& b3 &&& b4 &&& b6 &&& b7 &&& b9 &&& b10 &&& b11 &&& b12 &&& b14) ||| (b0 &&& b1 &&& b3 &&& b5 &&& b6 &&& b9 &&& b10 &&& b11 &&& b13 &&& b14)

theorem grpBit0 (b : Fin 15 → BitVec 32768) (i : Fin 32768) :
    (grpV0 (b 0) (b 1) (b 2) (b 3) (b 4) (b 5) (b 6) (b 7) (b 8) (b 9) (b 10) (b 11) (b 12) (b 13) (b 14)).getLsbD i.val = grpB0 (fun j => (b j).getLsbD i.val) := by
  simp only [grpV0, grpB0, BitVec.getLsbD_or, BitVec.getLsbD_and]

def grpB1 (x : Fin 15 → Bool) : Bool :=
  grpB0 x || (x 0 && x 1 && x 4 && x 5 && x 7 && x 9 && x 10 && x 11 && x 12 && x 13) || (x 2 && x 3 && x 4 && x 5 && x 6 && x 8 && x 9 && x 10 && x 12 && x 13) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 6 && x 11 && x 12 && x 14) || (x 0 && x 1 && x 4 && x 6 && x 8 && x 10 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 2 && x 3 && x 7 && x 8 && x 9 && x 10 && x 11 && x 12 && x 14) || (x 1 && x 2 && x 3 && x 5 && x 7 && x 8 && x 9 && x 10 && x 11 && x 13) || (x 0 && x 1 && x 3 && x 6 && x 7 && x 10 && x 11 && x 12 && x 13 && x 14) || (x 1 && x 2 && x 4 && x 5 && x 7 && x 8 && x 9 && x 10 && x 11 && x 12) || (x 0 && x 1 && x 2 && x 5 && x 8 && x 9 && x 10 && x 11 && x 12 && x 14) || (x 0 && x 2 && x 4 && x 7 && x 8 && x 9 && x 10 && x 11 && x 13 && x 14)

def grpV1 (b0 : BitVec 32768) (b1 : BitVec 32768) (b2 : BitVec 32768) (b3 : BitVec 32768) (b4 : BitVec 32768) (b5 : BitVec 32768) (b6 : BitVec 32768) (b7 : BitVec 32768) (b8 : BitVec 32768) (b9 : BitVec 32768) (b10 : BitVec 32768) (b11 : BitVec 32768) (b12 : BitVec 32768) (b13 : BitVec 32768) (b14 : BitVec 32768) : BitVec 32768 :=
  grpV0 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 ||| (b0 &&& b1 &&& b4 &&& b5 &&& b7 &&& b9 &&& b10 &&& b11 &&& b12 &&& b13) ||| (b2 &&& b3 &&& b4 &&& b5 &&& b6 &&& b8 &&& b9 &&& b10 &&& b12 &&& b13) ||| (b0 &&& b1 &&& b2 &&& b3 &&& b4 &&& b5 &&& b6 &&& b11 &&& b12 &&& b14) ||| (b0 &&& b1 &&& b4 &&& b6 &&& b8 &&& b10 &&& b11 &&& b12 &&& b13 &&& b14) ||| (b0 &&& b2 &&& b3 &&& b7 &&& b8 &&& b9 &&& b10 &&& b11 &&& b12 &&& b14) ||| (b1 &&& b2 &&& b3 &&& b5 &&& b7 &&& b8 &&& b9 &&& b10 &&& b11 &&& b13) ||| (b0 &&& b1 &&& b3 &&& b6 &&& b7 &&& b10 &&& b11 &&& b12 &&& b13 &&& b14) ||| (b1 &&& b2 &&& b4 &&& b5 &&& b7 &&& b8 &&& b9 &&& b10 &&& b11 &&& b12) ||| (b0 &&& b1 &&& b2 &&& b5 &&& b8 &&& b9 &&& b10 &&& b11 &&& b12 &&& b14) ||| (b0 &&& b2 &&& b4 &&& b7 &&& b8 &&& b9 &&& b10 &&& b11 &&& b13 &&& b14)

theorem grpBit1 (b : Fin 15 → BitVec 32768) (i : Fin 32768) :
    (grpV1 (b 0) (b 1) (b 2) (b 3) (b 4) (b 5) (b 6) (b 7) (b 8) (b 9) (b 10) (b 11) (b 12) (b 13) (b 14)).getLsbD i.val = grpB1 (fun j => (b j).getLsbD i.val) := by
  simp only [grpV1, grpB1, BitVec.getLsbD_or, BitVec.getLsbD_and, grpBit0 b i]

def grpB2 (x : Fin 15 → Bool) : Bool :=
  grpB1 x || (x 0 && x 1 && x 2 && x 5 && x 6 && x 7 && x 8 && x 11 && x 12 && x 14) || (x 0 && x 1 && x 3 && x 5 && x 8 && x 9 && x 10 && x 11 && x 12 && x 13) || (x 1 && x 2 && x 4 && x 6 && x 7 && x 8 && x 9 && x 10 && x 12 && x 13) || (x 2 && x 3 && x 4 && x 5 && x 7 && x 8 && x 9 && x 10 && x 12 && x 14) || (x 0 && x 2 && x 3 && x 5 && x 6 && x 9 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 6 && x 7 && x 9 && x 11 && x 14) || (x 0 && x 1 && x 2 && x 5 && x 6 && x 7 && x 8 && x 10 && x 13 && x 14) || (x 0 && x 1 && x 3 && x 5 && x 7 && x 10) || (x 0 && x 3 && x 4 && x 6 && x 8 && x 9 && x 10 && x 11 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 6 && x 7 && x 10 && x 11 && x 13)

def grpV2 (b0 : BitVec 32768) (b1 : BitVec 32768) (b2 : BitVec 32768) (b3 : BitVec 32768) (b4 : BitVec 32768) (b5 : BitVec 32768) (b6 : BitVec 32768) (b7 : BitVec 32768) (b8 : BitVec 32768) (b9 : BitVec 32768) (b10 : BitVec 32768) (b11 : BitVec 32768) (b12 : BitVec 32768) (b13 : BitVec 32768) (b14 : BitVec 32768) : BitVec 32768 :=
  grpV1 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 ||| (b0 &&& b1 &&& b2 &&& b5 &&& b6 &&& b7 &&& b8 &&& b11 &&& b12 &&& b14) ||| (b0 &&& b1 &&& b3 &&& b5 &&& b8 &&& b9 &&& b10 &&& b11 &&& b12 &&& b13) ||| (b1 &&& b2 &&& b4 &&& b6 &&& b7 &&& b8 &&& b9 &&& b10 &&& b12 &&& b13) ||| (b2 &&& b3 &&& b4 &&& b5 &&& b7 &&& b8 &&& b9 &&& b10 &&& b12 &&& b14) ||| (b0 &&& b2 &&& b3 &&& b5 &&& b6 &&& b9 &&& b11 &&& b12 &&& b13 &&& b14) ||| (b0 &&& b1 &&& b2 &&& b3 &&& b4 &&& b6 &&& b7 &&& b9 &&& b11 &&& b14) ||| (b0 &&& b1 &&& b2 &&& b5 &&& b6 &&& b7 &&& b8 &&& b10 &&& b13 &&& b14) ||| (b0 &&& b1 &&& b3 &&& b5 &&& b7 &&& b10) ||| (b0 &&& b3 &&& b4 &&& b6 &&& b8 &&& b9 &&& b10 &&& b11 &&& b13 &&& b14) ||| (b0 &&& b1 &&& b2 &&& b3 &&& b4 &&& b6 &&& b7 &&& b10 &&& b11 &&& b13)

theorem grpBit2 (b : Fin 15 → BitVec 32768) (i : Fin 32768) :
    (grpV2 (b 0) (b 1) (b 2) (b 3) (b 4) (b 5) (b 6) (b 7) (b 8) (b 9) (b 10) (b 11) (b 12) (b 13) (b 14)).getLsbD i.val = grpB2 (fun j => (b j).getLsbD i.val) := by
  simp only [grpV2, grpB2, BitVec.getLsbD_or, BitVec.getLsbD_and, grpBit1 b i]

def grpB3 (x : Fin 15 → Bool) : Bool :=
  grpB2 x || (x 9 && x 10 && x 11 && x 12 && x 13 && x 14) || (x 2 && x 3 && x 4 && x 5 && x 6 && x 7 && x 10 && x 11 && x 12 && x 14) || (x 0 && x 1 && x 2 && x 5 && x 6 && x 9) || (x 2 && x 3 && x 4 && x 5 && x 7 && x 8 && x 9 && x 11 && x 13 && x 14) || (x 1 && x 2 && x 3 && x 5 && x 7 && x 8 && x 10 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 8 && x 9 && x 12 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 7 && x 8 && x 9 && x 10 && x 13) || (x 0 && x 1 && x 4 && x 5 && x 6 && x 7 && x 8 && x 10 && x 12 && x 13) || (x 0 && x 2 && x 4 && x 6 && x 7 && x 9 && x 10 && x 11 && x 12 && x 13) || (x 1 && x 3 && x 4 && x 5 && x 6 && x 7 && x 10 && x 12 && x 13 && x 14)

def grpV3 (b0 : BitVec 32768) (b1 : BitVec 32768) (b2 : BitVec 32768) (b3 : BitVec 32768) (b4 : BitVec 32768) (b5 : BitVec 32768) (b6 : BitVec 32768) (b7 : BitVec 32768) (b8 : BitVec 32768) (b9 : BitVec 32768) (b10 : BitVec 32768) (b11 : BitVec 32768) (b12 : BitVec 32768) (b13 : BitVec 32768) (b14 : BitVec 32768) : BitVec 32768 :=
  grpV2 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 ||| (b9 &&& b10 &&& b11 &&& b12 &&& b13 &&& b14) ||| (b2 &&& b3 &&& b4 &&& b5 &&& b6 &&& b7 &&& b10 &&& b11 &&& b12 &&& b14) ||| (b0 &&& b1 &&& b2 &&& b5 &&& b6 &&& b9) ||| (b2 &&& b3 &&& b4 &&& b5 &&& b7 &&& b8 &&& b9 &&& b11 &&& b13 &&& b14) ||| (b1 &&& b2 &&& b3 &&& b5 &&& b7 &&& b8 &&& b10 &&& b12 &&& b13 &&& b14) ||| (b0 &&& b1 &&& b2 &&& b3 &&& b4 &&& b5 &&& b8 &&& b9 &&& b12 &&& b14) ||| (b0 &&& b1 &&& b2 &&& b3 &&& b4 &&& b7 &&& b8 &&& b9 &&& b10 &&& b13) ||| (b0 &&& b1 &&& b4 &&& b5 &&& b6 &&& b7 &&& b8 &&& b10 &&& b12 &&& b13) ||| (b0 &&& b2 &&& b4 &&& b6 &&& b7 &&& b9 &&& b10 &&& b11 &&& b12 &&& b13) ||| (b1 &&& b3 &&& b4 &&& b5 &&& b6 &&& b7 &&& b10 &&& b12 &&& b13 &&& b14)

theorem grpBit3 (b : Fin 15 → BitVec 32768) (i : Fin 32768) :
    (grpV3 (b 0) (b 1) (b 2) (b 3) (b 4) (b 5) (b 6) (b 7) (b 8) (b 9) (b 10) (b 11) (b 12) (b 13) (b 14)).getLsbD i.val = grpB3 (fun j => (b j).getLsbD i.val) := by
  simp only [grpV3, grpB3, BitVec.getLsbD_or, BitVec.getLsbD_and, grpBit2 b i]

def grpB4 (x : Fin 15 → Bool) : Bool :=
  grpB3 x || (x 1 && x 2 && x 4 && x 5 && x 7 && x 8 && x 11 && x 12 && x 13 && x 14) || (x 1 && x 3 && x 4 && x 6 && x 7 && x 8 && x 9 && x 11 && x 13 && x 14) || (x 0 && x 2 && x 4 && x 5 && x 8 && x 10 && x 11 && x 12 && x 13 && x 14) || (x 1 && x 3 && x 4 && x 5 && x 6 && x 8 && x 9 && x 10 && x 11 && x 12) || (x 0 && x 3 && x 4 && x 7 && x 8 && x 14) || (x 1 && x 2 && x 3 && x 6 && x 7 && x 8 && x 10 && x 11 && x 12 && x 14) || (x 2 && x 3 && x 4 && x 5 && x 6 && x 8 && x 10 && x 11 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 7 && x 8 && x 9 && x 11 && x 12) || (x 0 && x 2 && x 3 && x 6 && x 7 && x 12) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 8 && x 10 && x 12 && x 13)

def grpV4 (b0 : BitVec 32768) (b1 : BitVec 32768) (b2 : BitVec 32768) (b3 : BitVec 32768) (b4 : BitVec 32768) (b5 : BitVec 32768) (b6 : BitVec 32768) (b7 : BitVec 32768) (b8 : BitVec 32768) (b9 : BitVec 32768) (b10 : BitVec 32768) (b11 : BitVec 32768) (b12 : BitVec 32768) (b13 : BitVec 32768) (b14 : BitVec 32768) : BitVec 32768 :=
  grpV3 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 ||| (b1 &&& b2 &&& b4 &&& b5 &&& b7 &&& b8 &&& b11 &&& b12 &&& b13 &&& b14) ||| (b1 &&& b3 &&& b4 &&& b6 &&& b7 &&& b8 &&& b9 &&& b11 &&& b13 &&& b14) ||| (b0 &&& b2 &&& b4 &&& b5 &&& b8 &&& b10 &&& b11 &&& b12 &&& b13 &&& b14) ||| (b1 &&& b3 &&& b4 &&& b5 &&& b6 &&& b8 &&& b9 &&& b10 &&& b11 &&& b12) ||| (b0 &&& b3 &&& b4 &&& b7 &&& b8 &&& b14) ||| (b1 &&& b2 &&& b3 &&& b6 &&& b7 &&& b8 &&& b10 &&& b11 &&& b12 &&& b14) ||| (b2 &&& b3 &&& b4 &&& b5 &&& b6 &&& b8 &&& b10 &&& b11 &&& b13 &&& b14) ||| (b0 &&& b1 &&& b2 &&& b3 &&& b4 &&& b7 &&& b8 &&& b9 &&& b11 &&& b12) ||| (b0 &&& b2 &&& b3 &&& b6 &&& b7 &&& b12) ||| (b0 &&& b1 &&& b2 &&& b3 &&& b4 &&& b5 &&& b8 &&& b10 &&& b12 &&& b13)

theorem grpBit4 (b : Fin 15 → BitVec 32768) (i : Fin 32768) :
    (grpV4 (b 0) (b 1) (b 2) (b 3) (b 4) (b 5) (b 6) (b 7) (b 8) (b 9) (b 10) (b 11) (b 12) (b 13) (b 14)).getLsbD i.val = grpB4 (fun j => (b j).getLsbD i.val) := by
  simp only [grpV4, grpB4, BitVec.getLsbD_or, BitVec.getLsbD_and, grpBit3 b i]

def grpB5 (x : Fin 15 → Bool) : Bool :=
  grpB4 x || (x 1 && x 3 && x 4 && x 5 && x 6 && x 8 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 3 && x 5 && x 6 && x 7 && x 8 && x 11 && x 12 && x 13) || (x 1 && x 3 && x 4 && x 6 && x 7 && x 8 && x 9 && x 10 && x 12 && x 14) || (x 0 && x 3 && x 4 && x 5 && x 6 && x 7 && x 8 && x 9 && x 10 && x 13) || (x 0 && x 2 && x 4 && x 5 && x 6 && x 7 && x 8 && x 10 && x 11 && x 12) || (x 0 && x 2 && x 4 && x 5 && x 6 && x 7 && x 8 && x 9 && x 10 && x 14) || (x 0 && x 1 && x 2 && x 6 && x 8 && x 9 && x 10 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 4 && x 5 && x 6 && x 9 && x 10 && x 11 && x 12 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 7 && x 11 && x 12 && x 13) || (x 1 && x 2 && x 3 && x 5 && x 6 && x 8 && x 9 && x 10 && x 11 && x 14)

def grpV5 (b0 : BitVec 32768) (b1 : BitVec 32768) (b2 : BitVec 32768) (b3 : BitVec 32768) (b4 : BitVec 32768) (b5 : BitVec 32768) (b6 : BitVec 32768) (b7 : BitVec 32768) (b8 : BitVec 32768) (b9 : BitVec 32768) (b10 : BitVec 32768) (b11 : BitVec 32768) (b12 : BitVec 32768) (b13 : BitVec 32768) (b14 : BitVec 32768) : BitVec 32768 :=
  grpV4 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 ||| (b1 &&& b3 &&& b4 &&& b5 &&& b6 &&& b8 &&& b11 &&& b12 &&& b13 &&& b14) ||| (b0 &&& b1 &&& b3 &&& b5 &&& b6 &&& b7 &&& b8 &&& b11 &&& b12 &&& b13) ||| (b1 &&& b3 &&& b4 &&& b6 &&& b7 &&& b8 &&& b9 &&& b10 &&& b12 &&& b14) ||| (b0 &&& b3 &&& b4 &&& b5 &&& b6 &&& b7 &&& b8 &&& b9 &&& b10 &&& b13) ||| (b0 &&& b2 &&& b4 &&& b5 &&& b6 &&& b7 &&& b8 &&& b10 &&& b11 &&& b12) ||| (b0 &&& b2 &&& b4 &&& b5 &&& b6 &&& b7 &&& b8 &&& b9 &&& b10 &&& b14) ||| (b0 &&& b1 &&& b2 &&& b6 &&& b8 &&& b9 &&& b10 &&& b12 &&& b13 &&& b14) ||| (b0 &&& b1 &&& b4 &&& b5 &&& b6 &&& b9 &&& b10 &&& b11 &&& b12 &&& b14) ||| (b0 &&& b1 &&& b2 &&& b3 &&& b4 &&& b5 &&& b7 &&& b11 &&& b12 &&& b13) ||| (b1 &&& b2 &&& b3 &&& b5 &&& b6 &&& b8 &&& b9 &&& b10 &&& b11 &&& b14)

theorem grpBit5 (b : Fin 15 → BitVec 32768) (i : Fin 32768) :
    (grpV5 (b 0) (b 1) (b 2) (b 3) (b 4) (b 5) (b 6) (b 7) (b 8) (b 9) (b 10) (b 11) (b 12) (b 13) (b 14)).getLsbD i.val = grpB5 (fun j => (b j).getLsbD i.val) := by
  simp only [grpV5, grpB5, BitVec.getLsbD_or, BitVec.getLsbD_and, grpBit4 b i]

def grpB6 (x : Fin 15 → Bool) : Bool :=
  grpB5 x || (x 0 && x 1 && x 4 && x 5 && x 8 && x 11) || (x 1 && x 2 && x 3 && x 9 && x 10 && x 12) || (x 0 && x 1 && x 4 && x 7 && x 8 && x 9 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 6 && x 8 && x 9 && x 10 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 6 && x 8 && x 10 && x 11 && x 12) || (x 0 && x 2 && x 3 && x 5 && x 6 && x 7 && x 8 && x 10 && x 11 && x 13) || (x 0 && x 1 && x 2 && x 5 && x 7 && x 9 && x 10 && x 11 && x 13 && x 14) || (x 5 && x 7 && x 8 && x 10 && x 11 && x 14) || (x 0 && x 1 && x 3 && x 5 && x 6 && x 7 && x 8 && x 9 && x 13 && x 14) || (x 2 && x 3 && x 4 && x 12 && x 13 && x 14)

def grpV6 (b0 : BitVec 32768) (b1 : BitVec 32768) (b2 : BitVec 32768) (b3 : BitVec 32768) (b4 : BitVec 32768) (b5 : BitVec 32768) (b6 : BitVec 32768) (b7 : BitVec 32768) (b8 : BitVec 32768) (b9 : BitVec 32768) (b10 : BitVec 32768) (b11 : BitVec 32768) (b12 : BitVec 32768) (b13 : BitVec 32768) (b14 : BitVec 32768) : BitVec 32768 :=
  grpV5 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 ||| (b0 &&& b1 &&& b4 &&& b5 &&& b8 &&& b11) ||| (b1 &&& b2 &&& b3 &&& b9 &&& b10 &&& b12) ||| (b0 &&& b1 &&& b4 &&& b7 &&& b8 &&& b9 &&& b11 &&& b12 &&& b13 &&& b14) ||| (b0 &&& b1 &&& b2 &&& b3 &&& b4 &&& b6 &&& b8 &&& b9 &&& b10 &&& b14) ||| (b0 &&& b1 &&& b2 &&& b3 &&& b4 &&& b6 &&& b8 &&& b10 &&& b11 &&& b12) ||| (b0 &&& b2 &&& b3 &&& b5 &&& b6 &&& b7 &&& b8 &&& b10 &&& b11 &&& b13) ||| (b0 &&& b1 &&& b2 &&& b5 &&& b7 &&& b9 &&& b10 &&& b11 &&& b13 &&& b14) ||| (b5 &&& b7 &&& b8 &&& b10 &&& b11 &&& b14) ||| (b0 &&& b1 &&& b3 &&& b5 &&& b6 &&& b7 &&& b8 &&& b9 &&& b13 &&& b14) ||| (b2 &&& b3 &&& b4 &&& b12 &&& b13 &&& b14)

theorem grpBit6 (b : Fin 15 → BitVec 32768) (i : Fin 32768) :
    (grpV6 (b 0) (b 1) (b 2) (b 3) (b 4) (b 5) (b 6) (b 7) (b 8) (b 9) (b 10) (b 11) (b 12) (b 13) (b 14)).getLsbD i.val = grpB6 (fun j => (b j).getLsbD i.val) := by
  simp only [grpV6, grpB6, BitVec.getLsbD_or, BitVec.getLsbD_and, grpBit5 b i]

def grpB7 (x : Fin 15 → Bool) : Bool :=
  grpB6 x || (x 6 && x 7 && x 8 && x 12 && x 13 && x 14) || (x 1 && x 2 && x 4 && x 6 && x 7 && x 8 && x 10 && x 11 && x 13 && x 14) || (x 0 && x 2 && x 3 && x 5 && x 7 && x 10 && x 11 && x 12 && x 13 && x 14) || (x 5 && x 6 && x 8 && x 9 && x 11 && x 13) || (x 0 && x 2 && x 3 && x 5 && x 6 && x 7 && x 8 && x 9 && x 11 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 6 && x 10 && x 13 && x 14) || (x 1 && x 2 && x 3 && x 6 && x 7 && x 8 && x 9 && x 11 && x 12 && x 13) || (x 1 && x 3 && x 4 && x 10 && x 11 && x 14) || (x 0 && x 2 && x 3 && x 6 && x 8 && x 9 && x 10 && x 11 && x 12 && x 13) || (x 1 && x 2 && x 4 && x 9 && x 11 && x 13)

def grpV7 (b0 : BitVec 32768) (b1 : BitVec 32768) (b2 : BitVec 32768) (b3 : BitVec 32768) (b4 : BitVec 32768) (b5 : BitVec 32768) (b6 : BitVec 32768) (b7 : BitVec 32768) (b8 : BitVec 32768) (b9 : BitVec 32768) (b10 : BitVec 32768) (b11 : BitVec 32768) (b12 : BitVec 32768) (b13 : BitVec 32768) (b14 : BitVec 32768) : BitVec 32768 :=
  grpV6 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 ||| (b6 &&& b7 &&& b8 &&& b12 &&& b13 &&& b14) ||| (b1 &&& b2 &&& b4 &&& b6 &&& b7 &&& b8 &&& b10 &&& b11 &&& b13 &&& b14) ||| (b0 &&& b2 &&& b3 &&& b5 &&& b7 &&& b10 &&& b11 &&& b12 &&& b13 &&& b14) ||| (b5 &&& b6 &&& b8 &&& b9 &&& b11 &&& b13) ||| (b0 &&& b2 &&& b3 &&& b5 &&& b6 &&& b7 &&& b8 &&& b9 &&& b11 &&& b14) ||| (b0 &&& b1 &&& b2 &&& b3 &&& b4 &&& b5 &&& b6 &&& b10 &&& b13 &&& b14) ||| (b1 &&& b2 &&& b3 &&& b6 &&& b7 &&& b8 &&& b9 &&& b11 &&& b12 &&& b13) ||| (b1 &&& b3 &&& b4 &&& b10 &&& b11 &&& b14) ||| (b0 &&& b2 &&& b3 &&& b6 &&& b8 &&& b9 &&& b10 &&& b11 &&& b12 &&& b13) ||| (b1 &&& b2 &&& b4 &&& b9 &&& b11 &&& b13)

theorem grpBit7 (b : Fin 15 → BitVec 32768) (i : Fin 32768) :
    (grpV7 (b 0) (b 1) (b 2) (b 3) (b 4) (b 5) (b 6) (b 7) (b 8) (b 9) (b 10) (b 11) (b 12) (b 13) (b 14)).getLsbD i.val = grpB7 (fun j => (b j).getLsbD i.val) := by
  simp only [grpV7, grpB7, BitVec.getLsbD_or, BitVec.getLsbD_and, grpBit6 b i]

def grpB8 (x : Fin 15 → Bool) : Bool :=
  grpB7 x || (x 5 && x 6 && x 7 && x 9 && x 10 && x 12) || (x 0 && x 3 && x 4 && x 5 && x 6 && x 7 && x 8 && x 9 && x 11 && x 12) || (x 1 && x 2 && x 3 && x 5 && x 6 && x 8 && x 9 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 4 && x 5 && x 6 && x 7 && x 8 && x 9 && x 12 && x 14) || (x 0 && x 3 && x 4 && x 5 && x 8 && x 9 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 2 && x 4 && x 5 && x 6 && x 9 && x 10 && x 12 && x 13 && x 14) || (x 1 && x 2 && x 4 && x 5 && x 6 && x 7 && x 9 && x 12 && x 13 && x 14)

def grpV8 (b0 : BitVec 32768) (b1 : BitVec 32768) (b2 : BitVec 32768) (b3 : BitVec 32768) (b4 : BitVec 32768) (b5 : BitVec 32768) (b6 : BitVec 32768) (b7 : BitVec 32768) (b8 : BitVec 32768) (b9 : BitVec 32768) (b10 : BitVec 32768) (b11 : BitVec 32768) (b12 : BitVec 32768) (b13 : BitVec 32768) (b14 : BitVec 32768) : BitVec 32768 :=
  grpV7 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 ||| (b5 &&& b6 &&& b7 &&& b9 &&& b10 &&& b12) ||| (b0 &&& b3 &&& b4 &&& b5 &&& b6 &&& b7 &&& b8 &&& b9 &&& b11 &&& b12) ||| (b1 &&& b2 &&& b3 &&& b5 &&& b6 &&& b8 &&& b9 &&& b12 &&& b13 &&& b14) ||| (b0 &&& b1 &&& b4 &&& b5 &&& b6 &&& b7 &&& b8 &&& b9 &&& b12 &&& b14) ||| (b0 &&& b3 &&& b4 &&& b5 &&& b8 &&& b9 &&& b11 &&& b12 &&& b13 &&& b14) ||| (b0 &&& b2 &&& b4 &&& b5 &&& b6 &&& b9 &&& b10 &&& b12 &&& b13 &&& b14) ||| (b1 &&& b2 &&& b4 &&& b5 &&& b6 &&& b7 &&& b9 &&& b12 &&& b13 &&& b14)

theorem grpBit8 (b : Fin 15 → BitVec 32768) (i : Fin 32768) :
    (grpV8 (b 0) (b 1) (b 2) (b 3) (b 4) (b 5) (b 6) (b 7) (b 8) (b 9) (b 10) (b 11) (b 12) (b 13) (b 14)).getLsbD i.val = grpB8 (fun j => (b j).getLsbD i.val) := by
  simp only [grpV8, grpB8, BitVec.getLsbD_or, BitVec.getLsbD_and, grpBit7 b i]

def targetFun (x : Fin 15 → Bool) : Bool :=
  !(grpB8 x)

def bvTarget (b : Fin 15 → BitVec 32768) : BitVec 32768 :=
  ~~~(grpV8 (b 0) (b 1) (b 2) (b 3) (b 4) (b 5) (b 6) (b 7) (b 8) (b 9) (b 10) (b 11) (b 12) (b 13) (b 14))

theorem bvTarget_bit (b : Fin 15 → BitVec 32768) (i : Fin 32768) :
    (bvTarget b).getLsbD i.val = targetFun (fun j => (b j).getLsbD i.val) := by
  simp only [bvTarget, targetFun, BitVec.getLsbD_not, i.isLt, decide_true, Bool.true_and, grpBit8 b i]

def evalBvTarget (bank : List (BitVec 32768)) : BitVec 32768 :=
  let b0 := bank.getD 0 0
  let b1 := bank.getD 1 0
  let b2 := bank.getD 2 0
  let b3 := bank.getD 3 0
  let b4 := bank.getD 4 0
  let b5 := bank.getD 5 0
  let b6 := bank.getD 6 0
  let b7 := bank.getD 7 0
  let b8 := bank.getD 8 0
  let b9 := bank.getD 9 0
  let b10 := bank.getD 10 0
  let b11 := bank.getD 11 0
  let b12 := bank.getD 12 0
  let b13 := bank.getD 13 0
  let b14 := bank.getD 14 0
  ~~~(grpV8 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14)

theorem evalBvTarget_eq (bank : List (BitVec 32768)) :
    evalBvTarget bank = bvTarget (fun j : Fin 15 => bank.getD j.val 0) := rfl

def witness : Circuit :=
  ⟨[
    ⟨.and, [0, 9]⟩,
    ⟨.and, [1, 6]⟩,
    ⟨.and, [2, 5]⟩,
    ⟨.and, [15, 16]⟩,
    ⟨.and, [17, 18]⟩,
    ⟨.and, [0, 10]⟩,
    ⟨.and, [1, 7]⟩,
    ⟨.and, [3, 5]⟩,
    ⟨.and, [20, 21]⟩,
    ⟨.and, [22, 23]⟩,
    ⟨.and, [0, 11]⟩,
    ⟨.and, [1, 8]⟩,
    ⟨.and, [4, 5]⟩,
    ⟨.and, [25, 26]⟩,
    ⟨.and, [27, 28]⟩,
    ⟨.and, [0, 12]⟩,
    ⟨.and, [2, 7]⟩,
    ⟨.and, [3, 6]⟩,
    ⟨.and, [30, 31]⟩,
    ⟨.and, [32, 33]⟩,
    ⟨.and, [0, 13]⟩,
    ⟨.and, [2, 8]⟩,
    ⟨.and, [4, 6]⟩,
    ⟨.and, [35, 36]⟩,
    ⟨.and, [37, 38]⟩,
    ⟨.and, [0, 14]⟩,
    ⟨.and, [3, 8]⟩,
    ⟨.and, [4, 7]⟩,
    ⟨.and, [40, 41]⟩,
    ⟨.and, [42, 43]⟩,
    ⟨.and, [1, 12]⟩,
    ⟨.and, [2, 10]⟩,
    ⟨.and, [3, 9]⟩,
    ⟨.and, [45, 46]⟩,
    ⟨.and, [47, 48]⟩,
    ⟨.and, [1, 13]⟩,
    ⟨.and, [2, 11]⟩,
    ⟨.and, [4, 9]⟩,
    ⟨.and, [50, 51]⟩,
    ⟨.and, [52, 53]⟩,
    ⟨.and, [1, 14]⟩,
    ⟨.and, [3, 11]⟩,
    ⟨.and, [4, 10]⟩,
    ⟨.and, [55, 56]⟩,
    ⟨.and, [57, 58]⟩,
    ⟨.and, [2, 14]⟩,
    ⟨.and, [3, 13]⟩,
    ⟨.and, [4, 12]⟩,
    ⟨.and, [60, 61]⟩,
    ⟨.and, [62, 63]⟩,
    ⟨.and, [5, 12]⟩,
    ⟨.and, [6, 10]⟩,
    ⟨.and, [7, 9]⟩,
    ⟨.and, [65, 66]⟩,
    ⟨.and, [67, 68]⟩,
    ⟨.and, [5, 13]⟩,
    ⟨.and, [6, 11]⟩,
    ⟨.and, [8, 9]⟩,
    ⟨.and, [70, 71]⟩,
    ⟨.and, [72, 73]⟩,
    ⟨.and, [5, 14]⟩,
    ⟨.and, [7, 11]⟩,
    ⟨.and, [8, 10]⟩,
    ⟨.and, [75, 76]⟩,
    ⟨.and, [77, 78]⟩,
    ⟨.and, [6, 14]⟩,
    ⟨.and, [7, 13]⟩,
    ⟨.and, [8, 12]⟩,
    ⟨.and, [80, 81]⟩,
    ⟨.and, [82, 83]⟩,
    ⟨.and, [9, 14]⟩,
    ⟨.and, [10, 13]⟩,
    ⟨.and, [11, 12]⟩,
    ⟨.and, [85, 86]⟩,
    ⟨.and, [87, 88]⟩,
    ⟨.and, [0, 1]⟩,
    ⟨.and, [2, 90]⟩,
    ⟨.and, [3, 91]⟩,
    ⟨.and, [4, 92]⟩,
    ⟨.or, [86, 87]⟩,
    ⟨.or, [85, 87]⟩,
    ⟨.or, [85, 86]⟩,
    ⟨.and, [5, 6]⟩,
    ⟨.and, [14, 97]⟩,
    ⟨.and, [7, 8]⟩,
    ⟨.and, [9, 99]⟩,
    ⟨.or, [98, 100]⟩,
    ⟨.and, [94, 101]⟩,
    ⟨.and, [5, 7]⟩,
    ⟨.and, [13, 103]⟩,
    ⟨.and, [6, 8]⟩,
    ⟨.and, [10, 105]⟩,
    ⟨.or, [104, 106]⟩,
    ⟨.and, [95, 107]⟩,
    ⟨.and, [5, 8]⟩,
    ⟨.and, [12, 109]⟩,
    ⟨.and, [6, 7]⟩,
    ⟨.and, [11, 111]⟩,
    ⟨.or, [110, 112]⟩,
    ⟨.and, [96, 113]⟩,
    ⟨.or, [102, 108]⟩,
    ⟨.or, [114, 115]⟩,
    ⟨.and, [93, 116]⟩,
    ⟨.and, [0, 5]⟩,
    ⟨.and, [6, 118]⟩,
    ⟨.and, [7, 119]⟩,
    ⟨.and, [8, 120]⟩,
    ⟨.and, [1, 2]⟩,
    ⟨.and, [14, 122]⟩,
    ⟨.and, [3, 4]⟩,
    ⟨.and, [9, 124]⟩,
    ⟨.or, [123, 125]⟩,
    ⟨.and, [94, 126]⟩,
    ⟨.and, [1, 3]⟩,
    ⟨.and, [13, 128]⟩,
    ⟨.and, [2, 4]⟩,
    ⟨.and, [10, 130]⟩,
    ⟨.or, [129, 131]⟩,
    ⟨.and, [95, 132]⟩,
    ⟨.and, [1, 4]⟩,
    ⟨.and, [12, 134]⟩,
    ⟨.and, [2, 3]⟩,
    ⟨.and, [11, 136]⟩,
    ⟨.or, [135, 137]⟩,
    ⟨.and, [96, 138]⟩,
    ⟨.or, [127, 133]⟩,
    ⟨.or, [139, 140]⟩,
    ⟨.and, [121, 141]⟩,
    ⟨.and, [1, 5]⟩,
    ⟨.and, [9, 143]⟩,
    ⟨.and, [10, 144]⟩,
    ⟨.and, [11, 145]⟩,
    ⟨.or, [81, 82]⟩,
    ⟨.or, [80, 82]⟩,
    ⟨.or, [80, 81]⟩,
    ⟨.and, [0, 2]⟩,
    ⟨.and, [14, 150]⟩,
    ⟨.and, [6, 124]⟩,
    ⟨.or, [151, 152]⟩,
    ⟨.and, [147, 153]⟩,
    ⟨.and, [0, 3]⟩,
    ⟨.and, [13, 155]⟩,
    ⟨.and, [7, 130]⟩,
    ⟨.or, [156, 157]⟩,
    ⟨.and, [148, 158]⟩,
    ⟨.and, [0, 4]⟩,
    ⟨.and, [12, 160]⟩,
    ⟨.and, [8, 136]⟩,
    ⟨.or, [161, 162]⟩,
    ⟨.and, [149, 163]⟩,
    ⟨.or, [154, 159]⟩,
    ⟨.or, [164, 165]⟩,
    ⟨.and, [146, 166]⟩,
    ⟨.and, [2, 6]⟩,
    ⟨.and, [9, 168]⟩,
    ⟨.and, [12, 169]⟩,
    ⟨.and, [13, 170]⟩,
    ⟨.or, [76, 77]⟩,
    ⟨.or, [75, 77]⟩,
    ⟨.or, [75, 76]⟩,
    ⟨.and, [14, 90]⟩,
    ⟨.and, [5, 124]⟩,
    ⟨.or, [175, 176]⟩,
    ⟨.and, [172, 177]⟩,
    ⟨.and, [11, 155]⟩,
    ⟨.and, [7, 134]⟩,
    ⟨.or, [179, 180]⟩,
    ⟨.and, [173, 181]⟩,
    ⟨.and, [10, 160]⟩,
    ⟨.and, [8, 128]⟩,
    ⟨.or, [183, 184]⟩,
    ⟨.and, [174, 185]⟩,
    ⟨.or, [178, 182]⟩,
    ⟨.or, [186, 187]⟩,
    ⟨.and, [171, 188]⟩,
    ⟨.and, [3, 7]⟩,
    ⟨.and, [10, 190]⟩,
    ⟨.and, [12, 191]⟩,
    ⟨.and, [14, 192]⟩,
    ⟨.or, [71, 72]⟩,
    ⟨.or, [70, 72]⟩,
    ⟨.or, [70, 71]⟩,
    ⟨.and, [13, 90]⟩,
    ⟨.and, [5, 130]⟩,
    ⟨.or, [197, 198]⟩,
    ⟨.and, [194, 199]⟩,
    ⟨.and, [11, 150]⟩,
    ⟨.and, [6, 134]⟩,
    ⟨.or, [201, 202]⟩,
    ⟨.and, [195, 203]⟩,
    ⟨.and, [9, 160]⟩,
    ⟨.and, [8, 122]⟩,
    ⟨.or, [205, 206]⟩,
    ⟨.and, [196, 207]⟩,
    ⟨.or, [200, 204]⟩,
    ⟨.or, [208, 209]⟩,
    ⟨.and, [193, 210]⟩,
    ⟨.and, [4, 8]⟩,
    ⟨.and, [11, 212]⟩,
    ⟨.and, [13, 213]⟩,
    ⟨.and, [14, 214]⟩,
    ⟨.or, [66, 67]⟩,
    ⟨.or, [65, 67]⟩,
    ⟨.or, [65, 66]⟩,
    ⟨.and, [12, 90]⟩,
    ⟨.and, [5, 136]⟩,
    ⟨.or, [219, 220]⟩,
    ⟨.and, [216, 221]⟩,
    ⟨.and, [10, 150]⟩,
    ⟨.and, [6, 128]⟩,
    ⟨.or, [223, 224]⟩,
    ⟨.and, [217, 225]⟩,
    ⟨.and, [9, 155]⟩,
    ⟨.and, [7, 122]⟩,
    ⟨.or, [227, 228]⟩,
    ⟨.and, [218, 229]⟩,
    ⟨.or, [222, 226]⟩,
    ⟨.or, [230, 231]⟩,
    ⟨.and, [215, 232]⟩,
    ⟨.or, [19, 24]⟩,
    ⟨.or, [29, 234]⟩,
    ⟨.or, [34, 235]⟩,
    ⟨.or, [39, 236]⟩,
    ⟨.or, [44, 237]⟩,
    ⟨.or, [49, 238]⟩,
    ⟨.or, [54, 239]⟩,
    ⟨.or, [59, 240]⟩,
    ⟨.or, [64, 241]⟩,
    ⟨.or, [69, 242]⟩,
    ⟨.or, [74, 243]⟩,
    ⟨.or, [79, 244]⟩,
    ⟨.or, [84, 245]⟩,
    ⟨.or, [89, 246]⟩,
    ⟨.or, [117, 247]⟩,
    ⟨.or, [142, 248]⟩,
    ⟨.or, [167, 249]⟩,
    ⟨.or, [189, 250]⟩,
    ⟨.or, [211, 251]⟩,
    ⟨.or, [233, 252]⟩,
    ⟨.not, [253]⟩], 254⟩

theorem basis : FanInTwo witness :=
  fanInTwo_of_bool witness (by decide +kernel)

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem hEval :
    (witness.gates.foldl hcsStep rawInputs).getD witness.output 0 = evalBvTarget rawInputs := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem eval_eq : ∀ x : Fin 15 → Bool, witness.eval (List.ofFn x) = targetFun x := by
  intro x
  let r := hcsBitsNat x
  have hr : r < 32768 := hcsBitsNat_lt x
  have hbank : rawInputs.map (fun v => v.getLsbD r) = List.ofFn x := rawInputs_map x
  have hev : (witness.gates.foldl hcsStep rawInputs).getD witness.output 0 =
      bvTarget (fun j : Fin 15 => rawInputs.getD j.val 0) := by
    rw [← evalBvTarget_eq]
    exact hEval
  have hbits := hcsFoldBits rawInputs ⟨r, hr⟩ witness.gates basis
  have hget : ∀ j : Fin 15, (rawInputs.getD j.val 0).getLsbD r = x j := by
    intro j
    rw [hcsGetDBit, hbank]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, j.isLt, dite_true, Option.getD_some]
  have hgoal : (bvTarget (fun j : Fin 15 => rawInputs.getD j.val 0)).getLsbD r = targetFun x := by
    rw [bvTarget_bit _ ⟨r, hr⟩]
    congr 1
    funext j
    exact hget j
  change (witness.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)])
    (List.ofFn x)).getD witness.output false = targetFun x
  rw [← hbank, ← hbits, ← hcsGetDBit, hev, hgoal]

end PEqualNP.Outside.L_meta_17126

open PEqualNP.Outside.L_meta_17126 in
theorem PEqualNP.Outside.L_meta_17126 : (PEqualNP.MetaComplexity.HasCircuitSize 15 (fun x : Fin 15 → Bool => !((x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 7 && x 9 && x 13 && x 14) || (x 0 && x 2 && x 4 && x 6 && x 8 && x 13) || (x 2 && x 3 && x 4 && x 5 && x 6 && x 7 && x 9 && x 11 && x 12 && x 13) || (x 0 && x 3 && x 4 && x 5 && x 7 && x 9 && x 10 && x 12 && x 13 && x 14) || (x 1 && x 2 && x 4 && x 5 && x 6 && x 7 && x 9 && x 10 && x 11 && x 14) || (x 0 && x 1 && x 2 && x 6 && x 7 && x 9 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 3 && x 7 && x 8 && x 9 && x 10 && x 12 && x 13 && x 14) || (x 1 && x 3 && x 4 && x 5 && x 6 && x 7 && x 9 && x 10 && x 11 && x 13) || (x 0 && x 3 && x 4 && x 6 && x 7 && x 9 && x 10 && x 11 && x 12 && x 14) || (x 0 && x 1 && x 3 && x 5 && x 6 && x 9 && x 10 && x 11 && x 13 && x 14) || (x 0 && x 1 && x 4 && x 5 && x 7 && x 9 && x 10 && x 11 && x 12 && x 13) || (x 2 && x 3 && x 4 && x 5 && x 6 && x 8 && x 9 && x 10 && x 12 && x 13) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 6 && x 11 && x 12 && x 14) || (x 0 && x 1 && x 4 && x 6 && x 8 && x 10 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 2 && x 3 && x 7 && x 8 && x 9 && x 10 && x 11 && x 12 && x 14) || (x 1 && x 2 && x 3 && x 5 && x 7 && x 8 && x 9 && x 10 && x 11 && x 13) || (x 0 && x 1 && x 3 && x 6 && x 7 && x 10 && x 11 && x 12 && x 13 && x 14) || (x 1 && x 2 && x 4 && x 5 && x 7 && x 8 && x 9 && x 10 && x 11 && x 12) || (x 0 && x 1 && x 2 && x 5 && x 8 && x 9 && x 10 && x 11 && x 12 && x 14) || (x 0 && x 2 && x 4 && x 7 && x 8 && x 9 && x 10 && x 11 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 5 && x 6 && x 7 && x 8 && x 11 && x 12 && x 14) || (x 0 && x 1 && x 3 && x 5 && x 8 && x 9 && x 10 && x 11 && x 12 && x 13) || (x 1 && x 2 && x 4 && x 6 && x 7 && x 8 && x 9 && x 10 && x 12 && x 13) || (x 2 && x 3 && x 4 && x 5 && x 7 && x 8 && x 9 && x 10 && x 12 && x 14) || (x 0 && x 2 && x 3 && x 5 && x 6 && x 9 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 6 && x 7 && x 9 && x 11 && x 14) || (x 0 && x 1 && x 2 && x 5 && x 6 && x 7 && x 8 && x 10 && x 13 && x 14) || (x 0 && x 1 && x 3 && x 5 && x 7 && x 10) || (x 0 && x 3 && x 4 && x 6 && x 8 && x 9 && x 10 && x 11 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 6 && x 7 && x 10 && x 11 && x 13) || (x 9 && x 10 && x 11 && x 12 && x 13 && x 14) || (x 2 && x 3 && x 4 && x 5 && x 6 && x 7 && x 10 && x 11 && x 12 && x 14) || (x 0 && x 1 && x 2 && x 5 && x 6 && x 9) || (x 2 && x 3 && x 4 && x 5 && x 7 && x 8 && x 9 && x 11 && x 13 && x 14) || (x 1 && x 2 && x 3 && x 5 && x 7 && x 8 && x 10 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 8 && x 9 && x 12 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 7 && x 8 && x 9 && x 10 && x 13) || (x 0 && x 1 && x 4 && x 5 && x 6 && x 7 && x 8 && x 10 && x 12 && x 13) || (x 0 && x 2 && x 4 && x 6 && x 7 && x 9 && x 10 && x 11 && x 12 && x 13) || (x 1 && x 3 && x 4 && x 5 && x 6 && x 7 && x 10 && x 12 && x 13 && x 14) || (x 1 && x 2 && x 4 && x 5 && x 7 && x 8 && x 11 && x 12 && x 13 && x 14) || (x 1 && x 3 && x 4 && x 6 && x 7 && x 8 && x 9 && x 11 && x 13 && x 14) || (x 0 && x 2 && x 4 && x 5 && x 8 && x 10 && x 11 && x 12 && x 13 && x 14) || (x 1 && x 3 && x 4 && x 5 && x 6 && x 8 && x 9 && x 10 && x 11 && x 12) || (x 0 && x 3 && x 4 && x 7 && x 8 && x 14) || (x 1 && x 2 && x 3 && x 6 && x 7 && x 8 && x 10 && x 11 && x 12 && x 14) || (x 2 && x 3 && x 4 && x 5 && x 6 && x 8 && x 10 && x 11 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 7 && x 8 && x 9 && x 11 && x 12) || (x 0 && x 2 && x 3 && x 6 && x 7 && x 12) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 8 && x 10 && x 12 && x 13) || (x 1 && x 3 && x 4 && x 5 && x 6 && x 8 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 3 && x 5 && x 6 && x 7 && x 8 && x 11 && x 12 && x 13) || (x 1 && x 3 && x 4 && x 6 && x 7 && x 8 && x 9 && x 10 && x 12 && x 14) || (x 0 && x 3 && x 4 && x 5 && x 6 && x 7 && x 8 && x 9 && x 10 && x 13) || (x 0 && x 2 && x 4 && x 5 && x 6 && x 7 && x 8 && x 10 && x 11 && x 12) || (x 0 && x 2 && x 4 && x 5 && x 6 && x 7 && x 8 && x 9 && x 10 && x 14) || (x 0 && x 1 && x 2 && x 6 && x 8 && x 9 && x 10 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 4 && x 5 && x 6 && x 9 && x 10 && x 11 && x 12 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 7 && x 11 && x 12 && x 13) || (x 1 && x 2 && x 3 && x 5 && x 6 && x 8 && x 9 && x 10 && x 11 && x 14) || (x 0 && x 1 && x 4 && x 5 && x 8 && x 11) || (x 1 && x 2 && x 3 && x 9 && x 10 && x 12) || (x 0 && x 1 && x 4 && x 7 && x 8 && x 9 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 6 && x 8 && x 9 && x 10 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 6 && x 8 && x 10 && x 11 && x 12) || (x 0 && x 2 && x 3 && x 5 && x 6 && x 7 && x 8 && x 10 && x 11 && x 13) || (x 0 && x 1 && x 2 && x 5 && x 7 && x 9 && x 10 && x 11 && x 13 && x 14) || (x 5 && x 7 && x 8 && x 10 && x 11 && x 14) || (x 0 && x 1 && x 3 && x 5 && x 6 && x 7 && x 8 && x 9 && x 13 && x 14) || (x 2 && x 3 && x 4 && x 12 && x 13 && x 14) || (x 6 && x 7 && x 8 && x 12 && x 13 && x 14) || (x 1 && x 2 && x 4 && x 6 && x 7 && x 8 && x 10 && x 11 && x 13 && x 14) || (x 0 && x 2 && x 3 && x 5 && x 7 && x 10 && x 11 && x 12 && x 13 && x 14) || (x 5 && x 6 && x 8 && x 9 && x 11 && x 13) || (x 0 && x 2 && x 3 && x 5 && x 6 && x 7 && x 8 && x 9 && x 11 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 6 && x 10 && x 13 && x 14) || (x 1 && x 2 && x 3 && x 6 && x 7 && x 8 && x 9 && x 11 && x 12 && x 13) || (x 1 && x 3 && x 4 && x 10 && x 11 && x 14) || (x 0 && x 2 && x 3 && x 6 && x 8 && x 9 && x 10 && x 11 && x 12 && x 13) || (x 1 && x 2 && x 4 && x 9 && x 11 && x 13) || (x 5 && x 6 && x 7 && x 9 && x 10 && x 12) || (x 0 && x 3 && x 4 && x 5 && x 6 && x 7 && x 8 && x 9 && x 11 && x 12) || (x 1 && x 2 && x 3 && x 5 && x 6 && x 8 && x 9 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 4 && x 5 && x 6 && x 7 && x 8 && x 9 && x 12 && x 14) || (x 0 && x 3 && x 4 && x 5 && x 8 && x 9 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 2 && x 4 && x 5 && x 6 && x 9 && x 10 && x 12 && x 13 && x 14) || (x 1 && x 2 && x 4 && x 5 && x 6 && x 7 && x 9 && x 12 && x 13 && x 14))) 374) := by
  exact ⟨witness, basis, by decide +kernel, eval_eq⟩
