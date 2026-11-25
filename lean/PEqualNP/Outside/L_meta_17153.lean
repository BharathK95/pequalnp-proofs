import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17153

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def hcsGateVal (bank : List (BitVec 1024)) (g : Gate) : BitVec 1024 :=
  let args := g.inputs.map fun i => bank.getD i 0
  match g.op with
  | .and => args.foldr (· &&& ·) (BitVec.allOnes 1024)
  | .or => args.foldr (· ||| ·) 0
  | .not => ~~~(args.headD 0)
  | _ => 0

def hcsStep (bank : List (BitVec 1024)) (g : Gate) : List (BitVec 1024) :=
  bank ++ [hcsGateVal bank g]

theorem hcsGetDBit (bank : List (BitVec 1024)) (i : Nat) (k : Nat) :
    (bank.getD k 0).getLsbD i = (bank.map fun w => w.getLsbD i).getD k false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases bank[k]? <;> simp

theorem hcsAndBit (xs : List (BitVec 1024)) (i : Fin 1024) :
    (xs.foldr (· &&& ·) (BitVec.allOnes 1024)).getLsbD i.val = (xs.map fun w => w.getLsbD i.val).all id := by
  induction xs with
  | nil => simp only [List.foldr_nil, BitVec.getLsbD_allOnes, i.isLt, decide_true, List.map_nil, List.all_nil]
  | cons a t ih => simp only [List.foldr_cons, BitVec.getLsbD_and, List.map_cons, List.all_cons, id_eq, ih]

theorem hcsOrBit (xs : List (BitVec 1024)) (i : Fin 1024) :
    (xs.foldr (· ||| ·) 0).getLsbD i.val = (xs.map fun w => w.getLsbD i.val).any id := by
  induction xs with
  | nil => simp
  | cons a t ih => simp only [List.foldr_cons, BitVec.getLsbD_or, List.map_cons, List.any_cons, id_eq, ih]

theorem hcsGateBit (bank : List (BitVec 1024)) (i : Fin 1024) (g : Gate)
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

theorem hcsFoldBits (bank : List (BitVec 1024)) (i : Fin 1024) (gs : List Gate)
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

def hcsCheckPow (p : Nat → Bool) : Nat → Nat → Bool
  | 0, s => p s
  | k + 1, s => hcsCheckPow p k s && hcsCheckPow p k (s + 2 ^ k)

theorem hcsCheckPow_spec {p : Nat → Bool} {k s i : Nat}
    (h : hcsCheckPow p k s = true) (lo : s ≤ i) (hi : i < s + 2 ^ k) : p i = true := by
  induction k generalizing s with
  | zero =>
    have e : i = s := by omega
    simpa [hcsCheckPow, e] using h
  | succ k ih =>
    simp only [hcsCheckPow, Bool.and_eq_true] at h
    by_cases hlt : i < s + 2 ^ k
    · exact ih h.1 lo hlt
    · exact ih h.2 (by omega) (by rw [Nat.pow_succ] at hi; omega)

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

def witness : Circuit :=
  ⟨[
    ⟨.not, [0]⟩,
    ⟨.not, [1]⟩,
    ⟨.and, [10, 11]⟩,
    ⟨.and, [0, 11]⟩,
    ⟨.and, [10, 1]⟩,
    ⟨.and, [0, 1]⟩,
    ⟨.not, [2]⟩,
    ⟨.not, [3]⟩,
    ⟨.not, [4]⟩,
    ⟨.and, [16, 17]⟩,
    ⟨.and, [2, 17]⟩,
    ⟨.and, [16, 3]⟩,
    ⟨.and, [2, 3]⟩,
    ⟨.and, [19, 18]⟩,
    ⟨.and, [20, 18]⟩,
    ⟨.and, [21, 18]⟩,
    ⟨.and, [22, 18]⟩,
    ⟨.and, [19, 4]⟩,
    ⟨.and, [20, 4]⟩,
    ⟨.and, [21, 4]⟩,
    ⟨.and, [22, 4]⟩,
    ⟨.and, [12, 23]⟩,
    ⟨.and, [13, 23]⟩,
    ⟨.and, [14, 23]⟩,
    ⟨.and, [15, 23]⟩,
    ⟨.and, [12, 24]⟩,
    ⟨.and, [13, 24]⟩,
    ⟨.and, [14, 24]⟩,
    ⟨.and, [15, 24]⟩,
    ⟨.and, [12, 25]⟩,
    ⟨.and, [13, 25]⟩,
    ⟨.and, [14, 25]⟩,
    ⟨.and, [15, 25]⟩,
    ⟨.and, [12, 26]⟩,
    ⟨.and, [13, 26]⟩,
    ⟨.and, [14, 26]⟩,
    ⟨.and, [15, 26]⟩,
    ⟨.and, [12, 27]⟩,
    ⟨.and, [13, 27]⟩,
    ⟨.and, [14, 27]⟩,
    ⟨.and, [15, 27]⟩,
    ⟨.and, [12, 28]⟩,
    ⟨.and, [13, 28]⟩,
    ⟨.and, [14, 28]⟩,
    ⟨.and, [15, 28]⟩,
    ⟨.and, [12, 29]⟩,
    ⟨.and, [13, 29]⟩,
    ⟨.and, [14, 29]⟩,
    ⟨.and, [15, 29]⟩,
    ⟨.and, [12, 30]⟩,
    ⟨.and, [13, 30]⟩,
    ⟨.and, [14, 30]⟩,
    ⟨.and, [15, 30]⟩,
    ⟨.or, [48, 62]⟩,
    ⟨.or, [39, 49]⟩,
    ⟨.or, [33, 59]⟩,
    ⟨.or, [38, 52]⟩,
    ⟨.or, [32, 57]⟩,
    ⟨.or, [37, 56]⟩,
    ⟨.or, [44, 47]⟩,
    ⟨.or, [50, 61]⟩,
    ⟨.or, [36, 63]⟩,
    ⟨.or, [34, 60]⟩,
    ⟨.or, [46, 53]⟩,
    ⟨.or, [41, 54]⟩,
    ⟨.or, [40, 58]⟩,
    ⟨.or, [35, 55]⟩,
    ⟨.or, [65, 70]⟩,
    ⟨.or, [51, 57]⟩,
    ⟨.or, [43, 45]⟩,
    ⟨.or, [64, 72]⟩,
    ⟨.or, [40, 73]⟩,
    ⟨.or, [45, 67]⟩,
    ⟨.or, [54, 55]⟩,
    ⟨.or, [42, 69]⟩,
    ⟨.or, [41, 61]⟩,
    ⟨.or, [42, 44]⟩,
    ⟨.or, [31, 68]⟩,
    ⟨.or, [66, 75]⟩,
    ⟨.or, [50, 59]⟩,
    ⟨.or, [43, 53]⟩,
    ⟨.or, [77, 90]⟩,
    ⟨.or, [39, 69]⟩,
    ⟨.or, [36, 52]⟩,
    ⟨.or, [66, 78]⟩,
    ⟨.or, [36, 48]⟩,
    ⟨.or, [46, 86]⟩,
    ⟨.or, [34, 38]⟩,
    ⟨.or, [65, 93]⟩,
    ⟨.or, [68, 74]⟩,
    ⟨.or, [62, 81]⟩,
    ⟨.or, [32, 91]⟩,
    ⟨.or, [35, 39]⟩,
    ⟨.or, [83, 96]⟩,
    ⟨.or, [49, 88]⟩,
    ⟨.or, [31, 60]⟩,
    ⟨.or, [50, 79]⟩,
    ⟨.or, [80, 89]⟩,
    ⟨.or, [49, 85]⟩,
    ⟨.or, [64, 82]⟩,
    ⟨.or, [72, 87]⟩,
    ⟨.or, [33, 54]⟩,
    ⟨.or, [46, 47]⟩,
    ⟨.or, [71, 73]⟩,
    ⟨.or, [71, 76]⟩,
    ⟨.or, [41, 107]⟩,
    ⟨.or, [43, 78]⟩,
    ⟨.or, [58, 92]⟩,
    ⟨.or, [63, 77]⟩,
    ⟨.or, [34, 53]⟩,
    ⟨.or, [58, 85]⟩,
    ⟨.or, [37, 49]⟩,
    ⟨.or, [38, 67]⟩,
    ⟨.or, [31, 74]⟩,
    ⟨.or, [51, 55]⟩,
    ⟨.or, [60, 98]⟩,
    ⟨.or, [76, 115]⟩,
    ⟨.or, [42, 94]⟩,
    ⟨.or, [63, 120]⟩,
    ⟨.or, [52, 56]⟩,
    ⟨.or, [84, 126]⟩,
    ⟨.or, [50, 99]⟩,
    ⟨.or, [123, 124]⟩,
    ⟨.or, [87, 108]⟩,
    ⟨.or, [52, 86]⟩,
    ⟨.or, [82, 95]⟩,
    ⟨.or, [99, 127]⟩,
    ⟨.or, [40, 101]⟩,
    ⟨.or, [132, 137]⟩,
    ⟨.or, [125, 131]⟩,
    ⟨.or, [45, 108]⟩,
    ⟨.or, [80, 128]⟩,
    ⟨.or, [59, 94]⟩,
    ⟨.or, [84, 89]⟩,
    ⟨.or, [70, 123]⟩,
    ⟨.or, [135, 136]⟩,
    ⟨.or, [76, 119]⟩,
    ⟨.or, [133, 134]⟩,
    ⟨.or, [146, 147]⟩,
    ⟨.or, [53, 89]⟩,
    ⟨.or, [145, 149]⟩,
    ⟨.or, [48, 81]⟩,
    ⟨.or, [121, 151]⟩,
    ⟨.or, [144, 152]⟩,
    ⟨.or, [44, 95]⟩,
    ⟨.or, [58, 59]⟩,
    ⟨.or, [33, 96]⟩,
    ⟨.or, [68, 69]⟩,
    ⟨.or, [110, 116]⟩,
    ⟨.or, [32, 129]⟩,
    ⟨.or, [55, 100]⟩,
    ⟨.or, [57, 60]⟩,
    ⟨.or, [57, 102]⟩,
    ⟨.or, [32, 49]⟩,
    ⟨.or, [139, 163]⟩,
    ⟨.or, [35, 154]⟩,
    ⟨.or, [71, 103]⟩,
    ⟨.or, [161, 166]⟩,
    ⟨.or, [65, 114]⟩,
    ⟨.or, [140, 142]⟩,
    ⟨.or, [160, 169]⟩,
    ⟨.or, [155, 165]⟩,
    ⟨.or, [39, 62]⟩,
    ⟨.or, [67, 171]⟩,
    ⟨.or, [121, 173]⟩,
    ⟨.or, [91, 104]⟩,
    ⟨.or, [67, 175]⟩,
    ⟨.or, [129, 143]⟩,
    ⟨.or, [162, 177]⟩,
    ⟨.or, [79, 84]⟩,
    ⟨.or, [158, 172]⟩,
    ⟨.or, [93, 180]⟩,
    ⟨.or, [50, 103]⟩,
    ⟨.or, [141, 159]⟩,
    ⟨.or, [156, 183]⟩,
    ⟨.or, [71, 102]⟩,
    ⟨.or, [97, 114]⟩,
    ⟨.or, [101, 186]⟩,
    ⟨.or, [128, 157]⟩,
    ⟨.or, [97, 188]⟩,
    ⟨.or, [37, 66]⟩,
    ⟨.or, [104, 110]⟩,
    ⟨.or, [168, 179]⟩,
    ⟨.or, [81, 192]⟩,
    ⟨.or, [75, 105]⟩,
    ⟨.or, [112, 191]⟩,
    ⟨.or, [80, 122]⟩,
    ⟨.or, [70, 136]⟩,
    ⟨.or, [88, 105]⟩,
    ⟨.or, [113, 122]⟩,
    ⟨.or, [80, 87]⟩,
    ⟨.or, [185, 198]⟩,
    ⟨.or, [112, 201]⟩,
    ⟨.or, [98, 117]⟩,
    ⟨.or, [119, 203]⟩,
    ⟨.or, [35, 65]⟩,
    ⟨.or, [195, 205]⟩,
    ⟨.or, [37, 116]⟩,
    ⟨.or, [126, 207]⟩,
    ⟨.or, [40, 208]⟩,
    ⟨.or, [37, 194]⟩,
    ⟨.or, [71, 197]⟩,
    ⟨.or, [200, 211]⟩,
    ⟨.or, [36, 182]⟩,
    ⟨.or, [34, 106]⟩,
    ⟨.or, [31, 47]⟩,
    ⟨.or, [70, 214]⟩,
    ⟨.or, [95, 216]⟩,
    ⟨.or, [84, 210]⟩,
    ⟨.or, [51, 117]⟩,
    ⟨.or, [83, 109]⟩,
    ⟨.or, [75, 214]⟩,
    ⟨.or, [62, 125]⟩,
    ⟨.or, [68, 79]⟩,
    ⟨.or, [196, 223]⟩,
    ⟨.or, [66, 113]⟩,
    ⟨.or, [43, 199]⟩,
    ⟨.or, [97, 109]⟩,
    ⟨.or, [111, 227]⟩,
    ⟨.or, [100, 228]⟩,
    ⟨.or, [64, 118]⟩,
    ⟨.or, [218, 230]⟩,
    ⟨.or, [64, 74]⟩,
    ⟨.or, [92, 225]⟩,
    ⟨.or, [63, 78]⟩,
    ⟨.or, [62, 83]⟩,
    ⟨.or, [219, 235]⟩,
    ⟨.or, [111, 221]⟩,
    ⟨.or, [76, 222]⟩,
    ⟨.or, [118, 220]⟩,
    ⟨.or, [215, 239]⟩,
    ⟨.or, [88, 238]⟩,
    ⟨.or, [232, 241]⟩,
    ⟨.or, [56, 226]⟩,
    ⟨.or, [64, 243]⟩,
    ⟨.or, [49, 234]⟩,
    ⟨.or, [237, 245]⟩,
    ⟨.or, [124, 233]⟩,
    ⟨.or, [106, 247]⟩,
    ⟨.or, [190, 213]⟩,
    ⟨.or, [82, 249]⟩,
    ⟨.not, [5]⟩,
    ⟨.and, [251, 184]⟩,
    ⟨.and, [5, 164]⟩,
    ⟨.or, [252, 253]⟩,
    ⟨.and, [251, 178]⟩,
    ⟨.and, [5, 138]⟩,
    ⟨.or, [255, 256]⟩,
    ⟨.and, [251, 148]⟩,
    ⟨.and, [5, 150]⟩,
    ⟨.or, [258, 259]⟩,
    ⟨.and, [251, 170]⟩,
    ⟨.and, [5, 189]⟩,
    ⟨.or, [261, 262]⟩,
    ⟨.and, [251, 153]⟩,
    ⟨.and, [5, 187]⟩,
    ⟨.or, [264, 265]⟩,
    ⟨.and, [251, 174]⟩,
    ⟨.and, [5, 181]⟩,
    ⟨.or, [267, 268]⟩,
    ⟨.and, [251, 202]⟩,
    ⟨.and, [5, 167]⟩,
    ⟨.or, [270, 271]⟩,
    ⟨.and, [251, 176]⟩,
    ⟨.and, [5, 193]⟩,
    ⟨.or, [273, 274]⟩,
    ⟨.and, [251, 206]⟩,
    ⟨.and, [5, 250]⟩,
    ⟨.or, [276, 277]⟩,
    ⟨.and, [251, 204]⟩,
    ⟨.and, [5, 244]⟩,
    ⟨.or, [279, 280]⟩,
    ⟨.and, [251, 224]⟩,
    ⟨.and, [5, 231]⟩,
    ⟨.or, [282, 283]⟩,
    ⟨.and, [251, 212]⟩,
    ⟨.and, [5, 248]⟩,
    ⟨.or, [285, 286]⟩,
    ⟨.and, [251, 209]⟩,
    ⟨.and, [5, 240]⟩,
    ⟨.or, [288, 289]⟩,
    ⟨.and, [251, 130]⟩,
    ⟨.and, [5, 217]⟩,
    ⟨.or, [291, 292]⟩,
    ⟨.and, [251, 246]⟩,
    ⟨.and, [5, 236]⟩,
    ⟨.or, [294, 295]⟩,
    ⟨.and, [251, 242]⟩,
    ⟨.and, [5, 229]⟩,
    ⟨.or, [297, 298]⟩,
    ⟨.not, [6]⟩,
    ⟨.not, [7]⟩,
    ⟨.not, [8]⟩,
    ⟨.not, [9]⟩,
    ⟨.and, [300, 301]⟩,
    ⟨.and, [6, 301]⟩,
    ⟨.and, [300, 7]⟩,
    ⟨.and, [6, 7]⟩,
    ⟨.and, [302, 303]⟩,
    ⟨.and, [8, 303]⟩,
    ⟨.and, [302, 9]⟩,
    ⟨.and, [8, 9]⟩,
    ⟨.and, [304, 308]⟩,
    ⟨.and, [305, 308]⟩,
    ⟨.and, [306, 308]⟩,
    ⟨.and, [307, 308]⟩,
    ⟨.and, [304, 309]⟩,
    ⟨.and, [305, 309]⟩,
    ⟨.and, [306, 309]⟩,
    ⟨.and, [307, 309]⟩,
    ⟨.and, [304, 310]⟩,
    ⟨.and, [305, 310]⟩,
    ⟨.and, [306, 310]⟩,
    ⟨.and, [307, 310]⟩,
    ⟨.and, [304, 311]⟩,
    ⟨.and, [305, 311]⟩,
    ⟨.and, [306, 311]⟩,
    ⟨.and, [307, 311]⟩,
    ⟨.and, [312, 254]⟩,
    ⟨.and, [313, 257]⟩,
    ⟨.and, [314, 260]⟩,
    ⟨.and, [315, 263]⟩,
    ⟨.and, [316, 266]⟩,
    ⟨.and, [317, 269]⟩,
    ⟨.and, [318, 272]⟩,
    ⟨.and, [319, 275]⟩,
    ⟨.and, [320, 278]⟩,
    ⟨.and, [321, 281]⟩,
    ⟨.and, [322, 284]⟩,
    ⟨.and, [323, 287]⟩,
    ⟨.and, [324, 290]⟩,
    ⟨.and, [325, 293]⟩,
    ⟨.and, [326, 296]⟩,
    ⟨.and, [327, 299]⟩,
    ⟨.or, [328, 329]⟩,
    ⟨.or, [344, 330]⟩,
    ⟨.or, [345, 331]⟩,
    ⟨.or, [346, 332]⟩,
    ⟨.or, [347, 333]⟩,
    ⟨.or, [348, 334]⟩,
    ⟨.or, [349, 335]⟩,
    ⟨.or, [350, 336]⟩,
    ⟨.or, [351, 337]⟩,
    ⟨.or, [352, 338]⟩,
    ⟨.or, [353, 339]⟩,
    ⟨.or, [354, 340]⟩,
    ⟨.or, [355, 341]⟩,
    ⟨.or, [356, 342]⟩,
    ⟨.or, [357, 343]⟩], 358⟩

theorem basis : FanInTwo witness :=
  fanInTwo_of_bool witness (by decide +kernel)

def words (xs : List ℕ) : BitVec 1024 :=
  BitVec.ofNat 1024 (xs.foldr (fun w rest => w + rest * 2 ^ 64) 0)

def inputTables : List (BitVec 1024) := [
  words [0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa],
  words [0xcccccccccccccccc, 0xcccccccccccccccc, 0xcccccccccccccccc, 0xcccccccccccccccc, 0xcccccccccccccccc, 0xcccccccccccccccc, 0xcccccccccccccccc, 0xcccccccccccccccc, 0xcccccccccccccccc, 0xcccccccccccccccc, 0xcccccccccccccccc, 0xcccccccccccccccc, 0xcccccccccccccccc, 0xcccccccccccccccc, 0xcccccccccccccccc, 0xcccccccccccccccc],
  words [0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0],
  words [0xff00ff00ff00ff00, 0xff00ff00ff00ff00, 0xff00ff00ff00ff00, 0xff00ff00ff00ff00, 0xff00ff00ff00ff00, 0xff00ff00ff00ff00, 0xff00ff00ff00ff00, 0xff00ff00ff00ff00, 0xff00ff00ff00ff00, 0xff00ff00ff00ff00, 0xff00ff00ff00ff00, 0xff00ff00ff00ff00, 0xff00ff00ff00ff00, 0xff00ff00ff00ff00, 0xff00ff00ff00ff00, 0xff00ff00ff00ff00],
  words [0xffff0000ffff0000, 0xffff0000ffff0000, 0xffff0000ffff0000, 0xffff0000ffff0000, 0xffff0000ffff0000, 0xffff0000ffff0000, 0xffff0000ffff0000, 0xffff0000ffff0000, 0xffff0000ffff0000, 0xffff0000ffff0000, 0xffff0000ffff0000, 0xffff0000ffff0000, 0xffff0000ffff0000, 0xffff0000ffff0000, 0xffff0000ffff0000, 0xffff0000ffff0000],
  words [0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000],
  words [0x0000000000000000, 0xffffffffffffffff, 0x0000000000000000, 0xffffffffffffffff, 0x0000000000000000, 0xffffffffffffffff, 0x0000000000000000, 0xffffffffffffffff, 0x0000000000000000, 0xffffffffffffffff, 0x0000000000000000, 0xffffffffffffffff, 0x0000000000000000, 0xffffffffffffffff, 0x0000000000000000, 0xffffffffffffffff],
  words [0x0000000000000000, 0x0000000000000000, 0xffffffffffffffff, 0xffffffffffffffff, 0x0000000000000000, 0x0000000000000000, 0xffffffffffffffff, 0xffffffffffffffff, 0x0000000000000000, 0x0000000000000000, 0xffffffffffffffff, 0xffffffffffffffff, 0x0000000000000000, 0x0000000000000000, 0xffffffffffffffff, 0xffffffffffffffff],
  words [0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff],
  words [0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff]]

def outputTable : BitVec 1024 := words [0x32ac0466ea26ad0e, 0x51d8160716292910, 0x16fa4ce243642c59, 0xca0324c8d574c680, 0xd14a10be40ce8641, 0xa63011691c062072, 0xa582a820a82383b1, 0x9143fa345c6c1286, 0x05a8e8e23a2582dd, 0x864691a21861212c, 0xf80f2b45260451ca, 0x817bf1a0e6be0de9, 0xd58f4107351c1758, 0x400a5028310d2d18, 0x899121008c9e520c, 0x84c4c38eb9a407b4]

set_option maxHeartbeats 10000000 in
theorem hRaw :
    hcsCheckPow (fun r => (inputTables.map fun v => v.getLsbD r) ==
      List.ofFn fun j : Fin 10 => r.testBit j.val) 10 0 = true := by
  decide +kernel

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem hGoal :
    hcsCheckPow (fun r => outputTable.getLsbD r ==
      PEqualNP.Represents.adjFun (k := 5) (l := 5)
        (fun u v : Fin (2 ^ 5) => Nat.testBit 0xf2e8bac10a6043d9457138034725c66e70255481935a6c64005908b76782a258f242212a808cc37840c7587731c008681fe2432ed77945531ae8b7a126a59084808bb1419a92806024a6a4951998ca080462a035454001fbd121d148e7fc1805c0db52e001730db248cebe22450196149d550a91d225c20b821a462b02611918 (32 * u.val + v.val))
        (fun j : Fin 10 => r.testBit j.val)) 10 0 = true := by
  decide +kernel

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem hEval :
    (witness.gates.foldl hcsStep inputTables).getD witness.output 0 = outputTable := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem eval_eq : ∀ x : Fin 10 → Bool, witness.eval (List.ofFn x) =
    PEqualNP.Represents.adjFun (k := 5) (l := 5)
      (fun u v : Fin (2 ^ 5) => Nat.testBit 0xf2e8bac10a6043d9457138034725c66e70255481935a6c64005908b76782a258f242212a808cc37840c7587731c008681fe2432ed77945531ae8b7a126a59084808bb1419a92806024a6a4951998ca080462a035454001fbd121d148e7fc1805c0db52e001730db248cebe22450196149d550a91d225c20b821a462b02611918 (32 * u.val + v.val)) x := by
  intro x
  let r := hcsBitsNat x
  have hr : r < 1024 := hcsBitsNat_lt x
  have hx : x = fun j : Fin 10 => r.testBit j.val := by
    funext j
    exact (hcsBitsNat_testBit x j).symm
  rw [hx]
  have hbank : inputTables.map (fun v => v.getLsbD r) = List.ofFn fun j : Fin 10 => r.testBit j.val :=
    beq_iff_eq.mp (hcsCheckPow_spec hRaw (Nat.zero_le r) (by omega))
  have hfg : outputTable.getLsbD r =
      PEqualNP.Represents.adjFun (k := 5) (l := 5)
        (fun u v : Fin (2 ^ 5) => Nat.testBit 0xf2e8bac10a6043d9457138034725c66e70255481935a6c64005908b76782a258f242212a808cc37840c7587731c008681fe2432ed77945531ae8b7a126a59084808bb1419a92806024a6a4951998ca080462a035454001fbd121d148e7fc1805c0db52e001730db248cebe22450196149d550a91d225c20b821a462b02611918 (32 * u.val + v.val))
        (fun j : Fin 10 => r.testBit j.val) :=
    beq_iff_eq.mp (hcsCheckPow_spec hGoal (Nat.zero_le r) (by omega))
  have hbits := hcsFoldBits inputTables ⟨r, hr⟩ witness.gates basis
  change (witness.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)])
    (List.ofFn fun j : Fin 10 => r.testBit j.val)).getD witness.output false = _
  rw [← hbank, ← hbits, ← hcsGetDBit, hEval, hfg]

end PEqualNP.Outside.L_meta_17153

open PEqualNP.Outside.L_meta_17153 in
theorem PEqualNP.Outside.L_meta_17153 : (PEqualNP.MetaComplexity.HasCircuitSize 10 (PEqualNP.Represents.adjFun (k := 5) (l := 5) (fun u v : Fin (2 ^ 5) => Nat.testBit 0xf2e8bac10a6043d9457138034725c66e70255481935a6c64005908b76782a258f242212a808cc37840c7587731c008681fe2432ed77945531ae8b7a126a59084808bb1419a92806024a6a4951998ca080462a035454001fbd121d148e7fc1805c0db52e001730db248cebe22450196149d550a91d225c20b821a462b02611918 (32 * u.val + v.val))) 365) := by
  exact ⟨witness, basis, by decide +kernel, eval_eq⟩
