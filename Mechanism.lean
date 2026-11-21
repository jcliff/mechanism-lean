/-!
# Two classics of mechanism design, in core Lean 4 (no Mathlib)

1. The revelation principle (dominant-strategy version).
2. Truthful bidding is weakly dominant in a second-price (Vickrey) auction,
   for *any* tie-breaking rule.

Plus two sanity checks of the kind used to audit AI-generated proofs:
the Vickrey hypotheses are satisfiable (the theorem isn't vacuous), and the
analogous claim for a first-price auction is provably false.
-/

namespace MechDesign

/-! ## Profiles and unilateral deviations -/

/-- Replace agent `i`'s entry of a (dependently typed) profile `x` with `a`. -/
def upd {ι : Type} [DecidableEq ι] {α : ι → Type}
    (x : (j : ι) → α j) (i : ι) (a : α i) : (j : ι) → α j :=
  fun j => if h : j = i then h ▸ a else x j

theorem upd_self {ι : Type} [DecidableEq ι] {α : ι → Type}
    (x : (j : ι) → α j) (i : ι) : upd x i (x i) = x := by
  funext j
  by_cases h : j = i
  · subst h; simp [upd]
  · simp [upd, h]

/-- Applying a strategy profile commutes with a unilateral deviation. -/
theorem upd_comp {ι : Type} [DecidableEq ι] {Θ M : ι → Type}
    (s : (j : ι) → Θ j → M j) (θ : (j : ι) → Θ j) (i : ι) (t : Θ i) :
    (fun j => s j (upd θ i t j)) = upd (fun j => s j (θ j)) i (s i t) := by
  funext j
  by_cases h : j = i
  · subst h; simp [upd]
  · simp [upd, h]

/-! ## 1. The revelation principle -/

section Revelation

variable {ι : Type} [DecidableEq ι]
  {Θ : ι → Type}        -- private types
  {M : ι → Type}        -- message spaces of the indirect mechanism
  {O : Type}            -- outcomes
  {V : Type} [LE V]     -- utility scale (any order-like relation)

/-- `s` is a dominant-strategy equilibrium of mechanism `g` under utilities `u`:
whatever the others send, reporting `s i θᵢ` is at least as good for type `θᵢ`
as sending any other message. -/
def IsDominantEq (u : (i : ι) → Θ i → O → V)
    (g : ((i : ι) → M i) → O) (s : (i : ι) → Θ i → M i) : Prop :=
  ∀ (i : ι) (θi : Θ i) (m : (j : ι) → M j) (m' : M i),
    u i θi (g (upd m i m')) ≤ u i θi (g (upd m i (s i θi)))

/-- A direct mechanism `f` is dominant-strategy incentive compatible:
truth-telling beats any misreport `t`, whatever the others report. -/
def IsDSIC (u : (i : ι) → Θ i → O → V) (f : ((i : ι) → Θ i) → O) : Prop :=
  ∀ (i : ι) (θ : (j : ι) → Θ j) (t : Θ i),
    u i (θ i) (f (upd θ i t)) ≤ u i (θ i) (f θ)

/-- **Revelation principle.** If `s` is a dominant-strategy equilibrium of `g`,
the direct mechanism "ask for types, then play `s` on everyone's behalf" is
DSIC and produces the same outcome as `g` at every type profile. -/
theorem revelation_principle (u : (i : ι) → Θ i → O → V)
    (g : ((i : ι) → M i) → O) (s : (i : ι) → Θ i → M i)
    (hs : IsDominantEq u g s) :
    IsDSIC u (fun θ => g (fun j => s j (θ j))) ∧
    ∀ θ : (j : ι) → Θ j, (fun θ => g (fun j => s j (θ j))) θ = g (fun j => s j (θ j)) := by
  refine ⟨?_, fun _ => rfl⟩
  intro i θ t
  -- misreporting `t` = the agent deviating to message `s i t`
  have hdev := hs i (θ i) (fun j => s j (θ j)) (s i t)
  -- reporting truthfully = sending `s i (θ i)`, i.e. the profile is unchanged
  have htruth : upd (fun j => s j (θ j)) i (s i (θ i)) = (fun j => s j (θ j)) :=
    upd_self (fun j => s j (θ j)) i
  simp only [upd_comp, htruth] at hdev ⊢
  exact hdev

end Revelation

/-! ## 2. Second-price auctions -/

section Vickrey

variable {n : Nat}

/-- Change bidder `i`'s bid to `x`. -/
def setBid (b : Fin n → Nat) (i : Fin n) (x : Nat) : Fin n → Nat :=
  fun j => if j = i then x else b j

/-- Fold computing the highest bid among the bidders in `l` other than `i`
(0 if there are none). -/
def maxOthersAux (i : Fin n) (b : Fin n → Nat) : List (Fin n) → Nat
  | [] => 0
  | j :: l => if j = i then maxOthersAux i b l else max (b j) (maxOthersAux i b l)

/-- The price in a second-price auction: the highest *competing* bid. -/
def price (i : Fin n) (b : Fin n → Nat) : Nat :=
  maxOthersAux i b (List.finRange n)

theorem maxOthersAux_ge (i : Fin n) (b : Fin n → Nat) :
    ∀ (l : List (Fin n)) (j : Fin n), j ∈ l → j ≠ i → b j ≤ maxOthersAux i b l
  | [], _, h, _ => by simp at h
  | k :: l, j, h, hji => by
    have ih := maxOthersAux_ge i b l j
    simp only [List.mem_cons] at h
    by_cases hk : k = i
    · rcases h with h | h
      · exact absurd (h.trans hk) hji
      · simp [maxOthersAux, hk, ih h hji]
    · simp only [maxOthersAux, hk, if_false]
      rcases h with h | h
      · subst h; omega
      · have := ih h hji; omega

theorem maxOthersAux_le (i : Fin n) (b : Fin n → Nat) (c : Nat) :
    ∀ (l : List (Fin n)), (∀ j, j ∈ l → j ≠ i → b j ≤ c) → maxOthersAux i b l ≤ c
  | [], _ => by simp [maxOthersAux]
  | k :: l, h => by
    have ih := maxOthersAux_le i b c l (fun j hj hji => h j (by simp [hj]) hji)
    by_cases hk : k = i
    · simp [maxOthersAux, hk, ih]
    · have := h k (by simp) hk
      simp only [maxOthersAux, hk, if_false]
      omega

/-- Your own bid never affects your price. -/
theorem maxOthersAux_setBid (i : Fin n) (b : Fin n → Nat) (x : Nat) :
    ∀ l, maxOthersAux i (setBid b i x) l = maxOthersAux i b l
  | [] => rfl
  | k :: l => by
    have ih := maxOthersAux_setBid i b x l
    by_cases hk : k = i
    · simp [maxOthersAux, hk, ih]
    · simp [maxOthersAux, hk, ih, setBid]

theorem price_ge (i : Fin n) (b : Fin n → Nat) (j : Fin n) (hji : j ≠ i) :
    b j ≤ price i b :=
  maxOthersAux_ge i b _ j (List.mem_finRange j) hji

theorem price_le (i : Fin n) (b : Fin n → Nat) (c : Nat)
    (h : ∀ j, j ≠ i → b j ≤ c) : price i b ≤ c :=
  maxOthersAux_le i b c _ (fun j _ hji => h j hji)

theorem price_setBid (i : Fin n) (b : Fin n → Nat) (x : Nat) :
    price i (setBid b i x) = price i b :=
  maxOthersAux_setBid i b x _

/-- A winner-selection rule is *valid* if it always picks a highest bidder.
How ties are broken is left completely arbitrary. -/
def ValidWinner (win : (Fin n → Nat) → Fin n) : Prop :=
  ∀ (b : Fin n → Nat) (j : Fin n), b j ≤ b (win b)

/-- Quasilinear utility of bidder `i` with value `v` at bid profile `b`:
the winner pays the highest competing bid; losers pay nothing. -/
def utility (win : (Fin n → Nat) → Fin n) (i : Fin n) (v : Nat)
    (b : Fin n → Nat) : Int :=
  if win b = i then (v : Int) - (price i b : Int) else 0

/-- **Vickrey (1961).** In a second-price auction with any valid tie-breaking
rule, bidding your true value `v` is weakly dominant: for every profile of
others' bids and every alternative bid `x`, truthful bidding does at least as
well. -/
theorem vickrey_truthful (win : (Fin n → Nat) → Fin n) (hwin : ValidWinner win)
    (i : Fin n) (v : Nat) (b : Fin n → Nat) (x : Nat) :
    utility win i v (setBid b i x) ≤ utility win i v (setBid b i v) := by
  have hp1 := price_setBid i b x
  have hp2 := price_setBid i b v
  -- Truthful utility is ≥ 0 and ≥ v - price.
  have truth_nonneg_and_ge :
      0 ≤ utility win i v (setBid b i v) ∧
      (v : Int) - (price i b : Int) ≤ utility win i v (setBid b i v) := by
    unfold utility
    rw [hp2]
    by_cases hw : win (setBid b i v) = i
    · -- winning truthfully: v is a highest bid, so v ≥ price
      have hle : price i b ≤ v := by
        rw [← hp2]
        apply price_le
        intro j _
        have := hwin (setBid b i v) j
        rw [hw] at this
        simpa [setBid] using this
      simp only [hw, if_true]; omega
    · -- losing truthfully: the winner w ≠ i outbid v and w's bid ≤ price
      have hwv : v ≤ price i b := by
        have h1 := hwin (setBid b i v) i
        have h2 := price_ge i (setBid b i v) (win (setBid b i v)) hw
        simp only [setBid, hw, if_true, if_false] at h1 h2
        rw [← hp2]
        omega
      simp only [hw, if_false]; omega
  -- Any deviation yields either 0 or v - price.
  unfold utility at *
  rw [hp1]
  by_cases hx : win (setBid b i x) = i
  · simp only [hx, if_true]; exact truth_nonneg_and_ge.2
  · simp only [hx, if_false]; exact truth_nonneg_and_ge.1

/-! ### Sanity check 1: the hypothesis is satisfiable (no vacuous truth) -/

/-- Highest bidder, ties broken in favour of the earliest bidder. -/
def highestAux (b : Fin (n+1) → Nat) : List (Fin (n+1)) → Fin (n+1)
  | [] => 0
  | j :: l => let acc := highestAux b l; if b acc < b j then j else acc

def highest (b : Fin (n+1) → Nat) : Fin (n+1) := highestAux b (List.finRange (n+1))

theorem highestAux_ge (b : Fin (n+1) → Nat) :
    ∀ (l : List (Fin (n+1))) (j : Fin (n+1)), j ∈ l → b j ≤ b (highestAux b l)
  | [], _, h => by simp at h
  | k :: l, j, h => by
    have ih := highestAux_ge b l j
    simp only [List.mem_cons] at h
    simp only [highestAux]
    by_cases hlt : b (highestAux b l) < b k
    · simp only [hlt, if_true]
      rcases h with h | h
      · subst h; exact Nat.le_refl _
      · have := ih h; omega
    · simp only [hlt, if_false]
      rcases h with h | h
      · subst h; omega
      · exact ih h

theorem highest_valid : ValidWinner (highest (n := n)) := by
  intro b j
  exact highestAux_ge b _ j (List.mem_finRange j)

/-- So the theorem applies to an actual auction. -/
theorem vickrey_truthful_concrete (i : Fin (n+1)) (v : Nat) (b : Fin (n+1) → Nat) (x : Nat) :
    utility highest i v (setBid b i x) ≤ utility highest i v (setBid b i v) :=
  vickrey_truthful highest highest_valid i v b x

/-! ### Sanity check 2: the same claim is FALSE for a first-price auction -/

def utilityFirstPrice (win : (Fin n → Nat) → Fin n) (i : Fin n) (v : Nat)
    (b : Fin n → Nat) : Int :=
  if win b = i then (v : Int) - (b i : Int) else 0

/-- Two bidders; bidder 0 values the item at 10, bidder 1 bids 4.
Shading to 5 earns 5; bidding the true value earns 0. -/
theorem first_price_not_truthful :
    ¬ ∀ (i : Fin 2) (v : Nat) (b : Fin 2 → Nat) (x : Nat),
        utilityFirstPrice highest i v (setBid b i x) ≤
        utilityFirstPrice highest i v (setBid b i v) := by
  intro h
  have := h 0 10 (fun _ => 4) 5
  revert this
  decide

end Vickrey

end MechDesign
