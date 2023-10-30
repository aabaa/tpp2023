# TPPmark 2023

Author: Makoto Kanazawa, Faculty of Science and Engineering, Hosei University

Last updated: October 30, 2023

This is an Agda formalization of [TPPmark 2023](https://aabaa.github.io/tpp2023/).

Tested with Agda 2.6.4 and the Agda standard library version 1.7.3.

```agda
open import Algebra.Definitions using (Associative; Commutative; Involutive; LeftCancellative; RightCancellative)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin as F using (Fin; zero; suc; toℕ; fromℕ; fromℕ<)
open import Data.Fin.Properties as Fₚ
  using (toℕ-injective; fromℕ<-injective; toℕ<n; toℕ-fromℕ<; fromℕ<-cong; all?)
open import Data.Integer 
  using (ℤ; +_; -[1+_]; 0ℤ; 1ℤ; -1ℤ; -_; _⊖_; _+_; _-_; _*_; ∣_∣)
  renaming (suc to sucℤ)
open import Data.Integer.DivMod using (n%ℕd<d; a≡a%ℕn+[a/ℕn]*n)
  renaming (_divℕ_ to _/ℕ_; _modℕ_ to _%ℕ_)
open import Data.Integer.Properties as ℤₚ
  using (+-injective; neg-involutive; +-assoc; +-comm; +-identityˡ; +-identityʳ; 
         +-inverseˡ; +-inverseʳ; *-zeroˡ; suc-*; n⊖n≡0)
open import Data.List
  using (List; []; _∷_; _++_; length; map; foldr; applyUpTo; upTo)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
-- open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Properties as Lₚ 
  using (map-compose; map-cong; ∷-injectiveˡ; length-map; length-applyUpTo) 
  renaming (≡-dec to List-≡-dec)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.List.Relation.Binary.Subset.Propositional.Properties
  using (⊆-refl; ⊆-trans; xs⊆x∷xs; ∷⁺ʳ; ∈-∷⁺ʳ)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (All¬⇒¬Any)
open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
open import Data.Nat as ℕ using (ℕ; zero; suc; pred; _⊔_)
open import Data.Nat.DivMod using (_%_; _mod_)
open import Data.Nat.Properties as ℕₚ 
  using (_<?_; ≤-pred; ≤∧≮⇒≡; n≤0⇒n≡0; ≰⇒>; suc[pred[n]]≡n; m≤m⊔n; m≤n⊔m; 
         ⊔-idem; ≤-reflexive; ≤-trans; 1+n≰n)
-- This comment about m≤n⊔m in Data.Nat.Properties is wrong.
-- : ∀ m n → m ≤ n ⊔ m
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Product.Properties as Pₚ using () renaming (≡-dec to ×-≡-dec)
open import Data.Sum using (_⊎_; inj₁; inj₂; swap)
open import Data.Unit using (tt)
open import Function using (_∘_; id)
open import Relation.Binary as B using (DecidableEquality)
open import Relation.Binary.PropositionalEquality as Eq 
  using (_≡_; refl; _≢_; trans; sym; cong; cong₂; subst; _≗_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable 
  using (True; False; toWitness; toWitnessFalse)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Unary using (Decidable) renaming (_⊆_ to _⇒_)

open import Miscellaneous

module TPPmark where

```

## Positional games

Let us define positional games (with infinitely many positions).

```agda
module PositionalGame 
  (Position : Set) 
  (_≟_ : DecidableEquality Position)
  (newPos : (xs : List Position) → Σ Position λ y → ¬ y ∈ xs)
  (WinningSet : List Position → Set)
  (¬ws[] : ¬ WinningSet [])
  where

  open import Data.List.Membership.DecPropositional _≟_ using (_∈?_) 

```

A state of the game is represented by a pair of lists of positions. The first
list is the sequence of moves made by the player who is going to make the
next move. The second list is the sequence of moves made by the other player.

```agda
  IncludesWinningSet : List Position → Set
  IncludesWinningSet xs = Σ (List Position) λ ws → WinningSet ws × ws ⊆ xs

```

The first player can force a win if the second player has not already won and 
the first player can make a move that results in a state where the second 
(formerly first) player can force a win. The second player can force a win if 
the second player has already won or else no matter how the first player moves, 
it results in a state where the first (formerly second) player can force a win.

I choose not to use representations of players in the formalization. Information
about the turn (which player is going to make the next move) is buried inside 
the predicates `FirstCanForceWin` and `SecondCanForceWin`. This makes everything 
much simpler.

```agda
  FirstCanForceWin : List Position → List Position → Set
  data SecondCanForceWin : List Position → List Position → Set

  FirstCanForceWin xs ys = 
    ¬ IncludesWinningSet ys × 
    Σ Position λ x → ¬ x ∈ xs × ¬ x ∈ ys × SecondCanForceWin ys (x ∷ xs)

  data SecondCanForceWin where
    now :   ∀ {xs} ys → IncludesWinningSet ys → SecondCanForceWin xs ys
    later : {xs ys : List Position} → 
            ({x : Position} → ¬ x ∈ xs → ¬ x ∈ ys → 
            FirstCanForceWin ys (x ∷ xs)) → SecondCanForceWin xs ys

```

Only one player can force a win from any given state.

```agda
  onlyOnePlayerCanForceWin : 
    (xs ys : List Position) → FirstCanForceWin xs ys → SecondCanForceWin xs ys →
    ⊥
  onlyOnePlayerCanForceWin xs ys (¬iws[ys] , h₁) (now .ys iws[ys]) = 
    ¬iws[ys] iws[ys]
  onlyOnePlayerCanForceWin xs ys (_ , x , ¬x∈xs , ¬x∈ys , h₁) (later h₂) = 
    onlyOnePlayerCanForceWin ys (x ∷ xs) (h₂ {x = x} ¬x∈xs ¬x∈ys) h₁

```

### The first player can force a draw

We are going to prove that the second player has no winning strategy in any 
positional game.

Consider two states of the game. If the first component of the first state is
included in the first component of the second state, and in addition the second 
components of the two states are the same, then whenever the first state is a
winning state for the first player, so is the second state. Likewise, if the
second component of the first state is included in the second component of the 
second state, and the first components of the two states are identical, then
whenever the first state is a winning state for the second player, so is the 
second state. In other words, having secured additional positions is never a 
disadvantage for either player.

```agda
  monotonicityLemma₁ : (xs xs′ ys : List Position) →
    FirstCanForceWin xs ys → xs ⊆ xs′ → FirstCanForceWin xs′ ys

  monotonicityLemma₂ : (xs ys ys′ : List Position) →
    SecondCanForceWin xs ys → ys ⊆ ys′ → SecondCanForceWin xs ys′

  monotonicityLemma₁ xs xs′ ys (¬iws[ys] , x , ¬x∈xs , ¬x∈ys , h) xs⊆xs′ 
    with x ∈? xs′
  ... | no ¬x∈xs′ = ¬iws[ys] , x , ¬x∈xs′ , ¬x∈ys , 
                    monotonicityLemma₂ ys (x ∷ xs) (x ∷ xs′) h (∷⁺ʳ x xs⊆xs′)
  ... | yes x∈xs′ = ¬iws[ys] , y , ¬y∈xs′ , ¬y∈ys , 
                    monotonicityLemma₂ ys (x ∷ xs) (y ∷ xs′) h x∷xs⊆y∷xs′
    where
    y = proj₁ (newPos (xs′ ++ ys))
    ¬y∈xs′++ys : ¬ y ∈ xs′ ++ ys
    ¬y∈xs′++ys = proj₂ (newPos (xs′ ++ ys))
    ¬y∈xs′ : ¬ y ∈ xs′
    ¬y∈xs′ y∈xs′ = ¬y∈xs′++ys (∈-++⁺ˡ y∈xs′)
    ¬y∈ys : ¬ y ∈ ys
    ¬y∈ys y∈ys = ¬y∈xs′++ys (∈-++⁺ʳ xs′ y∈ys)
    x∷xs⊆xs′ : x ∷ xs ⊆ xs′
    x∷xs⊆xs′ = ∈-∷⁺ʳ x∈xs′ xs⊆xs′
    x∷xs⊆y∷xs′ : x ∷ xs ⊆ y ∷ xs′
    x∷xs⊆y∷xs′ = ⊆-trans x∷xs⊆xs′ (xs⊆x∷xs xs′ y)
  monotonicityLemma₂ xs ys ys′ (now .ys iws[ys]) ys⊆ys′ = 
    now ys′ (zs , ws[zs] , ⊆-trans zs⊆ys ys⊆ys′)
    where
    zs : List Position
    zs = proj₁ iws[ys]
    ws[zs] : WinningSet zs
    ws[zs] = proj₁ (proj₂ iws[ys])
    zs⊆ys : zs ⊆ ys
    zs⊆ys = proj₂ (proj₂ iws[ys])    
  monotonicityLemma₂ xs ys ys′ (later h) ys⊆ys′         = later h′
    where
    h′ : {x : Position} → ¬ x ∈ xs → ¬ x ∈ ys′ → FirstCanForceWin ys′ (x ∷ xs)
    h′ {x} ¬x∈xs ¬x∈ys′ = 
      monotonicityLemma₁ ys ys′ (x ∷ xs) (h ¬x∈xs ¬x∈ys) ys⊆ys′
      where
      ¬x∈ys : ¬ x ∈ ys
      ¬x∈ys x∈ys = ¬x∈ys′ (ys⊆ys′ x∈ys)

```

If the second player can force a win starting from a state `xs`, `ys`, then the
first player can force a win starting from a state `ys`, `xs` by mimicking the
second player's strategy.

```agda
  strategyStealing : (xs ys : List Position) → ¬ IncludesWinningSet xs →
    SecondCanForceWin xs ys → FirstCanForceWin ys xs
  strategyStealing xs ys ¬iws[xs] h = ¬iws[xs] , x , ¬x∈ys , ¬x∈xs , [1]
    where
    x = proj₁ (newPos (xs ++ ys))
    ¬x∈xs++ys : ¬ x ∈ xs ++ ys
    ¬x∈xs++ys = proj₂ (newPos (xs ++ ys))
    ¬x∈xs : ¬ x ∈ xs
    ¬x∈xs x∈xs = ¬x∈xs++ys (∈-++⁺ˡ x∈xs)
    ¬x∈ys : ¬ x ∈ ys
    ¬x∈ys x∈ys = ¬x∈xs++ys (∈-++⁺ʳ xs x∈ys)
    [1] : SecondCanForceWin xs (x ∷ ys)
    [1] = monotonicityLemma₂ xs ys (x ∷ ys) h (xs⊆x∷xs ys x)

```

This proves that the second player has no winning strategy starting from the 
empty board.

```agda
  secondHasNoWinningStrategy : ¬ SecondCanForceWin [] []
  secondHasNoWinningStrategy h = onlyOnePlayerCanForceWin [] [] [2] h
    where
    [1] : ¬ IncludesWinningSet []
    [1] ([] , ws[zs] , zs⊆[])         = ¬ws[] ws[zs]
    [1] (x ∷ zs , ws[x∷zs] , x∷zs⊆[]) = [1-3] [1-2]
      where
      [1-1] : x ∈ x ∷ zs
      [1-1] = here refl
      [1-2] : x ∈ []
      [1-2] = x∷zs⊆[] [1-1]
      [1-3] : ¬ x ∈ []
      [1-3] ()
    [2] : FirstCanForceWin [] []
    [2] = strategyStealing [] [] [1] h

```

### Pairing strategies

Now we are going to show that the existence of a pairing implies that the first 
player has no winning strategy. A function from the set of positions to the set 
of positions is a *pairing* if it is a permutation entirely consisting of 
2-cycles.

```agda
  record Pairing : Set where
    field
      func       : Position → Position
      noFix      : (x : Position) → func x ≢ x
      involutive : (x : Position) → func (func x) ≡ x

  open Pairing

```

A pairing `p` *blocks* a list of positions `xs` by a position `x` if both `x`
and `func p x` are in `xs`.

```agda
  BlocksBy : Pairing → Position → List Position → Set
  BlocksBy p x xs = x ∈ xs × func p x ∈ xs

  Blocks : Pairing → List Position → Set
  Blocks p xs = Σ Position λ x → BlocksBy p x xs

  Blocks′ : Pairing → List Position → Set
  Blocks′ p xs = Any (λ x → func p x ∈ xs) xs

  blocks′? : B.Decidable Blocks′
  blocks′? p xs = Any.any? (λ x → func p x ∈? xs) xs

  postulate
    blocks-equiv : (p : Pairing) (xs : List Position) → 
      (Blocks p xs ↔ Blocks′ p xs)
  -- blocks-equiv p xs = {!   !}

  blocks? : B.Decidable Blocks
  blocks? p xs with blocks′? p xs
  ... | no ¬blocks′ = no (λ h → ¬blocks′ (proj₁ (blocks-equiv p xs) h))
  ... | yes blocks′ = yes (proj₂ (blocks-equiv p xs) blocks′)

```

We can easily prove that a pairing `p` blocks a list of positions `xs` by 
position `x` if and only `p` blocks `xs` by `func p x`.

```agda
  blockingPair : (p : Pairing) (x : Position) (xs : List Position) →
    BlocksBy p x xs → BlocksBy p (func p x) xs
  blockingPair p x xs (fst , snd) rewrite involutive p x = snd , fst

```

A pairing is *good* if it blocks all winning sets.

```agda
  Good : Pairing → Set
  Good p = {xs : List Position} → WinningSet xs → Blocks p xs

```

The existence of a good pairing implies that the second player can force a draw,
i.e., the first player cannot force a win. We first prove that a certain 
invariant that is incompatible with the first player's win can be maintained 
throughout the game.

```agda
  module _ (p : Pairing) (good : Good p) where

    private
      f = func p

    f-injective : {x y : Position} → f x ≡ f y → x ≡ y
    f-injective {x} {y} f[x]≡f[y] = 
      trans (trans (sym (involutive p x)) (cong f f[x]≡f[y])) (involutive p y)

    blockingPos : {xs : List Position} (ws[xs] : WinningSet xs) → Position
    blockingPos ws[xs] = proj₁ (good ws[xs])

    blocksByBlockingPos : {xs : List Position} (ws[xs] : WinningSet xs) → 
      BlocksBy p (blockingPos ws[xs]) xs
    blocksByBlockingPos ws[xs] = proj₂ (good ws[xs])

    record Invariant (xs ys : List Position) : Set
    record Invariant xs ys where
      field
        disjoint : ¬ Σ Position λ x → x ∈ xs × x ∈ ys
        pair     : (x : Position) → (x ∈ xs → f x ∈ ys) × (f x ∈ ys → x ∈ xs)

    open Invariant

```

`Invariant xs ys` implies that neither `xs` nor `ys` can include a winning set.

```agda
    invariant⇒¬IWS : (xs ys : List Position) → Invariant xs ys → 
      ¬ IncludesWinningSet xs × ¬ IncludesWinningSet ys
    invariant⇒¬IWS xs ys h = [1] , [2]
      where
      [1] : ¬ IncludesWinningSet xs
      [1] (zs , ws[zs] , zs⊆xs) = disjoint h (f z , f[z]∈xs , f[z]∈ys)
        where
        z = blockingPos ws[zs]
        [1-1] : BlocksBy p z zs
        [1-1] = blocksByBlockingPos ws[zs]
        z∈zs : z ∈ zs
        z∈zs = proj₁ [1-1]
        f[z]∈zs : f z ∈ zs
        f[z]∈zs = proj₂ [1-1]
        z∈xs : z ∈ xs
        z∈xs = zs⊆xs z∈zs
        f[z]∈xs : f z ∈ xs
        f[z]∈xs = zs⊆xs f[z]∈zs
        f[z]∈ys : f z ∈ ys
        f[z]∈ys = proj₁ (pair h z) z∈xs
      [2] : ¬ IncludesWinningSet ys
      [2] (zs , ws[zs] , zs⊆ys) = disjoint h (z , z∈xs , z∈ys)
        where
        z = blockingPos ws[zs]
        [2-1] : BlocksBy p z zs
        [2-1] = blocksByBlockingPos ws[zs]
        z∈zs = proj₁ [2-1]
        f[z]∈zs : f z ∈ zs
        f[z]∈zs = proj₂ [2-1]
        z∈ys : z ∈ ys
        z∈ys = zs⊆ys z∈zs
        f[z]∈ys : f z ∈ ys
        f[z]∈ys = zs⊆ys f[z]∈zs
        z∈xs : z ∈ xs
        z∈xs = proj₂ (pair h z) f[z]∈ys

```

The invariant holds of the initial state.

```agda
    invariantInitial : Invariant [] []
    invariantInitial = record { disjoint = [1] ; pair = [2] }
      where
      [1] : ¬ Σ Position λ x → x ∈ [] × x ∈ []
      [1] ()
      [2] : (x : Position) → (x ∈ [] → f x ∈ []) × (f x ∈ [] → x ∈ [])
      [2] x = (λ ()) , λ ()

```

The invariant can be maintained throughout the game, which is inconsistent with
the existence of a winning strategy for the first player.

```agda
    invariant⇒¬FirstCanForceWin : (xs ys : List Position) → Invariant xs ys → 
      ¬ FirstCanForceWin xs ys

```

Suppose `Invariant xs ys` and `FirstCanForceWin xs ys`. Then the first player 
can make a move `x` that results in a state where the now second (i.e., formerly 
first) player can force a win.

Case 1. The second (formerly first) player has already won, i.e., `x ∷ xs` now 
includes a winning set `zs`. Let `z₁`, `z₂ = f z₁` be the blocking pair for 
`zs`. Then both `z₁` and `z₂` are in `x ∷ xs`.

```agda
    invariant⇒¬FirstCanForceWin xs ys h₁ 
      (¬iws[ys] , x , ¬x∈xs , ¬x∈ys , now .(x ∷ xs) iws[x∷xs]) = contra
      where
      ¬iws[xs] : ¬ IncludesWinningSet xs
      ¬iws[xs] = proj₁ (invariant⇒¬IWS xs ys h₁)
      zs = proj₁ iws[x∷xs]
      ws[zs] : WinningSet zs
      ws[zs] = proj₁ (proj₂ iws[x∷xs])
      zs⊆x∷xs : zs ⊆ x ∷ xs
      zs⊆x∷xs = proj₂ (proj₂ iws[x∷xs])
      z₁ = blockingPos ws[zs]
      z₁∈zs : z₁ ∈ zs
      z₁∈zs = proj₁ (blocksByBlockingPos ws[zs])
      z₁∈x∷xs : z₁ ∈ x ∷ xs
      z₁∈x∷xs = zs⊆x∷xs z₁∈zs
      z₂ = f z₁
      z₂∈zs : z₂ ∈ zs
      z₂∈zs = proj₂ (blocksByBlockingPos ws[zs])
      z₂∈x∷xs : z₂ ∈ x ∷ xs
      z₂∈x∷xs = zs⊆x∷xs z₂∈zs

```

There are four cases to consider, depending on whether `z₁ ≡ x` or `z₁ ∈ xs` and
on whether `z₂ ≡ x` or `z₂ ∈ xs`. All cases will result in a contradiction.

```agda
      [1] : z₁ ∈ xs → z₂ ∈ ys
      [1] = proj₁ (pair h₁ z₁)
      [2] : z₂ ∈ xs → z₁ ∈ ys
      [2] = subst (λ z → z₂ ∈ xs → z ∈ ys) (involutive p z₁) (proj₁ (pair h₁ z₂))
      contra : ⊥
      contra with z₁∈x∷xs | z₂∈x∷xs
      ... | here z₁≡x | here z₂≡x     = noFix p z₁ z₂≡z₁
        where
        z₂≡z₁ : z₂ ≡ z₁
        z₂≡z₁ rewrite z₁≡x | z₂≡x = refl
      ... | here z₁≡x | there z₂∈xs   = ¬z₁∈ys z₁∈ys
        where
        z₁∈ys : z₁ ∈ ys
        z₁∈ys = [2] z₂∈xs
        ¬z₁∈ys : ¬ z₁ ∈ ys
        ¬z₁∈ys rewrite z₁≡x = ¬x∈ys
      ... | there z₁∈xs | here z₂≡x   = ¬z₂∈ys z₂∈ys
        where
        z₂∈ys : z₂ ∈ ys
        z₂∈ys = [1] z₁∈xs
        ¬z₂∈ys : ¬ z₂ ∈ ys
        ¬z₂∈ys rewrite z₂≡x = ¬x∈ys
      ... | there z₁∈xs | there z₂∈xs = disjoint h₁ (z₂ , z₂∈xs , z₂∈ys)
        where
        z₂∈ys : z₂ ∈ ys
        z₂∈ys = [1] z₁∈xs

```

Case 2. The first (formerly second) player responds with an arbitrary move. 
Suppose the move is `f x`. It must result in a state where the original first 
player has a winning strategy. It suffices to show that the invariant still 
holds in that state.

```agda
    invariant⇒¬FirstCanForceWin xs ys h₁ 
      (¬iws[ys] , x , ¬x∈xs , ¬x∈ys , later h₂) = 
      invariant⇒¬FirstCanForceWin (x ∷ xs) (f x ∷ ys) [5]
      (h₂ ¬f[x]∈ys ¬f[x]∈x∷xs)  -- Writing [*] here makes termination checking fail.
      where
      [1] : f x ∈ ys → x ∈ xs
      [1] = proj₂ (pair h₁ x)
      [2] : f x ∈ xs → x ∈ ys
      [2] = subst (λ z → f x ∈ xs → z ∈ ys) (involutive p x) 
            (proj₁ (pair h₁ (f x)))
      ¬f[x]∈ys : ¬ f x ∈ ys
      ¬f[x]∈ys fx∈ys = ¬x∈xs ([1] fx∈ys)
      ¬f[x]∈xs : ¬ f x ∈ xs
      ¬f[x]∈xs fx∈xs = ¬x∈ys ([2] fx∈xs)
      ¬f[x]∈x∷xs : ¬ f x ∈ x ∷ xs
      ¬f[x]∈x∷xs (here f[x]≡x)   = noFix p x f[x]≡x
      ¬f[x]∈x∷xs (there f[x]∈xs) = ¬f[x]∈xs f[x]∈xs
      [3] : ¬ Σ Position λ z → z ∈ x ∷ xs × z ∈ f x ∷ ys
      [3] (z , here refl , here z≡f[x]) = noFix p x (sym z≡f[x])
      [3] (z , here refl , there z∈ys) = ¬x∈ys z∈ys
      [3] (z , there f[x]∈xs , here refl) = ¬f[x]∈xs f[x]∈xs
      [3] (z , there z∈xs , there z∈ys) = disjoint h₁ (z , z∈xs , z∈ys)
      [4] : (z : Position) → 
            (z ∈ x ∷ xs → f z ∈ f x ∷ ys) × (f z ∈ f x ∷ ys → z ∈ x ∷ xs)
      [4] z = [4-3] , [4-4]
        where
        [4-1] : z ∈ xs → f z ∈ ys
        [4-1] = proj₁ (pair h₁ z)
        [4-2] : f z ∈ ys → z ∈ xs
        [4-2] = proj₂ (pair h₁ z)
        [4-3] : z ∈ x ∷ xs → f z ∈ f x ∷ ys
        [4-3] (here refl) = here refl
        [4-3] (there z∈xs) = there ([4-1] z∈xs)
        [4-4] : f z ∈ f x ∷ ys → z ∈ x ∷ xs
        [4-4] (here f[z]≡f[x])     = here (f-injective f[z]≡f[x])
        [4-4] (there f[z]∈ys) = there ([4-2] f[z]∈ys)
      [5] : Invariant (x ∷ xs) (f x ∷ ys)
      [5] = record { disjoint = [3] ; pair = [4] }
      -- [*] : FirstCanForceWin (x ∷ xs) (f x ∷ ys)
      -- [*] = h₂ ¬f[x]∈ys ¬f[x]∈x∷xs

```

We can now conlude that the first player has no winning strategy. This
conclusion was derived under the assumption of the existence of a good pairing.

```agda
    FirstHasNoWinningStrategy : ¬ FirstCanForceWin [] []
    FirstHasNoWinningStrategy = 
      invariant⇒¬FirstCanForceWin [] [] invariantInitial

```

## N-in-a-row

We define the N-in-a-row game.

```agda
Position : Set
Position = ℤ × ℤ

maxAbs : List Position → ℕ
maxAbs = foldr (λ { (k , l) m → ∣ k ∣ ⊔ ∣ l ∣ ⊔ m }) 0

maxAbs-head : (k l : ℤ) (xs : List Position) → 
              ∣ k ∣ ⊔ ∣ l ∣ ℕ.≤ maxAbs ((k , l) ∷ xs)
maxAbs-head k l xs = m≤m⊔n (∣ k ∣ ⊔ ∣ l ∣) (maxAbs xs)  

maxAbs-tail : (m n : ℤ) (xs : List Position) → maxAbs xs ℕ.≤ maxAbs ((m , n) ∷ xs)
maxAbs-tail m n xs = m≤n⊔m (∣ m ∣ ⊔ ∣ n ∣) (maxAbs xs)

maxAbs-≤ : (xs : List Position) → 
           All (λ { (k , l) → ∣ k ∣ ⊔ ∣ l ∣ ℕ.≤ maxAbs xs }) xs
maxAbs-≤ []             = []
maxAbs-≤ ((m , n) ∷ xs) = maxAbs-head m n xs ∷ [1] 
  where
  P : Position → Set
  P = λ{ (k , l) → ∣ k ∣ ⊔ ∣ l ∣ ℕ.≤ maxAbs xs }
  Q : Position → Position → Set
  Q (x , y) = λ{ (k , l) → ∣ k ∣ ⊔ ∣ l ∣ ℕ.≤ maxAbs ((x , y) ∷ xs) }
  [1] : All (λ { (k , l) → ∣ k ∣ ⊔ ∣ l ∣ ℕ.≤ maxAbs ((m , n) ∷ xs) }) xs
  [1] = all-⇒ {A = Position} {P = P} {Q = Q (m , n)} 
        (λ h → ℕₚ.≤-trans h (maxAbs-tail m n xs)) (maxAbs-≤ xs)

newPos : (xs : List Position) → Σ Position λ y → ¬ y ∈ xs
newPos xs = ( + suc (maxAbs xs) , + suc (maxAbs xs) ) , [1]
  where
  [1] : ¬ (+ suc (maxAbs xs) , + suc (maxAbs xs)) ∈ xs
  [1] h = 1+n≰n [1-1]
    where
    [1-1] : suc (maxAbs xs) ℕ.≤ maxAbs xs
    [1-1] = ≤-trans (≤-reflexive (sym (⊔-idem (suc (maxAbs xs))))) 
      (all-∈ (maxAbs-≤ xs) h)

directions : List (ℤ × ℤ)
directions = (1ℤ , 0ℤ) ∷ (0ℤ , 1ℤ) ∷ (1ℤ , 1ℤ) ∷ (-1ℤ , 1ℤ) ∷ []

[_] : ℕ → List ℕ
[ n ] = upTo n

length-[n] : (n : ℕ) → length [ n ] ≡ n
length-[n] = length-applyUpTo id

module _ (n : ℕ) {n≢0 : False (n ℕₚ.≟ 0)} where

  ¬n≡0 : ¬ n ≡ 0
  ¬n≡0 = toWitnessFalse n≢0

  1≤n : 1 ℕ.≤ n
  1≤n = ≰⇒> (λ x → ¬n≡0 (n≤0⇒n≡0 x))

  suc-pred : suc (pred n) ≡ n
  suc-pred = suc[pred[n]]≡n ¬n≡0

  WinningSet : List Position → Set
  WinningSet xs = 
    Σ Position λ z → Any (λ d → xs ≡ applyUpTo (λ k → (k · d) +₂ z) n) directions

```

It is clear that `WinningSet` is decidable.

```agda
  winningSet-cons : ∀ x xs → WinningSet (x ∷ xs) → 
    Any (λ d → x ∷ xs ≡ applyUpTo (λ k → (k · d) +₂ x) n) directions
  winningSet-cons x xs (z , h) = 
    subst (λ w → Any (λ d → x ∷ xs ≡ applyUpTo (λ k → (k · d) +₂ w) n) directions)
    (sym ([1] directions h)) h
    where
    [1] : ∀ ys → 
      Any (λ d → x ∷ xs ≡ applyUpTo (λ k → (k · d) +₂ z) n) ys → 
      x ≡ z
    [1] (y ∷ ys) (here px) rewrite sym suc-pred = 
      trans (∷-injectiveˡ px) 
      (cong₂ _,_ (+-identityˡ (proj₁ z)) (+-identityˡ (proj₂ z)))
    [1] (y ∷ ys) (there h₁) = [1] ys h₁

  ¬WinningSet[] : ¬ WinningSet []
  ¬WinningSet[] (z , h) rewrite sym suc-pred = ∀¬-¬any [1] directions h
    where
    P = λ d → [] ≡ (0 · d) +₂ z ∷ applyUpTo (λ k → (suc k · d) +₂ z) (pred n)
    [1] : ∀ d → ¬ P d
    [1] d ()

  winningSet-equiv : 
    ∀ x xs → (WinningSet (x ∷ xs) ↔ 
    Any (λ d → x ∷ xs ≡ applyUpTo (λ k → (k · d) +₂ x) n) directions)
  winningSet-equiv x xs = winningSet-cons x xs , λ h → (x , h)

  winningSet? : Decidable WinningSet
  winningSet? [] = no ¬WinningSet[]
  winningSet? (x ∷ xs) 
    with Any.any? (λ d → List-≡-dec _ℤ×ℤ-≟_ (x ∷ xs) 
        (applyUpTo (λ k → (k · d) +₂ x) n)) directions
  ... | no ¬p = no (λ v → ¬p (proj₁ (winningSet-equiv x xs) v))
  ... | yes p = yes (proj₂ (winningSet-equiv x xs) p)

```

## Doubly periodic predicates and functions

A predicate `P : ℤ × ℤ → Set` or a function `g : {A : Set} → ℤ × ℤ → A` is 
*doubly `d`-periodic* if it is periodic with period `d` with respect to both 
coordinates. We state some important properties of doubly periodic predicates
and funcitons.

```agda
module _ (d : ℕ) {d≢0 : False (d ℕ.≟ 0)} where

  Periodic₂ : (ℤ × ℤ → Set) → Set
  Periodic₂ P = (k l : ℤ) → P (k , l) ↔ P (+ (k %ℕ d) {d≢0} , + (l %ℕ d) {d≢0})

  UnivFin : (ℤ × ℤ → Set) → Set
  UnivFin P = (i j : Fin d) → P (+ (toℕ i) , + (toℕ j))

  univFin? : {P : ℤ × ℤ → Set} → Decidable P → Dec (UnivFin P)
  univFin? P? = all? (λ i → all? λ j → P? (+ toℕ i , + toℕ j))

  periodic₂-univ : {P : ℤ × ℤ → Set} → Periodic₂ P → 
    UnivFin P → (m n : ℤ) → P (m , n)
  periodic₂-univ {P} h h₁ m n = proj₂ (h m n) [1]
    where
    [1] : P (+ (m %ℕ d) {d≢0} , + (n %ℕ d) {d≢0})
    [1] rewrite sym (toℕ-fromℕ< (n%ℕd<d m d {d≢0})) | 
                sym (toℕ-fromℕ< (n%ℕd<d n d {d≢0}))
      = h₁ (fromℕ< (n%ℕd<d m d {d≢0})) (fromℕ< (n%ℕd<d n d {d≢0}))

  PeriodicF₂ : {A : Set} → (ℤ × ℤ → A) → Set
  PeriodicF₂ g = (k l : ℤ) → 
    g (k , l) ≡ g (+ (k %ℕ d) {d≢0} , + (l %ℕ d) {d≢0})

```

### Hales-Jewett pairing

We define the *Hales-Jewett pairing*. This is one of several pairings for the 
N-in-a-row game that are good for N ≥ 9.

```agda
pattern 0F = F.zero
pattern 1F = F.suc F.zero
pattern 2F = F.suc (F.suc F.zero)
pattern 3F = F.suc (F.suc (F.suc F.zero))
pattern 4F = F.suc (F.suc (F.suc (F.suc F.zero)))
pattern 5F = F.suc (F.suc (F.suc (F.suc (F.suc F.zero))))
pattern 6F = F.suc (F.suc (F.suc (F.suc (F.suc (F.suc F.zero)))))
pattern 7F = F.suc (F.suc (F.suc (F.suc (F.suc (F.suc (F.suc F.zero))))))

table : Fin 8 → Fin 8 → ℤ × ℤ
table 0F 0F = (0ℤ , 1ℤ)
table 0F 1F = -₂ (0ℤ , 1ℤ)
table 0F 2F = (1ℤ , 1ℤ)
table 0F 3F = -₂ (-1ℤ , 1ℤ)
table 0F 4F = -₂ (1ℤ , 0ℤ)
table 0F 5F = -₂ (1ℤ , 0ℤ)
table 0F 6F = (1ℤ , 1ℤ)
table 0F 7F = -₂ (-1ℤ , 1ℤ)
table 1F 0F = (1ℤ , 0ℤ)
table 1F 1F = (1ℤ , 0ℤ)
table 1F 2F = (-1ℤ , 1ℤ)
table 1F 3F = -₂ (1ℤ , 1ℤ)
table 1F 4F = (0ℤ , 1ℤ)
table 1F 5F = -₂ (0ℤ , 1ℤ)
table 1F 6F = (-1ℤ , 1ℤ)
table 1F 7F = -₂ (1ℤ , 1ℤ)
table 2F 0F = -₂ (1ℤ , 0ℤ)
table 2F 1F = -₂ (1ℤ , 0ℤ)
table 2F 2F = -₂ (-1ℤ , 1ℤ)
table 2F 3F = (1ℤ , 1ℤ)
table 2F 4F = (0ℤ , 1ℤ)
table 2F 5F = -₂ (0ℤ , 1ℤ)
table 2F 6F = -₂ (-1ℤ , 1ℤ)
table 2F 7F = (1ℤ , 1ℤ)
table 3F 0F = -₂ (1ℤ , 1ℤ)
table 3F 1F = (-1ℤ , 1ℤ)
table 3F 2F = (0ℤ , 1ℤ)
table 3F 3F = -₂ (0ℤ , 1ℤ)
table 3F 4F = -₂ (1ℤ , 1ℤ)
table 3F 5F = (-1ℤ , 1ℤ)
table 3F 6F = (1ℤ , 0ℤ)
table 3F 7F = (1ℤ , 0ℤ)
table 4F 0F = (1ℤ , 1ℤ)
table 4F 1F = -₂ (-1ℤ , 1ℤ)
table 4F 2F = (0ℤ , 1ℤ)
table 4F 3F = -₂ (0ℤ , 1ℤ)
table 4F 4F = (1ℤ , 1ℤ)
table 4F 5F = -₂ (-1ℤ , 1ℤ)
table 4F 6F = -₂ (1ℤ , 0ℤ)
table 4F 7F = -₂ (1ℤ , 0ℤ)
table 5F 0F = (-1ℤ , 1ℤ)
table 5F 1F = -₂ (1ℤ , 1ℤ)
table 5F 2F = (1ℤ , 0ℤ)
table 5F 3F = (1ℤ , 0ℤ)
table 5F 4F = (-1ℤ , 1ℤ)
table 5F 5F = -₂ (1ℤ , 1ℤ)
table 5F 6F = (0ℤ , 1ℤ)
table 5F 7F = -₂ (0ℤ , 1ℤ)
table 6F 0F = -₂ (-1ℤ , 1ℤ)
table 6F 1F = (1ℤ , 1ℤ)
table 6F 2F = -₂ (1ℤ , 0ℤ)
table 6F 3F = -₂ (1ℤ , 0ℤ)
table 6F 4F = -₂ (-1ℤ , 1ℤ)
table 6F 5F = (1ℤ , 1ℤ)
table 6F 6F = (0ℤ , 1ℤ)
table 6F 7F = -₂ (0ℤ , 1ℤ)
table 7F 0F = (0ℤ , 1ℤ)
table 7F 1F = -₂ (0ℤ , 1ℤ)
table 7F 2F = -₂ (1ℤ , 1ℤ)
table 7F 3F = (-1ℤ , 1ℤ)
table 7F 4F = (1ℤ , 0ℤ)
table 7F 5F = (1ℤ , 0ℤ)
table 7F 6F = -₂ (1ℤ , 1ℤ)
table 7F 7F = (-1ℤ , 1ℤ)

TableNonZero : Set
TableNonZero = (i j : Fin 8) → table i j ≢ (0ℤ , 0ℤ)

tableNonZero? : Dec (TableNonZero)
tableNonZero? = 
  all? (λ i → all? λ j → ¬? (_ℤ×ℤ-≟_ (table i j) ((0ℤ , 0ℤ))))

tableNonZero : TableNonZero
tableNonZero = toWitness {Q = tableNonZero?} tt

tableℤ×ℤ : (ℤ × ℤ) → (ℤ × ℤ)
tableℤ×ℤ (k , l) = table (fromℕ< (n%ℕd<d k 8)) (fromℕ< (n%ℕd<d l 8))

tableℤ×ℤ-periodic : PeriodicF₂ 8 tableℤ×ℤ
tableℤ×ℤ-periodic k l = sym (cong₂ table [3] [4])
  where
  [1] : + (k %ℕ 8) %ℕ 8 ≡ k %ℕ 8
  [1] = [[m]%ℕn]%ℕn≡[m]%ℕn k 8
  [2] : + (l %ℕ 8) %ℕ 8 ≡ l %ℕ 8
  [2] = [[m]%ℕn]%ℕn≡[m]%ℕn l 8
  [3] : fromℕ< (n%ℕd<d (+ (k %ℕ 8)) 8) ≡ fromℕ< (n%ℕd<d k 8)
  [3] = fromℕ<-cong (+ (k %ℕ 8) %ℕ 8) (k %ℕ 8) [1] 
        (n%ℕd<d (+ (k %ℕ 8)) 8) (n%ℕd<d k 8)
  [4] : fromℕ< (n%ℕd<d (+ (l %ℕ 8)) 8) ≡ fromℕ< (n%ℕd<d l 8)
  [4] = fromℕ<-cong (+ (l %ℕ 8) %ℕ 8) (l %ℕ 8) [2] 
        (n%ℕd<d (+ (l %ℕ 8)) 8) (n%ℕd<d l 8)

f : Position → Position
f (k , l) = tableℤ×ℤ (k , l) +₂ (k , l)

noFix : ∀ z → f z ≢ z
noFix (k , l) h = tableNonZero (fromℕ< (n%ℕd<d k 8)) (fromℕ< (n%ℕd<d l 8)) [1]
  where
  [1] : tableℤ×ℤ (k , l) ≡ (0ℤ , 0ℤ)
  [1] = z+w≡w⇒z≡0 h

tableℤ×ℤ∘f-periodic : PeriodicF₂ 8 (tableℤ×ℤ ∘ f)
tableℤ×ℤ∘f-periodic k l = begin
  tableℤ×ℤ (f (k , l))
    ≡⟨⟩
  tableℤ×ℤ (tableℤ×ℤ (k , l) +₂ (k , l))
    ≡⟨ cong (λ z → tableℤ×ℤ (z +₂ (k , l))) (tableℤ×ℤ-periodic k l) ⟩
  tableℤ×ℤ ((k′ , l′) +₂ (k , l))
    ≡⟨⟩
  table (fromℕ< (n%ℕd<d (k′ + k) 8)) (fromℕ< (n%ℕd<d (l′ + l) 8)) 
    ≡⟨ cong₂ table [7] [8] ⟩
  table (fromℕ< (n%ℕd<d (k′ + + (k %ℕ 8)) 8)) 
      (fromℕ< (n%ℕd<d (l′ + + (l %ℕ 8)) 8)) 
    ≡⟨⟩
  tableℤ×ℤ ((k′ , l′) +₂ (+ (k %ℕ 8) , + (l %ℕ 8))) 
    ≡⟨⟩ 
  tableℤ×ℤ (f (+ (k %ℕ 8) , + (l %ℕ 8))) 
    ∎
  where
  open Eq.≡-Reasoning
  k′ = proj₁ (tableℤ×ℤ (+ (k %ℕ 8) , + (l %ℕ 8)))
  l′ = proj₂ (tableℤ×ℤ (+ (k %ℕ 8) , + (l %ℕ 8)))
  [1] : k ≡ + (k %ℕ 8) + k /ℕ 8 * + 8
  [1] = a≡a%ℕn+[a/ℕn]*n k 8
  [2] : l ≡ + (l %ℕ 8) + l /ℕ 8 * + 8
  [2] = a≡a%ℕn+[a/ℕn]*n l 8
  [3] : k′ + k ≡ k′ + + (k %ℕ 8) + k /ℕ 8 * + 8
  [3] rewrite +-assoc k′ (+ (k %ℕ 8)) (k /ℕ 8 * + 8) = cong (_+_ k′) [1]
  [4] : l′ + l ≡ l′ + + (l %ℕ 8) + l /ℕ 8 * + 8
  [4] rewrite +-assoc l′ (+ (l %ℕ 8)) (l /ℕ 8 * + 8) = cong (_+_ l′) [2]
  [5] : (k′ + k) %ℕ 8 ≡ (k′ + + (k %ℕ 8)) %ℕ 8
  [5] = trans (cong (_%ℕ 8) [3]) ([m+kn]%ℕn≡[m]%ℕn (k′ + + (k %ℕ 8)) (k /ℕ 8) 8)
  [6] : (l′ + l) %ℕ 8 ≡ (l′ + + (l %ℕ 8)) %ℕ 8
  [6] = trans (cong (_%ℕ 8) [4]) ([m+kn]%ℕn≡[m]%ℕn (l′ + + (l %ℕ 8)) (l /ℕ 8) 8)
  [7] : fromℕ< (n%ℕd<d (k′ + k) 8) ≡ fromℕ< (n%ℕd<d (k′ + + (k %ℕ 8)) 8)
  [7] = fromℕ<-cong ((k′ + k) %ℕ 8) ((k′ + + (k %ℕ 8)) %ℕ 8) [5] 
    (n%ℕd<d (k′ + k) 8) (n%ℕd<d (k′ + + (k %ℕ 8)) 8)
  [8] : fromℕ< (n%ℕd<d (l′ + l) 8) ≡ fromℕ< (n%ℕd<d (l′ + + (l %ℕ 8)) 8)
  [8] = fromℕ<-cong ((l′ + l) %ℕ 8) ((l′ + + (l %ℕ 8)) %ℕ 8) [6] 
    (n%ℕd<d (l′ + l) 8) (n%ℕd<d (l′ + + (l %ℕ 8)) 8)

Invol : Position → Set
Invol z = f (f z) ≡ z

invol-periodic : Periodic₂ 8 Invol
invol-periodic k l = ↔-trans [2] (↔-sym [4])
  where
  k′ = proj₁ (tableℤ×ℤ (f (+ (k %ℕ 8) , + (l %ℕ 8))) +₂ 
          tableℤ×ℤ (+ (k %ℕ 8) , + (l %ℕ 8)))
  l′ = proj₂ (tableℤ×ℤ (f (+ (k %ℕ 8) , + (l %ℕ 8))) +₂ 
          tableℤ×ℤ (+ (k %ℕ 8) , + (l %ℕ 8)))
  [1] : f (f (k , l)) ≡ (k′ , l′) +₂ (k , l)
  [1] = begin
    f (f (k , l)) 
      ≡⟨⟩
    tableℤ×ℤ (f (k , l)) +₂ (tableℤ×ℤ (k , l) +₂ (k , l)) 
      ≡˘⟨ +₂-assoc (tableℤ×ℤ (f (k , l))) (tableℤ×ℤ (k , l)) (k , l) ⟩
    tableℤ×ℤ (f (k , l)) +₂ tableℤ×ℤ (k , l) +₂ (k , l) 
      ≡⟨ cong (_+₂ (k , l)) 
         (cong₂ _+₂_ (tableℤ×ℤ∘f-periodic k l) (tableℤ×ℤ-periodic k l)) ⟩
    tableℤ×ℤ (f (+ (k %ℕ 8) , + (l %ℕ 8))) +₂ 
      tableℤ×ℤ (+ (k %ℕ 8) , + (l %ℕ 8)) +₂ (k , l) 
      ≡⟨⟩
    (k′ , l′) +₂ (k , l)
      ∎ where open Eq.≡-Reasoning
  [2] : f (f (k , l)) ≡ (k , l) ↔ (k′ , l′) ≡ (0ℤ , 0ℤ)
  [2] rewrite [1] = z+w≡w⇔z≡0 (k′ , l′) (k , l)
  [3] : f (f (+ (k %ℕ 8) , + (l %ℕ 8))) ≡ (k′ , l′) +₂ (+ (k %ℕ 8) , + (l %ℕ 8))
  [3] = sym (+₂-assoc (tableℤ×ℤ (f (+ (k %ℕ 8) , + (l %ℕ 8)))) 
        (tableℤ×ℤ (+ (k %ℕ 8) , + (l %ℕ 8))) (+ (k %ℕ 8) , + (l %ℕ 8)))
  [4] : f (f (+ (k %ℕ 8) , + (l %ℕ 8))) ≡ (+ (k %ℕ 8) , + (l %ℕ 8)) ↔ 
        (k′ , l′) ≡ (0ℤ , 0ℤ)
  [4] rewrite [3] = z+w≡w⇔z≡0 (k′ , l′) (+ (k %ℕ 8) , + (l %ℕ 8))

invol? : Decidable Invol
invol? z = f (f z) ℤ×ℤ-≟ z

univFin8Invol? : Dec (UnivFin 8 Invol)
univFin8Invol? = univFin? 8 invol?

univFin8Invol : UnivFin 8 Invol
univFin8Invol = toWitness {Q = univFin8Invol?} tt

involutive : Involutive _≡_ f
involutive (k , l) = periodic₂-univ 8 invol-periodic univFin8Invol k l

```

We have shown that the function `f` is a pairing of `ℤ × ℤ`.

```agda
module N-in-a-row (n : ℕ) {n≢0 : False (n ℕ.≟ 0)} where
  open PositionalGame Position _ℤ×ℤ-≟_ newPos (WinningSet n {n≢0}) 
    (¬WinningSet[] n {n≢0}) public

  pairing : Pairing
  pairing = record 
    { func       = f
    ; noFix      = noFix
    ; involutive = involutive
    }


```

We are now going to show that this pairing is good when `n ≡ 9`. For this, we 
will express `Good pairing` in terms of the universal closure of a predicate
`BlocksWinningSetAt`. This predicate is doubly periodic with period 8, so we 
can decide whether its universal closure holds.

```agda
  BlocksWinningSetsAt : Pairing → Position → Set
  BlocksWinningSetsAt p z = 
    All (λ d → Blocks p (applyUpTo (λ k → (k · d) +₂ z) n)) directions

  postulate
    blocksAllWinningSets-equiv : (p : Pairing) → 
      ((z : Position) → BlocksWinningSetsAt p z) ↔ Good p
  -- blocksAllWinningSets-equiv p = {!   !}

  blocksWinningSetsAt? : B.Decidable BlocksWinningSetsAt
  blocksWinningSetsAt? p z = 
    All.all? (λ d → blocks? p (applyUpTo (λ k → (k · d) +₂ z) n)) directions

  postulate  
    blocksWinningSetsAt-periodic : Periodic₂ 8 (BlocksWinningSetsAt pairing)
  -- blocksWinningSetsAt-periodic = {!   !}

  univFin8Blocks? : Dec (UnivFin 8 (BlocksWinningSetsAt pairing))
  univFin8Blocks? = univFin? 8 (blocksWinningSetsAt? pairing)

```

## 9-in-a-row

The universal closure of `BlocksWinningSetAt` is true when `n ≡ 9`. This means
that the pairing `pairing` is `Good`, and that the 9-in-a-row game is a draw.

```agda
module 9-in-a-row where

  open N-in-a-row 9

  univFin8Blocks : UnivFin 8 (BlocksWinningSetsAt pairing)
  univFin8Blocks = toWitness {Q = univFin8Blocks?} tt

  good : Good pairing
  good = proj₁ (blocksAllWinningSets-equiv pairing) 
    λ { (k , l) → 
    (periodic₂-univ 8 blocksWinningSetsAt-periodic univFin8Blocks) k l }

  9-in-a-rowIsADraw : ¬ FirstCanForceWin [] [] × ¬ SecondCanForceWin [] []
  9-in-a-rowIsADraw = 
    FirstHasNoWinningStrategy pairing good , secondHasNoWinningStrategy

```

TODO:

1. (hard) Show `(m : ℤ) (n : ℕ) → ((m + -[1+ n ]) %ℕ suc n) ≡ (m %ℕ suc n)`.

2. (easy) Show the equivalence of the two formulations of `Blocks`. This is 
necessary to show the decidability of `Blocks`.

3. (easy) Show that `Good p` is equivalent to the universal closure of
`BlocksWinningSetsAt`.

4. (hard) Show that `BlocksWinningSetsAt` is doubly periodic with period 8.

5. (medium) Show that N-in-a-row is a draw when N ≥ 9. It suffices to show that
a pairing blocks all winning sets for N ≥ N′ if it blocks all winning sets for
N′.
