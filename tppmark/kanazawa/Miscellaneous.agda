open import Algebra.Definitions using (Associative; Commutative; Involutive; LeftCancellative; RightCancellative)
open import Data.Bool using (T; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin as F using (Fin; toℕ)
open import Data.Fin.Properties using (toℕ<n)
open import Data.Integer using (ℤ; +_; -[1+_]; -_; _+_; _-_; _*_)
open import Data.Integer.DivMod using () renaming (_modℕ_ to _%ℕ_)
open import Data.Integer.Properties as ℤₚ
  using (neg-involutive; +-assoc; +-identityˡ; +-identityʳ; +-inverseˡ; +-inverseʳ; pos-distrib-*)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Nat as ℕ using (ℕ; zero; suc; _∸_; _≤_; _<_; s≤s; _<ᵇ_; _⊔_)
open import Data.Nat.DivMod 
  using (_%_; _divMod_; result; m%n%n≡m%n; m≤n⇒m%n≡m; [m+n]%n≡m%n; [m+kn]%n≡m%n; m*n%n≡0)
open import Data.Nat.Properties as ℕₚ using (_≟_; m∸n≤m; suc-injective; <⇒<ᵇ; <ᵇ⇒<; m≤m+n; m≤n+m; m≤n⇒m∸n≡0; m∸n≡0⇒m≤n; ≤⇒≯; m+[n∸m]≡n; <⇒≤; ≤-refl; n∸n≡0; m∸n+n≡m; +-suc; m≤m⊔n; m≤n⊔m)
-- This comment about m≤n⊔m in Data.Nat.Properties is wrong.
-- : ∀ m n → m ≤ n ⊔ m
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Product.Properties using () renaming (≡-dec to ×-≡-dec)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_; id)
open import Relation.Binary as B using (DecidableEquality)
open import Relation.Binary.PropositionalEquality as Eq 
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; _≗_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (False)
open import Relation.Unary using (Decidable) renaming (_⊆_ to _⇒_)

-- I don't know why I can't find the following in the standard library!

disjunctiveSyllogism : {A B : Set} → A ⊎ B → ¬ A → B
disjunctiveSyllogism (inj₁ x) h = ⊥-elim (h x)
disjunctiveSyllogism (inj₂ y) h = y

infix 3 _↔_

_↔_ : (A B : Set) → Set
A ↔ B = (A → B) × (B → A)

↔-refl : {A : Set} → A ↔ A
↔-refl = id , id

↔-trans : {A B C : Set} → (A ↔ B) → (B ↔ C) → (A ↔ C)
↔-trans (A→B , B→A) (B→C , C→B) = B→C ∘ A→B , B→A ∘ C→B

↔-sym : {A B : Set} → (A ↔ B) → (B ↔ A)
↔-sym (A→B , B→A) = (B→A , A→B)

↔-¬ : {A B : Set} → (A ↔ B) → ((¬ A) ↔ (¬ B))
↔-¬ (A→B , B→A) = (λ ¬a b → ¬a (B→A b)) , λ ¬b a → ¬b (A→B a)

_⇔_ : {A : Set} (P Q : A → Set) → Set
-- P ⇔ Q = ∀ {x} → P x ↔ Q x
P ⇔ Q = (P ⇒ Q) × (Q ⇒ P)

↔-dec : {A B : Set} → (A ↔ B) → Dec A → Dec B
↔-dec A↔B (no ¬a) = no λ b → ¬a (proj₂ A↔B b)
↔-dec A↔B (yes a) = yes (proj₁ A↔B a)

⇔-dec : {A : Set} {P Q : A → Set} → (P ⇔ Q) → Decidable P → Decidable Q
⇔-dec (P⇒Q , Q⇒P) p? x = ↔-dec (P⇒Q {x} , Q⇒P {x}) (p? x)

any-⇒ : {A : Set} {P Q : A → Set} → (P ⇒ Q) → Any P ⇒ Any Q
any-⇒ P⇒Q (here px)    = here (P⇒Q px)
any-⇒ P⇒Q (there anyP) = there (any-⇒ P⇒Q anyP)

any-⇔ : {A : Set} {P Q : A → Set} → (P ⇔ Q) → Any P ⇔ Any Q
any-⇔ (P⇒Q , Q⇒P) = any-⇒ P⇒Q , any-⇒ Q⇒P

¬any-⊥ : {A : Set} (xs : List A) → ¬ Any (λ (_ : A) → ⊥) xs
¬any-⊥ (x ∷ xs) (there h) = ¬any-⊥ xs h

∀¬-¬any : {A : Set} {P : A → Set} → (∀ x → ¬ P x) → ∀ xs → ¬ Any P xs
∀¬-¬any h xs h₁ = ¬any-⊥ xs (any-⇒ (λ {x} px → h x px) h₁)

all-⇒ : {A : Set} {P Q : A → Set} → (P ⇒ Q) → All P ⇒ All Q
all-⇒ P⇒Q [] = []
all-⇒ P⇒Q (px ∷ allP) = P⇒Q px ∷ all-⇒ P⇒Q allP

all-∈ : ∀ {A : Set} {P : A → Set} {xs : List A} {x : A} → All P xs → x ∈ xs → P x
all-∈ {xs = x₁ ∷ xs} (Px₁ ∷ AllPxs) (here refl) = Px₁
all-∈ {xs = x₁ ∷ xs} (_ ∷ AllPxs) (there x∈xs) = all-∈ {xs = xs} AllPxs x∈xs

∈-All : ∀ {A : Set} {P : A → Set} (xs : List A) → (∀ (x : A) → x ∈ xs → P x) → All P xs
∈-All [] h = []
∈-All (x ∷ xs) h = (h x (here refl)) ∷ (∈-All xs (λ x₁ h₁ → h x₁ (there h₁)))

m+n≡n⇒m≡0 : {m n : ℤ} → m + n ≡ n → m ≡ + 0
m+n≡n⇒m≡0 {m} {n} h = begin
  m           ≡˘⟨ +-identityʳ m ⟩
  m + + 0     ≡˘⟨ cong (_+_ m) (+-inverseʳ n) ⟩
  m + (n - n) ≡˘⟨ +-assoc m n (- n) ⟩
  (m + n) - n ≡⟨ cong (_+ - n) h ⟩
  n - n       ≡⟨ +-inverseʳ n ⟩
  + 0         ∎ where open Eq.≡-Reasoning

[m]%ℕn%n≡[m]%ℕ : (m : ℤ) (n : ℕ) {n≢0 : False (n ≟ 0)} → 
         ((m %ℕ n) {n≢0} % n) {n≢0} ≡ (m %ℕ n) {n≢0}
[m]%ℕn%n≡[m]%ℕ (+ k) (suc n) = m%n%n≡m%n k n
[m]%ℕn%n≡[m]%ℕ -[1+ k ] (suc n) with (suc k divMod (suc n))
... | result q F.zero    eq = refl
... | result q (F.suc r) eq = m≤n⇒m%n≡m [1]
  where
  [1] : n ∸ toℕ r ≤ n
  [1] = m∸n≤m n (toℕ r)

[[m]%ℕn]%ℕn≡[m]%ℕn : (m : ℤ) (n : ℕ) {n≢0 : False (n ≟ 0)} → 
            (+ (m %ℕ n) {n≢0} %ℕ n) {n≢0} ≡ (m %ℕ n) {n≢0}
[[m]%ℕn]%ℕn≡[m]%ℕn m n {n≢0} = begin 
  (+ (m %ℕ n) {n≢0} %ℕ n) {n≢0} ≡⟨⟩
  ((m %ℕ n) {n≢0} % n) {n≢0}      ≡⟨ [m]%ℕn%n≡[m]%ℕ m n {n≢0} ⟩
  (m %ℕ n) {n≢0}                  ∎
  where open Eq.≡-Reasoning

[m+n]%ℕn≡[m]%ℕn : (m : ℤ) (n : ℕ) {n≢0 : False (n ≟ 0)} →
  ((m + + n) %ℕ n) {n≢0} ≡ (m %ℕ n) {n≢0}
[m+n]%ℕn≡[m]%ℕn m (suc n) with m
... | + m₁      = [m+n]%n≡m%n m₁ n
... | -[1+ m₁ ] with n <ᵇ m₁ in eq
... | false = [1] -- with suc m₁ divMod (suc n)
  where
  [1] : + (n ∸ m₁) %ℕ suc n ≡ -[1+ m₁ ] %ℕ suc n
  [1] with suc m₁ divMod (suc n)
  ... | result (suc q) F.zero property = [1-4]
    where
    [1-1] : m₁ ≡ n ℕ.+ q ℕ.* suc n
    [1-1] = suc-injective property
    [1-2] : n ≤ m₁
    [1-2] rewrite [1-1] = m≤m+n n (q ℕ.* suc n)
    [1-3] : n ∸ m₁ ≡ 0
    [1-3] = m≤n⇒m∸n≡0 [1-2]
    [1-4] : + (n ∸ m₁) %ℕ suc n ≡ 0
    [1-4] rewrite [1-3] = refl
  ... | result zero (F.suc r) property = [1-4]
    where
    [1-1] : m₁ ≡ toℕ r
    [1-1] rewrite ℕₚ.+-identityʳ (toℕ r) = suc-injective property
    [1-2] : n ∸ m₁ ≤ n
    [1-2] = m∸n≤m n m₁
    [1-3] : (n ∸ m₁) % (suc n) ≡ n ∸ m₁
    [1-3] = m≤n⇒m%n≡m [1-2]
    [1-4] : (n ∸ m₁) % (suc n) ≡ n ∸ toℕ r
    [1-4] rewrite [1-3] | [1-1] = refl
  ... | result (suc q) (F.suc r) property = ⊥-elim contra
    where
    [1-1] : m₁ ≡ toℕ r ℕ.+ (suc n ℕ.+ q ℕ.* suc n)
    [1-1] = suc-injective property
    n<m₁ : n < m₁
    n<m₁ rewrite [1-1] = 
      ℕₚ.≤-trans (m≤m+n (suc n) (q ℕ.* suc n)) 
      (m≤n+m (suc n ℕ.+ q ℕ.* suc n) (toℕ r))
    contra : ⊥
    contra = subst T eq (<⇒<ᵇ n<m₁)
... | true with m₁ ∸ n in eq₁
... | zero = ⊥-elim (¬n<m₁ (<ᵇ⇒< n m₁ (subst T (sym eq) tt)))
  where
  m₁≤n : m₁ ≤ n
  m₁≤n = m∸n≡0⇒m≤n eq₁
  ¬n<m₁ : ¬ n < m₁
  ¬n<m₁ = ≤⇒≯ m₁≤n
... | suc k with suc k divMod (suc n) | suc m₁ divMod (suc n)
... | result q F.zero property | result q₁ F.zero property₁ = refl
... | result q F.zero property | result q₁ (F.suc r₁) property₁ = 
  subst (λ z → 0 ≡ n ∸ z) [6] (sym (n∸n≡0 n))
  where
  n≤m₁ : n ≤ m₁
  n≤m₁ = <⇒≤ (<ᵇ⇒< n m₁ (subst T (sym eq) tt))
  [1] : n ℕ.+ (m₁ ∸ n) ≡ m₁ 
  [1] = m+[n∸m]≡n n≤m₁
  [2] : m₁ ≡ n ℕ.+ q ℕ.* suc n
  [2] rewrite sym eq₁ = trans (sym [1]) (cong (n ℕ.+_) property)
  [3] : m₁ % (suc n) ≡ n
  [3] rewrite [2] = trans ([m+kn]%n≡m%n n q n) (m≤n⇒m%n≡m ≤-refl)
  [4] : m₁ % (suc n) ≡ toℕ r₁ % (suc n)
  [4] rewrite suc-injective property₁ = [m+kn]%n≡m%n (toℕ r₁) q₁ n
  [5] : toℕ r₁ % (suc n) ≡ toℕ r₁
  [5] = m≤n⇒m%n≡m (<⇒≤ (toℕ<n r₁))
  [6] : n ≡ toℕ r₁
  [6] = trans (sym [3]) (trans [4] [5])
... | result q (F.suc r) property | result q₁ F.zero property₁ = 
  ⊥-elim ([6] [5])
  where
  n≤m₁ : n ≤ m₁
  n≤m₁ = <⇒≤ (<ᵇ⇒< n m₁ (subst T (sym eq) tt))
  [1] : suc m₁ % (suc n) ≡ 0
  [1] rewrite property₁ = m*n%n≡0 q₁ n
  [2] : suc m₁ ≡ suc (toℕ r) ℕ.+ q ℕ.* suc n ℕ.+ suc n
  [2] = begin
    suc m₁                                ≡˘⟨ cong suc (m+[n∸m]≡n n≤m₁) ⟩
    suc n ℕ.+ (m₁ ∸ n)                    ≡⟨ ℕₚ.+-comm (suc n) (m₁ ∸ n) ⟩
    m₁ ∸ n ℕ.+ suc n                      ≡⟨ cong (ℕ._+ suc n) eq₁ ⟩
    suc k ℕ.+ suc n                       ≡⟨ cong (ℕ._+ suc n) property ⟩ 
    suc (toℕ r) ℕ.+ q ℕ.* suc n ℕ.+ suc n ∎
    where open Eq.≡-Reasoning
  [3] : suc m₁ % suc n ≡ suc (toℕ r) % suc n
  [3] = begin 
    suc m₁ % suc n 
      ≡⟨ cong (_% suc n) [2] ⟩
    (suc (toℕ r) ℕ.+ q ℕ.* suc n ℕ.+ suc n) % suc n 
      ≡⟨ [m+n]%n≡m%n (suc (toℕ r) ℕ.+ q ℕ.* suc n) n ⟩
    (suc (toℕ r) ℕ.+ q ℕ.* suc n) % suc n 
      ≡⟨ [m+kn]%n≡m%n (suc (toℕ r)) q n ⟩
    suc (toℕ r) % suc n 
      ∎ where open Eq.≡-Reasoning
  [4] : suc (toℕ r) % suc n ≡ 0
  [4] = trans (sym [3]) [1]
  [5] : suc (toℕ r) ≡ 0
  [5] = trans (sym (m≤n⇒m%n≡m (toℕ<n r))) [4]
  [6] : suc (toℕ r) ≢ 0
  [6] ()
... | result q (F.suc r) property | result q₁ (F.suc r₁) property₁ = 
  cong (n ∸_) (suc-injective (trans (sym [3]) [1]))
  where
  n≤m₁ : n ≤ m₁
  n≤m₁ = <⇒≤ (<ᵇ⇒< n m₁ (subst T (sym eq) tt))
  [1] : suc m₁ % suc n ≡ suc (toℕ r₁)
  [1] = begin
    suc m₁ % suc n 
      ≡⟨ cong (_% suc n) property₁ ⟩
    (suc (toℕ r₁) ℕ.+ q₁ ℕ.* suc n) % suc n 
      ≡⟨ [m+kn]%n≡m%n (suc (toℕ r₁)) q₁ n ⟩
    suc (toℕ r₁) % suc n 
      ≡⟨ m≤n⇒m%n≡m (toℕ<n r₁) ⟩
    suc (toℕ r₁) 
      ∎ where open Eq.≡-Reasoning
  [2] : suc m₁ ≡ suc (toℕ r) ℕ.+ q ℕ.* suc n ℕ.+ suc n
  [2] = begin
    suc m₁                                ≡˘⟨ cong suc (m+[n∸m]≡n n≤m₁) ⟩
    suc n ℕ.+ (m₁ ∸ n)                    ≡⟨ ℕₚ.+-comm (suc n) (m₁ ∸ n) ⟩
    m₁ ∸ n ℕ.+ suc n                      ≡⟨ cong (ℕ._+ suc n) eq₁ ⟩
    suc k ℕ.+ suc n                       ≡⟨ cong (ℕ._+ suc n) property ⟩ 
    suc (toℕ r) ℕ.+ q ℕ.* suc n ℕ.+ suc n ∎
    where open Eq.≡-Reasoning
  [3] : suc m₁ % suc n ≡ suc (toℕ r)
  [3] = begin 
    suc m₁ % suc n 
      ≡⟨ cong (_% suc n) [2] ⟩
    (suc (toℕ r) ℕ.+ q ℕ.* suc n ℕ.+ suc n) % suc n 
      ≡⟨ [m+n]%n≡m%n (suc (toℕ r) ℕ.+ q ℕ.* suc n) n ⟩
    (suc (toℕ r) ℕ.+ q ℕ.* suc n) % suc n 
      ≡⟨ [m+kn]%n≡m%n (suc (toℕ r)) q n ⟩
    suc (toℕ r) % suc n 
      ≡⟨ m≤n⇒m%n≡m (toℕ<n r) ⟩
    suc (toℕ r)
      ∎ where open Eq.≡-Reasoning

postulate
  [m-n]%ℕn≡[m]%ℕn : (m : ℤ) (n : ℕ) → ((m + -[1+ n ]) %ℕ suc n) ≡ (m %ℕ suc n)
-- [m-n]%ℕn≡[m]%ℕn m n = {!   !}

[m+kn]%ℕn≡[m]%ℕn : (m k : ℤ) (n : ℕ) {n≢0 : False (n ≟ 0)} →
  ((m + k * (+ n)) %ℕ n) {n≢0} ≡ (m %ℕ n) {n≢0}
[m+kn]%ℕn≡[m]%ℕn m (+ zero)     (suc n) = cong (_%ℕ suc n) (+-identityʳ m)
[m+kn]%ℕn≡[m]%ℕn m (+ k₁) (suc n) = [1] m k₁
  where
  [1] : (m : ℤ) (k₁ : ℕ) → (m + + k₁ * (+ suc n)) %ℕ suc n ≡ m %ℕ suc n
  [1] m zero     = cong (_%ℕ suc n) (+-identityʳ m)
  [1] m (suc k₁) = begin
    (m + + suc k₁ * + suc n) %ℕ suc n         ≡⟨⟩
    (m + + (suc n ℕ.+ k₁ ℕ.* suc n)) %ℕ suc n ≡⟨⟩
    (m + (+ suc n + + (k₁ ℕ.* suc n))) %ℕ suc n ≡˘⟨ cong (_%ℕ suc n) (+-assoc m (+ suc n) (+ (k₁ ℕ.* suc n))) ⟩
    (m + + suc n + + (k₁ ℕ.* suc n)) %ℕ suc n 
      ≡˘⟨ cong (λ z → (m + + suc n + z) %ℕ suc n) (pos-distrib-* k₁ (suc n)) ⟩
    (m + + suc n + + k₁ * + suc n) %ℕ suc n   ≡⟨ [1] (m + + suc n) k₁ ⟩
    (m + + suc n) %ℕ suc n                    ≡⟨ [m+n]%ℕn≡[m]%ℕn m (suc n) ⟩
    m %ℕ suc n                                ∎
    where open Eq.≡-Reasoning
[m+kn]%ℕn≡[m]%ℕn m (-[1+ k₁ ])   (suc n) = [1] m k₁
  where
  [1] : (m : ℤ) (k₁ : ℕ) → (m + -[1+ n ℕ.+ k₁ ℕ.* suc n ]) %ℕ suc n ≡ m %ℕ suc n
  [1] m zero     rewrite ℕₚ.+-identityʳ n = [m-n]%ℕn≡[m]%ℕn m n
  [1] m (suc k₁) = begin 
    (m + -[1+ n ℕ.+ suc (n ℕ.+ k₁ ℕ.* suc n) ]) %ℕ suc n  
      ≡⟨ cong (λ z → (m + -[1+ z ]) %ℕ suc n) (+-suc n (n ℕ.+ k₁ ℕ.* suc n)) ⟩
    (m + (-[1+ n ] + -[1+ n ℕ.+ k₁ ℕ.* suc n ])) %ℕ suc n 
      ≡˘⟨ cong (_%ℕ suc n) (+-assoc m (-[1+ n ]) (-[1+ n ℕ.+ k₁ ℕ.* suc n ])) ⟩ 
    (m + -[1+ n ] + -[1+ n ℕ.+ k₁ ℕ.* suc n ]) %ℕ suc n   
      ≡⟨ [1] (m + -[1+ n ]) k₁ ⟩
    (m + -[1+ n ]) %ℕ suc n                             
      ≡⟨ [m-n]%ℕn≡[m]%ℕn m n ⟩ 
    m %ℕ suc n ∎
    where open Eq.≡-Reasoning

infixl 20 _+₂_

_ℤ×ℤ-≟_ : DecidableEquality (ℤ × ℤ)
_ℤ×ℤ-≟_ = ×-≡-dec ℤₚ._≟_ ℤₚ._≟_

_+₂_ : ℤ × ℤ → ℤ × ℤ → ℤ × ℤ
(m₁ , n₁) +₂ (m₂ , n₂) = (m₁ + m₂ , n₁ + n₂)

+₂-assoc : (v w z : ℤ × ℤ) → (v +₂ w) +₂ z ≡ v +₂ (w +₂ z)
+₂-assoc (m₁ , n₁) (m₂ , n₂) (m₃ , n₃) = 
  cong₂ _,_ (+-assoc m₁ m₂ m₃) (+-assoc n₁ n₂ n₃)

+₂-identityˡ : (v : ℤ × ℤ) → (+ 0 , + 0) +₂ v ≡ v
+₂-identityˡ (m , n) = cong₂ _,_ (+-identityˡ m) (+-identityˡ n)

z+w≡w⇒z≡0 : {z w : ℤ × ℤ} → z +₂ w ≡ w → z ≡ (+ 0 , + 0)
z+w≡w⇒z≡0 {m₁ , n₁} {m₂ , n₂} h =  cong₂ _,_ (m+n≡n⇒m≡0 (cong proj₁ h)) (m+n≡n⇒m≡0 (cong proj₂ h))

z+w≡w⇔z≡0 : (z w : ℤ × ℤ) → z +₂ w ≡ w ↔ z ≡ (+ 0 , + 0)
z+w≡w⇔z≡0 z w = (z+w≡w⇒z≡0 {z} {w} , λ {refl → +₂-identityˡ w})

-₂_ : ℤ × ℤ → ℤ × ℤ
-₂ (m , n) = (- m , - n)

-₂-involutive : Involutive _≡_ -₂_  -- -₂_ ∘ -₂_ ≗ id
-₂-involutive (m , n) = cong₂ _,_ (neg-involutive m) (neg-involutive n)

+₂-inverseˡ : (v : ℤ × ℤ) → (-₂ v) +₂ v ≡ (+ 0 , + 0)
+₂-inverseˡ (m , n) = cong₂ _,_ (+-inverseˡ m) (+-inverseˡ n)

_·_ : ℕ → ℤ × ℤ → ℤ × ℤ
k · (m , n) = (+ k) * m , (+ k) * n

translate : ℤ × ℤ → List (ℤ × ℤ) → List (ℤ × ℤ)
translate (m , n) zs = map ((m , n) +₂_) zs

translate- : (v : ℤ × ℤ) → translate (-₂ v) ∘ translate v ≗ id
translate- v []       = refl
translate- v (z ∷ zs) = cong₂ _∷_ [1] (translate- v zs)
  where
  [1] : (-₂ v) +₂ (v +₂ z) ≡ z
  [1] = begin
    (-₂ v) +₂ (v +₂ z)   ≡˘⟨ +₂-assoc (-₂ v) v z ⟩
    (((-₂ v) +₂ v) +₂ z) ≡⟨ cong (_+₂ z) (+₂-inverseˡ v) ⟩
    ((+ 0 , + 0) +₂ z)     ≡⟨ +₂-identityˡ z ⟩
    z                    ∎ where open Eq.≡-Reasoning
 