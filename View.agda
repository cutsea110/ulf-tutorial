module View where

open import Data.Nat

data Parity : ℕ → Set where
  even : (k : ℕ) → Parity (k * 2)
  odd  : (k : ℕ) → Parity (1 + k * 2)

parity : (n : ℕ) → Parity n
parity zero = even zero
parity (suc n) with parity n
parity (suc .(k * 2)) | even k = odd k
parity (suc .(suc (k * 2))) | odd k = even (suc k)

half : ℕ → ℕ
half n with parity n
half .(k * 2) | even k = k
half .(suc (k * 2)) | odd k = k

open import Data.Bool
open import Function using (_∘_; const)

isEven : ℕ → Bool
isEven n with parity n
isEven .(k * 2) | even k = true
isEven .(suc (k * 2)) | odd k = false

isOdd : ℕ → Bool
isOdd = not ∘ isEven

data Trity : ℕ → Set where
  none : (k : ℕ) → Trity (k * 3)
  one : (k : ℕ) → Trity (1 + k * 3)
  two : (k : ℕ) → Trity (2 + k * 3)

trity : (n : ℕ) → Trity n
trity zero = none zero
trity (suc zero) = one zero
trity (suc (suc n)) with trity n
trity (suc (suc .(k * 3))) | none k = two k
trity (suc (suc .(suc (k * 3)))) | one k = none (suc k)
trity (suc (suc .(suc (suc (k * 3))))) | two k = one (suc k)

div3 : ℕ → ℕ
div3 n with trity n
div3 .(k * 3) | none k = k
div3 .(suc (k * 3)) | one k = k
div3 .(suc (suc (k * 3))) | two k = k

open import Data.List using (List; []; _∷_; _++_; filter; length)

data All {A : Set} (P : A → Set) : List A → Set where
  ∅ : All P []
  _:all:_ : ∀ {x xs} → P x → All P xs → All P (x ∷ xs)

open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)

-- partial for Bool <- its NG
-- data isTrue : (b : Bool) → Set where
--   trueIsTrue : isTrue true

isTrue : Bool → Set
isTrue false = ⊥
isTrue true = ⊤

data _≡_ {A : Set}(x : A) : (y : A) → Set where
  refl : x ≡ x

cong : ∀ {A B : Set} {x y : A} (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

trueIsTrue : {x : Bool} → x ≡ true → isTrue x
trueIsTrue refl = tt

satisfies : {A : Set} → (A → Bool) → A → Set
satisfies p x = isTrue (p x)

data Find {A : Set} (p : A → Bool) : List A → Set where
  found : (xs : List A) (y : A) → satisfies p y → (ys : List A) → Find p (xs ++ y ∷ ys)
  not-found : ∀ {xs} → All (satisfies (not ∘ p)) xs → Find p xs

-- find₁ : {A : Set} (p : A → Bool) (xs : List A) → Find p xs
-- find₁ p [] = not-found ∅
-- find₁ p (x ∷ xs) with p x
-- find₁ p (x ∷ xs) | false = {!!}
-- find₁ p (x ∷ xs) | true = found [] x {!!} xs


data Inspect {A : Set} (x : A) : Set where
  it : (y : A) → x ≡ y → Inspect x

inspect : {A : Set} (x : A) → Inspect x
inspect y = it y refl

find : {A : Set}(p : A → Bool)(xs : List A) → Find p xs
find p [] = not-found ∅
find p (x ∷ xs) with inspect (p x)
find p (x ∷ xs) | it false px≡false with find p xs
find p (x ∷ .(xs ++ y ∷ ys)) | it false px≡false | found xs y py≡true ys = found (x ∷ xs) y py≡true ys
find p (x ∷ xs) | it false px≡false | not-found npxs = not-found (trueIsTrue (cong not px≡false) :all: npxs)
find p (x ∷ xs) | it true px≡true = found [] x (trueIsTrue px≡true) xs

infixl 0 _∈_
data _∈_ {A : Set}(x : A) : List A → Set where
  hd : ∀ {xs} → x ∈ x ∷ xs
  tl : ∀ {y xs} → x ∈ xs → x ∈ y ∷ xs

index : ∀ {A}{x : A}{xs} → x ∈ xs → ℕ
index hd = zero
index (tl p) = suc (index p)

data Lookup {A : Set}(xs : List A) : ℕ → Set where
  inside : (x : A) (p : x ∈ xs) → Lookup xs (index p)
  outside : (m : ℕ) → Lookup xs (length xs + m)

_!_ : {A : Set} (xs : List A) (n : ℕ) → Lookup xs n
[] ! n = outside n
(x ∷ xs) ! zero = inside x hd
(x ∷ xs) ! suc n with xs ! n
(x ∷ xs) ! suc .(index p) | inside y p = inside y (tl p)
(x ∷ xs) ! suc .(length xs + m) | outside m = outside m

open import Data.Maybe using (Maybe; nothing; just)

lookup : {A : Set} (xs : List A)(n : ℕ) → Maybe A
lookup xs n with xs ! n
lookup xs .(index p) | inside x p = just x
lookup xs .(length xs + m) | outside m = nothing

