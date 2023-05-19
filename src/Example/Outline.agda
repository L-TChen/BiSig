module Example.Outline (Id : Set) where

open import Prelude

variable
  m m' m'' n : ℕ
  mode : Mode

-- Syntax.Simple.Term
data Ty (m : ℕ) : Set where
  `_   : Fin m → Ty m
  base : Ty m
  imp  : Ty m → Ty m → Ty m

variable
  σ τ : Ty m
  Γ   : Vec (Ty m) n

TSub : ℕ → ℕ → Set
TSub m m' = Vec (Ty m') m

tsub : TSub m m' → Ty m → Ty m'
tsub ts (` i)     = V.lookup ts i
tsub ts  base     = base
tsub ts (imp t u) = imp (tsub ts t) (tsub ts u)

compTSub : TSub m' m'' → TSub m m' → TSub m m''
compTSub ts' ts = V.map (tsub ts') ts

tsub-comp : (ts : TSub m' m'') (us : TSub m m')
          → tsub (compTSub ts us) ≐ tsub ts ∘ tsub us
tsub-comp ts us (` i)     = V.lookup-map i (tsub ts) us
tsub-comp ts us  base     = refl
tsub-comp ts us (imp t u) = cong₂ imp (tsub-comp ts us t) (tsub-comp ts us u)

extTSub : (d : ℕ) → TSub m (d + m)
extTSub d = tabulate (`_ ∘ (d ↑ʳ_))

-- assuming the existence of a base type
baseTy : {m : ℕ} → Ty m
baseTy = base

fillBase : (d : ℕ) → TSub m m' → TSub (d + m) m'
fillBase _ = V.replicate baseTy V.++_

fillBase-extTSub : (d : ℕ) (ts : TSub m m')
                 → compTSub (fillBase d ts) (extTSub d) ≡ ts
fillBase-extTSub d ts =
  begin
    compTSub (fillBase d ts) (extTSub d)
      ≡⟨ refl ⟩
    V.map (tsub (fillBase d ts)) (tabulate (`_ ∘ (d ↑ʳ_)))
      ≡⟨ sym (V.tabulate-∘ (tsub (fillBase d ts)) (`_ ∘ (d ↑ʳ_))) ⟩
    tabulate (tsub (fillBase d ts) ∘ `_ ∘ (d ↑ʳ_))
      ≡⟨ refl ⟩
    tabulate (lookup (V.replicate base V.++ ts) ∘ (d ↑ʳ_))
      ≡⟨ V.tabulate-cong (V.lookup-++ʳ {m = d} (V.replicate base) ts) ⟩
    tabulate (lookup ts)
      ≡⟨ V.tabulate∘lookup ts ⟩
    ts
  ∎
  where open ≡-Reasoning

-- -- Syntax.BiTyped.RawNoMode.Term
-- data Parsed : Set where
--   `_  : Id → Parsed
--   _∋_ : Ty 0 → Parsed → Parsed
--   app : Parsed → Parsed → Parsed
--   abs : Id → Parsed → Parsed

data Raw (m : ℕ) : ℕ → Set where
  `_  : Fin n → Raw m n
  _∋_ : Ty m → Raw m n → Raw m n
  app : Raw m n → Raw m n → Raw m n
  abs : Raw m (suc n) → Raw m n

variable r s : Raw _ _

mapRaw : (Ty m → Ty m') → Raw m n → Raw m' n
mapRaw f (` i)     = ` i
mapRaw f (τ ∋ r)   = f τ ∋ mapRaw f r
mapRaw f (app r s) = app (mapRaw f r) (mapRaw f s)
mapRaw f (abs r)   = abs (mapRaw f r)

mapRaw-∘ : (f : Ty m' → Ty m'') (g : Ty m → Ty m')
           (r : Raw m n) → mapRaw (f ∘ g) r ≡ mapRaw f (mapRaw g r)
mapRaw-∘ f g (` i)     = refl
mapRaw-∘ f g (τ ∋ r)   = cong (f (g τ) ∋_) (mapRaw-∘ f g r)
mapRaw-∘ f g (app r s) = cong₂ app (mapRaw-∘ f g r) (mapRaw-∘ f g s)
mapRaw-∘ f g (abs r)   = cong  abs (mapRaw-∘ f g r)

mapRaw-cong : {f g : Ty m → Ty m'} → f ≐ g
            → (r : Raw m n) → mapRaw f r ≡ mapRaw g r
mapRaw-cong f≗g (` i)     = refl
mapRaw-cong f≗g (τ ∋  r)  = cong₂ _∋_ (f≗g τ) (mapRaw-cong f≗g r)
mapRaw-cong f≗g (app r s) = cong₂ app (mapRaw-cong f≗g r) (mapRaw-cong f≗g s)
mapRaw-cong f≗g (abs r)   = cong  abs (mapRaw-cong f≗g r)

-- module _ where

--   private variable
--     iden : Id
--     i    : Fin n
--     ids  : Vec Id n
--     p p' : Parsed

  -- data deBruijn : Parsed → ∀ {n} → Raw n → Vec Id n → Set where
  --   `_  : ids [ i ]= iden → deBruijn (` iden) (` i) ids
  --   _∋_ : σ ≡ τ → deBruijn p r ids → deBruijn (σ ∋ p) (τ ∋ r) ids
  --   app : deBruijn p r ids → deBruijn p' r' ids → deBruijn (app p p') (app r r') ids
  --   abs : deBruijn p r (iden ∷ ids) → deBruijn (abs iden p) (abs r) ids

data Typed {m : ℕ} : Ty m → {n : ℕ} → Vec (Ty m) n → Set where
  `_  : τ V.∈ Γ → Typed τ Γ
  _∋_ : (τ : Ty m) → Typed τ Γ → Typed τ Γ
  app : Typed (imp σ τ) Γ → Typed σ Γ → Typed τ Γ
  abs : Typed τ (σ ∷ Γ) → Typed (imp σ τ) Γ

eraseType : {Γ : Vec (Ty m) n} → Typed τ Γ → Raw m n
eraseType (` i)     = ` V.index i
eraseType (τ ∋ t)   = τ ∋  eraseType t
eraseType (app t u) = app (eraseType t) (eraseType u)
eraseType (abs t)   = abs (eraseType t)

data Core {m : ℕ} : Ty m → {n : ℕ} → Vec (Ty m) n → Set where
  `_  : τ V.∈ Γ → Core τ Γ
  app : Core (imp σ τ) Γ → Core σ Γ → Core τ Γ
  abs : Core τ (σ ∷ Γ) → Core (imp σ τ) Γ

toCore : Typed τ Γ → Core τ Γ
toCore (` i)     = ` i
toCore (τ ∋ t)   = toCore t
toCore (app t u) = app (toCore t) (toCore u)
toCore (abs t)   = abs (toCore t)

record Typed' (τ : Ty m) (Γ : Vec (Ty m) n) (r : Raw m n) : Set where
  constructor _,_
  field
    term : Typed τ Γ
    proof : eraseType term ≡ r

module Typed'EnrichedConstructors where

  var' : (i : τ V.∈ Γ) → Typed' τ Γ (` V.index i)
  var' i = (` i) , refl

  ann' : ∀ τ → Typed' τ Γ r → Typed' τ Γ (τ ∋ r)
  ann' τ (t , eq) = (τ ∋ t) , cong (_∋_ τ) eq

  app' : Typed' (imp σ τ) Γ r → Typed' σ Γ s → Typed' τ Γ (app r s)
  app' (t , teq) (u , ueq) = app t u , cong₂ app teq ueq

  abs' : Typed' τ (σ ∷ Γ) r → Typed' (imp σ τ) Γ (abs r)
  abs' (t , eq) = abs t , cong abs eq

TypeInference : Set
TypeInference = {m n : ℕ} (Γ : Vec (Ty m) n) (r : Raw m n)
              → Dec (Σ[ m' ∈ ℕ ] Σ[ τ ∈ Ty m' ] Σ[ ts ∈ TSub m m' ]
                     Typed' τ (V.map (tsub ts) Γ) (mapRaw (tsub ts) r))

data Raw⇆ (m : ℕ) : ℕ → Mode → Set where
  `_   : Fin n → Raw⇆ m n Infer
  _∋_  : Ty m → Raw⇆ m n Check → Raw⇆ m n Infer
  _∋⇆_ : Ty m → Raw⇆ m n Check → Raw⇆ m n Infer
  _↑   : Raw⇆ m n Infer → Raw⇆ m n Check
  app  : Raw⇆ m n Infer → Raw⇆ m n Check → Raw⇆ m n Infer
  abs  : Raw⇆ m (suc n) Check → Raw⇆ m n Check

mapRaw⇆ : (Ty m → Ty m') → Raw⇆ m n mode → Raw⇆ m' n mode
mapRaw⇆ f (` i)     = ` i
mapRaw⇆ f (τ ∋  r)  = f τ ∋  mapRaw⇆ f r
mapRaw⇆ f (τ ∋⇆ r)  = f τ ∋⇆ mapRaw⇆ f r
mapRaw⇆ f (r ↑)     = mapRaw⇆ f r ↑
mapRaw⇆ f (app r s) = app (mapRaw⇆ f r) (mapRaw⇆ f s)
mapRaw⇆ f (abs r)   = abs (mapRaw⇆ f r)

eraseMode : Raw⇆ m n mode → Raw m n
eraseMode (` i)     = ` i
eraseMode (τ ∋  r)  = τ ∋  eraseMode r
eraseMode (τ ∋⇆ r)  =      eraseMode r
eraseMode (r ↑)     =      eraseMode r
eraseMode (app r s) = app (eraseMode r) (eraseMode s)
eraseMode (abs r)   = abs (eraseMode r)

eraseMode-mapRaw⇆ : (f : Ty m → Ty m') (r : Raw⇆ m n mode)
                  → eraseMode (mapRaw⇆ f r) ≡ mapRaw f (eraseMode r)
eraseMode-mapRaw⇆ f (` i)     = refl
eraseMode-mapRaw⇆ f (τ ∋  r)  = cong (f τ ∋_) (eraseMode-mapRaw⇆ f r)
eraseMode-mapRaw⇆ f (τ ∋⇆ r)  = eraseMode-mapRaw⇆ f r
eraseMode-mapRaw⇆ f (r ↑)     = eraseMode-mapRaw⇆ f r
eraseMode-mapRaw⇆ f (app r s) = cong₂ app (eraseMode-mapRaw⇆ f r) (eraseMode-mapRaw⇆ f s)
eraseMode-mapRaw⇆ f (abs r)   = cong  abs (eraseMode-mapRaw⇆ f r)

record Raw⇆' (mode : Mode) (r : Raw m n) : Set where
  constructor _,_
  field
    term : Raw⇆ m n mode
    proof : eraseMode term ≡ r

Bidirectionalisation : Set
Bidirectionalisation = {m n : ℕ} (r : Raw m n)
                     → Σ[ d ∈ ℕ ] Raw⇆' Infer (mapRaw (tsub (extTSub d)) r)

-- ~ Syntax.BiTyped.Intrinsic.Term
data Typed⇆ {m : ℕ} : Ty m → {n : ℕ} → (Γ : Vec (Ty m) n) → Mode → Set where
  `_   : (i : τ V.∈ Γ) → Typed⇆ τ Γ Infer
  _∋_  : (τ : Ty m) → Typed⇆ τ Γ Check → Typed⇆ τ Γ Infer
  _∋⇆_ : (τ : Ty m) → Typed⇆ τ Γ Check → Typed⇆ τ Γ Infer
  _↑_  : Typed⇆ σ Γ Infer → σ ≡ τ → Typed⇆ τ Γ Check
  app  : Typed⇆ (imp σ τ) Γ Infer → Typed⇆ σ Γ Check → Typed⇆ τ Γ Infer
  abs  : Typed⇆ τ (σ ∷ Γ) Check → Typed⇆ (imp σ τ) Γ Check

eraseType⇆ : {Γ : Vec (Ty m) n} → Typed⇆ τ Γ mode → Raw⇆ m n mode
eraseType⇆ (` i)     = ` V.index i
eraseType⇆ (τ ∋  t)  = τ ∋  eraseType⇆ t
eraseType⇆ (τ ∋⇆ t)  = τ ∋⇆ eraseType⇆ t
eraseType⇆ (t ↑ eq)  = eraseType⇆ t ↑
eraseType⇆ (app t u) = app (eraseType⇆ t) (eraseType⇆ u)
eraseType⇆ (abs t)   = abs (eraseType⇆ t)

record Typed⇆' {m n : ℕ} (τ : Ty m) (Γ : Vec (Ty m) n)
               {mode : Mode} (r : Raw⇆ m n mode) : Set where
  constructor _,_
  field
    term : Typed⇆ τ Γ mode
    proof : eraseType⇆ term ≡ r

TypeInference⇆ : Set
TypeInference⇆ = {m n : ℕ} (Γ : Vec (Ty m) n) (r : Raw⇆ m n Infer)
               → Dec (Σ[ m' ∈ ℕ ] Σ[ τ ∈ Ty m' ] Σ[ ts ∈ TSub m m' ]
                      Typed⇆' τ (V.map (tsub ts) Γ) (mapRaw⇆ (tsub ts) r))

Soundness : Set
Soundness = ∀ {m n τ Γ mode} {r : Raw⇆ m n mode}
          → Typed⇆' τ Γ r → Typed' τ Γ (eraseMode r)

Completeness : Set
Completeness = ∀ {m n τ Γ mode} {r : Raw⇆ m n mode}
             → Typed' τ Γ (eraseMode r) → Typed⇆' τ Γ r

module Implementation (bidir : Bidirectionalisation) (inf⇆ : TypeInference⇆)
                      (soundness : Soundness) (completeness : Completeness) where

  open ≡-Reasoning

  inf : TypeInference
  inf Γ r =
    let (d , r') = bidir r
    in  map′
          (λ { (m' , τ , ts , t) →
                m' , τ , compTSub ts (extTSub d) ,
                subst₂ (Typed' τ)
                  (begin
                     V.map (tsub ts) (V.map (tsub (extTSub d)) Γ)
                       ≡⟨ sym (V.map-∘ (tsub ts) (tsub (extTSub d)) Γ) ⟩
                     V.map (tsub ts ∘ tsub (extTSub d)) Γ
                       ≡⟨ sym (V.map-cong (tsub-comp ts (extTSub d)) Γ) ⟩
                     V.map (tsub (compTSub ts (extTSub d))) Γ
                   ∎)
                  (begin
                     eraseMode (mapRaw⇆ (tsub ts) (Raw⇆'.term r'))
                       ≡⟨ eraseMode-mapRaw⇆ (tsub ts) (Raw⇆'.term r') ⟩
                     mapRaw (tsub ts) (eraseMode (Raw⇆'.term r'))
                       ≡⟨ cong (mapRaw (tsub ts)) (Raw⇆'.proof r') ⟩
                     mapRaw (tsub ts) (mapRaw (tsub (extTSub d)) r)
                       ≡⟨ sym (mapRaw-∘ (tsub ts) (tsub (extTSub d)) r) ⟩
                     mapRaw (tsub ts ∘ tsub (extTSub d)) r
                       ≡⟨ sym (mapRaw-cong (tsub-comp ts (extTSub d)) r) ⟩
                     mapRaw (tsub (compTSub ts (extTSub d))) r
                   ∎)
                  (soundness t) })
          (λ { (m' , τ , ts , t) →
                m' , τ , fillBase d ts ,
                completeness
                  (subst₂ (Typed' τ)
                     (begin
                        V.map (tsub ts) Γ
                          ≡⟨ sym (V.map-cong (λ σ → cong (flip tsub σ) (fillBase-extTSub d ts)) Γ) ⟩
                        V.map (tsub (compTSub (fillBase d ts) (extTSub d))) Γ
                          ≡⟨ V.map-cong (tsub-comp (fillBase d ts) (extTSub d)) Γ ⟩
                        V.map (tsub (fillBase d ts) ∘ tsub (extTSub d)) Γ
                          ≡⟨ V.map-∘ (tsub (fillBase d ts)) (tsub (extTSub d)) Γ ⟩
                        V.map (tsub (fillBase d ts)) (V.map (tsub (extTSub d)) Γ)
                      ∎)
                     (begin
                        mapRaw (tsub ts) r
                          ≡⟨ sym (mapRaw-cong (λ σ → cong (flip tsub σ) (fillBase-extTSub d ts)) r) ⟩
                        mapRaw (tsub (compTSub (fillBase d ts) (extTSub d))) r
                          ≡⟨ mapRaw-cong (tsub-comp (fillBase d ts) (extTSub d)) r ⟩
                        mapRaw (tsub (fillBase d ts) ∘ tsub (extTSub d)) r
                          ≡⟨ mapRaw-∘ (tsub (fillBase d ts)) (tsub (extTSub d)) r ⟩
                        mapRaw (tsub (fillBase d ts)) (mapRaw (tsub (extTSub d)) r)
                          ≡⟨ cong (mapRaw (tsub (fillBase d ts))) (sym (Raw⇆'.proof r')) ⟩
                        mapRaw (tsub (fillBase d ts)) (eraseMode (Raw⇆'.term r'))
                          ≡⟨ sym (eraseMode-mapRaw⇆ (tsub (fillBase d ts)) (Raw⇆'.term r')) ⟩
                        eraseMode (mapRaw⇆ (tsub (fillBase d ts)) (Raw⇆'.term r'))
                      ∎)
                     t) })
          (inf⇆ (V.map (tsub (extTSub d)) Γ) (Raw⇆'.term r'))

module _ where

  open Typed'EnrichedConstructors

  soundness : Soundness
  soundness ((` i)      , refl) = var' i
  soundness ((τ ∋  t)   , refl) = ann' τ (soundness (t , refl))
  soundness ((τ ∋⇆ t)   , refl) =         soundness (t , refl)
  soundness ((t ↑ refl) , refl) =         soundness (t , refl)
  soundness (app t u    , refl) = app'   (soundness (t , refl)) (soundness (u , refl))
  soundness (abs t      , refl) = abs'   (soundness (t , refl))

-- completeness : Completeness
-- completeness {r = ` i} t = {!   !}
-- completeness {r = σ ∋  r} ((τ ∋ t) , eq) = let (t' , eq') = completeness (t , {!   !})
--                                            in  (τ ∋ t') , cong₂ _∋_ {!   !} eq'
-- completeness {r = σ ∋⇆ r} (     t  , eq) = let (t' , eq') = completeness {r = r} (t , eq)
--                                            in  (_ ∋⇆ t') , {!   !}
-- completeness {r = r ↑} t = {!   !}
-- completeness {r = app r s} t = {!   !}
-- completeness {r = abs r} t = {!   !}
