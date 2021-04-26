module Abstract where

import Concrete as C
open C public using (_◇_; Access); open Access public
open import Library
open Dec

open import Data.Maybe
import Data.List
open Data.List using (mapMaybe)
import Data.Product

open import Data.Maybe.Instances using (maybeFunctor; maybeApplicative)
open RawApplicative {F = Maybe {Agda.Primitive.lzero}} maybeApplicative

open import Data.List.Instances using (listFunctor; listApplicative)
-- TODO can I use an overloaded <$>?
open RawApplicative {F = List {Agda.Primitive.lzero}} listApplicative renaming (_<$>_ to _[<$>]_)

variable
  x  y  : C.Name
  xs ys xs' ys' : C.QName

interleaved mutual

  -- Scope of a declaration.

  data Scope : Set
  variable
    sc sc' sc'' : Scope

  -- Declarations in a scope.

  data Decls (sc : Scope) : Set
  variable
    ds₀ ds ds' : Decls sc

  -- The name exists in scope, and is a module that defines a scope.
  -- Technically, only the Decls of the module is needed, but since it depends
  -- on the scope, it's cleaner to just pass the scope
  --
  -- no need for generalization yet: everything is a module
  data SNameM : Scope → C.QName → (sc' : Scope) → Set

  -- an interface entry defines a mapping between the exported name, and
  -- the SNameM of the internal name
  InterfaceEntry : Scope → Set
  InterfaceEntry sc = C.QName × Σ (C.QName × Scope) λ (xs , sc') → SNameM sc xs sc' -- can avoid sc' by restoring SName

  Interface : Scope → Set
  Interface sc = List (InterfaceEntry sc)

  -- A well-scoped declaration is one of
  --
  --   * A module definition.
  --   * Importing the declarations of another module via `open`.

  data Decl (sc : Scope) : Set where
    modl : (x : C.Name) (ds : Decls sc) → Decl sc
    opn : (m : SNameM sc xs sc')
        → (iface : Interface sc)
        → Decl sc

  variable
    d d' : Decl sc

  -- A scope is a snoc list of lists of declarations.

  constructor  -- Scope
    ε   : Scope
    _⦊_ : (sc : Scope) (ds : Decls sc) → Scope

  -- Lists of declarations are also given in snoc-form.

  constructor  -- Decls
    ε   : Decls sc
    _⦊_ : (ds : Decls sc) (d : Decl (sc ⦊ ds)) → Decls sc

  data DNameM : (sc : Scope) → Decl sc → C.QName → Scope → Set

  data DsNameM : (sc : Scope) → Decls sc → C.QName → Scope → Set where
    here : DNameM (sc ⦊ ds) d xs sc' → DsNameM sc (ds ⦊ d) xs sc'
    there : DsNameM sc ds xs sc' → DsNameM sc (ds ⦊ d) xs sc'

  constructor -- DNameM
    content : DNameM sc (modl x ds) (C.qName x) (sc ⦊ ds)
    inside : DsNameM sc ds xs sc' → DNameM sc (modl x ds) (C.qual x xs) sc'
    imp : ∀{iface m sn} → (xs , ((ys , sc'') , sn)) ∈ iface
        → DNameM sc (opn {sc = sc} {xs = xs'} {sc' = sc'} m iface) xs sc''

  constructor -- SNameM
    site : DsNameM sc ds xs sc' → SNameM (sc ⦊ ds) xs sc'
    parent : SNameM sc xs sc' → SNameM (sc ⦊ ds) xs sc'

-- TODO shadowing stuff with Resolution

interleaved mutual
  dlookup : (d : Decl sc) → (xs : C.QName) → Maybe (∃ λ sc' → DNameM sc d xs sc')
  dslookup : (ds : Decls sc) → (xs : C.QName) → Maybe (∃ λ sc' → DsNameM sc ds xs sc')
  slookup : (sc : Scope) → (xs : C.QName) → Maybe (∃ λ sc' → SNameM sc xs sc')
  ilookup : (iface : Interface sc)
          → (xs : C.QName)
          → Maybe ( Σ (C.QName × Scope) λ (ys , sc')
                  → Σ (SNameM sc ys sc') λ sn
                  → (xs , ((ys , sc') , sn)) ∈ iface)

  -- XXX from here until the end of the mutual block the variable names are awful

  dlookup {sc} (modl x ds) (C.qName x₁) with x C.≟ x₁
  ... | yes! = just ((sc ⦊ ds) , content)
  ... | no ¬p = nothing
  dlookup (modl x ds) (C.qual x₁ xs) with x C.≟ x₁ | dslookup ds xs
  ... | yes! | just x₁ = just (proj₁ x₁ , inside (proj₂ x₁))
  ... | yes! | nothing = nothing
  ... | no ¬p | _ = nothing
  dlookup {sc} (opn m iface) xs with ilookup iface xs
  ... | just ((qn , sc') , sn , stuff∈iface) = just (sc' , imp stuff∈iface)
  ... | nothing = nothing

  dslookup ε xs = nothing
  dslookup (ds ⦊ d) xs with dlookup d xs | dslookup ds xs
  ... | just (fst , snd) | _ = just (fst , here snd)
  ... | nothing | just x = just (proj₁ x , there (proj₂ x))
  ... | nothing | nothing = nothing

  slookup ε xs = nothing
  slookup (sc ⦊ ds) xs with dslookup ds xs | slookup sc xs
  ... | just (fst , snd) | _ = just (fst , site snd)
  ... | nothing | just (fst , snd) = just (fst , parent snd)
  ... | nothing | nothing = nothing

  ilookup [] xs = nothing
  ilookup ((qn , (qn1,sc , sn)) ∷ iface) xs with xs C.≟q qn | ilookup iface xs
  ... | yes p | r2 = just ((proj₁ qn1,sc , proj₂ qn1,sc) , (sn , here (cong₂ _,_ p refl)))
  ... | no ¬p | just ((fst , snd) , fst₁ , snd₁) = just ((fst , snd) , (fst₁ , there snd₁))
  ... | no ¬p | nothing = nothing

interleaved mutual
  slookupAll1 : (sc : Scope) → List (Σ (C.QName × Scope) λ (xs , sc') → SNameM sc xs sc')
  dslookupAll : (sc : Scope) → (ds : Decls sc) → List (Σ (C.QName × Scope) λ (xs , sc') → DsNameM sc ds xs sc')
  dlookupAll : (sc : Scope) → (d : Decl sc) → List (Σ (C.QName × Scope) λ (xs , sc') → DNameM sc d xs sc')
  ilookupAll : (iface : Interface sc)
             → List (∃ λ xs → ( Σ (C.QName × Scope) λ (ys , sc')
                              → Σ (SNameM sc ys sc') λ sn
                              → (xs , ((ys , sc') , sn)) ∈ iface))

  slookupAll1 ε = []
  -- We only need the direct contents of the module so we only look at the first level.
  -- TODO: do we also need a slookupAll that looks at all the levels?
  slookupAll1 (sc ⦊ ds) = Data.Product.map₂ site [<$>] dslookupAll sc ds

  dslookupAll sc ε = []
  dslookupAll sc (ds ⦊ d) =
    (Data.Product.map₂ here [<$>] dlookupAll (sc ⦊ ds) d) ++
    (Data.Product.map₂ there [<$>] dslookupAll sc ds)

  dlookupAll sc (modl x ds) =
    Data.Product.map (Data.Product.map₁ (C.qual x)) inside [<$>] dslookupAll sc ds
  dlookupAll sc (opn m iface) =
    -- TODO This is a bit of a mess. Same with ilookupEntry.
    --      Is it possible to clean it up a bit by restructuring the sigmas?
    (λ (xs , ((ys , sc') , (sn , entry∈iface))) →
      ((xs , sc') , imp entry∈iface)
    )
    [<$>] ilookupAll iface

  ilookupEntry : ∀{sc iface} → {entry : InterfaceEntry sc} → entry ∈ iface
               → (∃ λ xs → ( Σ (C.QName × Scope) λ (ys , sc')
                           → Σ (SNameM sc ys sc') λ sn
                           → (xs , ((ys , sc') , sn)) ∈ iface))
  ilookupEntry {sc} {iface} {xs , ys,sc' , sn} entry∈iface = xs , (ys,sc' , (sn , entry∈iface))

  ilookupAll iface = mapWith∈ iface ilookupEntry

-- Get from the ImportDirective the name we (may) open some value as
-- considering renaming, using, hiding
assignExportedName : C.ImportDirective
                   → (Σ (C.QName × Scope) λ (ys , sc') → SNameM sc ys sc')
                   → Maybe (InterfaceEntry sc)
-- TODO oops... ImportDirective here is just private/public... we don't have hiding/using/renaming!
-- ...so for now we just export everything as is
assignExportedName dir ((ys , sc') , sn) = just (ys , ((ys , sc') , sn))

interleaved mutual
  checkDecl : (sc : Scope) → C.Decl → Maybe (Decl sc)
  checkDecls : (sc : Scope) → C.Decls → Maybe (Decls sc)

  checkDecl sc (C.modl x d) = modl x <$> checkDecls sc d
  checkDecl sc (C.opn q i)
    with slookup sc q | mapMaybe (assignExportedName i) (slookupAll1 sc)
  ... | just (modSc , modSn) | iface = just (opn modSn iface)
  ... | nothing | iface = nothing
  checkDecl sc (C.priv d) = nothing -- TODO private blocks

  checkDecls sc C.dNil = just ε
  checkDecls sc (C.dSnoc ds d) with checkDecls sc ds
  ... | nothing = nothing
  ... | just ds' with checkDecl (sc ⦊ ds') d
  ... | just d' = just (ds' ⦊ d')
  ... | _ = nothing

data Program : Set where
  prg : C.Name → Decls sc → Program

checkProgram : C.Program → Maybe Program
checkProgram (C.prg x ds) = prg x <$> checkDecls ε ds
