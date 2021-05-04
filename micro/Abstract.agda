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
open import Data.List.Instances using (listFunctor; listApplicative)
open RawApplicative {{...}}

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
  record InterfaceEntry (sc : Scope) : Set where
    inductive
    constructor interfaceEntry
    field
      exportedName : C.QName
      innerName : C.QName
      innerScope : Scope
      innerSName : SNameM sc innerName innerScope

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
    imp : ∀{iface m sn} → interfaceEntry xs ys sc'' sn ∈ iface
        → DNameM sc (opn {sc = sc} {xs = xs'} {sc' = sc'} m iface) xs sc''

  constructor -- SNameM
    site : DsNameM sc ds xs sc' → SNameM (sc ⦊ ds) xs sc'
    parent : SNameM sc xs sc' → SNameM (sc ⦊ ds) xs sc'

-- TODO shadowing stuff with Resolution

record Export (sc : Scope) (iface : Interface sc) (exportedName : C.QName) : Set where
  constructor export
  field
    innerName : C.QName
    innerScope : Scope
    innerSName : SNameM sc innerName innerScope
    inIface : interfaceEntry exportedName innerName innerScope innerSName ∈ iface

interleaved mutual
  dlookup  : (d : Decl sc) → (xs : C.QName)
           → Maybe (∃ λ sc' → DNameM sc d xs sc')
  dslookup : (ds : Decls sc) → (xs : C.QName)
           → Maybe (∃ λ sc' → DsNameM sc ds xs sc')
  slookup  : (sc : Scope) → (xs : C.QName)
           → Maybe (∃ λ sc' → SNameM sc xs sc')
  ilookup  : (iface : Interface sc) → (xs : C.QName)
           → Maybe (Export sc iface xs)

  dlookup {sc} (modl x ds) (C.qName x') with x C.≟ x'
  ... | yes! = just ((sc ⦊ ds) , content)
  ... | no ¬p = nothing
  dlookup (modl x ds) (C.qual x' xs) with x C.≟ x' | dslookup ds xs
  ... | yes! | just (sc , dsName) = just (sc , inside dsName)
  ... | yes! | nothing = nothing
  ... | no ¬p | _ = nothing
  dlookup (opn m iface) xs with ilookup iface xs
  ... | just (export ys sc sName entry∈iface) = just (sc , imp entry∈iface)
  ... | nothing = nothing

  dslookup ε xs = nothing
  dslookup (ds ⦊ d) xs with dlookup d xs | dslookup ds xs
  ... | just (sc , dName) | _ = just (sc , here dName)
  ... | nothing | just (sc , dsName) = just (sc , there dsName)
  ... | nothing | nothing = nothing

  slookup ε xs = nothing
  slookup (sc ⦊ ds) xs with dslookup ds xs | slookup sc xs
  ... | just (sc' , dsName) | _ = just (sc' , site dsName)
  ... | nothing | just (sc' , sName) = just (sc' , parent sName)
  ... | nothing | nothing = nothing

  ilookup [] xs = nothing
  ilookup (interfaceEntry xs' ys sc sn ∷ iface) xs with xs C.≟q xs' | ilookup iface xs
  ... | yes p | _ = just (export ys sc sn (here
                      (cong-app (cong-app (cong-app
                        (cong interfaceEntry p)
                        ys) sc) sn)))
  ... | no ¬p | just (export ys' sc' sn' entry∈iface) = just (export ys' sc' sn' (there entry∈iface))
  ... | no ¬p | nothing = nothing

interleaved mutual
  slookupAll1 : (sc : Scope)
              → List (Σ (C.QName × Scope) λ (xs , sc') → SNameM sc xs sc')
  dslookupAll : (sc : Scope) → (ds : Decls sc)
              → List (Σ (C.QName × Scope) λ (xs , sc') → DsNameM sc ds xs sc')
  dlookupAll  : (sc : Scope) → (d : Decl sc)
              → List (Σ (C.QName × Scope) λ (xs , sc') → DNameM sc d xs sc')
  ilookupAll  : (iface : Interface sc)
              → List (∃ λ xs → Export sc iface xs)

  slookupAll1 ε = []
  slookupAll1 (sc ⦊ ds) = Data.Product.map₂ site <$> dslookupAll sc ds

  dslookupAll sc ε = []
  dslookupAll sc (ds ⦊ d) =
    (Data.Product.map₂ here <$> dlookupAll (sc ⦊ ds) d) ++
    (Data.Product.map₂ there <$> dslookupAll sc ds)

  dlookupAll sc (modl x ds) =
    Data.Product.map (Data.Product.map₁ (C.qual x)) inside <$> dslookupAll sc ds
  dlookupAll sc (opn m iface) =
    (λ (xs , export ys sc' sn entry∈iface) → (xs , sc') , imp entry∈iface)
    <$> ilookupAll iface

  ilookupEntry : ∀{sc iface} → {entry : InterfaceEntry sc} → entry ∈ iface
               → (∃ λ xs → Export sc iface xs)
  ilookupEntry {sc} {iface} {interfaceEntry xs ys sc' sn} entry∈iface =
    xs , export ys sc' sn entry∈iface

  ilookupAll iface = mapWith∈ iface ilookupEntry

-- Get from the ImportDirective the name we (may) open some value as
-- considering renaming, using, hiding
assignExportedName : C.ImportDirective
                   → (Σ (C.QName × Scope) λ (ys , sc') → SNameM sc ys sc')
                   → Maybe (InterfaceEntry sc)
-- TODO oops... ImportDirective here is just private/public... we don't have hiding/using/renaming!
-- ...so for now we just export everything as is
assignExportedName dir ((ys , sc') , sn) = just (interfaceEntry ys ys sc' sn)

interleaved mutual
  checkDecl : (sc : Scope) → C.Decl → Maybe (Decl sc)
  checkDecls : (sc : Scope) → C.Decls → Maybe (Decls sc)

  checkDecl sc (C.modl x d) = modl x <$> checkDecls sc d
  checkDecl sc (C.opn q i)
                        -- We only need the direct contents of the module
                        -- so we only look at the first level with slookupAll1.
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
