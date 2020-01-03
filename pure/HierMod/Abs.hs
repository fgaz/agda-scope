-- Haskell data types for the abstract syntax.
-- Generated by the BNF converter.

{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module HierMod.Abs where

import Prelude (Char, Double, Integer, String)
import qualified Prelude as C (Eq, Ord, Show, Read)
import qualified Data.String

newtype Name = Name String
  deriving (C.Eq, C.Ord, C.Show, C.Read, Data.String.IsString)

data Program = Prg Name [Decl]
  deriving (C.Eq, C.Ord, C.Show, C.Read)

data Decl
    = Modl Name [Decl]
    | PrivateModl Name [Decl]
    | Open [Name]
    | OpenPublic [Name]
  deriving (C.Eq, C.Ord, C.Show, C.Read)

