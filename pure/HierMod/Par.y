-- This Happy file was machine-generated by the BNF converter
{
{-# OPTIONS_GHC -fno-warn-incomplete-patterns -fno-warn-overlapping-patterns #-}
module HierMod.Par where
import HierMod.Abs
import HierMod.Lex
import HierMod.ErrM

}

%name pProgram Program
%name pDecl Decl
%name pListDecl ListDecl
%name pListName ListName
-- no lexer declaration
%monad { Err } { thenM } { returnM }
%tokentype {Token}
%token
  '.' { PT _ (TS _ 1) }
  ';' { PT _ (TS _ 2) }
  'module' { PT _ (TS _ 3) }
  'open' { PT _ (TS _ 4) }
  'private' { PT _ (TS _ 5) }
  'public' { PT _ (TS _ 6) }
  'where' { PT _ (TS _ 7) }
  '{' { PT _ (TS _ 8) }
  '}' { PT _ (TS _ 9) }
  L_Name { PT _ (T_Name $$) }

%%

Name :: { Name}
Name  : L_Name { Name ($1)}

Program :: { Program }
Program : 'module' Name 'where' '{' ListDecl '}' { HierMod.Abs.Prg $2 $5 }
Decl :: { Decl }
Decl : 'module' Name 'where' '{' ListDecl '}' { HierMod.Abs.Modl $2 $5 }
     | 'private' 'module' Name 'where' '{' ListDecl '}' { HierMod.Abs.PrivateModl $3 $6 }
     | 'open' ListName { HierMod.Abs.Open $2 }
     | 'open' ListName 'public' { HierMod.Abs.OpenPublic $2 }
ListDecl :: { [Decl] }
ListDecl : {- empty -} { [] }
         | Decl { (:[]) $1 }
         | Decl ';' ListDecl { (:) $1 $3 }
ListName :: { [Name] }
ListName : Name { (:[]) $1 } | Name '.' ListName { (:) $1 $3 }
{

returnM :: a -> Err a
returnM = return

thenM :: Err a -> (a -> Err b) -> Err b
thenM = (>>=)

happyError :: [Token] -> Err a
happyError ts =
  Bad $ "syntax error at " ++ tokenPos ts ++
  case ts of
    []      -> []
    [Err _] -> " due to lexer error"
    t:_     -> " before `" ++ id(prToken t) ++ "'"

myLexer = tokens
}

