-- -*- haskell -*-
-- This Alex file was machine-generated by the BNF converter
{
{-# OPTIONS -fno-warn-incomplete-patterns #-}
{-# OPTIONS_GHC -w #-}
module HierMod.Lex where

import qualified Data.Text
import qualified Data.Bits
import Data.Word (Word8)
import Data.Char (ord)
}


$c = [A-Z\192-\221] # [\215]  -- capital isolatin1 letter (215 = \times) FIXME
$s = [a-z\222-\255] # [\247]  -- small   isolatin1 letter (247 = \div  ) FIXME
$l = [$c $s]         -- letter
$d = [0-9]           -- digit
$i = [$l $d _ ']     -- identifier character
$u = [. \n]          -- universal: any character

@rsyms =    -- symbols and non-identifier-like reserved words
   \{ | \} | \( | \) | \; | \.

:-
"--" [.]* ; -- Toss single line comments
"{-" ([$u # \-] | \-+ [$u # [\- \}]])* ("-")+ "}" ;

$white+ ;
@rsyms
    { tok (\p s -> PT p (eitherResIdent (TV . share) s)) }
($u # [\- \( \) \{ \} \; \. \@ \" \  \n \r \t \f]) +
    { tok (\p s -> PT p (eitherResIdent (T_Name . share) s)) }

$l $i*
    { tok (\p s -> PT p (eitherResIdent (TV . share) s)) }





{

tok :: (Posn -> Data.Text.Text -> Token) -> (Posn -> Data.Text.Text -> Token)
tok f p s = f p s

share :: Data.Text.Text -> Data.Text.Text
share = id

data Tok =
   TS !Data.Text.Text !Int    -- reserved words and symbols
 | TL !Data.Text.Text         -- string literals
 | TI !Data.Text.Text         -- integer literals
 | TV !Data.Text.Text         -- identifiers
 | TD !Data.Text.Text         -- double precision float literals
 | TC !Data.Text.Text         -- character literals
 | T_Name !Data.Text.Text

 deriving (Eq,Show,Ord)

data Token =
   PT  Posn Tok
 | Err Posn
  deriving (Eq,Show,Ord)

printPosn :: Posn -> String
printPosn (Pn _ l c) = "line " ++ show l ++ ", column " ++ show c

tokenPos :: [Token] -> String
tokenPos (t:_) = printPosn (tokenPosn t)
tokenPos [] = "end of file"

tokenPosn :: Token -> Posn
tokenPosn (PT p _) = p
tokenPosn (Err p) = p

tokenLineCol :: Token -> (Int, Int)
tokenLineCol = posLineCol . tokenPosn

posLineCol :: Posn -> (Int, Int)
posLineCol (Pn _ l c) = (l,c)

mkPosToken :: Token -> ((Int, Int), String)
mkPosToken t@(PT p _) = (posLineCol p, prToken t)

prToken :: Token -> String
prToken t = case t of
  PT _ (TS s _) -> Data.Text.unpack s
  PT _ (TL s)   -> show s
  PT _ (TI s)   -> Data.Text.unpack s
  PT _ (TV s)   -> Data.Text.unpack s
  PT _ (TD s)   -> Data.Text.unpack s
  PT _ (TC s)   -> Data.Text.unpack s
  Err _         -> "#error"
  PT _ (T_Name s) -> Data.Text.unpack s


data BTree = N | B Data.Text.Text Tok BTree BTree deriving (Show)

eitherResIdent :: (Data.Text.Text -> Tok) -> Data.Text.Text -> Tok
eitherResIdent tv s = treeFind resWords
  where
  treeFind N = tv s
  treeFind (B a t left right) | s < a  = treeFind left
                              | s > a  = treeFind right
                              | s == a = t

resWords :: BTree
resWords = b "open" 6 (b "." 3 (b ")" 2 (b "(" 1 N N) N) (b "module" 5 (b ";" 4 N N) N)) (b "{" 9 (b "where" 8 (b "using" 7 N N) N) (b "}" 10 N N))
   where b s n = let bs = Data.Text.pack s
                  in B bs (TS bs n)

unescapeInitTail :: Data.Text.Text -> Data.Text.Text
unescapeInitTail = Data.Text.pack . unesc . tail . Data.Text.unpack where
  unesc s = case s of
    '\\':c:cs | elem c ['\"', '\\', '\''] -> c : unesc cs
    '\\':'n':cs  -> '\n' : unesc cs
    '\\':'t':cs  -> '\t' : unesc cs
    '\\':'r':cs  -> '\r' : unesc cs
    '\\':'f':cs  -> '\f' : unesc cs
    '"':[]    -> []
    c:cs      -> c : unesc cs
    _         -> []

-------------------------------------------------------------------
-- Alex wrapper code.
-- A modified "posn" wrapper.
-------------------------------------------------------------------

data Posn = Pn !Int !Int !Int
      deriving (Eq, Show,Ord)

alexStartPos :: Posn
alexStartPos = Pn 0 1 1

alexMove :: Posn -> Char -> Posn
alexMove (Pn a l c) '\t' = Pn (a+1)  l     (((c+7) `div` 8)*8+1)
alexMove (Pn a l c) '\n' = Pn (a+1) (l+1)   1
alexMove (Pn a l c) _    = Pn (a+1)  l     (c+1)

type Byte = Word8

type AlexInput = (Posn,     -- current position,
                  Char,     -- previous char
                  [Byte],   -- pending bytes on the current char
                  Data.Text.Text)   -- current input string

tokens :: Data.Text.Text -> [Token]
tokens str = go (alexStartPos, '\n', [], str)
    where
      go :: AlexInput -> [Token]
      go inp@(pos, _, _, str) =
               case alexScan inp 0 of
                AlexEOF                   -> []
                AlexError (pos, _, _, _)  -> [Err pos]
                AlexSkip  inp' len        -> go inp'
                AlexToken inp' len act    -> act pos (Data.Text.take len str) : (go inp')

alexGetByte :: AlexInput -> Maybe (Byte,AlexInput)
alexGetByte (p, c, (b:bs), s) = Just (b, (p, c, bs, s))
alexGetByte (p, _, [], s) =
  case Data.Text.uncons s of
    Nothing  -> Nothing
    Just (c,s) ->
             let p'     = alexMove p c
                 (b:bs) = utf8Encode c
              in p' `seq` Just (b, (p', c, bs, s))

alexInputPrevChar :: AlexInput -> Char
alexInputPrevChar (p, c, bs, s) = c

-- | Encode a Haskell String to a list of Word8 values, in UTF8 format.
utf8Encode :: Char -> [Word8]
utf8Encode = map fromIntegral . go . ord
 where
  go oc
   | oc <= 0x7f       = [oc]

   | oc <= 0x7ff      = [ 0xc0 + (oc `Data.Bits.shiftR` 6)
                        , 0x80 + oc Data.Bits..&. 0x3f
                        ]

   | oc <= 0xffff     = [ 0xe0 + (oc `Data.Bits.shiftR` 12)
                        , 0x80 + ((oc `Data.Bits.shiftR` 6) Data.Bits..&. 0x3f)
                        , 0x80 + oc Data.Bits..&. 0x3f
                        ]
   | otherwise        = [ 0xf0 + (oc `Data.Bits.shiftR` 18)
                        , 0x80 + ((oc `Data.Bits.shiftR` 12) Data.Bits..&. 0x3f)
                        , 0x80 + ((oc `Data.Bits.shiftR` 6) Data.Bits..&. 0x3f)
                        , 0x80 + oc Data.Bits..&. 0x3f
                        ]
}
