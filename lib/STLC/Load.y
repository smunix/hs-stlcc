{
module STLC.Load where

import STLC.Def qualified as Def
import STLC.Term qualified as Term
import STLC.Tok (Tok (..))
import STLC.Tok qualified as Tok
import STLC.Type qualified as Ty
import Util.Happy qualified as Happy
import Util
}

%name stlc
%tokentype { Tok }
%error { parseError }
%monad { Happy.P }
%lexer { Happy.span Tok.step } { Tok.EoF }

%token
      type            { TType }
      mu              { TMuT }
      exists          { TEx }
      extern          { TExtern }
      from            { TFrom }
      let             { TLet }
      in              { TIn }
      case            { TCase }
      of              { TOf }
      roll            { TRoll }
      unroll          { TUnroll }
      pack            { TPack }
      as              { TAs }
      unpack          { TUnpack }
      new             { TNew }
      int             { TInt $$ }
      sym             { TSym $$ }
      str             { TStr $$ }
      unit            { TUnit }
      hasty           { THasTy }
      '->'            { TFnArrow }
      ':'             { TColon }
      ';'             { TSemiColon }
      '.'             { TDot }
      '='             { TEqual }
      '('             { TLParen }
      ')'             { TRParen }
      '<'             { TLT }
      '>'             { TGT }
      '|'             { TBar }
      '['             { TLBracket }
      ']'             { TRBracket }
      '{'             { TLBrace }
      '}'             { TRBrace }
      ','             { TComma }
      '+'             { TPlus }
      '-'             { TMinus }
%%

Pgm : Pgm Def { $2 : $1 }
    | {- nothing -} { [] }

Def : sym hasty Type '=' Term ';' {% Happy.reduce 6 \spn -> Def.Named (MkNote spn ($1, Empty, $3, $5))}
    | sym hasty Type FnDef '=' Term ';' {% Happy.reduce 7 \spn -> if $1 == (view _1 $4) then Def.Named (MkNote spn ($1, inv (view _2 $4), $3, $6)) else error $ unwords ["found different names in definition of ", $1, " vs ", (view _1 $4) ] }
    | extern sym hasty Type ';' {% Happy.reduce 5 \spn -> Def.Extrn (MkNote spn ($2, $4)) }
    | type sym '=' Type ';' {% Happy.reduce 5 \spn -> Def.Alias (MkNote spn ($2, $4)) }

FnDef : sym '(' Args ')' {% Happy.reduce 4 \spn -> ($1, $3) }

Args : Args ',' sym {% Happy.reduce 3 \spn -> $3 :< $1 }
     | sym {% Happy.reduce 1 \spn -> [$1] }

Type : PType '->' PType {% Happy.reduce 3 \spn -> Ty.Fun spn [$1] $3 }
     | '(' TyArgs ')' '->' Type {% Happy.reduce 5 \spn -> Ty.Fun spn (inv $2) $5 }
     | PType {% Happy.reduce 1 \spn -> $1 }

TyArgs : TyArgs ',' Type {% Happy.reduce 3 \spn -> $3 :< $1 }
       | Type {% Happy.reduce 1 \spn -> [$1] }

PType : sym {% Happy.reduce 1 \spn -> case Ty.prim spn $1 of Just ty -> ty; Empty -> Ty.Var spn $1 }
      | '<' Row '>' {% Happy.reduce 3 \spn -> Ty.Variant spn (inv $2) }
      | '{' Row '}' {% Happy.reduce 3 \spn -> Ty.Record spn (inv $2) }
      | exists sym '.' Type {% Happy.reduce 4 \spn -> Ty.Exists spn $2 $4 }
      | '[' Type ']' {% Happy.reduce 3 \spn -> Ty.Array spn $2 }
      | mu sym '.' Type {% Happy.reduce 4 \spn -> Ty.Mu spn $2 $4 }

Row : Row ',' RowE {% Happy.reduce 3 \spn -> $3 :< $1 }
    | RowE {% Happy.reduce 1 \spn -> [$1] }

RowE : sym ':' Type {% Happy.reduce 3 \spn -> ($1, $3) }

Term : PTerm '(' TermArgs ')' {% Happy.reduce 4 \spn -> Term.App spn $1 (inv $3) }

TermArgs : TermArgs ',' Term {% Happy.reduce 3 \spn -> $3 :< $1 }
         | Term {% Happy.reduce 1 \spn -> [$1] }

PTerm : sym {% Happy.reduce 1 \spn -> Term.Var spn $1 }

{
parseError :: Tok -> Happy.P a
parseError = undefined
}
