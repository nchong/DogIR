%{
open DogIR
%}

%token <string> ORACLE
%token <string> EVENTSYM
%token <string> NAME
%token <int> NUM
%token COMPLETE
%token BANG
%token ASSIGN OR AND EQ
%token LPAR RPAR
%token STAR PLUS MINUS
%token ATEND ATSTART COMMA SEMI
%token ASSERT IMPLIES ARROW COLON
%token EOF

%type <DogIR.dog> main
%start main

%%

main:
| rule_list dog_assert_list EOF { $1, $2 }

rule_list:
| rule SEMI rule_list { $1::$3 }
| rule {[$1]}
| {[]}

rule:
| ORACLE ARROW ORACLE COLON eventexpr { ($1, $3, $5) }
| NAME ARROW NAME COLON eventexpr { ($1, $3, $5) }

eventexpr:
| EVENTSYM { ExprIdentifier($1) }
| NAME { ExprIdentifier($1) }
| ORACLE { ExprOracle(tr_oracle $1) }
| NUM { ExprNum($1) }
| BANG eventexpr { ExprNot($2) }
| LPAR eventexpr OR eventexpr RPAR { ExprBool(BoolOr, $2, $4) }
| LPAR eventexpr AND eventexpr RPAR { ExprBool(BoolAnd, $2, $4) }
| LPAR eventexpr EQ eventexpr RPAR { ExprBool(BoolEq, $2, $4) }
| LPAR eventexpr ASSIGN eventexpr RPAR { ExprAssign($2, $4) }
| event { ExprEvent($1) }

event:
| COMPLETE { EventComplete }
| EVENTSYM LPAR event_actual_list RPAR startend star { Event($1, $3, $5, $6) }

event_actual_list:
| event_actual COMMA event_actual_list {$1::$3}
| event_actual {[$1]}
| {[]}

event_actual:
| ORACLE { EventActualOracle(tr_oracle $1) }
| NAME { EventActualAttribute($1) }
| BANG event_actual { EventActualNot($2) }

startend:
| ATSTART { AtStart }
| ATEND   { AtEnd   }

star:
| STAR            { Star }
| STAR PLUS       { StarPlus }
| STAR MINUS      { StarMinus }
| STAR BANG PLUS  { StarNotPlus }
| STAR BANG MINUS { StarNotMinus }
|                 { StarNone }

dog_assert_list:
| dog_assert SEMI dog_assert_list { $1::$3 }
| dog_assert {[$1]}
| {[]}

dog_assert:
| ASSERT ORACLE IMPLIES ORACLE { ($2, $4) }
