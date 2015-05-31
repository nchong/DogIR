%{
open DogIR
open DogGraph
%}

%token <string> ORACLE
%token <string> EVENTSYM
%token <string> NAME
%token <int> NUM
%token LET LETEQ COMPLETE
%token BANG
%token ASSIGN OR AND EQ
%token LPAR RPAR
%token STAR PLUS MINUS
%token ATEND ATSTART COMMA SEMI
%token ASSERT IMPLIES ARROW COLON
%token LS_INIT RW_INIT
%token EOF

%left OR
%left AND
%left EQ
%left ASSIGN
%nonassoc BANG

%type <DogGraph.dog_t> main
%start main

%%

main:
| letdef_list rule_list dog_assert_list ls_init_list rw_init_list EOF { { letdefs = $1; rules = (graph_of_rule_list $2); asserts = $3; ls_inits = $4; rw_inits = $5 } }

letdef_list:
| letdef SEMI letdef_list { $1::$3 }
| letdef {[$1]}
| {[]}

letdef:
| LET EVENTSYM LETEQ eventexpr { ($2, $4) }
| LET NAME LETEQ eventexpr { ($2, $4) }

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
| NUM { ExprNum($1) }
| BANG eventexpr { ExprNot($2) }
| eventexpr OR eventexpr { ExprBool(BoolOr, $1, $3) }
| eventexpr AND eventexpr { ExprBool(BoolAnd, $1, $3) }
| eventexpr EQ eventexpr { ExprBool(BoolEq, $1, $3) }
| eventexpr ASSIGN eventexpr { ExprAssign($1, $3) }
| event { ExprEvent($1) }
| LPAR eventexpr RPAR { $2 }

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
| ATEND { AtEnd   }

star:
| STAR { Star }
| STAR PLUS { StarPlus }
| STAR MINUS { StarMinus }
| STAR BANG PLUS { StarNotPlus }
| STAR BANG MINUS { StarNotMinus }
| { StarNone }

dog_assert_list:
| dog_assert SEMI dog_assert_list { $1::$3 }
| dog_assert {[$1]}
| {[]}

dog_assert:
| ASSERT ORACLE IMPLIES ORACLE { ([$2], [$4]) }
| ASSERT LPAR and_state_list RPAR IMPLIES ORACLE { (tr_dog_assert $3 [$6]) }
| ASSERT ORACLE IMPLIES LPAR or_state_list RPAR { (tr_dog_assert [$2] $5) }
| ASSERT LPAR and_state_list RPAR IMPLIES LPAR or_state_list RPAR { (tr_dog_assert $3 $7) }

and_state_list:
| ORACLE AND and_state_list { $1::$3 }
| ORACLE {[$1]}

or_state_list:
| ORACLE OR or_state_list { $1::$3 }
| ORACLE {[$1]}

ls_init_list:
| ls_init SEMI ls_init_list { $1::$3 }
| ls_init {[$1]}
| {[]}

ls_init:
| LS_INIT COLON ORACLE { $3 }
| LS_INIT COLON NAME { $3 }

rw_init_list:
| rw_init SEMI rw_init_list { $1::$3 }
| rw_init {[$1]}
| {[]}

rw_init:
| RW_INIT COLON ORACLE { $3 }
| RW_INIT COLON NAME { $3 }
