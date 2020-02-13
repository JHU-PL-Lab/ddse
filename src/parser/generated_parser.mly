%{
open Odefa_ast;;
open Ast;;
module List = BatList;;
%}

%token <string> IDENTIFIER
%token <int> INT_LITERAL
%token EOF
%token OPEN_BRACE
%token CLOSE_BRACE
%token OPEN_PAREN
%token CLOSE_PAREN
%token SEMICOLON
%token COMMA
%token EQUALS
%token ARROW
%token QUESTION_MARK
%token TILDE
%token COLON
%token DOT
%token KEYWORD_INPUT
%token KEYWORD_FUN
%token KEYWORD_INT
%token KEYWORD_TRUE
%token KEYWORD_FALSE
%token KEYWORD_AND
%token KEYWORD_OR
%token KEYWORD_XOR
%token KEYWORD_ANY
%token UNDERSCORE
%token PLUS
%token MINUS
%token ASTERISK
%token SLASH
%token PERCENT
%token LESS
%token LESS_EQUAL
%token EQUAL_EQUAL
%token DOUBLE_SEMICOLON

%start <Odefa_ast.Ast.expr> prog
%start <Odefa_ast.Ast.expr option> delim_expr

%%

prog:
  | expr EOF
      { $1 }
  ;

delim_expr:
  | EOF
      { None }
  | expr DOUBLE_SEMICOLON
      { Some($1) }
  | expr EOF
      { Some($1) }
  ;

expr:
  | separated_nonempty_trailing_list(SEMICOLON, clause)
      { Expr($1) }
  ;

clause:
  | variable EQUALS clause_body
      { Clause($1,$3) }
  ;

variable:
  | identifier
      { Var($1,None) }
  ;

identifier:
  | IDENTIFIER
      { Ident $1 }
  ;

clause_body:
  | value
      { Value_body($1) }
  | KEYWORD_INPUT
      { Input_body }
  | variable
      { Var_body($1) }
  | variable variable
      { Appl_body($1,$2) }
  | variable QUESTION_MARK
        OPEN_PAREN expr CLOSE_PAREN COLON
        OPEN_PAREN expr CLOSE_PAREN
      { Conditional_body($1,$4,$8) }
  | variable TILDE pattern
      { Match_body($1,$3) }
  | variable DOT identifier
      { Projection_body($1,$3) }
  | variable PLUS variable
      { Binary_operation_body($1,Binary_operator_plus,$3) }
  | variable MINUS variable
      { Binary_operation_body($1,Binary_operator_minus,$3) }
  | variable ASTERISK variable
      { Binary_operation_body($1,Binary_operator_times,$3) }
  | variable SLASH variable
      { Binary_operation_body($1,Binary_operator_divide,$3) }
  | variable PERCENT variable
      { Binary_operation_body($1,Binary_operator_modulus,$3) }
  | variable LESS variable
      { Binary_operation_body($1,Binary_operator_less_than,$3) }
  | variable LESS_EQUAL variable
      { Binary_operation_body($1,Binary_operator_less_than_or_equal_to,$3) }
  | variable EQUAL_EQUAL variable
      { Binary_operation_body($1,Binary_operator_equal_to,$3) }
  | variable KEYWORD_AND variable
      { Binary_operation_body($1,Binary_operator_and,$3) }
  | variable KEYWORD_OR variable
      { Binary_operation_body($1,Binary_operator_or,$3) }
  | variable KEYWORD_XOR variable
      { Binary_operation_body($1,Binary_operator_xor,$3) }
  ;

value:
  | record_value
      { Value_record($1) }
  | function_value
      { Value_function($1) }
  | int_value
      { Value_int($1) }
  | bool_value
      { Value_bool($1) }
  ;

record_value:
  | OPEN_BRACE CLOSE_BRACE
      { Record_value(Ident_map.empty) }
  | OPEN_BRACE separated_nonempty_trailing_list(COMMA, record_element) CLOSE_BRACE
      { Record_value(Ident_map.of_enum @@ List.enum $2) }
  ;

record_element:
  | identifier EQUALS variable
      { ($1,$3) }
  ;

function_value:
  | KEYWORD_FUN variable ARROW OPEN_PAREN expr CLOSE_PAREN
      { Function_value($2,$5) }
  ;

int_value:
  | INT_LITERAL
      { $1 }
  ;

bool_value:
  | KEYWORD_TRUE
      { true }
  | KEYWORD_FALSE
      { false }
  ;

pattern:
  | record_pattern
      { $1 }
  | KEYWORD_FUN
      { Fun_pattern }
  | KEYWORD_INT
      { Int_pattern }
  | bool_pattern
      { Bool_pattern($1) }
  | KEYWORD_ANY
      { Any_pattern }
  | UNDERSCORE
      { Any_pattern }
  ;

record_pattern:
  | OPEN_BRACE CLOSE_BRACE
      { Record_pattern(Ident_map.empty) }
  | OPEN_BRACE separated_nonempty_trailing_list(COMMA, record_pattern_element) CLOSE_BRACE
      { Record_pattern(Ident_map.of_enum @@ List.enum $2) }
  ;

record_pattern_element:
  | identifier EQUALS pattern
      { ($1,$3) }
  ;

bool_pattern:
  | KEYWORD_TRUE
      { true }
  | KEYWORD_FALSE
      { false }
  ;

separated_nonempty_trailing_list(separator, rule):
  | nonempty_list(terminated(rule, separator))
      { $1 }
  | separated_nonempty_list(separator,rule)
      { $1 }
  ;
