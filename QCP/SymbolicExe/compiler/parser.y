/* References: The C89 Draft */

%define parse.error verbose

%{
  #include <stdio.h>
  #include <stdlib.h>
  #include "utils.h"
  #include "env.h"
  #include "plang.h"
  #include "parser.h"
  #include "lexer.h"
  #include "parser_driver.h"
  #define K ((void (*)(struct partial_program *, struct environment *))k)
  extern int exec_type;
  void addCustomStrategyLib(char *file,struct environment * env);
%}

%define api.pure full
%define api.push-pull push
%lex-param {struct environment *env} // actually it's redundant, because this is a push parser so yylex is called by us, not by the parser. whether a push parser really necessary is another story.
%parse-param {char *path}
             {void *k}
             {struct environment *env}

%union {
  struct {
    unsigned long long n;
    int hex;
    int u;
    int l;
  } nat;
  char *string;
  struct { } *dummy;

  struct partial_program *partial_program;
  struct pp_pretype *pretype;
  struct pp_trivtype *trivtype;
  struct pp_derivtype *derivtype;
  struct pp_type *type;
  struct pp_expr *expr;
  struct pp_expr_list *expr_list;
  struct annot *field_dec;
  struct annot_list *field_dec_list;
  struct annot *para;
  struct annot_list *para_list;
  struct pp_enum_list *enum_list;
  struct name_list *name_list;
  struct pp_simple *simple_cmd;
  struct annot_list *var_list;
  struct RAssertion *RAssertion;
  struct pp_initializer *initializer;
  struct pp_initializer_list *initializer_list;
  struct pp_designator *designator;
  struct atype *atype;
  struct kind *kind;
  struct atype_list *atype_list;
  struct lvar_list *lvar_list;
  struct term_list *term_list;
  struct pp_spec *spec;
  struct type_arg_list *type_arg;
  struct pp_varg_list *varg;
  struct StringList *string_list;
}

/* reserved */
%token <dummy> PT_EXTERN
%token <dummy> PT_STATIC
%token <dummy> PT_CONST
%token <dummy> PT_RESTRICT
%token <dummy> PT_VOLATILE
%token <dummy> PT_INLINE

%token <dummy> PT_STRUCT
%token <dummy> PT_UNION
%token <dummy> PT_ENUM
%token <dummy> PT_INT
%token <dummy> PT_VOID
%token <dummy> PT_CHAR
%token <dummy> PT_SHORT
%token <dummy> PT_UNSIGNED
%token <dummy> PT_LONG

%token <dummy> PT_IF
%token <dummy> PT_ELSE
%token <dummy> PT_WHILE
%token <dummy> PT_FOR
%token <dummy> PT_BREAK
%token <dummy> PT_CONTINUE
%token <dummy> PT_RETURN
%token <dummy> PT_DO
%token <dummy> PT_SWITCH
%token <dummy> PT_CASE
%token <dummy> PT_DEFAULT
%token <dummy> PT_SIZEOF
%token <dummy> PT_TYPEDEF

%token <dummy> PT_WITH
%token <dummy> PT_REQUIRE
%token <dummy> PT_ENSURE
%token <dummy> PT_INV
%token <dummy> PT_FORALL
%token <dummy> PT_EXISTS
%token <dummy> PT_LET
%token <dummy> PT_EMP
%token <dummy> PT___RETURN
%token <dummy> PT_ATMARK
%token <dummy> PT_DATA_AT
%token <dummy> PT_UNDEF_DATA_AT
%token <dummy> PT_FIELD_ADDR
%token <dummy> PT_ARR
%token <dummy> PT___TIME_COST
%token <dummy> PT_EXTERNCOQ
%token <dummy> PT_FIELD
%token <dummy> PT_RECORD
%token <dummy> PT_WHERE
%token <dummy> PT_WHICHIMPLIES
%token <dummy> PT_BY
%token <dummy> PT_IMPORTCOQ
%token <dummy> PT_INCLUDESTRATEGIES

%token <dummy> PT_INCLUDE
%token <nat> PT_LINEMARK

/* symbol */
%token <dummy> PT_LPAREN
%token <dummy> PT_RPAREN
%token <dummy> PT_LBRACK
%token <dummy> PT_RBRACK
%token <dummy> PT_LBRACE
%token <dummy> PT_RBRACE

%token <dummy> PT_PLUS
%token <dummy> PT_MINUS
%token <dummy> PT_STAR
%token <dummy> PT_SLASH
%token <dummy> PT_PERCENT
%token <dummy> PT_LESS
%token <dummy> PT_LESSEQ
%token <dummy> PT_GREATER
%token <dummy> PT_GREATEREQ
%token <dummy> PT_EQEQ
%token <dummy> PT_EXCLAMEQ
%token <dummy> PT_ANDAND
%token <dummy> PT_BARBAR
%token <dummy> PT_AND
%token <dummy> PT_BAR
%token <dummy> PT_CARET
%token <dummy> PT_LESSLESS
%token <dummy> PT_GREATERGREATER

%token <dummy> PT_EXCLAM
%token <dummy> PT_TLIDE

%token <dummy> PT_DOT
%token <dummy> PT_MINUSGREATER

%token <dummy> PT_EQ
%token <dummy> PT_PLUSEQ
%token <dummy> PT_MINUSEQ
%token <dummy> PT_STAREQ
%token <dummy> PT_SLASHEQ
%token <dummy> PT_PERCENTEQ
%token <dummy> PT_ANDEQ
%token <dummy> PT_BAREQ
%token <dummy> PT_CARETEQ
%token <dummy> PT_LESSLESSEQ
%token <dummy> PT_GREATERGREATEREQ
%token <dummy> PT_QUESTION

%token <dummy> PT_PLUSPLUS
%token <dummy> PT_MINUSMINUS

%token <dummy> PT_SEMI
%token <dummy> PT_COLON

%token <dummy> PT_STARSLASH
%token <dummy> PT_SLASHSTARAT
%token <dummy> PT_SLASHSLASHAT
%token <dummy> PT_SLASHSTARPROOF
%token <dummy> PT_SLASHSLASHPROOF
%token <dummy> PT_FILLININV
%token <dummy> PT_COMMA
%token <dummy> PT_EQGREATER
%token <dummy> PT_LESSEQGREATER
%token <dummy> PT_COLONCOLON
%token <dummy> PT_COLONEQ
%token <dummy> PT_ASSERT
%token <dummy> PT_NEWLINE

%token <dummy> PT_AT
%token <dummy> PT_HASH

/* literal */
%token <nat> PT_NATLIT
%token <string> PT_RAW


/* others */
%token <string> PT_TIDENT // maybe a type alias
%token <string> PT_IDENT  // everything else
%token <string> PT_STRINGLIT
%type <string> ident   // anything


/* non-terminal */
%type <partial_program> comment
%type <partial_program> inv
%type <partial_program> which_implies
%type <string_list> scope_list
%type <dummy> partial_program
%type <dummy> preprocess_cmd
%type <dummy> natlist

%type <dummy> storage_specifier
%type <dummy> type_qualifier
%type <dummy> function_specifier
%type <trivtype> declaration_specifier
%type <trivtype> field_specifier
%type <trivtype> parameter_specifier

%type <pretype> type_name
%type <trivtype> spec
%type <derivtype> abstr_decl
%type <derivtype> decl
%type <derivtype> abstr_direct
%type <derivtype> abstr_decl_except_function
%type <derivtype> abstr_direct_except_function
%type <derivtype> direct

%type <expr_list> exprs
%type <expr> expr
%type <expr> expr0
%type <type_arg> type_arg
%type <varg> varg
%type <expr> call_varg
%type <expr> call_name_varg
%type <expr> call_name_scope_varg
%type <expr> expr1
%type <expr> expr2
%type <expr> expr3
%type <expr> expr4
%type <expr> expr5
%type <expr> expr6
%type <expr> expr7
%type <expr> expr8
%type <expr> expr9
%type <expr> expr10
%type <expr> expr11
%type <expr> expr12

%type <kind> kind0
%type <kind> kind
%type <atype> atype0
%type <atype> atype1
%type <atype> atype2
%type <atype> atype
%type <name_list> ident_list_space
%type <name_list> ident_list_comma
%type <atype_list> brace_atype_list
%type <atype_list> paren_atype_list
%type <atype_list> paren_atype_list_maybe_null
%type <atype_list> brace_comma_atype_list
%type <lvar_list> comma_lvar_list
%type <lvar_list> paren_lvar_list
%type <lvar_list> semi_lvar_list
%type <term_list> term_list

%type <RAssertion> ras
%type <RAssertion> ra
%type <RAssertion> ra0_5
%type <RAssertion> ra0
%type <RAssertion> ra1
%type <RAssertion> ra2
%type <RAssertion> ra3
%type <RAssertion> ra4
%type <RAssertion> ra4_75
%type <RAssertion> ra5
%type <RAssertion> ra6
%type <RAssertion> ra7
%type <RAssertion> ra8
%type <RAssertion> ra9
%type <RAssertion> ra10
%type <RAssertion> ra11
%type <RAssertion> ra12
%type <RAssertion> ra13
%type <RAssertion> ra14
%type <RAssertion> raq
%type <RAssertion> forall_aux
%type <RAssertion> exists_aux
%type <RAssertion> tail0
%type <RAssertion> tail

%type <initializer> initializer
%type <initializer_list> initializer_list
%type <designator> designator

%type <simple_cmd> simple_cmd

%type <dummy> decls
%type <simple_cmd> for_init
%type <expr> for_cond
%type <simple_cmd> for_step

%type <field_dec> field_dec
%type <field_dec_list> field_decs

%type <enum_list> enums

%type <para> para
%type <para_list> paras
%type <spec> fun_contra
%type <spec> fun_contra_body

%type <partial_program> sepdef

%start next

%%

ident :
    PT_TIDENT
      { $$ = $1; }
  | PT_IDENT
      { $$ = $1; }
;

next :
    partial_program
  | preprocess_cmd
  | partial_program next
  | preprocess_cmd next
;

preprocess_cmd :
    PT_INCLUDE PT_STRINGLIT
      {
      if (path == NULL) {
        parse_program_path($2, k, env);
        free($2);
      } else {
        char *fpath = find_file_in_search_path(path, $2);
        free($2);
        parse_program_path(fpath, k, env);
        free(fpath);
      }
      }
  | PT_SLASHSLASHAT PT_IMPORTCOQ PT_RAW PT_NEWLINE
      { add_coq_module($3, &env->persist); }
  | PT_SLASHSTARAT PT_IMPORTCOQ PT_RAW PT_STARSLASH
      { add_coq_module($3, &env->persist); }
  | PT_SLASHSLASHAT PT_INCLUDESTRATEGIES PT_STRINGLIT PT_NEWLINE
      {
        if (exec_type) {
          free($3);
        }
        else {
          if (path == NULL) {
            addCustomStrategyLib($3, env);
            free($3);
          } else {
            char *fpath = find_file_in_same_dir(path, $3);
            free($3);
            addCustomStrategyLib(fpath, env);
            free(fpath);
          }
        }
      }
  | PT_SLASHSTARAT PT_INCLUDESTRATEGIES PT_STRINGLIT PT_STARSLASH
      {
        if (exec_type) {
          free($3);
        }
        else {
          if (path == NULL) {
            addCustomStrategyLib($3, env);
            free($3);
          } else {
            char *fpath = find_file_in_same_dir(path, $3);
            free($3);
            addCustomStrategyLib(fpath, env);
            free(fpath);
          }
        }
      }
  | PT_LINEMARK PT_STRINGLIT natlist PT_NEWLINE
      {
        free(__current_file);
        __current_file = $2;
        yyset_lineno($1.n, __current_scanner);
      }
;

natlist :
    %empty {}
  | natlist PT_NATLIT {}
;

comment :
    ra
      { $$ = PPAssert($1, NULL, 1, NULL); }
  | ra PT_ATMARK ident
      { $$ = PPAssert($1, $3, 1, NULL); }
  | PT_ASSERT ra
      { $$ = PPAssert($2, NULL, 0, NULL); }
  | PT_ASSERT ra PT_ATMARK ident
      { $$ = PPAssert($2, $4, 0, NULL); }
  | ra PT_BY scope_list
      { $$ = PPAssert($1, NULL, 1, $3); }
  | ra PT_ATMARK ident PT_BY scope_list
      { $$ = PPAssert($1, $3, 1, $5); }
  | PT_ASSERT ra PT_BY scope_list
      { $$ = PPAssert($2, NULL, 0, $4); }
  | PT_ASSERT ra PT_ATMARK ident PT_BY scope_list
      { $$ = PPAssert($2, $4, 0, $6); }
;

inv :
    PT_INV ra
      { $$ = PPInv($2, 1, NULL); }
  | PT_ASSERT PT_INV ra
      { $$ = PPInv($3, 0, NULL); }
  |  PT_INV ra PT_BY scope_list
      { $$ = PPInv($2, 1, $4); }
  | PT_ASSERT PT_INV ra PT_BY scope_list
      { $$ = PPInv($3, 0, $5); }
;

which_implies :
    ra PT_WHICHIMPLIES ra
      { $$ = PPWI($1, NULL, $3, NULL); }
  | ra PT_BY scope_list PT_WHICHIMPLIES ra
      { $$ = PPWI($1, $3, $5, NULL); }
  | ra PT_WHICHIMPLIES ra PT_BY scope_list
      { $$ = PPWI($1, NULL, $3, $5); }
  | ra PT_BY scope_list PT_WHICHIMPLIES ra PT_BY scope_list
      { $$ = PPWI($1, $3, $5, $7); }
;

scope_list:
    ident
      { $$ = StringListCons($1, StringListNil()); }
  | ident scope_list
      { $$ = StringListCons($1, $2); }
;

partial_program :
    declaration_specifier decl { K(PPFirstDecl(1, 0, PreType($1, $2), NULL), env); } PT_SEMI
      { }
  | PT_TYPEDEF parameter_specifier decl { K(PPFirstDecl(1, 1, PreType($2, $3), NULL), env); } PT_SEMI
      { }
  | declaration_specifier decl PT_EQ initializer { K(PPFirstDecl(1, 0, PreType($1, $2), $4), env); } PT_SEMI
      { }
  | declaration_specifier decl { K(PPFirstDecl(0, 0, PreType($1, $2), NULL), env); } PT_COMMA decls
      { }
  | PT_TYPEDEF parameter_specifier decl { K(PPFirstDecl(0, 1, PreType($2, $3), NULL), env); } PT_COMMA decls
      { }
  | declaration_specifier decl PT_EQ initializer { K(PPFirstDecl(0, 0, PreType($1, $2), $4), env); } PT_COMMA decls
      { }
  | simple_cmd PT_SEMI
      { K(PPSimple($1), env); }
  | PT_BREAK PT_SEMI
      { K(PPBreak(), env); }
  | PT_CONTINUE PT_SEMI
      { K(PPContinue(), env); }
  | PT_RETURN expr PT_SEMI
      { K(PPReturn($2), env); }
  | PT_RETURN PT_SEMI
      { K(PPReturn(NULL), env); }
  | PT_WHILE PT_LPAREN expr PT_RPAREN
      { K(PPWhile($3), env); }
  | PT_IF PT_LPAREN expr PT_RPAREN
      { K(PPIf($3), env); }
  | PT_ELSE
      { K(PPElse(), env); }
  | PT_DO
      { K(PPDo(), env); }
  | PT_FOR PT_LPAREN for_init for_cond for_step
      { K(PPFor($3, $4, $5), env); }
  | PT_SWITCH PT_LPAREN expr PT_RPAREN PT_LBRACE
      { K(PPSwitch($3), env); }
  | PT_CASE expr PT_COLON
      { K(PPCase($2), env); }
  | PT_DEFAULT PT_COLON
      { K(PPDefault(), env); }
  | PT_LBRACE
      { K(PPBlock(), env); }
  | PT_RBRACE
      { K(PPEnd(), env); }
  | PT_SLASHSTARAT comment PT_STARSLASH
      { K($2, env); }
  | PT_SLASHSLASHAT comment PT_NEWLINE
      { K($2, env); }
  | PT_SLASHSLASHAT inv PT_NEWLINE
      { K($2, env); }
  | PT_SLASHSTARAT inv PT_STARSLASH
      { K($2, env); }
  | PT_SLASHSTARAT which_implies PT_STARSLASH
      { K($2, env); }
  | PT_SLASHSLASHAT which_implies PT_NEWLINE
      { K($2, env); }
  | PT_SLASHSTARPROOF PT_RAW PT_STARSLASH
      { K(PPProof($2), env); }
  | PT_SLASHSLASHPROOF PT_RAW PT_NEWLINE
      { K(PPProof($2), env); }
  | PT_SLASHSTARAT PT_FILLININV PT_STARSLASH
      { K(PPMissingInv(), env); }
  | PT_SLASHSLASHAT PT_FILLININV PT_NEWLINE
      { K(PPMissingInv(), env); }
  | PT_SLASHSTARAT PT_DO ident PT_STARSLASH
      { K(PPDoStrategy($3), env); }
  | PT_SLASHSLASHAT PT_DO ident PT_NEWLINE
      { K(PPDoStrategy($3), env); }
  | PT_SLASHSLASHAT PT_EXTERNCOQ term_list PT_NEWLINE
      { K(PPCoqDec($3), env); }
  | PT_SLASHSTARAT PT_EXTERNCOQ term_list PT_STARSLASH
      { K(PPCoqDec($3), env); }
  | PT_SLASHSLASHAT PT_EXTERNCOQ paren_atype_list PT_NEWLINE
      { K(PPATypeDec($3), env); }
  | PT_SLASHSTARAT PT_EXTERNCOQ paren_atype_list PT_STARSLASH
      { K(PPATypeDec($3), env); }
  | PT_SLASHSLASHAT PT_EXTERNCOQ ident PT_COLONEQ atype PT_NEWLINE
      { K(PPCoqTypeAlias($3, $5), env); }
  | PT_SLASHSTARAT PT_EXTERNCOQ ident PT_COLONEQ atype PT_STARSLASH
      { K(PPCoqTypeAlias($3, $5), env); }
  | PT_SLASHSTARAT PT_EXTERNCOQ PT_FIELD term_list PT_STARSLASH
      { K(PPProjDec($4), env); }
  | PT_SLASHSLASHAT PT_EXTERNCOQ PT_FIELD term_list PT_NEWLINE
      { K(PPProjDec($4), env); }
  | PT_SLASHSTARAT PT_EXTERNCOQ PT_RECORD ident paren_atype_list_maybe_null PT_LBRACE semi_lvar_list PT_RBRACE PT_STARSLASH
      { K(PPRecordDec($5, $4, NULL, $7), env); }
  | PT_SLASHSLASHAT PT_EXTERNCOQ PT_RECORD ident paren_atype_list_maybe_null PT_LBRACE semi_lvar_list PT_RBRACE PT_NEWLINE
      { K(PPRecordDec($5, $4, NULL, $7), env); }
  | PT_SLASHSTARAT PT_EXTERNCOQ PT_RECORD ident paren_atype_list_maybe_null PT_EQ ident PT_LBRACE semi_lvar_list PT_RBRACE PT_STARSLASH
      { K(PPRecordDec($5, $4, $7, $9), env); }
  | PT_SLASHSLASHAT PT_EXTERNCOQ PT_RECORD ident paren_atype_list_maybe_null PT_EQ ident PT_LBRACE semi_lvar_list PT_RBRACE PT_NEWLINE
      { K(PPRecordDec($5, $4, $7, $9), env); }
  | PT_SEMI
      { K(PPSkip(), env); }
  | PT_UNION ident PT_LBRACE field_decs PT_RBRACE PT_SEMI
      { K(PPUnionDef($2, $4), env); }
  | PT_UNION ident PT_LBRACE PT_RBRACE PT_SEMI
      { K(PPUnionDef($2, NULL), env); }
  | PT_UNION ident PT_SEMI
      { K(PPUnionDec($2), env); }
  | PT_STRUCT ident PT_LBRACE field_decs PT_RBRACE PT_SEMI
      { K(PPStructDef($2, $4), env); }
  | PT_STRUCT ident PT_LBRACE PT_RBRACE PT_SEMI
      { K(PPStructDef($2, NULL), env); }
  | PT_STRUCT ident PT_SEMI
      { K(PPStructDec($2), env); }
  | PT_ENUM ident PT_LBRACE enums PT_RBRACE PT_SEMI
      { K(PPEnumDef($2, $4), env); }
  | PT_ENUM ident PT_SEMI
      { K(PPEnumDec($2), env); }
  | PT_SLASHSLASHAT sepdef PT_NEWLINE
      { K($2, env); }
  | PT_SLASHSTARAT sepdef PT_STARSLASH
      { K($2, env); }
  | declaration_specifier decl PT_LBRACE
      { K(PPFuncDef(PreType($1, $2), NULL), env); }
  | declaration_specifier decl PT_SLASHSTARAT fun_contra PT_STARSLASH PT_LBRACE
      { K(PPFuncDef(PreType($1, $2), $4), env); }
  | declaration_specifier decl PT_SLASHSTARAT fun_contra PT_STARSLASH PT_SEMI
      { K(PPFuncDec(PreType($1, $2), $4), env); }
;

/* type */
storage_specifier : PT_EXTERN | PT_STATIC;

type_qualifier : PT_CONST | PT_RESTRICT | PT_VOLATILE;

function_specifier : PT_INLINE;

declaration_specifier :
    spec
      { $$ = $1; }
  | storage_specifier declaration_specifier
      { $$ = TRIVExternOrStatic($2); }
  | type_qualifier declaration_specifier
      { $$ = $2; }
  | function_specifier declaration_specifier
      { $$ = $2; }
;

field_specifier :
    spec
      { $$ = $1; }
  | type_qualifier declaration_specifier
      { $$ = $2; }
;

parameter_specifier :
    spec
      { $$ = $1; }
  | type_qualifier declaration_specifier
      { $$ = $2; }
  | function_specifier declaration_specifier
      { $$ = $2; }
;

type_name :
    declaration_specifier
      { $$ = PreType($1, DERIVEnd(NULL)); }
  | declaration_specifier abstr_decl
      { $$ = PreType($1, $2); }
;

spec :
    PT_VOID
      { $$ = TRIVBasic(T_VOID); }
  | PT_CHAR
      { $$ = TRIVBasic(T_CHAR); }
  | PT_UNSIGNED PT_CHAR
      { $$ = TRIVBasic(T_U8); }
  | PT_SHORT
      { $$ = TRIVBasic(T_SHORT); }
  | PT_UNSIGNED PT_SHORT
      { $$ = TRIVBasic(T_U16); }
  | PT_INT
      { $$ = TRIVBasic(T_INT); }
  | PT_LONG
      { $$ = TRIVBasic(T_INT64); }
  | PT_LONG PT_LONG
      { $$ = TRIVBasic(T_INT64); }
  | PT_LONG PT_INT
      { $$ = TRIVBasic(T_INT64); }
  | PT_LONG PT_LONG PT_INT
      { $$ = TRIVBasic(T_INT64); }
  | PT_UNSIGNED
      { $$ = TRIVBasic(T_UINT); }
  | PT_UNSIGNED PT_INT
      { $$ = TRIVBasic(T_UINT); }
  | PT_UNSIGNED PT_LONG
      { $$ = TRIVBasic(T_UINT64); }
  | PT_UNSIGNED PT_LONG PT_LONG
      { $$ = TRIVBasic(T_UINT64); }
  | PT_UNSIGNED PT_LONG PT_INT
      { $$ = TRIVBasic(T_UINT64); }
  | PT_UNSIGNED PT_LONG PT_LONG PT_INT
      { $$ = TRIVBasic(T_UINT64); }
  | PT_STRUCT ident
      { $$ = TRIVStruct($2); }
  | PT_UNION ident
      { $$ = TRIVUnion($2); }
  | PT_ENUM ident
      { $$ = TRIVEnum($2); }
  | PT_STRUCT PT_LBRACE PT_RBRACE
      { $$ = TRIVAnonStruct(NULL, NULL); }
  | PT_STRUCT PT_LBRACE field_decs PT_RBRACE
      { $$ = TRIVAnonStruct(NULL, $3); }
  | PT_STRUCT ident PT_LBRACE PT_RBRACE
      { $$ = TRIVAnonStruct($2, NULL); }
  | PT_STRUCT ident PT_LBRACE field_decs PT_RBRACE
      { $$ = TRIVAnonStruct($2, $4); }
  | PT_UNION PT_LBRACE PT_RBRACE
      { $$ = TRIVAnonUnion(NULL, NULL); }
  | PT_UNION PT_LBRACE field_decs PT_RBRACE
      { $$ = TRIVAnonUnion(NULL, $3); }
  | PT_UNION ident PT_LBRACE PT_RBRACE
      { $$ = TRIVAnonUnion($2, NULL); }
  | PT_UNION ident PT_LBRACE field_decs PT_RBRACE
      { $$ = TRIVAnonUnion($2, $4); }
  | PT_ENUM PT_LBRACE enums PT_RBRACE
      { $$ = TRIVAnonEnum(NULL, $3); }
  | PT_ENUM ident PT_LBRACE enums PT_RBRACE
      { $$ = TRIVAnonEnum($2, $4); }
  | PT_TIDENT
      { $$ = TRIVTypeAlias($1); }
;

abstr_decl :
    PT_STAR abstr_decl
      { $$ = DERIVPtr($2); }
  | abstr_direct
      { $$ = $1; }
  | PT_STAR
      { $$ = DERIVPtr(DERIVEnd(NULL)); }
;

decl :
    PT_STAR decl
      { $$ = DERIVPtr($2); }
  | type_qualifier decl
      { $$ = $2; }
  | direct
      { $$ = $1; }
;

abstr_direct :
    PT_LPAREN abstr_decl PT_RPAREN
      { $$ = $2; }
  | abstr_direct PT_LBRACK expr PT_RBRACK
      { $$ = DERIVArray($1, $3); }
  | PT_LBRACK expr PT_RBRACK
      { $$ = DERIVArray(DERIVEnd(NULL), $2); }
  | abstr_direct PT_LPAREN PT_RPAREN
      { $$ = DERIVFunction($1, NULL); }
  | abstr_direct PT_LPAREN paras PT_RPAREN
      { $$ = DERIVFunction($1, $3); }
  | PT_LPAREN PT_RPAREN
      { $$ = DERIVFunction(DERIVEnd(NULL), NULL); }
  | PT_LPAREN paras PT_RPAREN
      { $$ = DERIVFunction(DERIVEnd(NULL), $2); }
;

direct :
    PT_LPAREN decl PT_RPAREN
      { $$ = $2; }
  | ident
      { $$ = DERIVEnd($1); }
  | direct PT_LBRACK expr PT_RBRACK
      { $$ = DERIVArray($1, $3); }
  | direct PT_LPAREN PT_RPAREN
      { $$ = DERIVFunction($1, NULL); }
  | direct PT_LPAREN paras PT_RPAREN
      { $$ = DERIVFunction($1, $3); }
;

abstr_decl_except_function :
    PT_STAR abstr_decl_except_function
      { $$ = DERIVPtr($2); }
  | abstr_direct_except_function
      { $$ = $1; }
  | PT_STAR
      { $$ = DERIVPtr(DERIVEnd(NULL)); }
;

abstr_direct_except_function :
    PT_LPAREN abstr_decl_except_function PT_RPAREN
      { $$ = $2; }
  | abstr_direct_except_function PT_LBRACK expr PT_RBRACK
      { $$ = DERIVArray($1, $3); }
  | PT_LBRACK expr PT_RBRACK
      { $$ = DERIVArray(DERIVEnd(NULL), $2); }
  | abstr_direct_except_function PT_LPAREN PT_RPAREN
      { $$ = DERIVFunction($1, NULL); }
  | abstr_direct_except_function PT_LPAREN paras PT_RPAREN
      { $$ = DERIVFunction($1, $3); }
;
/* type end */


/* expr */
exprs :
    expr
      { $$ = PELCons($1, PELNil()); }
  | expr PT_COMMA exprs
      { $$ = PELCons($1, $3); }
;

expr0 : 
    PT_LPAREN expr PT_RPAREN
      { $$ = $2; }
  | PT_NATLIT
      { $$ = PPConst($1.n, $1.hex, $1.l, $1.u); }
  | PT_STRINGLIT
      { $$ = PPString($1); }
  | PT_IDENT
      { $$ = PPVar($1); }
  | PT_SIZEOF PT_LPAREN type_name PT_RPAREN
      { $$ = PPSizeofType($3); }
;

type_arg :
    ident PT_EQ atype
      { $$ = ATypeArg($1, $3, NULL); }
  | ident PT_EQ atype PT_COMMA type_arg
      { $$ = ATypeArg($1, $3, $5); }
;

varg :
    ident PT_EQ ra
      { $$ = PPVArg($1, $3, NULL); }
  | ident PT_EQ ra PT_COMMA varg
      { $$ = PPVArg($1, $3, $5); }
;

call_varg :
    varg
      { $$ = PPCall(NULL, NULL, NULL, NULL, NULL, $1); }
  | PT_SEMI type_arg
      { $$ = PPCall(NULL, NULL, NULL, NULL, $2, NULL); }
  | varg PT_SEMI type_arg
      { $$ = PPCall(NULL, NULL, NULL, NULL, $3, $1); }
;

call_name_varg :
    PT_WHERE call_varg
      { $$ = $2; }
  | PT_WHERE PT_LPAREN ident PT_RPAREN call_varg
      { $5->d.CALL.vargs->spec_name = $3; $$ = $5; }
  | PT_WHERE PT_LPAREN ident PT_RPAREN
      { $$ = PPCall(NULL, NULL, $3, NULL, NULL, NULL);  }
;

call_name_scope_varg:
    call_name_varg
      { $$ = $1; }
  | call_name_varg PT_BY scope_list
      { $$ = $1; $$->d.CALL.vargs->scopes = $3; }
  | PT_BY scope_list
      { $$ = PPCall(NULL, NULL, NULL, $2, NULL, NULL); }      
;

expr1 :
    expr0
      { $$ = $1; }
  | expr1 PT_LBRACK expr PT_RBRACK
      { $$ = PPIndex($1, $3); }
  | expr1 PT_DOT ident
      { $$ = PPFieldof($1, $3); }
  | expr1 PT_MINUSGREATER ident
      { $$ = PPFieldofptr($1, $3); }
  | expr1 PT_LPAREN PT_RPAREN
      { $$ = PPCall($1, PELNil(), NULL, NULL, NULL, NULL); }
  | expr1 PT_LPAREN exprs PT_RPAREN
      { $$ = PPCall($1, $3, NULL, NULL, NULL, NULL); }
  | expr1 PT_LPAREN PT_RPAREN PT_SLASHSTARAT call_name_scope_varg PT_STARSLASH
      { $5->d.CALL.func = $1; $5->d.CALL.args = NULL; $$ = $5; }
  | expr1 PT_LPAREN exprs PT_RPAREN PT_SLASHSTARAT call_name_scope_varg PT_STARSLASH
      { $6->d.CALL.func = $1; $6->d.CALL.args = $3; $$ = $6; }
;

expr2 : 
    expr1
      { $$ = $1; }
  | PT_MINUS expr2
      { $$ = PPUnop(T_UMINUS, $2); }
  | PT_PLUS expr2
      { $$ = PPUnop(T_UPLUS, $2); }
  | PT_EXCLAM expr2
      { $$ = PPUnop(T_NOTBOOL, $2); }
  | PT_TLIDE expr2
      { $$ = PPUnop(T_NOTINT, $2); }
  | PT_STAR expr2
      { $$ = PPDeref($2); }
  | PT_AND expr2
      { $$ = PPAddress($2); }
  | PT_LPAREN type_name PT_RPAREN expr2
      { $$ = PPCast($2, $4); }
;

expr3 :
    expr2
      { $$ = $1; }
  | expr3 PT_STAR expr2
      { $$ = PPBinop(T_MUL, $1, $3); }
  | expr3 PT_SLASH expr2
      { $$ = PPBinop(T_DIV, $1, $3); }
  | expr3 PT_PERCENT expr2
      { $$ = PPBinop(T_MOD, $1, $3); }
;

expr4 :
    expr3
      { $$ = $1; }
  | expr4 PT_PLUS expr3
      { $$ = PPBinop(T_PLUS, $1, $3); }
  | expr4 PT_MINUS expr3
      { $$ = PPBinop(T_MINUS, $1, $3); }
;

expr5 :
    expr4
      { $$ = $1; }
  | expr5 PT_LESSLESS expr4
      { $$ = PPBinop(T_SHL, $1, $3); }
  | expr5 PT_GREATERGREATER expr4
      { $$ = PPBinop(T_SHR, $1, $3); }
;

expr6 :
    expr5
      { $$ = $1; }
  | expr6 PT_LESS expr5
      { $$ = PPBinop(T_LT, $1, $3); }
  | expr6 PT_GREATER expr5
      { $$ = PPBinop(T_GT, $1, $3); }
  | expr6 PT_LESSEQ expr5
      { $$ = PPBinop(T_LE, $1, $3); }
  | expr6 PT_GREATEREQ expr5
      { $$ = PPBinop(T_GE, $1, $3); }
;

expr7 :
    expr6
      { $$ = $1; }
  | expr7 PT_EQEQ expr6
      { $$ = PPBinop(T_EQ, $1, $3); }
  | expr7 PT_EXCLAMEQ expr6
      { $$ = PPBinop(T_NE, $1, $3); }
;

expr8 :
    expr7
      { $$ = $1; }
  | expr8 PT_AND expr7
      { $$ = PPBinop(T_BAND, $1, $3); }
;

expr9 :
    expr8
      { $$ = $1; }
  | expr9 PT_CARET expr8
      { $$ = PPBinop(T_XOR, $1, $3); }
;

expr10 :
    expr9
      { $$ = $1; }
  | expr10 PT_BAR expr9
      { $$ = PPBinop(T_BOR, $1, $3); }
;

expr11 :
    expr10
      { $$ = $1; }
  | expr11 PT_ANDAND expr10
      { $$ = PPBinop(T_AND, $1, $3); }
;

expr12 :
    expr11
      { $$ = $1; }
  | expr12 PT_BARBAR expr11
      { $$ = PPBinop(T_OR, $1, $3); }
;

expr :
    expr12
      { $$ = $1; }
  | expr12 PT_QUESTION expr PT_COLON expr
      { $$ = PPCondition($1, $3, $5); }
;
/* expr end */


/* type system */

kind0 :
    PT_STAR
      { $$ = KStar(); }
  | PT_LPAREN kind PT_RPAREN
      { $$ = $2; }
;

kind :
    kind0
      { $$ = $1; }
  | kind0 PT_EQGREATER kind
      { $$ = KArrow($1, $3); }
;

atype0 :
    ident
      { $$ = ATTVar($1, NULL); }
  | PT_LPAREN atype PT_RPAREN
      { $$ = $2; }
;

atype1 :
    atype0
      { $$ = $1; }
  | atype1 atype0
      { $$ = ATApp($1, $2); }
;

atype2 :
    atype1
      { $$ = $1; }
  | atype2 PT_STAR atype1
      { $$ = ATApp(ATApp(ATTVar(clone_str("prod"), NULL), $1), $3); }
;

atype :
    atype2
      { $$ = $1; }
  | atype2 PT_MINUSGREATER atype
      { $$ = ATArrow($1, $3); }
;

ident_list_space:
    ident
      { $$ = NLCons($1, NULL); }
  | ident ident_list_space
      { $$ = NLCons($1, $2); }
;

ident_list_comma:
    ident
      { $$ = NLCons($1, NULL); }
  | ident PT_COMMA ident_list_comma
      { $$ = NLCons($1, $3); }
;

brace_atype_list :
    PT_LBRACE ident_list_space PT_COLONCOLON kind PT_RBRACE
      { $$ = atype_list_cons_multi($2, $4, NULL); }
  | PT_LBRACE ident_list_space PT_COLONCOLON kind PT_RBRACE brace_atype_list
      { $$ = atype_list_cons_multi($2, $4, $6); }
  | PT_LBRACE ident_list_space PT_RBRACE
      { $$ = atype_list_cons_multi($2, NULL, NULL); }
  | PT_LBRACE ident_list_space PT_RBRACE brace_atype_list
      { $$ = atype_list_cons_multi($2, NULL, $4); }
;

paren_atype_list :
    PT_LPAREN ident_list_space PT_COLONCOLON kind PT_RPAREN
      { $$ = atype_list_cons_multi($2, $4, NULL); }
  | PT_LPAREN ident_list_space PT_COLONCOLON kind PT_RPAREN paren_atype_list
      { $$ = atype_list_cons_multi($2, $4, $6); }
;

paren_atype_list_maybe_null :
   %empty
      { $$ = NULL; }
  | ident paren_atype_list_maybe_null
      { $$ = atype_list_cons($1, NULL, $2); }
  | PT_LPAREN ident_list_space PT_COLONCOLON kind PT_RPAREN paren_atype_list_maybe_null
      { $$ = atype_list_cons_multi($2, $4, $6); }
;

brace_comma_atype_list :
    PT_LBRACE ident_list_comma PT_COLONCOLON kind PT_RBRACE
      { $$ = atype_list_cons_multi($2, $4, NULL); }
  | PT_LBRACE ident_list_comma PT_COLONCOLON kind PT_RBRACE PT_COMMA brace_comma_atype_list
      { $$ = atype_list_cons_multi($2, $4, $7); }
  | PT_LBRACE ident_list_comma PT_RBRACE
      { $$ = atype_list_cons_multi($2, NULL, NULL); }
  | PT_LBRACE ident_list_comma PT_RBRACE PT_COMMA brace_comma_atype_list
      { $$ = atype_list_cons_multi($2, NULL, $5); }
;

comma_lvar_list :
    ident
      { $$ = lvar_list_cons($1, NULL, NULL); }
  | ident PT_COLON atype
      { $$ = lvar_list_cons_multi(NLCons($1, NULL), $3, NULL); }
  | ident PT_COMMA comma_lvar_list
      { $$ = lvar_list_cons($1, NULL, $3); }
  | ident PT_COLON atype PT_COMMA comma_lvar_list
      { $$ = lvar_list_cons_multi(NLCons($1, NULL), $3, $5); }
;

paren_lvar_list :
    ident
      { $$ = lvar_list_cons($1, NULL, NULL); }
  | PT_LPAREN ident_list_space PT_COLON atype PT_RPAREN
      { $$ = lvar_list_cons_multi($2, $4, NULL); }
  | ident paren_lvar_list
      { $$ = lvar_list_cons($1, NULL, $2); }
  | PT_LPAREN ident_list_space PT_COLON atype PT_RPAREN paren_lvar_list
      { $$ = lvar_list_cons_multi($2, $4, $6); }
;

semi_lvar_list :
    ident PT_COLON atype PT_SEMI
      { $$ = lvar_list_cons($1, $3, NULL); }
  | ident PT_COLON atype PT_SEMI semi_lvar_list
      { $$ = lvar_list_cons($1, $3, $5); }
;

term_list :
    ident
      { $$ = term_list_cons($1, NULL, NULL, NULL); }
  | PT_LPAREN ident_list_space PT_COLON atype PT_RPAREN
      { $$ = term_list_cons_multi($2, NULL, $4, NULL); }
  | PT_LPAREN ident_list_space PT_COLON brace_atype_list PT_MINUSGREATER atype PT_RPAREN
      { $$ = term_list_cons_multi($2, $4, $6, NULL); }
  | ident term_list
      { $$ = term_list_cons($1, NULL, NULL, $2); }
  | PT_LPAREN ident_list_space PT_COLON atype PT_RPAREN term_list
      { $$ = term_list_cons_multi($2, NULL, $4, $6); }
  | PT_LPAREN ident_list_space PT_COLON brace_atype_list PT_MINUSGREATER atype PT_RPAREN term_list
      { $$ = term_list_cons_multi($2, $4, $6, $8); }
;

/* type system end */


/* RA. similar to expr */
ra0_5 :
    PT_IDENT
      { $$ = RAVar($1); }
  | PT_HASH ra0_5
      { $$ = RAShadow($2); }
;

ra0 :
    ra0_5
      { $$ = $1; }
  | PT_LPAREN ra PT_RPAREN
      { $$ = $2; }
  | PT___TIME_COST
      { $$ = RATimeCost(); }
  | PT_NATLIT
      { $$ = RAConst($1.n); }
  | PT_DATA_AT PT_LPAREN ra PT_COMMA ra PT_RPAREN
      { $$ = RAData_at(NULL, $3, $5); }
  | PT_DATA_AT PT_LPAREN ra PT_COMMA type_name PT_COMMA ra PT_RPAREN
      { $$ = RAData_at($5, $3, $7); }
  | PT_UNDEF_DATA_AT PT_LPAREN ra PT_RPAREN
      { $$ = RAUndef_data_at(NULL, $3); }
  | PT_UNDEF_DATA_AT PT_LPAREN ra PT_COMMA type_name PT_RPAREN
      { $$ = RAUndef_data_at($5, $3); }
  | PT_FIELD_ADDR PT_LPAREN ra PT_COMMA ident PT_RPAREN
      { $$ = RAField_addr($3, NULL, $5); }
  | PT_FIELD_ADDR PT_LPAREN ra PT_COMMA type_name PT_COMMA ident PT_RPAREN
      { $$ = RAField_addr($3, $5, $7); }
  | PT_FIELD_ADDR PT_LPAREN ra PT_COMMA PT_IDENT PT_COMMA ident PT_RPAREN
      { $$ = RAField_addr($3, PreType(TRIVTypeAlias($5), DERIVEnd(NULL)), $7); }
  | PT_ARR PT_LPAREN ra PT_COMMA ra PT_COMMA ra PT_RPAREN
      { $$ = RAArr($3, NULL, $5, $7); }
  | PT_ARR PT_LPAREN ra PT_COMMA type_name PT_COMMA ra PT_COMMA ra PT_RPAREN
      { $$ = RAArr($3, $5, $7, $9); }
  | PT_EMP
      { $$ = RAEmp(); }
  | PT___RETURN
      { $$ = RA__return(); }
  | PT_SIZEOF PT_LPAREN type_name PT_RPAREN
      { $$ = RASizeOf($3); }
;

ra1 :
    ra0
      { $$ = $1; }
  | ra1 PT_LBRACK ra PT_RBRACK
      { $$ = RAIndex($1, $3); }
  | ra1 PT_DOT PT_LBRACE type_name PT_DOT ident PT_RBRACE
      { $$ = RAFieldof($1, $6, $4); }
  | ra1 PT_DOT PT_LBRACE PT_IDENT PT_DOT ident PT_RBRACE
      { $$ = RAFieldof($1, $6, PreType(TRIVTypeAlias($4), DERIVEnd(NULL))); }
  | ra1 PT_MINUSGREATER PT_LBRACE type_name PT_DOT ident PT_RBRACE
      { $$ = RAFieldofptr($1, $6, $4); }
  | ra1 PT_MINUSGREATER PT_LBRACE PT_IDENT PT_DOT ident PT_RBRACE
      { $$ = RAFieldofptr($1, $6, PreType(TRIVTypeAlias($4), DERIVEnd(NULL))); }
  | ra1 PT_DOT ident
      { $$ = RAFieldof($1, $3, NULL); }
  | ra1 PT_MINUSGREATER ident
      { $$ = RAFieldofptr($1, $3, NULL); }
  | ra1 PT_AT ident
      { $$ = RAOld($3, $1); }
  | ra1 PT_LPAREN PT_RPAREN
      { $$ = $1; }
  | ras PT_RPAREN
      { $$ = $1; }
;

ras :
    ra1 PT_LPAREN ra
      { $$ = RAApp($1, $3); }
  | ras PT_COMMA ra
      { $$ = RAApp($1, $3); }
;

ra2 : 
    ra1
      { $$ = $1; }
  | PT_MINUS ra2
      { $$ = RAUnop(T_UMINUS, $2); }
  | PT_PLUS ra2
      { $$ = RAUnop(T_UPLUS, $2); }
  | PT_EXCLAM ra2
      { $$ = RAUnop(T_NOTBOOL, $2); }
  | PT_TLIDE ra2
      { $$ = RAUnop(T_NOTINT, $2); }
  | PT_STAR PT_LBRACE type_name PT_RBRACE ra2
      { $$ = RADeref($3, $5); }
  | PT_STAR ra2
      { $$ = RADeref(NULL, $2); }
  | PT_AND ra2
      { $$ = RAAddress($2); }
  | PT_LPAREN type_name PT_RPAREN ra2
      { $$ = RACast($2, $4); }
;

ra3 :
    ra2
      { $$ = $1; }
  | ra3 PT_STAR ra2
      { $$ = RABinop(T_MUL, $1, $3); }
  | ra3 PT_SLASH ra2
      { $$ = RABinop(T_DIV, $1, $3); }
  | ra3 PT_PERCENT ra2
      { $$ = RABinop(T_MOD, $1, $3); }
;

ra4 :
    ra3
      { $$ = $1; }
  | ra4 PT_PLUS ra3
      { $$ = RABinop(T_PLUS, $1, $3); }
  | ra4 PT_MINUS ra3
      { $$ = RABinop(T_MINUS, $1, $3); }
;

ra4_75 :
    ra4
      { $$ = $1; }
  | ra4 PT_COLON atype
      { $$ = RAAnn($3, $1); }
;

ra5 :
    ra4_75
      { $$ = $1; }
  | ra5 PT_LESSLESS ra4_75
      { $$ = RABinop(T_SHL, $1, $3); }
  | ra5 PT_GREATERGREATER ra4_75
      { $$ = RABinop(T_SHR, $1, $3); }
;

ra6 :
    ra5
      { $$ = $1; }
  | ra6 PT_LESS ra5
      { $$ = RABinop(T_LT, $1, $3); }
  | ra6 PT_GREATER ra5
      { $$ = RABinop(T_GT, $1, $3); }
  | ra6 PT_LESSEQ ra5
      { $$ = RABinop(T_LE, $1, $3); }
  | ra6 PT_GREATEREQ ra5
      { $$ = RABinop(T_GE, $1, $3); }
;

ra7 :
    ra6
      { $$ = $1; }
  | ra7 PT_EQEQ ra6
      { $$ = RABinop(T_EQ, $1, $3); }
  | ra7 PT_EXCLAMEQ ra6
      { $$ = RABinop(T_NE, $1, $3); }
;

ra8 :
    ra7
      { $$ = $1; }
  | ra8 PT_AND ra7
      { $$ = RABinop(T_BAND, $1, $3); }
;

ra9 :
    ra8
      { $$ = $1; }
  | ra9 PT_CARET ra8
      { $$ = RABinop(T_XOR, $1, $3); }
;

ra10 :
    ra9
      { $$ = $1; }
  | ra10 PT_BAR ra9
      { $$ = RABinop(T_BOR, $1, $3); }
;

ra11 :
    ra10
      { $$ = $1; }
  | ra11 PT_ANDAND ra10
      { $$ = RABinop(T_AND, $1, $3); }
;

ra12 :
    ra11
      { $$ = $1; }
  | ra12 PT_BARBAR ra11
      { $$ = RABinop(T_OR, $1, $3); }
;

ra13 :
    ra12
      { $$ = $1; }
  | ra12 PT_EQGREATER ra13
      { $$ = RAConn(A_IMPLY, $1, $3); }
  | ra12 PT_LESSEQGREATER ra13
      { $$ = RAConn(A_IFF, $1, $3); }
;

ra14 :
  ra1 PT_BAREQ type_name fun_contra_body
    { $$ = RASpec($1, $3, $4); }
;

raq :
    PT_FORALL forall_aux
      { $$ = $2; }
  | PT_EXISTS exists_aux
      { $$ = $2; }
;

forall_aux :
    ident PT_COMMA ra
      { $$ = RAQfop(A_FORALL, 0, $1, NULL, NULL, $3); }
  | ident forall_aux
      { $$ = RAQfop(A_FORALL, 0, $1, NULL, NULL, $2); }
  | PT_LPAREN ident_list_space PT_COLON atype PT_RPAREN  PT_COMMA ra
      { $$ = RAMultiQfop(A_FORALL, 0, $2, NULL, $4, $7); }
  | PT_LPAREN ident_list_space PT_COLON atype PT_RPAREN forall_aux
      { $$ = RAMultiQfop(A_FORALL, 0, $2, NULL, $4, $6); }
  | PT_LPAREN ident_list_space PT_COLON brace_atype_list PT_MINUSGREATER atype PT_RPAREN PT_COMMA ra
      { $$ = RAMultiQfop(A_FORALL, 0, $2, $4, $6, $9); }
  | PT_LPAREN ident_list_space PT_COLON brace_atype_list PT_MINUSGREATER atype PT_RPAREN forall_aux
      { $$ = RAMultiQfop(A_FORALL, 0, $2, $4, $6, $8); }
;

exists_aux :
    ident PT_COMMA ra
      { $$ = RAQfop(A_EXISTS, 0, $1, NULL, NULL, $3); }
  | ident exists_aux
      { $$ = RAQfop(A_EXISTS, 0, $1, NULL, NULL, $2); }
  | PT_LPAREN ident_list_space PT_COLON atype PT_RPAREN  PT_COMMA ra
      { $$ = RAMultiQfop(A_EXISTS, 0, $2, NULL, $4, $7); }
  | PT_LPAREN ident_list_space PT_COLON atype PT_RPAREN exists_aux
      { $$ = RAMultiQfop(A_EXISTS, 0, $2, NULL, $4, $6); }
  | PT_LPAREN ident_list_space PT_COLON brace_atype_list PT_MINUSGREATER atype PT_RPAREN PT_COMMA ra
      { $$ = RAMultiQfop(A_EXISTS, 0, $2, $4, $6, $9); }
  | PT_LPAREN ident_list_space PT_COLON brace_atype_list PT_MINUSGREATER atype PT_RPAREN exists_aux
      { $$ = RAMultiQfop(A_EXISTS, 0, $2, $4, $6, $8); }
  | PT_LBRACK ident PT_RBRACK PT_COMMA ra
      { $$ = RAQfop(A_EXISTS, 1, $2, NULL, NULL, $5); }
  | PT_LBRACK ident PT_RBRACK exists_aux
      { $$ = RAQfop(A_EXISTS, 1, $2, NULL, NULL, $4); }
  | PT_LBRACK ident_list_space PT_COLON atype PT_RBRACK  PT_COMMA ra
      { $$ = RAMultiQfop(A_EXISTS, 1, $2, NULL, $4, $7); }
  | PT_LBRACK ident_list_space PT_COLON atype PT_RBRACK exists_aux
      { $$ = RAMultiQfop(A_EXISTS, 1, $2, NULL, $4, $6); }
  | PT_LBRACK ident_list_space PT_COLON brace_atype_list PT_MINUSGREATER atype PT_RBRACK PT_COMMA ra
      { $$ = RAMultiQfop(A_EXISTS, 1, $2, $4, $6, $9); }
  | PT_LBRACK ident_list_space PT_COLON brace_atype_list PT_MINUSGREATER atype PT_RBRACK exists_aux
      { $$ = RAMultiQfop(A_EXISTS, 1, $2, $4, $6, $8); }
;

tail0 :
    raq
      { $$ = $1; }
  | ra14
      { $$ = $1; }
  | PT_MINUS tail0
      { $$ = RAUnop(T_UMINUS, $2); }
  | PT_PLUS tail0
      { $$ = RAUnop(T_UPLUS, $2); }
  | PT_EXCLAM tail0
      { $$ = RAUnop(T_NOTBOOL, $2); }
  | PT_TLIDE tail0
      { $$ = RAUnop(T_NOTINT, $2); }
  | PT_STAR PT_LBRACE type_name PT_RBRACE tail0
      { $$ = RADeref($3, $5); }
  | PT_STAR tail0
      { $$ = RADeref(NULL, $2); }
  | PT_AND tail0
      { $$ = RAAddress($2); }
  | PT_LPAREN type_name PT_RPAREN tail0
      { $$ = RACast($2, $4); }
;

tail :
    tail0
      { $$ = $1; }
  | ra3 PT_STAR tail0
      { $$ = RABinop(T_MUL, $1, $3); }
  | ra3 PT_SLASH tail0
      { $$ = RABinop(T_DIV, $1, $3); }
  | ra3 PT_PERCENT tail0
      { $$ = RABinop(T_MOD, $1, $3); }
  | ra4 PT_PLUS tail0
      { $$ = RABinop(T_PLUS, $1, $3); }
  | ra4 PT_MINUS tail0
      { $$ = RABinop(T_MINUS, $1, $3); }
  | ra5 PT_LESSLESS tail0
      { $$ = RABinop(T_SHL, $1, $3); }
  | ra5 PT_GREATERGREATER tail0
      { $$ = RABinop(T_SHR, $1, $3); }
  | ra6 PT_LESS tail0
      { $$ = RABinop(T_LT, $1, $3); }
  | ra6 PT_GREATER tail0
      { $$ = RABinop(T_GT, $1, $3); }
  | ra6 PT_LESSEQ tail0
      { $$ = RABinop(T_LE, $1, $3); }
  | ra6 PT_GREATEREQ tail0
      { $$ = RABinop(T_GE, $1, $3); }
  | ra7 PT_EQEQ tail0
      { $$ = RABinop(T_EQ, $1, $3); }
  | ra7 PT_EXCLAMEQ tail0
      { $$ = RABinop(T_NE, $1, $3); }
  | ra8 PT_AND tail0
      { $$ = RABinop(T_BAND, $1, $3); }
  | ra9 PT_CARET tail0
      { $$ = RABinop(T_XOR, $1, $3); }
  | ra10 PT_BAR tail0
      { $$ = RABinop(T_BOR, $1, $3); }
  | ra11 PT_ANDAND tail0
      { $$ = RABinop(T_AND, $1, $3); }
  | ra12 PT_BARBAR tail0
      { $$ = RABinop(T_OR, $1, $3); }
  | ra12 PT_EQGREATER tail
      { $$ = RAConn(A_IMPLY, $1, $3); }
  | ra12 PT_LESSEQGREATER tail
      { $$ = RAConn(A_IFF, $1, $3); }
;

/* all binaries are left-assoc. however i'm not sure about correctness. */

ra :
    ra13
      { $$ = $1; }
  | tail
      { $$ = $1; }
;
/* RA end */


/* initialization */
initializer:
    expr
      { $$ = PPSingleExpr($1); }
  | PT_LBRACE initializer_list PT_RBRACE
      { $$ = PPInitList($2); }
;

initializer_list:
    initializer
      { $$ = PPNext($1, NULL); }
  | designator PT_EQ initializer
      { $$ = PPDesig($1, $3, NULL); }
  | initializer PT_COMMA initializer_list
      { $$ = PPNext($1, $3); }
  | designator PT_EQ initializer PT_COMMA initializer_list
      { $$ = PPDesig($1, $3, $5); }
;

designator:
    PT_LBRACK expr PT_RBRACK
      { $$ = PPAtIndex($2, NULL); }
  | PT_DOT ident
      { $$ = PPAtMember($2, NULL); }
  | PT_LBRACK expr PT_RBRACK designator
      { $$ = PPAtIndex($2, $4); }
  | PT_DOT ident designator
      { $$ = PPAtMember($2, $3); }
;
/* initialization end */


/* command */
decls:
    decl { K(PPMoreDecl(0, $1, NULL), env); } PT_COMMA decls
      { }
  | decl PT_EQ initializer { K(PPMoreDecl(0, $1, $3), env); } PT_COMMA decls
      { }
  | decl { K(PPMoreDecl(1, $1, NULL), env); } PT_SEMI
      { }
  | decl PT_EQ initializer { K(PPMoreDecl(1, $1, $3), env); } PT_SEMI
      { }
;

simple_cmd :
    expr
      { $$ = PPComputation($1); }
  | PT_PLUSPLUS expr 
      { $$ = PPIncDec(T_INC_F, $2); }
  | expr PT_PLUSPLUS
      { $$ = PPIncDec(T_INC_B, $1); }
  | PT_MINUSMINUS expr
      { $$ = PPIncDec(T_DEC_F, $2); }
  | expr PT_MINUSMINUS
      { $$ = PPIncDec(T_DEC_B, $1); }
  | expr PT_EQ expr
      { $$ = PPAsgn(T_ASSIGN, $1, $3); }
  | expr PT_PLUSEQ expr
      { $$ = PPAsgn(T_ADD_ASSIGN, $1, $3); }
  | expr PT_MINUSEQ expr
      { $$ = PPAsgn(T_SUB_ASSIGN, $1, $3); }
  | expr PT_STAREQ expr
      { $$ = PPAsgn(T_MUL_ASSIGN, $1, $3); }
  | expr PT_SLASHEQ expr
      { $$ = PPAsgn(T_DIV_ASSIGN, $1, $3); }
  | expr PT_PERCENTEQ expr
      { $$ = PPAsgn(T_MOD_ASSIGN, $1, $3); }
  | expr PT_ANDEQ expr
      { $$ = PPAsgn(T_BAND_ASSIGN, $1, $3); }
  | expr PT_BAREQ expr
      { $$ = PPAsgn(T_BOR_ASSIGN, $1, $3); }
  | expr PT_CARETEQ expr
      { $$ = PPAsgn(T_XOR_ASSIGN, $1, $3); }
  | expr PT_LESSLESSEQ expr
      { $$ = PPAsgn(T_SHL_ASSIGN, $1, $3); }
  | expr PT_GREATERGREATEREQ expr
      { $$ = PPAsgn(T_SHR_ASSIGN, $1, $3); }
;

for_init :
    PT_SEMI
      { $$ = NULL; }
  | simple_cmd PT_SEMI
      { $$ = $1; }
;

for_cond :
    PT_SEMI
      { $$ = NULL; }
  | expr PT_SEMI
      { $$ = $1; }
;

for_step :
    PT_RPAREN
      { $$ = NULL; }
  | simple_cmd PT_RPAREN
      { $$ = $1; }
;

/* command end */


/* def */
sepdef : 
    PT_LET ident PT_LPAREN brace_comma_atype_list PT_SEMI comma_lvar_list PT_RPAREN PT_EQ ra
      { $$ = PPSepdef($2, $4, $6, $9);}
  | PT_LET ident PT_LPAREN comma_lvar_list PT_RPAREN PT_EQ ra
      { $$ = PPSepdef($2, NULL, $4, $7); }
  | PT_LET ident PT_LPAREN brace_comma_atype_list PT_RPAREN PT_EQ ra
      { $$ = PPSepdef($2, $4, NULL, $7); }
  | PT_LET ident PT_LPAREN PT_RPAREN PT_EQ ra
      { $$ = PPSepdef($2, NULL, NULL, $6); }
;

field_dec :
    field_specifier decl
      { $$ = TAnnot(PreType($1, $2)); }
;

field_decs :
    field_dec PT_SEMI
      { $$ = ALCons($1, NULL); }
  | field_dec PT_SEMI field_decs
      { $$ = ALCons($1, $3); }
;

enums :
    ident
      { $$ = pp_enum_list_cons($1, 0, 0, 0, NULL); }
  | ident PT_COMMA enums
      { $$ = pp_enum_list_cons($1, 0, 0, 0, $3); }
  | ident PT_EQ PT_NATLIT
      { $$ = pp_enum_list_cons($1, 1, 0, $3.n, NULL); }
  | ident PT_EQ PT_NATLIT PT_COMMA enums
      { $$ = pp_enum_list_cons($1, 1, 0, $3.n, $5); }
  | ident PT_EQ PT_MINUS PT_NATLIT
      { $$ = pp_enum_list_cons($1, 1, 1, $4.n, NULL); }
  | ident PT_EQ PT_MINUS PT_NATLIT PT_COMMA enums
      { $$ = pp_enum_list_cons($1, 1, 1, $4.n, $6); }
;

para :
    parameter_specifier decl
      { $$ = TAnnot(PreType($1, $2)); }
  | parameter_specifier abstr_decl_except_function
      { $$ = TAnnot(PreType($1, $2)); }
  | parameter_specifier
      { $$ = TAnnot(PreType($1, DERIVEnd(NULL))); }
;

paras :
    para
      { $$ = ALCons($1, ALNil()); }
  | para PT_COMMA paras
      { $$ = ALCons($1, $3); }
;

fun_contra_body :
    PT_REQUIRE ra PT_ENSURE ra
      { $$ = PPSpec(NULL, NULL, NULL, NULL, $2, $4); }
  | PT_WITH brace_atype_list
            paren_lvar_list
    PT_REQUIRE ra PT_ENSURE ra
      { $$ = PPSpec(NULL, NULL, $2, $3, $5, $7); }
  | PT_WITH brace_atype_list
    PT_REQUIRE ra PT_ENSURE ra
      { $$ = PPSpec(NULL, NULL, $2, NULL, $4, $6); }
  | PT_WITH paren_lvar_list
    PT_REQUIRE ra PT_ENSURE ra
      { $$ = PPSpec(NULL, NULL, NULL, $2, $4, $6); }
;

fun_contra :
    fun_contra_body
      { $$ = $1; }
  | ident
      { $$ = PPSpec($1, NULL, NULL, NULL, NULL, NULL); }
  | ident fun_contra_body
      { $2->name = $1; $$ = $2; }
  | ident PT_LESSEQ ident fun_contra_body
      { $4->name = $1; $4->derived_by = $3; $$ = $4; }

/* def end */

%%

void yyerror(char *path, void *k, struct environment *env, char* s) {
  failwith("bison: %s", s);
  exit(0);
}
