%option noyywrap yylineno

%{
  #include "lang.h"
  #include "utils.h"
  #include "parser.h"
  #include "env.h"

  #define YY_USER_ACTION { \
    if(yytext[0] != '\n') \
      yyset_column(yyget_column(yyscanner) + yyget_leng(yyscanner), yyscanner); \
  }
  #define YY_DECL int yylex \
               (YYSTYPE * yylval_param , yyscan_t yyscanner, struct environment *env)

  char sbuffer[65536];
  int sindex;
  void push_s_char(char c);
  int last_lexer_ctx;
%}

%option bison-bridge
%option reentrant

%s IN_ASSERTION
%s IN_LINE_ASSERTION
%s IN_COMMENT
%s IN_LINE_COMMENT
%s IN_PROOF
%s IN_LINE_PROOF
%s IN_STRING
%s IN_IMPORT
%s IN_LINE_IMPORT
%s IN_LINEMARK

%%
<INITIAL>"#"[ \t\r\n]*"include" { return PT_INCLUDE; }
<INITIAL>"#"[ ][0-9]+    { yylval->nat.n = build_nat(yytext + 2, yyleng - 2); BEGIN(IN_LINEMARK); return PT_LINEMARK; }
<IN_LINEMARK>"\n" { BEGIN(INITIAL); return PT_NEWLINE; }

<INITIAL,IN_ASSERTION,IN_LINE_ASSERTION,IN_LINEMARK>"\"" { last_lexer_ctx = yyg->yy_start; BEGIN(IN_STRING); sindex = 0; }
<IN_STRING>"\\n" { push_s_char('\n'); }
<IN_STRING>"\\t" { push_s_char('\t'); }
<IN_STRING>"\\\"" { push_s_char('\"'); }
<IN_STRING>"\\\'" { push_s_char('\''); }
<IN_STRING>"\\\\" { push_s_char('\\'); }
<IN_STRING>"\\\?" { push_s_char('\?'); }
<IN_STRING>"\\\n" { }
<IN_STRING>"\""[ \t\r\n]*"\"" { }
<IN_STRING>"\"" {
  yyg->yy_start = last_lexer_ctx;
  push_s_char('\0');
  yylval->string = clone_str(sbuffer);
  return PT_STRINGLIT;
}
<IN_STRING>. { push_s_char(yytext[0]); }

<INITIAL>"/*" { BEGIN(IN_COMMENT); }
<IN_COMMENT>"*/" { BEGIN(INITIAL); }
<IN_COMMENT>[^*]* { }
<IN_COMMENT>"*" { }

<INITIAL>"//" { BEGIN(IN_LINE_COMMENT); }
<IN_LINE_COMMENT>[^\n]* { }
<IN_LINE_COMMENT>"\n" { BEGIN(INITIAL); }

<INITIAL>"/*"[ \n\t\r]+"Proof"[ \n\t\r]+ { BEGIN(IN_PROOF); return PT_SLASHSTARPROOF; }
<INITIAL>"//"[ \t]+"Proof"[ \t]+ { BEGIN(IN_LINE_PROOF); return PT_SLASHSLASHPROOF; }
<IN_PROOF,IN_LINE_PROOF>[_A-Za-z0-9]+ {
  yylval->string = new_str(yytext, yyleng);
  return PT_RAW;
}
<IN_PROOF>"*/"    { BEGIN(INITIAL); return PT_STARSLASH; }
<IN_LINE_PROOF>"\n" { BEGIN(INITIAL); return PT_NEWLINE; }

<IN_IMPORT>"*/" { BEGIN(INITIAL); return PT_STARSLASH; }
<IN_IMPORT>[.A-Za-z0-9_][.A-Za-z0-9_ \t\n]*[.A-Za-z0-9_] {
  yylval->string = new_str(yytext, yyleng);
  return PT_RAW;
}
<IN_IMPORT>[.A-Za-z0-9_] {
  yylval->string = new_str(yytext, yyleng);
  return PT_RAW;
}
<IN_LINE_IMPORT>[.A-Za-z0-9_][.A-Za-z0-9_ \t]*[.A-Za-z0-9_] {
  yylval->string = new_str(yytext, yyleng);
  return PT_RAW;
}
<IN_LINE_IMPORT>[.A-Za-z0-9_] {
  yylval->string = new_str(yytext, yyleng);
  return PT_RAW;
}
<IN_LINE_IMPORT>"\n" { BEGIN(INITIAL); return PT_NEWLINE; }

<INITIAL>"extern"   { return PT_EXTERN; }
<INITIAL>"static"   { return PT_STATIC; }
<INITIAL>"const"    { return PT_CONST; }
<INITIAL>"restrict" { return PT_RESTRICT; }
<INITIAL>"volatile" { return PT_VOLATILE; }
<INITIAL>"inline"   { return PT_INLINE; }

<INITIAL,IN_ASSERTION,IN_LINE_ASSERTION>"struct"    { return PT_STRUCT; }
<INITIAL,IN_ASSERTION,IN_LINE_ASSERTION>"union"     { return PT_UNION; }
<INITIAL,IN_ASSERTION,IN_LINE_ASSERTION>"enum"      { return PT_ENUM; }
<INITIAL,IN_ASSERTION,IN_LINE_ASSERTION>"int"       { return PT_INT; }
<INITIAL,IN_ASSERTION,IN_LINE_ASSERTION>"void"      { return PT_VOID; }
<INITIAL,IN_ASSERTION,IN_LINE_ASSERTION>"char"      { return PT_CHAR; }
<INITIAL,IN_ASSERTION,IN_LINE_ASSERTION>"short"     { return PT_SHORT; }
<INITIAL,IN_ASSERTION,IN_LINE_ASSERTION>"unsigned"  { return PT_UNSIGNED; }
<INITIAL,IN_ASSERTION,IN_LINE_ASSERTION>"long"      { return PT_LONG; }

<INITIAL>"if"        { return PT_IF; }
<INITIAL>"else"      { return PT_ELSE; }
<INITIAL>"while"     { return PT_WHILE; }
<INITIAL>"for"       { return PT_FOR; }
<INITIAL>"break"     { return PT_BREAK; }
<INITIAL>"continue"  { return PT_CONTINUE; }
<INITIAL>"return"    { return PT_RETURN; }
<INITIAL,IN_ASSERTION,IN_LINE_ASSERTION>"do"        { return PT_DO; }
<INITIAL>"switch"    { return PT_SWITCH; }
<INITIAL>"case"      { return PT_CASE; }
<INITIAL>"default"   { return PT_DEFAULT; }
<INITIAL>"typedef"   { return PT_TYPEDEF; }

<INITIAL,IN_ASSERTION,IN_LINE_ASSERTION>"sizeof"    { return PT_SIZEOF; }

<IN_ASSERTION,IN_LINE_ASSERTION>"With"          { return PT_WITH; }
<IN_ASSERTION,IN_LINE_ASSERTION>"Require"       { return PT_REQUIRE; }
<IN_ASSERTION,IN_LINE_ASSERTION>"Ensure"        { return PT_ENSURE; }
<IN_ASSERTION,IN_LINE_ASSERTION>"Inv"           { return PT_INV; }
<IN_ASSERTION,IN_LINE_ASSERTION>"forall"        { return PT_FORALL; }
<IN_ASSERTION,IN_LINE_ASSERTION>"exists"        { return PT_EXISTS; }
<IN_ASSERTION,IN_LINE_ASSERTION>"Let"           { return PT_LET; }
<IN_ASSERTION,IN_LINE_ASSERTION>"emp"           { return PT_EMP; }
<IN_ASSERTION,IN_LINE_ASSERTION>"__return"      { return PT___RETURN; }
<IN_ASSERTION,IN_LINE_ASSERTION>"data_at"       { return PT_DATA_AT; }
<IN_ASSERTION,IN_LINE_ASSERTION>"undef_data_at" { return PT_UNDEF_DATA_AT; }
<IN_ASSERTION,IN_LINE_ASSERTION>"field_addr"    { return PT_FIELD_ADDR; }
<IN_ASSERTION,IN_LINE_ASSERTION>"Arr"           { return PT_ARR; }
<IN_ASSERTION,IN_LINE_ASSERTION>"__time_cost"   { return PT___TIME_COST; }
<IN_ASSERTION,IN_LINE_ASSERTION>"Extern Coq"    { return PT_EXTERNCOQ; }
<IN_ASSERTION,IN_LINE_ASSERTION>"Field"         { return PT_FIELD; }
<IN_ASSERTION,IN_LINE_ASSERTION>"Record"        { return PT_RECORD; }
<IN_ASSERTION,IN_LINE_ASSERTION>"where"         { return PT_WHERE; }
<IN_ASSERTION,IN_LINE_ASSERTION>"which implies" { return PT_WHICHIMPLIES; }
<IN_ASSERTION,IN_LINE_ASSERTION>"by"            { return PT_BY; }
<IN_ASSERTION>"Import Coq"                      { BEGIN(IN_IMPORT); return PT_IMPORTCOQ; }
<IN_LINE_ASSERTION>"Import Coq"                 { BEGIN(IN_LINE_IMPORT); return PT_IMPORTCOQ; }
<IN_ASSERTION,IN_LINE_ASSERTION>"include"[ \t\n]+"strategies" { return PT_INCLUDESTRATEGIES; }
<IN_ASSERTION,IN_LINE_ASSERTION>[fF][iI][lL][lL][ ][iI][nN][ ][iI][nN][vV][aA][rR][iI][aA][nN][tT] { return PT_FILLININV; }


<INITIAL,IN_ASSERTION,IN_LINE_ASSERTION>"("   { return PT_LPAREN; }
<INITIAL,IN_ASSERTION,IN_LINE_ASSERTION>")"   { return PT_RPAREN; }
<INITIAL,IN_ASSERTION,IN_LINE_ASSERTION>"["   { return PT_LBRACK; }
<INITIAL,IN_ASSERTION,IN_LINE_ASSERTION>"]"   { return PT_RBRACK; }
<INITIAL,IN_ASSERTION,IN_LINE_ASSERTION>"{"   { return PT_LBRACE; }
<INITIAL,IN_ASSERTION,IN_LINE_ASSERTION>"}"   { return PT_RBRACE; }

<INITIAL,IN_ASSERTION,IN_LINE_ASSERTION>"+"   { return PT_PLUS; }
<INITIAL,IN_ASSERTION,IN_LINE_ASSERTION>"-"   { return PT_MINUS; }
<INITIAL,IN_ASSERTION,IN_LINE_ASSERTION>"*"   { return PT_STAR; }
<INITIAL,IN_ASSERTION,IN_LINE_ASSERTION>"/"   { return PT_SLASH; }
<INITIAL,IN_ASSERTION,IN_LINE_ASSERTION>"%"   { return PT_PERCENT; }
<INITIAL,IN_ASSERTION,IN_LINE_ASSERTION>"<"   { return PT_LESS; }
<INITIAL,IN_ASSERTION,IN_LINE_ASSERTION>"<="  { return PT_LESSEQ; }
<INITIAL,IN_ASSERTION,IN_LINE_ASSERTION>">"   { return PT_GREATER; }
<INITIAL,IN_ASSERTION,IN_LINE_ASSERTION>">="  { return PT_GREATEREQ; }
<INITIAL,IN_ASSERTION,IN_LINE_ASSERTION>"=="  { return PT_EQEQ; }
<INITIAL,IN_ASSERTION,IN_LINE_ASSERTION>"!="  { return PT_EXCLAMEQ; }
<INITIAL,IN_ASSERTION,IN_LINE_ASSERTION>"&&"  { return PT_ANDAND; }
<INITIAL,IN_ASSERTION,IN_LINE_ASSERTION>"||"  { return PT_BARBAR; }
<INITIAL,IN_ASSERTION,IN_LINE_ASSERTION>"&"   { return PT_AND; }
<INITIAL,IN_ASSERTION,IN_LINE_ASSERTION>"|"   { return PT_BAR; }
<INITIAL,IN_ASSERTION,IN_LINE_ASSERTION>"^"   { return PT_CARET; }
<INITIAL,IN_ASSERTION,IN_LINE_ASSERTION>"<<"  { return PT_LESSLESS; }
<INITIAL,IN_ASSERTION,IN_LINE_ASSERTION>">>"  { return PT_GREATERGREATER; }

<INITIAL,IN_ASSERTION,IN_LINE_ASSERTION>"!"   { return PT_EXCLAM; }
<INITIAL,IN_ASSERTION,IN_LINE_ASSERTION>"~"   { return PT_TLIDE; }

<INITIAL,IN_ASSERTION,IN_LINE_ASSERTION,IN_IMPORT,IN_LINE_IMPORT>"."   { return PT_DOT; }
<INITIAL,IN_ASSERTION,IN_LINE_ASSERTION>"->"  { return PT_MINUSGREATER; }

<INITIAL,IN_ASSERTION,IN_LINE_ASSERTION>"="   { return PT_EQ; } // Let .. = ...
<INITIAL>"+="  { return PT_PLUSEQ; }
<INITIAL>"-="  { return PT_MINUSEQ; }
<INITIAL>"*="  { return PT_STAREQ; }
<INITIAL>"/="  { return PT_SLASHEQ; }
<INITIAL>"%="  { return PT_PERCENTEQ; }
<INITIAL>"&="  { return PT_ANDEQ; }
<INITIAL,IN_ASSERTION,IN_LINE_ASSERTION>"|="  { return PT_BAREQ; }
<INITIAL>"^="  { return PT_CARETEQ; }
<INITIAL>"<<=" { return PT_LESSLESSEQ; }
<INITIAL>">>=" { return PT_GREATERGREATEREQ; }
<INITIAL>"?"   { return PT_QUESTION; }

<INITIAL>"++"  { return PT_PLUSPLUS; }
<INITIAL>"--"  { return PT_MINUSMINUS; }

<INITIAL,IN_ASSERTION,IN_LINE_ASSERTION>";"   { return PT_SEMI; }
<INITIAL,IN_ASSERTION,IN_LINE_ASSERTION>":"   { return PT_COLON; }


<INITIAL>"//@"   { BEGIN(IN_LINE_ASSERTION); return PT_SLASHSLASHAT; }
<INITIAL>"/*@"   { BEGIN(IN_ASSERTION); return PT_SLASHSTARAT; }
<IN_LINE_ASSERTION>"\n" { BEGIN(INITIAL); return PT_NEWLINE; }
<IN_ASSERTION>"*/"    { BEGIN(INITIAL); return PT_STARSLASH; }
<IN_ASSERTION,IN_LINE_ASSERTION>"@mark" { return PT_ATMARK; }
<IN_ASSERTION,IN_LINE_ASSERTION>"=>"    { return PT_EQGREATER; }
<IN_ASSERTION,IN_LINE_ASSERTION>"<=>"    { return PT_LESSEQGREATER; }
<IN_ASSERTION,IN_LINE_ASSERTION>"::"    { return PT_COLONCOLON; }
<IN_ASSERTION,IN_LINE_ASSERTION>":="    { return PT_COLONEQ; }
<IN_ASSERTION,IN_LINE_ASSERTION>"Assert"    { return PT_ASSERT; }

<INITIAL,IN_ASSERTION,IN_LINE_ASSERTION>","     { return PT_COMMA; }

<IN_ASSERTION,IN_LINE_ASSERTION>"@"   { return PT_AT; }
<IN_ASSERTION,IN_LINE_ASSERTION>"#"   { return PT_HASH; }

"\n" { }

<INITIAL,IN_ASSERTION,IN_LINE_ASSERTION,IN_LINEMARK>(0|[1-9][0-9]*)((u?(l|ll)?)|((l|ll)?u?)) {
  yylval->nat.n = build_nat(yytext, yyleng);
  yylval->nat.hex = 0;
  yylval->nat.l = yylval->nat.u = 0;
  for (int i = 0; i < 3; i++) {
    if (yytext[yyleng - i - 1] == 'u') {
      yylval->nat.u = 1;
    } else if (yytext[yyleng - i - 1] == 'l') {
      yylval->nat.l = 1;
    }
  }
  return PT_NATLIT;
}

<INITIAL,IN_ASSERTION,IN_LINE_ASSERTION>(0[xX][0-9a-fA-F]*)((u?(l|ll)?)|((l|ll)?u?)) {
  yylval->nat.n = build_hex(yytext + 2, yyleng - 2);
  yylval->nat.hex = 1;
  yylval->nat.l = yylval->nat.u = 0;
  for (int i = 0; i < 3; i++) {
    if (yytext[yyleng - i - 1] == 'u') {
      yylval->nat.u = 1;
    } else if (yytext[yyleng - i - 1] == 'l') {
      yylval->nat.l = 1;
    }
  }
  return PT_NATLIT;
}

<INITIAL,IN_ASSERTION,IN_LINE_ASSERTION,IN_IMPORT,IN_LINE_IMPORT>
[_A-Za-z]([_A-Za-z0-9']|"::")* {
  yylval->string = new_identifier(yytext, yyleng);
  int v;
  struct scope_env *ve;
  for (ve = env->ephemer.scope; ve != NULL; ve = ve->outer) {
    struct var_scope_union *u = hashtbl_find(&ve->var_scope, yylval->string, &v);
    if (u != NULL) {
      if (u->t == IS_TYPE)
        return PT_TIDENT;
      else if (u->t == IS_PROG_VAR || u->t == IS_LOGIC_VAR)
        return PT_IDENT;
    }
  }
  return PT_IDENT;
}

[ \t\r\n\b\f] { }

. {
  printf("Unrecognized character\n");
  printf("Char : '%c', Char value : %d\n", *yytext, *yytext);
  exit(1);
}

%%

void push_s_char(char c) {
  sbuffer[sindex++] = c;
  if (sindex > 65536)
    failwith("compiler limit: String exceeds 65535 bytes in length");
}
