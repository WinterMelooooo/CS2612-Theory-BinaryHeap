%option noyywrap yylineno
%option prefix = "ll"

%{
#include "lang.h"
#include "parser.h"
%}

%x IN_COMMENT
%x IN_LINE_COMMENT
%x IN_INCLUDE

%%

"/*"                { BEGIN(IN_COMMENT); }
<IN_COMMENT>"*/"    { BEGIN(INITIAL); }
<IN_COMMENT>[^*]*   { }
<IN_COMMENT>"*"     { }

"//"                { BEGIN(IN_LINE_COMMENT); }
<IN_LINE_COMMENT>"\n" { BEGIN(INITIAL); }
<IN_LINE_COMMENT>[^\n]*   { }

"id"            {return ID;}
"priority"      {return PRIO;}
"left"          {return LEFT;}
"right"         {return RIGHT;}
"action"        {return ACTION;}
"check"         {return CHECK;}

"null"          {return UPPER_NULL;}
"NULL"          {return LOWER_NULL;}

"I8"            {return I8;}
"U8"            {return U8;}
"I16"           {return I16;}
"U16"           {return U16;}
"I32"           {return I32;}
"U32"           {return U32;}
"I64"           {return I64;}
"U64"           {return U64;}
"PTR"           {return PTR;}

"#"             {return HASH;}
"("             {return LPAREN;}
")"             {return RPAREN;}
"["             {return LBRACKET;}
"]"             {return RBRACKET;}
"{"             {return LBRACES;}
"}"             {return RBRACES;}
";"             {return SEMI;}
":"             {return COLON;}
","             {return COMMA;}
<INITIAL>"\""            { BEGIN(IN_INCLUDE); return DQUATATION;}
<IN_INCLUDE>"\""         { BEGIN(INITIAL); return DQUATATION; }
"."             {return DOT;}

"?"             {return QUEST;}
"-"             {return MINUS;}
"+"             {return PLUS;}
"*"             {return MULT;}
"/"             {return DIV;}

"->"            {return MINUSGREATER;}
"=="            {return EQ;}
"!="            {return NEQ;}
"<="            {return LE;}
">="            {return GE;}
"<"             {return LT;}
">"             {return GT;}
"at"            {return AT;}
"||"            {return OR;}

"exists"        {return EXISTS;}
"atom"          {return ATOM;}
"sizeof"        {return SIZEOF;}
"include"       {return INCLUDE;}
"data_at"       {return DATA_AT;}
"undef_data_at" {return UNDEF_DATA_AT;}
"field_addr" {return FIELDADDR;}

"struct"    { return PT_STRUCT; }
"union"     { return PT_UNION; }
"enum"      { return PT_ENUM; }
"int"       { return PT_INT; }
"void"      { return PT_VOID; }
"char"      { return PT_CHAR; }
"unsigned"  { return PT_UNSIGNED; }
"long"      { return PT_LONG; }

0|[1-9][0-9]* {
    lllval.nat = lang_build_nat(yytext, yyleng, Signed, 0);
    return NAT;
}

0|[1-9][0-9]*u {
    lllval.nat = lang_build_nat(yytext, yyleng-1, Unsigned, 0);
    return NAT;
}

0|[1-9][0-9]*ll {
    lllval.nat = lang_build_nat(yytext, yyleng-2, Signed, 1);
    return NAT;
}

0|[1-9][0-9]*ull {
    lllval.nat = lang_build_nat(yytext, yyleng-3, Unsigned, 1);
    return NAT;
}

0[xX][0-9a-fA-F]* {
    lllval.nat = lang_build_hex(yytext + 2, yyleng - 2);
  return NAT;
}

[_A-Za-z]([_A-Za-z0-9]("::"?))* {
  lllval.s = lang_new_str(yytext, yyleng);
  return IDENT;
}

<IN_INCLUDE>[\./_A-Za-z0-9]*\.[_A-Za-z0-9]* {
  lllval.p = lang_new_str(yytext, yyleng);
  return PATH;
}

[ \t\r\n\b\f] { }

. {
  printf("Unrecognized character around line %d\n", llget_lineno() + 1);
  printf("Char : '%c', Char value : %d\n", *yytext, *yytext);
  exit(1);
}
%%
