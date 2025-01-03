/* A Bison parser, made by GNU Bison 3.8.2.  */

/* Bison interface for Yacc-like parsers in C

   Copyright (C) 1984, 1989-1990, 2000-2015, 2018-2021 Free Software Foundation,
   Inc.

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <https://www.gnu.org/licenses/>.  */

/* As a special exception, you may create a larger work that contains
   part or all of the Bison parser skeleton and distribute that work
   under terms of your choice, so long as that work isn't itself a
   parser generator using the skeleton or a modified version thereof
   as a parser skeleton.  Alternatively, if you modify or redistribute
   the parser skeleton itself, you may (at your option) remove this
   special exception, which will cause the skeleton and the resulting
   Bison output files to be licensed under the GNU General Public
   License without this special exception.

   This special exception was added by the Free Software Foundation in
   version 2.2 of Bison.  */

/* DO NOT RELY ON FEATURES THAT ARE NOT DOCUMENTED in the manual,
   especially those whose name start with YY_ or yy_.  They are
   private implementation details that can be changed or removed.  */

#ifndef YY_YY_MNT_D_SJTU_CS2612_2024FALL_CS2612_2024FALL_QCP_SYMBOLICEXE_TEST_COMPILER_PARSER_H_INCLUDED
# define YY_YY_MNT_D_SJTU_CS2612_2024FALL_CS2612_2024FALL_QCP_SYMBOLICEXE_TEST_COMPILER_PARSER_H_INCLUDED
/* Debug traces.  */
#ifndef YYDEBUG
# define YYDEBUG 0
#endif
#if YYDEBUG
extern int yydebug;
#endif

/* Token kinds.  */
#ifndef YYTOKENTYPE
# define YYTOKENTYPE
  enum yytokentype
  {
    YYEMPTY = -2,
    YYEOF = 0,                     /* "end of file"  */
    YYerror = 256,                 /* error  */
    YYUNDEF = 257,                 /* "invalid token"  */
    PT_EXTERN = 258,               /* PT_EXTERN  */
    PT_STATIC = 259,               /* PT_STATIC  */
    PT_CONST = 260,                /* PT_CONST  */
    PT_RESTRICT = 261,             /* PT_RESTRICT  */
    PT_VOLATILE = 262,             /* PT_VOLATILE  */
    PT_INLINE = 263,               /* PT_INLINE  */
    PT_STRUCT = 264,               /* PT_STRUCT  */
    PT_UNION = 265,                /* PT_UNION  */
    PT_ENUM = 266,                 /* PT_ENUM  */
    PT_INT = 267,                  /* PT_INT  */
    PT_VOID = 268,                 /* PT_VOID  */
    PT_CHAR = 269,                 /* PT_CHAR  */
    PT_SHORT = 270,                /* PT_SHORT  */
    PT_UNSIGNED = 271,             /* PT_UNSIGNED  */
    PT_LONG = 272,                 /* PT_LONG  */
    PT_IF = 273,                   /* PT_IF  */
    PT_ELSE = 274,                 /* PT_ELSE  */
    PT_WHILE = 275,                /* PT_WHILE  */
    PT_FOR = 276,                  /* PT_FOR  */
    PT_BREAK = 277,                /* PT_BREAK  */
    PT_CONTINUE = 278,             /* PT_CONTINUE  */
    PT_RETURN = 279,               /* PT_RETURN  */
    PT_DO = 280,                   /* PT_DO  */
    PT_SWITCH = 281,               /* PT_SWITCH  */
    PT_CASE = 282,                 /* PT_CASE  */
    PT_DEFAULT = 283,              /* PT_DEFAULT  */
    PT_SIZEOF = 284,               /* PT_SIZEOF  */
    PT_TYPEDEF = 285,              /* PT_TYPEDEF  */
    PT_WITH = 286,                 /* PT_WITH  */
    PT_REQUIRE = 287,              /* PT_REQUIRE  */
    PT_ENSURE = 288,               /* PT_ENSURE  */
    PT_INV = 289,                  /* PT_INV  */
    PT_FORALL = 290,               /* PT_FORALL  */
    PT_EXISTS = 291,               /* PT_EXISTS  */
    PT_LET = 292,                  /* PT_LET  */
    PT_EMP = 293,                  /* PT_EMP  */
    PT___RETURN = 294,             /* PT___RETURN  */
    PT_ATMARK = 295,               /* PT_ATMARK  */
    PT_DATA_AT = 296,              /* PT_DATA_AT  */
    PT_UNDEF_DATA_AT = 297,        /* PT_UNDEF_DATA_AT  */
    PT_FIELD_ADDR = 298,           /* PT_FIELD_ADDR  */
    PT_ARR = 299,                  /* PT_ARR  */
    PT___TIME_COST = 300,          /* PT___TIME_COST  */
    PT_EXTERNCOQ = 301,            /* PT_EXTERNCOQ  */
    PT_FIELD = 302,                /* PT_FIELD  */
    PT_RECORD = 303,               /* PT_RECORD  */
    PT_WHERE = 304,                /* PT_WHERE  */
    PT_WHICHIMPLIES = 305,         /* PT_WHICHIMPLIES  */
    PT_BY = 306,                   /* PT_BY  */
    PT_IMPORTCOQ = 307,            /* PT_IMPORTCOQ  */
    PT_INCLUDESTRATEGIES = 308,    /* PT_INCLUDESTRATEGIES  */
    PT_INCLUDE = 309,              /* PT_INCLUDE  */
    PT_LINEMARK = 310,             /* PT_LINEMARK  */
    PT_LPAREN = 311,               /* PT_LPAREN  */
    PT_RPAREN = 312,               /* PT_RPAREN  */
    PT_LBRACK = 313,               /* PT_LBRACK  */
    PT_RBRACK = 314,               /* PT_RBRACK  */
    PT_LBRACE = 315,               /* PT_LBRACE  */
    PT_RBRACE = 316,               /* PT_RBRACE  */
    PT_PLUS = 317,                 /* PT_PLUS  */
    PT_MINUS = 318,                /* PT_MINUS  */
    PT_STAR = 319,                 /* PT_STAR  */
    PT_SLASH = 320,                /* PT_SLASH  */
    PT_PERCENT = 321,              /* PT_PERCENT  */
    PT_LESS = 322,                 /* PT_LESS  */
    PT_LESSEQ = 323,               /* PT_LESSEQ  */
    PT_GREATER = 324,              /* PT_GREATER  */
    PT_GREATEREQ = 325,            /* PT_GREATEREQ  */
    PT_EQEQ = 326,                 /* PT_EQEQ  */
    PT_EXCLAMEQ = 327,             /* PT_EXCLAMEQ  */
    PT_ANDAND = 328,               /* PT_ANDAND  */
    PT_BARBAR = 329,               /* PT_BARBAR  */
    PT_AND = 330,                  /* PT_AND  */
    PT_BAR = 331,                  /* PT_BAR  */
    PT_CARET = 332,                /* PT_CARET  */
    PT_LESSLESS = 333,             /* PT_LESSLESS  */
    PT_GREATERGREATER = 334,       /* PT_GREATERGREATER  */
    PT_EXCLAM = 335,               /* PT_EXCLAM  */
    PT_TLIDE = 336,                /* PT_TLIDE  */
    PT_DOT = 337,                  /* PT_DOT  */
    PT_MINUSGREATER = 338,         /* PT_MINUSGREATER  */
    PT_EQ = 339,                   /* PT_EQ  */
    PT_PLUSEQ = 340,               /* PT_PLUSEQ  */
    PT_MINUSEQ = 341,              /* PT_MINUSEQ  */
    PT_STAREQ = 342,               /* PT_STAREQ  */
    PT_SLASHEQ = 343,              /* PT_SLASHEQ  */
    PT_PERCENTEQ = 344,            /* PT_PERCENTEQ  */
    PT_ANDEQ = 345,                /* PT_ANDEQ  */
    PT_BAREQ = 346,                /* PT_BAREQ  */
    PT_CARETEQ = 347,              /* PT_CARETEQ  */
    PT_LESSLESSEQ = 348,           /* PT_LESSLESSEQ  */
    PT_GREATERGREATEREQ = 349,     /* PT_GREATERGREATEREQ  */
    PT_QUESTION = 350,             /* PT_QUESTION  */
    PT_PLUSPLUS = 351,             /* PT_PLUSPLUS  */
    PT_MINUSMINUS = 352,           /* PT_MINUSMINUS  */
    PT_SEMI = 353,                 /* PT_SEMI  */
    PT_COLON = 354,                /* PT_COLON  */
    PT_STARSLASH = 355,            /* PT_STARSLASH  */
    PT_SLASHSTARAT = 356,          /* PT_SLASHSTARAT  */
    PT_SLASHSLASHAT = 357,         /* PT_SLASHSLASHAT  */
    PT_SLASHSTARPROOF = 358,       /* PT_SLASHSTARPROOF  */
    PT_SLASHSLASHPROOF = 359,      /* PT_SLASHSLASHPROOF  */
    PT_FILLININV = 360,            /* PT_FILLININV  */
    PT_COMMA = 361,                /* PT_COMMA  */
    PT_EQGREATER = 362,            /* PT_EQGREATER  */
    PT_LESSEQGREATER = 363,        /* PT_LESSEQGREATER  */
    PT_COLONCOLON = 364,           /* PT_COLONCOLON  */
    PT_COLONEQ = 365,              /* PT_COLONEQ  */
    PT_ASSERT = 366,               /* PT_ASSERT  */
    PT_NEWLINE = 367,              /* PT_NEWLINE  */
    PT_AT = 368,                   /* PT_AT  */
    PT_HASH = 369,                 /* PT_HASH  */
    PT_NATLIT = 370,               /* PT_NATLIT  */
    PT_RAW = 371,                  /* PT_RAW  */
    PT_TIDENT = 372,               /* PT_TIDENT  */
    PT_IDENT = 373,                /* PT_IDENT  */
    PT_STRINGLIT = 374             /* PT_STRINGLIT  */
  };
  typedef enum yytokentype yytoken_kind_t;
#endif

/* Value type.  */
#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED
union YYSTYPE
{
#line 26 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"

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

#line 223 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.h"

};
typedef union YYSTYPE YYSTYPE;
# define YYSTYPE_IS_TRIVIAL 1
# define YYSTYPE_IS_DECLARED 1
#endif




#ifndef YYPUSH_MORE_DEFINED
# define YYPUSH_MORE_DEFINED
enum { YYPUSH_MORE = 4 };
#endif

typedef struct yypstate yypstate;


int yypush_parse (yypstate *ps,
                  int pushed_char, YYSTYPE const *pushed_val, char *path, void *k, struct environment *env);

yypstate *yypstate_new (void);
void yypstate_delete (yypstate *ps);


#endif /* !YY_YY_MNT_D_SJTU_CS2612_2024FALL_CS2612_2024FALL_QCP_SYMBOLICEXE_TEST_COMPILER_PARSER_H_INCLUDED  */
