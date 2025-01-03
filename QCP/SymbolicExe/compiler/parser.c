/* A Bison parser, made by GNU Bison 3.8.2.  */

/* Bison implementation for Yacc-like parsers in C

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

/* C LALR(1) parser skeleton written by Richard Stallman, by
   simplifying the original so-called "semantic" parser.  */

/* DO NOT RELY ON FEATURES THAT ARE NOT DOCUMENTED in the manual,
   especially those whose name start with YY_ or yy_.  They are
   private implementation details that can be changed or removed.  */

/* All symbols defined below should begin with yy or YY, to avoid
   infringing on user name space.  This should be done even for local
   variables, as they might otherwise be expanded by user macros.
   There are some unavoidable exceptions within include files to
   define necessary library symbols; they are noted "INFRINGES ON
   USER NAME SPACE" below.  */

/* Identify Bison output, and Bison version.  */
#define YYBISON 30802

/* Bison version string.  */
#define YYBISON_VERSION "3.8.2"

/* Skeleton name.  */
#define YYSKELETON_NAME "yacc.c"

/* Pure parsers.  */
#define YYPURE 2

/* Push parsers.  */
#define YYPUSH 1

/* Pull parsers.  */
#define YYPULL 0




/* First part of user prologue.  */
#line 5 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"

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

#line 85 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"

# ifndef YY_CAST
#  ifdef __cplusplus
#   define YY_CAST(Type, Val) static_cast<Type> (Val)
#   define YY_REINTERPRET_CAST(Type, Val) reinterpret_cast<Type> (Val)
#  else
#   define YY_CAST(Type, Val) ((Type) (Val))
#   define YY_REINTERPRET_CAST(Type, Val) ((Type) (Val))
#  endif
# endif
# ifndef YY_NULLPTR
#  if defined __cplusplus
#   if 201103L <= __cplusplus
#    define YY_NULLPTR nullptr
#   else
#    define YY_NULLPTR 0
#   endif
#  else
#   define YY_NULLPTR ((void*)0)
#  endif
# endif

#include "parser.h"
/* Symbol kind.  */
enum yysymbol_kind_t
{
  YYSYMBOL_YYEMPTY = -2,
  YYSYMBOL_YYEOF = 0,                      /* "end of file"  */
  YYSYMBOL_YYerror = 1,                    /* error  */
  YYSYMBOL_YYUNDEF = 2,                    /* "invalid token"  */
  YYSYMBOL_PT_EXTERN = 3,                  /* PT_EXTERN  */
  YYSYMBOL_PT_STATIC = 4,                  /* PT_STATIC  */
  YYSYMBOL_PT_CONST = 5,                   /* PT_CONST  */
  YYSYMBOL_PT_RESTRICT = 6,                /* PT_RESTRICT  */
  YYSYMBOL_PT_VOLATILE = 7,                /* PT_VOLATILE  */
  YYSYMBOL_PT_INLINE = 8,                  /* PT_INLINE  */
  YYSYMBOL_PT_STRUCT = 9,                  /* PT_STRUCT  */
  YYSYMBOL_PT_UNION = 10,                  /* PT_UNION  */
  YYSYMBOL_PT_ENUM = 11,                   /* PT_ENUM  */
  YYSYMBOL_PT_INT = 12,                    /* PT_INT  */
  YYSYMBOL_PT_VOID = 13,                   /* PT_VOID  */
  YYSYMBOL_PT_CHAR = 14,                   /* PT_CHAR  */
  YYSYMBOL_PT_SHORT = 15,                  /* PT_SHORT  */
  YYSYMBOL_PT_UNSIGNED = 16,               /* PT_UNSIGNED  */
  YYSYMBOL_PT_LONG = 17,                   /* PT_LONG  */
  YYSYMBOL_PT_IF = 18,                     /* PT_IF  */
  YYSYMBOL_PT_ELSE = 19,                   /* PT_ELSE  */
  YYSYMBOL_PT_WHILE = 20,                  /* PT_WHILE  */
  YYSYMBOL_PT_FOR = 21,                    /* PT_FOR  */
  YYSYMBOL_PT_BREAK = 22,                  /* PT_BREAK  */
  YYSYMBOL_PT_CONTINUE = 23,               /* PT_CONTINUE  */
  YYSYMBOL_PT_RETURN = 24,                 /* PT_RETURN  */
  YYSYMBOL_PT_DO = 25,                     /* PT_DO  */
  YYSYMBOL_PT_SWITCH = 26,                 /* PT_SWITCH  */
  YYSYMBOL_PT_CASE = 27,                   /* PT_CASE  */
  YYSYMBOL_PT_DEFAULT = 28,                /* PT_DEFAULT  */
  YYSYMBOL_PT_SIZEOF = 29,                 /* PT_SIZEOF  */
  YYSYMBOL_PT_TYPEDEF = 30,                /* PT_TYPEDEF  */
  YYSYMBOL_PT_WITH = 31,                   /* PT_WITH  */
  YYSYMBOL_PT_REQUIRE = 32,                /* PT_REQUIRE  */
  YYSYMBOL_PT_ENSURE = 33,                 /* PT_ENSURE  */
  YYSYMBOL_PT_INV = 34,                    /* PT_INV  */
  YYSYMBOL_PT_FORALL = 35,                 /* PT_FORALL  */
  YYSYMBOL_PT_EXISTS = 36,                 /* PT_EXISTS  */
  YYSYMBOL_PT_LET = 37,                    /* PT_LET  */
  YYSYMBOL_PT_EMP = 38,                    /* PT_EMP  */
  YYSYMBOL_PT___RETURN = 39,               /* PT___RETURN  */
  YYSYMBOL_PT_ATMARK = 40,                 /* PT_ATMARK  */
  YYSYMBOL_PT_DATA_AT = 41,                /* PT_DATA_AT  */
  YYSYMBOL_PT_UNDEF_DATA_AT = 42,          /* PT_UNDEF_DATA_AT  */
  YYSYMBOL_PT_FIELD_ADDR = 43,             /* PT_FIELD_ADDR  */
  YYSYMBOL_PT_ARR = 44,                    /* PT_ARR  */
  YYSYMBOL_PT___TIME_COST = 45,            /* PT___TIME_COST  */
  YYSYMBOL_PT_EXTERNCOQ = 46,              /* PT_EXTERNCOQ  */
  YYSYMBOL_PT_FIELD = 47,                  /* PT_FIELD  */
  YYSYMBOL_PT_RECORD = 48,                 /* PT_RECORD  */
  YYSYMBOL_PT_WHERE = 49,                  /* PT_WHERE  */
  YYSYMBOL_PT_WHICHIMPLIES = 50,           /* PT_WHICHIMPLIES  */
  YYSYMBOL_PT_BY = 51,                     /* PT_BY  */
  YYSYMBOL_PT_IMPORTCOQ = 52,              /* PT_IMPORTCOQ  */
  YYSYMBOL_PT_INCLUDESTRATEGIES = 53,      /* PT_INCLUDESTRATEGIES  */
  YYSYMBOL_PT_INCLUDE = 54,                /* PT_INCLUDE  */
  YYSYMBOL_PT_LINEMARK = 55,               /* PT_LINEMARK  */
  YYSYMBOL_PT_LPAREN = 56,                 /* PT_LPAREN  */
  YYSYMBOL_PT_RPAREN = 57,                 /* PT_RPAREN  */
  YYSYMBOL_PT_LBRACK = 58,                 /* PT_LBRACK  */
  YYSYMBOL_PT_RBRACK = 59,                 /* PT_RBRACK  */
  YYSYMBOL_PT_LBRACE = 60,                 /* PT_LBRACE  */
  YYSYMBOL_PT_RBRACE = 61,                 /* PT_RBRACE  */
  YYSYMBOL_PT_PLUS = 62,                   /* PT_PLUS  */
  YYSYMBOL_PT_MINUS = 63,                  /* PT_MINUS  */
  YYSYMBOL_PT_STAR = 64,                   /* PT_STAR  */
  YYSYMBOL_PT_SLASH = 65,                  /* PT_SLASH  */
  YYSYMBOL_PT_PERCENT = 66,                /* PT_PERCENT  */
  YYSYMBOL_PT_LESS = 67,                   /* PT_LESS  */
  YYSYMBOL_PT_LESSEQ = 68,                 /* PT_LESSEQ  */
  YYSYMBOL_PT_GREATER = 69,                /* PT_GREATER  */
  YYSYMBOL_PT_GREATEREQ = 70,              /* PT_GREATEREQ  */
  YYSYMBOL_PT_EQEQ = 71,                   /* PT_EQEQ  */
  YYSYMBOL_PT_EXCLAMEQ = 72,               /* PT_EXCLAMEQ  */
  YYSYMBOL_PT_ANDAND = 73,                 /* PT_ANDAND  */
  YYSYMBOL_PT_BARBAR = 74,                 /* PT_BARBAR  */
  YYSYMBOL_PT_AND = 75,                    /* PT_AND  */
  YYSYMBOL_PT_BAR = 76,                    /* PT_BAR  */
  YYSYMBOL_PT_CARET = 77,                  /* PT_CARET  */
  YYSYMBOL_PT_LESSLESS = 78,               /* PT_LESSLESS  */
  YYSYMBOL_PT_GREATERGREATER = 79,         /* PT_GREATERGREATER  */
  YYSYMBOL_PT_EXCLAM = 80,                 /* PT_EXCLAM  */
  YYSYMBOL_PT_TLIDE = 81,                  /* PT_TLIDE  */
  YYSYMBOL_PT_DOT = 82,                    /* PT_DOT  */
  YYSYMBOL_PT_MINUSGREATER = 83,           /* PT_MINUSGREATER  */
  YYSYMBOL_PT_EQ = 84,                     /* PT_EQ  */
  YYSYMBOL_PT_PLUSEQ = 85,                 /* PT_PLUSEQ  */
  YYSYMBOL_PT_MINUSEQ = 86,                /* PT_MINUSEQ  */
  YYSYMBOL_PT_STAREQ = 87,                 /* PT_STAREQ  */
  YYSYMBOL_PT_SLASHEQ = 88,                /* PT_SLASHEQ  */
  YYSYMBOL_PT_PERCENTEQ = 89,              /* PT_PERCENTEQ  */
  YYSYMBOL_PT_ANDEQ = 90,                  /* PT_ANDEQ  */
  YYSYMBOL_PT_BAREQ = 91,                  /* PT_BAREQ  */
  YYSYMBOL_PT_CARETEQ = 92,                /* PT_CARETEQ  */
  YYSYMBOL_PT_LESSLESSEQ = 93,             /* PT_LESSLESSEQ  */
  YYSYMBOL_PT_GREATERGREATEREQ = 94,       /* PT_GREATERGREATEREQ  */
  YYSYMBOL_PT_QUESTION = 95,               /* PT_QUESTION  */
  YYSYMBOL_PT_PLUSPLUS = 96,               /* PT_PLUSPLUS  */
  YYSYMBOL_PT_MINUSMINUS = 97,             /* PT_MINUSMINUS  */
  YYSYMBOL_PT_SEMI = 98,                   /* PT_SEMI  */
  YYSYMBOL_PT_COLON = 99,                  /* PT_COLON  */
  YYSYMBOL_PT_STARSLASH = 100,             /* PT_STARSLASH  */
  YYSYMBOL_PT_SLASHSTARAT = 101,           /* PT_SLASHSTARAT  */
  YYSYMBOL_PT_SLASHSLASHAT = 102,          /* PT_SLASHSLASHAT  */
  YYSYMBOL_PT_SLASHSTARPROOF = 103,        /* PT_SLASHSTARPROOF  */
  YYSYMBOL_PT_SLASHSLASHPROOF = 104,       /* PT_SLASHSLASHPROOF  */
  YYSYMBOL_PT_FILLININV = 105,             /* PT_FILLININV  */
  YYSYMBOL_PT_COMMA = 106,                 /* PT_COMMA  */
  YYSYMBOL_PT_EQGREATER = 107,             /* PT_EQGREATER  */
  YYSYMBOL_PT_LESSEQGREATER = 108,         /* PT_LESSEQGREATER  */
  YYSYMBOL_PT_COLONCOLON = 109,            /* PT_COLONCOLON  */
  YYSYMBOL_PT_COLONEQ = 110,               /* PT_COLONEQ  */
  YYSYMBOL_PT_ASSERT = 111,                /* PT_ASSERT  */
  YYSYMBOL_PT_NEWLINE = 112,               /* PT_NEWLINE  */
  YYSYMBOL_PT_AT = 113,                    /* PT_AT  */
  YYSYMBOL_PT_HASH = 114,                  /* PT_HASH  */
  YYSYMBOL_PT_NATLIT = 115,                /* PT_NATLIT  */
  YYSYMBOL_PT_RAW = 116,                   /* PT_RAW  */
  YYSYMBOL_PT_TIDENT = 117,                /* PT_TIDENT  */
  YYSYMBOL_PT_IDENT = 118,                 /* PT_IDENT  */
  YYSYMBOL_PT_STRINGLIT = 119,             /* PT_STRINGLIT  */
  YYSYMBOL_YYACCEPT = 120,                 /* $accept  */
  YYSYMBOL_ident = 121,                    /* ident  */
  YYSYMBOL_next = 122,                     /* next  */
  YYSYMBOL_preprocess_cmd = 123,           /* preprocess_cmd  */
  YYSYMBOL_natlist = 124,                  /* natlist  */
  YYSYMBOL_comment = 125,                  /* comment  */
  YYSYMBOL_inv = 126,                      /* inv  */
  YYSYMBOL_which_implies = 127,            /* which_implies  */
  YYSYMBOL_scope_list = 128,               /* scope_list  */
  YYSYMBOL_partial_program = 129,          /* partial_program  */
  YYSYMBOL_130_1 = 130,                    /* $@1  */
  YYSYMBOL_131_2 = 131,                    /* $@2  */
  YYSYMBOL_132_3 = 132,                    /* $@3  */
  YYSYMBOL_133_4 = 133,                    /* $@4  */
  YYSYMBOL_134_5 = 134,                    /* $@5  */
  YYSYMBOL_135_6 = 135,                    /* $@6  */
  YYSYMBOL_storage_specifier = 136,        /* storage_specifier  */
  YYSYMBOL_type_qualifier = 137,           /* type_qualifier  */
  YYSYMBOL_function_specifier = 138,       /* function_specifier  */
  YYSYMBOL_declaration_specifier = 139,    /* declaration_specifier  */
  YYSYMBOL_field_specifier = 140,          /* field_specifier  */
  YYSYMBOL_parameter_specifier = 141,      /* parameter_specifier  */
  YYSYMBOL_type_name = 142,                /* type_name  */
  YYSYMBOL_spec = 143,                     /* spec  */
  YYSYMBOL_abstr_decl = 144,               /* abstr_decl  */
  YYSYMBOL_decl = 145,                     /* decl  */
  YYSYMBOL_abstr_direct = 146,             /* abstr_direct  */
  YYSYMBOL_direct = 147,                   /* direct  */
  YYSYMBOL_abstr_decl_except_function = 148, /* abstr_decl_except_function  */
  YYSYMBOL_abstr_direct_except_function = 149, /* abstr_direct_except_function  */
  YYSYMBOL_exprs = 150,                    /* exprs  */
  YYSYMBOL_expr0 = 151,                    /* expr0  */
  YYSYMBOL_type_arg = 152,                 /* type_arg  */
  YYSYMBOL_varg = 153,                     /* varg  */
  YYSYMBOL_call_varg = 154,                /* call_varg  */
  YYSYMBOL_call_name_varg = 155,           /* call_name_varg  */
  YYSYMBOL_call_name_scope_varg = 156,     /* call_name_scope_varg  */
  YYSYMBOL_expr1 = 157,                    /* expr1  */
  YYSYMBOL_expr2 = 158,                    /* expr2  */
  YYSYMBOL_expr3 = 159,                    /* expr3  */
  YYSYMBOL_expr4 = 160,                    /* expr4  */
  YYSYMBOL_expr5 = 161,                    /* expr5  */
  YYSYMBOL_expr6 = 162,                    /* expr6  */
  YYSYMBOL_expr7 = 163,                    /* expr7  */
  YYSYMBOL_expr8 = 164,                    /* expr8  */
  YYSYMBOL_expr9 = 165,                    /* expr9  */
  YYSYMBOL_expr10 = 166,                   /* expr10  */
  YYSYMBOL_expr11 = 167,                   /* expr11  */
  YYSYMBOL_expr12 = 168,                   /* expr12  */
  YYSYMBOL_expr = 169,                     /* expr  */
  YYSYMBOL_kind0 = 170,                    /* kind0  */
  YYSYMBOL_kind = 171,                     /* kind  */
  YYSYMBOL_atype0 = 172,                   /* atype0  */
  YYSYMBOL_atype1 = 173,                   /* atype1  */
  YYSYMBOL_atype2 = 174,                   /* atype2  */
  YYSYMBOL_atype = 175,                    /* atype  */
  YYSYMBOL_ident_list_space = 176,         /* ident_list_space  */
  YYSYMBOL_ident_list_comma = 177,         /* ident_list_comma  */
  YYSYMBOL_brace_atype_list = 178,         /* brace_atype_list  */
  YYSYMBOL_paren_atype_list = 179,         /* paren_atype_list  */
  YYSYMBOL_paren_atype_list_maybe_null = 180, /* paren_atype_list_maybe_null  */
  YYSYMBOL_brace_comma_atype_list = 181,   /* brace_comma_atype_list  */
  YYSYMBOL_comma_lvar_list = 182,          /* comma_lvar_list  */
  YYSYMBOL_paren_lvar_list = 183,          /* paren_lvar_list  */
  YYSYMBOL_semi_lvar_list = 184,           /* semi_lvar_list  */
  YYSYMBOL_term_list = 185,                /* term_list  */
  YYSYMBOL_ra0_5 = 186,                    /* ra0_5  */
  YYSYMBOL_ra0 = 187,                      /* ra0  */
  YYSYMBOL_ra1 = 188,                      /* ra1  */
  YYSYMBOL_ras = 189,                      /* ras  */
  YYSYMBOL_ra2 = 190,                      /* ra2  */
  YYSYMBOL_ra3 = 191,                      /* ra3  */
  YYSYMBOL_ra4 = 192,                      /* ra4  */
  YYSYMBOL_ra4_75 = 193,                   /* ra4_75  */
  YYSYMBOL_ra5 = 194,                      /* ra5  */
  YYSYMBOL_ra6 = 195,                      /* ra6  */
  YYSYMBOL_ra7 = 196,                      /* ra7  */
  YYSYMBOL_ra8 = 197,                      /* ra8  */
  YYSYMBOL_ra9 = 198,                      /* ra9  */
  YYSYMBOL_ra10 = 199,                     /* ra10  */
  YYSYMBOL_ra11 = 200,                     /* ra11  */
  YYSYMBOL_ra12 = 201,                     /* ra12  */
  YYSYMBOL_ra13 = 202,                     /* ra13  */
  YYSYMBOL_ra14 = 203,                     /* ra14  */
  YYSYMBOL_raq = 204,                      /* raq  */
  YYSYMBOL_forall_aux = 205,               /* forall_aux  */
  YYSYMBOL_exists_aux = 206,               /* exists_aux  */
  YYSYMBOL_tail0 = 207,                    /* tail0  */
  YYSYMBOL_tail = 208,                     /* tail  */
  YYSYMBOL_ra = 209,                       /* ra  */
  YYSYMBOL_initializer = 210,              /* initializer  */
  YYSYMBOL_initializer_list = 211,         /* initializer_list  */
  YYSYMBOL_designator = 212,               /* designator  */
  YYSYMBOL_decls = 213,                    /* decls  */
  YYSYMBOL_214_7 = 214,                    /* $@7  */
  YYSYMBOL_215_8 = 215,                    /* $@8  */
  YYSYMBOL_216_9 = 216,                    /* $@9  */
  YYSYMBOL_217_10 = 217,                   /* $@10  */
  YYSYMBOL_simple_cmd = 218,               /* simple_cmd  */
  YYSYMBOL_for_init = 219,                 /* for_init  */
  YYSYMBOL_for_cond = 220,                 /* for_cond  */
  YYSYMBOL_for_step = 221,                 /* for_step  */
  YYSYMBOL_sepdef = 222,                   /* sepdef  */
  YYSYMBOL_field_dec = 223,                /* field_dec  */
  YYSYMBOL_field_decs = 224,               /* field_decs  */
  YYSYMBOL_enums = 225,                    /* enums  */
  YYSYMBOL_para = 226,                     /* para  */
  YYSYMBOL_paras = 227,                    /* paras  */
  YYSYMBOL_fun_contra_body = 228,          /* fun_contra_body  */
  YYSYMBOL_fun_contra = 229                /* fun_contra  */
};
typedef enum yysymbol_kind_t yysymbol_kind_t;




#ifdef short
# undef short
#endif

/* On compilers that do not define __PTRDIFF_MAX__ etc., make sure
   <limits.h> and (if available) <stdint.h> are included
   so that the code can choose integer types of a good width.  */

#ifndef __PTRDIFF_MAX__
# include <limits.h> /* INFRINGES ON USER NAME SPACE */
# if defined __STDC_VERSION__ && 199901 <= __STDC_VERSION__
#  include <stdint.h> /* INFRINGES ON USER NAME SPACE */
#  define YY_STDINT_H
# endif
#endif

/* Narrow types that promote to a signed type and that can represent a
   signed or unsigned integer of at least N bits.  In tables they can
   save space and decrease cache pressure.  Promoting to a signed type
   helps avoid bugs in integer arithmetic.  */

#ifdef __INT_LEAST8_MAX__
typedef __INT_LEAST8_TYPE__ yytype_int8;
#elif defined YY_STDINT_H
typedef int_least8_t yytype_int8;
#else
typedef signed char yytype_int8;
#endif

#ifdef __INT_LEAST16_MAX__
typedef __INT_LEAST16_TYPE__ yytype_int16;
#elif defined YY_STDINT_H
typedef int_least16_t yytype_int16;
#else
typedef short yytype_int16;
#endif

/* Work around bug in HP-UX 11.23, which defines these macros
   incorrectly for preprocessor constants.  This workaround can likely
   be removed in 2023, as HPE has promised support for HP-UX 11.23
   (aka HP-UX 11i v2) only through the end of 2022; see Table 2 of
   <https://h20195.www2.hpe.com/V2/getpdf.aspx/4AA4-7673ENW.pdf>.  */
#ifdef __hpux
# undef UINT_LEAST8_MAX
# undef UINT_LEAST16_MAX
# define UINT_LEAST8_MAX 255
# define UINT_LEAST16_MAX 65535
#endif

#if defined __UINT_LEAST8_MAX__ && __UINT_LEAST8_MAX__ <= __INT_MAX__
typedef __UINT_LEAST8_TYPE__ yytype_uint8;
#elif (!defined __UINT_LEAST8_MAX__ && defined YY_STDINT_H \
       && UINT_LEAST8_MAX <= INT_MAX)
typedef uint_least8_t yytype_uint8;
#elif !defined __UINT_LEAST8_MAX__ && UCHAR_MAX <= INT_MAX
typedef unsigned char yytype_uint8;
#else
typedef short yytype_uint8;
#endif

#if defined __UINT_LEAST16_MAX__ && __UINT_LEAST16_MAX__ <= __INT_MAX__
typedef __UINT_LEAST16_TYPE__ yytype_uint16;
#elif (!defined __UINT_LEAST16_MAX__ && defined YY_STDINT_H \
       && UINT_LEAST16_MAX <= INT_MAX)
typedef uint_least16_t yytype_uint16;
#elif !defined __UINT_LEAST16_MAX__ && USHRT_MAX <= INT_MAX
typedef unsigned short yytype_uint16;
#else
typedef int yytype_uint16;
#endif

#ifndef YYPTRDIFF_T
# if defined __PTRDIFF_TYPE__ && defined __PTRDIFF_MAX__
#  define YYPTRDIFF_T __PTRDIFF_TYPE__
#  define YYPTRDIFF_MAXIMUM __PTRDIFF_MAX__
# elif defined PTRDIFF_MAX
#  ifndef ptrdiff_t
#   include <stddef.h> /* INFRINGES ON USER NAME SPACE */
#  endif
#  define YYPTRDIFF_T ptrdiff_t
#  define YYPTRDIFF_MAXIMUM PTRDIFF_MAX
# else
#  define YYPTRDIFF_T long
#  define YYPTRDIFF_MAXIMUM LONG_MAX
# endif
#endif

#ifndef YYSIZE_T
# ifdef __SIZE_TYPE__
#  define YYSIZE_T __SIZE_TYPE__
# elif defined size_t
#  define YYSIZE_T size_t
# elif defined __STDC_VERSION__ && 199901 <= __STDC_VERSION__
#  include <stddef.h> /* INFRINGES ON USER NAME SPACE */
#  define YYSIZE_T size_t
# else
#  define YYSIZE_T unsigned
# endif
#endif

#define YYSIZE_MAXIMUM                                  \
  YY_CAST (YYPTRDIFF_T,                                 \
           (YYPTRDIFF_MAXIMUM < YY_CAST (YYSIZE_T, -1)  \
            ? YYPTRDIFF_MAXIMUM                         \
            : YY_CAST (YYSIZE_T, -1)))

#define YYSIZEOF(X) YY_CAST (YYPTRDIFF_T, sizeof (X))


/* Stored state numbers (used for stacks). */
typedef yytype_int16 yy_state_t;

/* State numbers in computations.  */
typedef int yy_state_fast_t;

#ifndef YY_
# if defined YYENABLE_NLS && YYENABLE_NLS
#  if ENABLE_NLS
#   include <libintl.h> /* INFRINGES ON USER NAME SPACE */
#   define YY_(Msgid) dgettext ("bison-runtime", Msgid)
#  endif
# endif
# ifndef YY_
#  define YY_(Msgid) Msgid
# endif
#endif


#ifndef YY_ATTRIBUTE_PURE
# if defined __GNUC__ && 2 < __GNUC__ + (96 <= __GNUC_MINOR__)
#  define YY_ATTRIBUTE_PURE __attribute__ ((__pure__))
# else
#  define YY_ATTRIBUTE_PURE
# endif
#endif

#ifndef YY_ATTRIBUTE_UNUSED
# if defined __GNUC__ && 2 < __GNUC__ + (7 <= __GNUC_MINOR__)
#  define YY_ATTRIBUTE_UNUSED __attribute__ ((__unused__))
# else
#  define YY_ATTRIBUTE_UNUSED
# endif
#endif

/* Suppress unused-variable warnings by "using" E.  */
#if ! defined lint || defined __GNUC__
# define YY_USE(E) ((void) (E))
#else
# define YY_USE(E) /* empty */
#endif

/* Suppress an incorrect diagnostic about yylval being uninitialized.  */
#if defined __GNUC__ && ! defined __ICC && 406 <= __GNUC__ * 100 + __GNUC_MINOR__
# if __GNUC__ * 100 + __GNUC_MINOR__ < 407
#  define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN                           \
    _Pragma ("GCC diagnostic push")                                     \
    _Pragma ("GCC diagnostic ignored \"-Wuninitialized\"")
# else
#  define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN                           \
    _Pragma ("GCC diagnostic push")                                     \
    _Pragma ("GCC diagnostic ignored \"-Wuninitialized\"")              \
    _Pragma ("GCC diagnostic ignored \"-Wmaybe-uninitialized\"")
# endif
# define YY_IGNORE_MAYBE_UNINITIALIZED_END      \
    _Pragma ("GCC diagnostic pop")
#else
# define YY_INITIAL_VALUE(Value) Value
#endif
#ifndef YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_END
#endif
#ifndef YY_INITIAL_VALUE
# define YY_INITIAL_VALUE(Value) /* Nothing. */
#endif

#if defined __cplusplus && defined __GNUC__ && ! defined __ICC && 6 <= __GNUC__
# define YY_IGNORE_USELESS_CAST_BEGIN                          \
    _Pragma ("GCC diagnostic push")                            \
    _Pragma ("GCC diagnostic ignored \"-Wuseless-cast\"")
# define YY_IGNORE_USELESS_CAST_END            \
    _Pragma ("GCC diagnostic pop")
#endif
#ifndef YY_IGNORE_USELESS_CAST_BEGIN
# define YY_IGNORE_USELESS_CAST_BEGIN
# define YY_IGNORE_USELESS_CAST_END
#endif


#define YY_ASSERT(E) ((void) (0 && (E)))

#if 1

/* The parser invokes alloca or malloc; define the necessary symbols.  */

# ifdef YYSTACK_ALLOC
   /* Pacify GCC's 'empty if-body' warning.  */
#  define YYSTACK_FREE(Ptr) do { /* empty */; } while (0)
#  ifndef YYSTACK_ALLOC_MAXIMUM
    /* The OS might guarantee only one guard page at the bottom of the stack,
       and a page size can be as small as 4096 bytes.  So we cannot safely
       invoke alloca (N) if N exceeds 4096.  Use a slightly smaller number
       to allow for a few compiler-allocated temporary stack slots.  */
#   define YYSTACK_ALLOC_MAXIMUM 4032 /* reasonable circa 2006 */
#  endif
# else
#  define YYSTACK_ALLOC YYMALLOC
#  define YYSTACK_FREE YYFREE
#  ifndef YYSTACK_ALLOC_MAXIMUM
#   define YYSTACK_ALLOC_MAXIMUM YYSIZE_MAXIMUM
#  endif
#  if (defined __cplusplus && ! defined EXIT_SUCCESS \
       && ! ((defined YYMALLOC || defined malloc) \
             && (defined YYFREE || defined free)))
#   include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
#   ifndef EXIT_SUCCESS
#    define EXIT_SUCCESS 0
#   endif
#  endif
#  ifndef YYMALLOC
#   define YYMALLOC malloc
#   if ! defined malloc && ! defined EXIT_SUCCESS
void *malloc (YYSIZE_T); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
#  ifndef YYFREE
#   define YYFREE free
#   if ! defined free && ! defined EXIT_SUCCESS
void free (void *); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
# endif
#endif /* 1 */

#if (! defined yyoverflow \
     && (! defined __cplusplus \
         || (defined YYSTYPE_IS_TRIVIAL && YYSTYPE_IS_TRIVIAL)))

/* A type that is properly aligned for any stack member.  */
union yyalloc
{
  yy_state_t yyss_alloc;
  YYSTYPE yyvs_alloc;
};

/* The size of the maximum gap between one aligned stack and the next.  */
# define YYSTACK_GAP_MAXIMUM (YYSIZEOF (union yyalloc) - 1)

/* The size of an array large to enough to hold all stacks, each with
   N elements.  */
# define YYSTACK_BYTES(N) \
     ((N) * (YYSIZEOF (yy_state_t) + YYSIZEOF (YYSTYPE)) \
      + YYSTACK_GAP_MAXIMUM)

# define YYCOPY_NEEDED 1

/* Relocate STACK from its old location to the new one.  The
   local variables YYSIZE and YYSTACKSIZE give the old and new number of
   elements in the stack, and YYPTR gives the new location of the
   stack.  Advance YYPTR to a properly aligned location for the next
   stack.  */
# define YYSTACK_RELOCATE(Stack_alloc, Stack)                           \
    do                                                                  \
      {                                                                 \
        YYPTRDIFF_T yynewbytes;                                         \
        YYCOPY (&yyptr->Stack_alloc, Stack, yysize);                    \
        Stack = &yyptr->Stack_alloc;                                    \
        yynewbytes = yystacksize * YYSIZEOF (*Stack) + YYSTACK_GAP_MAXIMUM; \
        yyptr += yynewbytes / YYSIZEOF (*yyptr);                        \
      }                                                                 \
    while (0)

#endif

#if defined YYCOPY_NEEDED && YYCOPY_NEEDED
/* Copy COUNT objects from SRC to DST.  The source and destination do
   not overlap.  */
# ifndef YYCOPY
#  if defined __GNUC__ && 1 < __GNUC__
#   define YYCOPY(Dst, Src, Count) \
      __builtin_memcpy (Dst, Src, YY_CAST (YYSIZE_T, (Count)) * sizeof (*(Src)))
#  else
#   define YYCOPY(Dst, Src, Count)              \
      do                                        \
        {                                       \
          YYPTRDIFF_T yyi;                      \
          for (yyi = 0; yyi < (Count); yyi++)   \
            (Dst)[yyi] = (Src)[yyi];            \
        }                                       \
      while (0)
#  endif
# endif
#endif /* !YYCOPY_NEEDED */

/* YYFINAL -- State number of the termination state.  */
#define YYFINAL  184
/* YYLAST -- Last index in YYTABLE.  */
#define YYLAST   2295

/* YYNTOKENS -- Number of terminals.  */
#define YYNTOKENS  120
/* YYNNTS -- Number of nonterminals.  */
#define YYNNTS  110
/* YYNRULES -- Number of rules.  */
#define YYNRULES  475
/* YYNSTATES -- Number of states.  */
#define YYNSTATES  1013

/* YYMAXUTOK -- Last valid token kind.  */
#define YYMAXUTOK   374


/* YYTRANSLATE(TOKEN-NUM) -- Symbol number corresponding to TOKEN-NUM
   as returned by yylex, with out-of-bounds checking.  */
#define YYTRANSLATE(YYX)                                \
  (0 <= (YYX) && (YYX) <= YYMAXUTOK                     \
   ? YY_CAST (yysymbol_kind_t, yytranslate[YYX])        \
   : YYSYMBOL_YYUNDEF)

/* YYTRANSLATE[TOKEN-NUM] -- Symbol number corresponding to TOKEN-NUM
   as returned by yylex.  */
static const yytype_int8 yytranslate[] =
{
       0,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     1,     2,     3,     4,
       5,     6,     7,     8,     9,    10,    11,    12,    13,    14,
      15,    16,    17,    18,    19,    20,    21,    22,    23,    24,
      25,    26,    27,    28,    29,    30,    31,    32,    33,    34,
      35,    36,    37,    38,    39,    40,    41,    42,    43,    44,
      45,    46,    47,    48,    49,    50,    51,    52,    53,    54,
      55,    56,    57,    58,    59,    60,    61,    62,    63,    64,
      65,    66,    67,    68,    69,    70,    71,    72,    73,    74,
      75,    76,    77,    78,    79,    80,    81,    82,    83,    84,
      85,    86,    87,    88,    89,    90,    91,    92,    93,    94,
      95,    96,    97,    98,    99,   100,   101,   102,   103,   104,
     105,   106,   107,   108,   109,   110,   111,   112,   113,   114,
     115,   116,   117,   118,   119
};

#if YYDEBUG
/* YYRLINE[YYN] -- Source line where rule number YYN was defined.  */
static const yytype_int16 yyrline[] =
{
       0,   322,   322,   324,   329,   330,   331,   332,   336,   348,
     350,   352,   369,   386,   395,   396,   400,   402,   404,   406,
     408,   410,   412,   414,   419,   421,   423,   425,   430,   432,
     434,   436,   441,   443,   448,   448,   450,   450,   452,   452,
     454,   454,   456,   456,   458,   458,   460,   462,   464,   466,
     468,   470,   472,   474,   476,   478,   480,   482,   484,   486,
     488,   490,   492,   494,   496,   498,   500,   502,   504,   506,
     508,   510,   512,   514,   516,   518,   520,   522,   524,   526,
     528,   530,   532,   534,   536,   538,   540,   542,   544,   546,
     548,   550,   552,   554,   556,   558,   560,   562,   564,   569,
     569,   571,   571,   571,   573,   576,   578,   580,   582,   587,
     589,   594,   596,   598,   603,   605,   610,   612,   614,   616,
     618,   620,   622,   624,   626,   628,   630,   632,   634,   636,
     638,   640,   642,   644,   646,   648,   650,   652,   654,   656,
     658,   660,   662,   664,   666,   668,   673,   675,   677,   682,
     684,   686,   691,   693,   695,   697,   699,   701,   703,   708,
     710,   712,   714,   716,   721,   723,   725,   730,   732,   734,
     736,   738,   746,   748,   753,   755,   757,   759,   761,   766,
     768,   773,   775,   780,   782,   784,   789,   791,   793,   798,
     800,   802,   807,   809,   811,   813,   815,   817,   819,   821,
     826,   828,   830,   832,   834,   836,   838,   840,   845,   847,
     849,   851,   856,   858,   860,   865,   867,   869,   874,   876,
     878,   880,   882,   887,   889,   891,   896,   898,   903,   905,
     910,   912,   917,   919,   924,   926,   931,   933,   942,   944,
     949,   951,   956,   958,   963,   965,   970,   972,   977,   979,
     984,   986,   991,   993,   998,  1000,  1002,  1004,  1009,  1011,
    1016,  1018,  1020,  1025,  1027,  1029,  1031,  1036,  1038,  1040,
    1042,  1047,  1049,  1051,  1053,  1058,  1060,  1065,  1067,  1069,
    1071,  1073,  1075,  1084,  1086,  1091,  1093,  1095,  1097,  1099,
    1101,  1103,  1105,  1107,  1109,  1111,  1113,  1115,  1117,  1119,
    1121,  1126,  1128,  1130,  1132,  1134,  1136,  1138,  1140,  1142,
    1144,  1146,  1151,  1153,  1158,  1160,  1162,  1164,  1166,  1168,
    1170,  1172,  1174,  1179,  1181,  1183,  1185,  1190,  1192,  1194,
    1199,  1201,  1206,  1208,  1210,  1215,  1217,  1219,  1221,  1223,
    1228,  1230,  1232,  1237,  1239,  1244,  1246,  1251,  1253,  1258,
    1260,  1265,  1267,  1272,  1274,  1276,  1281,  1286,  1288,  1293,
    1295,  1297,  1299,  1301,  1303,  1308,  1310,  1312,  1314,  1316,
    1318,  1320,  1322,  1324,  1326,  1328,  1330,  1335,  1337,  1339,
    1341,  1343,  1345,  1347,  1349,  1351,  1353,  1358,  1360,  1362,
    1364,  1366,  1368,  1370,  1372,  1374,  1376,  1378,  1380,  1382,
    1384,  1386,  1388,  1390,  1392,  1394,  1396,  1398,  1405,  1407,
    1415,  1417,  1422,  1424,  1426,  1428,  1433,  1435,  1437,  1439,
    1447,  1447,  1449,  1449,  1451,  1451,  1453,  1453,  1458,  1460,
    1462,  1464,  1466,  1468,  1470,  1472,  1474,  1476,  1478,  1480,
    1482,  1484,  1486,  1488,  1493,  1495,  1500,  1502,  1507,  1509,
    1518,  1520,  1522,  1524,  1529,  1534,  1536,  1541,  1543,  1545,
    1547,  1549,  1551,  1556,  1558,  1560,  1565,  1567,  1572,  1574,
    1578,  1581,  1587,  1589,  1591,  1593
};
#endif

/** Accessing symbol of state STATE.  */
#define YY_ACCESSING_SYMBOL(State) YY_CAST (yysymbol_kind_t, yystos[State])

#if 1
/* The user-facing name of the symbol whose (internal) number is
   YYSYMBOL.  No bounds checking.  */
static const char *yysymbol_name (yysymbol_kind_t yysymbol) YY_ATTRIBUTE_UNUSED;

/* YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
   First, the terminals, then, starting at YYNTOKENS, nonterminals.  */
static const char *const yytname[] =
{
  "\"end of file\"", "error", "\"invalid token\"", "PT_EXTERN",
  "PT_STATIC", "PT_CONST", "PT_RESTRICT", "PT_VOLATILE", "PT_INLINE",
  "PT_STRUCT", "PT_UNION", "PT_ENUM", "PT_INT", "PT_VOID", "PT_CHAR",
  "PT_SHORT", "PT_UNSIGNED", "PT_LONG", "PT_IF", "PT_ELSE", "PT_WHILE",
  "PT_FOR", "PT_BREAK", "PT_CONTINUE", "PT_RETURN", "PT_DO", "PT_SWITCH",
  "PT_CASE", "PT_DEFAULT", "PT_SIZEOF", "PT_TYPEDEF", "PT_WITH",
  "PT_REQUIRE", "PT_ENSURE", "PT_INV", "PT_FORALL", "PT_EXISTS", "PT_LET",
  "PT_EMP", "PT___RETURN", "PT_ATMARK", "PT_DATA_AT", "PT_UNDEF_DATA_AT",
  "PT_FIELD_ADDR", "PT_ARR", "PT___TIME_COST", "PT_EXTERNCOQ", "PT_FIELD",
  "PT_RECORD", "PT_WHERE", "PT_WHICHIMPLIES", "PT_BY", "PT_IMPORTCOQ",
  "PT_INCLUDESTRATEGIES", "PT_INCLUDE", "PT_LINEMARK", "PT_LPAREN",
  "PT_RPAREN", "PT_LBRACK", "PT_RBRACK", "PT_LBRACE", "PT_RBRACE",
  "PT_PLUS", "PT_MINUS", "PT_STAR", "PT_SLASH", "PT_PERCENT", "PT_LESS",
  "PT_LESSEQ", "PT_GREATER", "PT_GREATEREQ", "PT_EQEQ", "PT_EXCLAMEQ",
  "PT_ANDAND", "PT_BARBAR", "PT_AND", "PT_BAR", "PT_CARET", "PT_LESSLESS",
  "PT_GREATERGREATER", "PT_EXCLAM", "PT_TLIDE", "PT_DOT",
  "PT_MINUSGREATER", "PT_EQ", "PT_PLUSEQ", "PT_MINUSEQ", "PT_STAREQ",
  "PT_SLASHEQ", "PT_PERCENTEQ", "PT_ANDEQ", "PT_BAREQ", "PT_CARETEQ",
  "PT_LESSLESSEQ", "PT_GREATERGREATEREQ", "PT_QUESTION", "PT_PLUSPLUS",
  "PT_MINUSMINUS", "PT_SEMI", "PT_COLON", "PT_STARSLASH", "PT_SLASHSTARAT",
  "PT_SLASHSLASHAT", "PT_SLASHSTARPROOF", "PT_SLASHSLASHPROOF",
  "PT_FILLININV", "PT_COMMA", "PT_EQGREATER", "PT_LESSEQGREATER",
  "PT_COLONCOLON", "PT_COLONEQ", "PT_ASSERT", "PT_NEWLINE", "PT_AT",
  "PT_HASH", "PT_NATLIT", "PT_RAW", "PT_TIDENT", "PT_IDENT",
  "PT_STRINGLIT", "$accept", "ident", "next", "preprocess_cmd", "natlist",
  "comment", "inv", "which_implies", "scope_list", "partial_program",
  "$@1", "$@2", "$@3", "$@4", "$@5", "$@6", "storage_specifier",
  "type_qualifier", "function_specifier", "declaration_specifier",
  "field_specifier", "parameter_specifier", "type_name", "spec",
  "abstr_decl", "decl", "abstr_direct", "direct",
  "abstr_decl_except_function", "abstr_direct_except_function", "exprs",
  "expr0", "type_arg", "varg", "call_varg", "call_name_varg",
  "call_name_scope_varg", "expr1", "expr2", "expr3", "expr4", "expr5",
  "expr6", "expr7", "expr8", "expr9", "expr10", "expr11", "expr12", "expr",
  "kind0", "kind", "atype0", "atype1", "atype2", "atype",
  "ident_list_space", "ident_list_comma", "brace_atype_list",
  "paren_atype_list", "paren_atype_list_maybe_null",
  "brace_comma_atype_list", "comma_lvar_list", "paren_lvar_list",
  "semi_lvar_list", "term_list", "ra0_5", "ra0", "ra1", "ras", "ra2",
  "ra3", "ra4", "ra4_75", "ra5", "ra6", "ra7", "ra8", "ra9", "ra10",
  "ra11", "ra12", "ra13", "ra14", "raq", "forall_aux", "exists_aux",
  "tail0", "tail", "ra", "initializer", "initializer_list", "designator",
  "decls", "$@7", "$@8", "$@9", "$@10", "simple_cmd", "for_init",
  "for_cond", "for_step", "sepdef", "field_dec", "field_decs", "enums",
  "para", "paras", "fun_contra_body", "fun_contra", YY_NULLPTR
};

static const char *
yysymbol_name (yysymbol_kind_t yysymbol)
{
  return yytname[yysymbol];
}
#endif

#define YYPACT_NINF (-849)

#define yypact_value_is_default(Yyn) \
  ((Yyn) == YYPACT_NINF)

#define YYTABLE_NINF (-427)

#define yytable_value_is_error(Yyn) \
  0

/* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
   STATE-NUM.  */
static const yytype_int16 yypact[] =
{
    1350,  -849,  -849,  -849,  -849,  -849,  -849,   150,   164,   351,
    -849,  -849,  -849,  -849,   606,   468,   109,  -849,   123,   126,
      23,   111,  1755,  -849,   167,  1900,   138,   190,  1305,   141,
     178,  1467,  -849,  -849,  1900,  1900,  1900,  1900,  1900,  1900,
    1900,  1900,  -849,  1726,  1813,   193,   270,  -849,  -849,  -849,
    -849,   324,  1350,  1350,  1046,  1046,  1046,   195,  -849,  -849,
     433,  -849,   563,   313,    22,   510,   428,   294,   341,   359,
     404,   137,  1027,   343,   515,  -849,  -849,   129,   968,   219,
     447,   235,  -849,  -849,  -849,   526,  -849,   450,  1900,  1900,
     612,  -849,  -849,  -849,   367,  1900,   385,  -849,  1046,   150,
     164,   351,  1046,  1046,   195,  -849,  -849,  -849,   403,   452,
     462,  -849,  -849,  -849,  -849,  -849,  -849,  -849,  -849,   447,
     431,  2089,   214,   186,   447,  -849,  -849,   434,   437,   488,
     513,  -849,    63,   458,   464,  1552,  2089,  2089,  1947,  2089,
    2089,  2089,   491,  1995,   107,  -849,  -849,   494,   497,   514,
    -849,  -849,   534,    33,  -849,   578,    36,  -849,   588,   567,
     623,   558,   561,   564,   573,   253,  -849,  -849,  -849,  -849,
    -849,   517,   599,   447,   182,   562,   571,   576,   593,   595,
     609,   614,   632,   622,  -849,  -849,  -849,  -849,  -849,  -849,
     195,   195,  -849,   195,   157,   368,   709,  1900,   447,   447,
    1900,  1900,  1900,  1900,  1900,  1900,  1900,  1900,  1900,  1900,
    1900,  1900,  1900,  1900,  1900,  1900,  1900,  1900,  1900,  1900,
    1900,  1900,  1900,  1900,  1900,  1900,  1900,  1900,  1900,  1900,
    -849,  -849,  -849,  -849,  1046,   195,  -849,   638,   676,  1642,
    -849,  -849,   682,  1666,  -849,    48,   683,   447,  -849,  -849,
     733,  -849,   689,   690,  -849,   652,  1880,  -849,   696,  -849,
     697,   707,   708,   717,  -849,  -849,   650,   226,  1192,  1900,
     403,  -849,   389,  1900,  -849,   669,  1046,   727,   447,    35,
    -849,   447,   447,    28,  -849,   725,  2089,  2089,  2089,  2089,
     217,   447,   447,    -4,   685,   686,   687,   694,   726,   738,
    -849,  -849,  -849,  -849,  1046,  -849,  -849,  -849,  -849,  -849,
    -849,  -849,  -849,  -849,  2089,    67,  -849,  -849,  -849,  -849,
    2042,  2089,   380,   393,  1046,   447,  -849,  2089,  2089,  2089,
    2089,  2089,  2089,   281,  2089,  2089,  2089,  2089,  2089,  2089,
    2089,  2089,  2089,  2089,  2089,  2089,  2089,  2089,  2089,   447,
    2089,   447,  -849,   670,   217,   447,   139,   684,   688,   692,
     693,  -849,  -849,  -849,  -849,  -849,  -849,  -849,   740,  -849,
    -849,  -849,  1457,    38,   700,   703,  1291,  1900,   698,   744,
     706,   747,  -849,  -849,  -849,  -849,  -849,   563,   563,   313,
     313,    22,    22,    22,    22,   510,   510,   428,   294,   341,
     359,   404,   716,  -849,  -849,  -849,  -849,  -849,  -849,  -849,
    -849,  -849,  -849,  -849,  -849,  -849,  1494,  -849,   718,   761,
    -849,   731,   769,    18,   447,  -849,   770,  -849,  -849,  -849,
    -849,  -849,   734,   695,   765,  -849,  1682,  1695,   447,   735,
     728,  -849,  -849,  -849,   378,   778,   730,   781,   783,  -849,
    1428,  1900,  -849,  -849,   786,   447,   447,   746,  2089,  -849,
     748,     6,   750,  2089,  -849,   117,   745,    65,   749,   751,
     447,   217,   752,   395,   255,   281,  -849,  -849,  -849,  -849,
    -849,  2089,  -849,   792,   803,   447,   447,  -849,  -849,   797,
     596,  -849,  1173,  -849,   672,  -849,  -849,  -849,  -849,  -849,
    -849,  -849,  -849,   607,  -849,   607,  -849,   281,  -849,  -849,
     281,    93,  -849,   607,   192,  -849,  -849,  -849,  -849,   633,
    -849,   633,  -849,   633,  -849,   633,  -849,   633,   590,  -849,
     590,  -849,   590,   644,  -849,   644,   787,  -849,   787,   788,
    -849,   788,   791,  -849,   791,   790,  -849,  -849,  -849,  -849,
    -849,   813,   817,   447,   820,  -849,   757,   395,   281,  -849,
    -849,  -849,  -849,  -849,  1839,  -849,   767,   245,  2089,   472,
    -849,   774,  -849,   195,  -849,   821,   818,   490,   775,  1900,
    -849,  1900,  -849,  -849,   798,  -849,   799,   780,   800,  -849,
     812,  -849,  -849,   841,  -849,  -849,  -849,   851,  -849,   852,
     854,  -849,   195,   378,  1900,   378,  -849,  -849,   493,  -849,
    1305,  -849,  -849,  -849,   860,   859,  -849,  -849,  -849,   263,
    -849,   263,   208,   263,  -849,   836,   447,   237,    39,   864,
    1552,  -849,  1046,  1268,  1552,   823,  -849,   447,   395,   155,
     263,   246,   824,  -849,  -849,  2089,   447,   874,  -849,  -849,
     857,   858,   862,   866,  -849,  2177,  2177,  2177,   884,  -849,
     281,   281,  2177,  2177,  2177,  2177,  2177,  2177,  2177,  2177,
    2177,  2177,  2177,  2177,  2177,  2177,   447,   447,  -849,  2089,
    -849,   227,   830,  1900,   447,   840,   888,   867,   855,   844,
     447,   447,   400,    26,   920,   921,   447,  -849,   247,     5,
    -849,  -849,  -849,   354,   447,   904,   856,   490,  -849,  -849,
    -849,  -849,   863,   447,  -849,  -849,  -849,  -849,  -849,  -849,
     903,   905,  -849,  1629,  1900,  -849,  -849,  -849,   906,   879,
     908,   883,  2089,  -849,   909,   887,  2089,   865,    59,   281,
     447,   907,   447,   910,   886,   933,   936,   952,   911,   953,
     912,   913,   914,   902,  -849,   447,   447,   955,   930,   246,
    -849,   915,   957,  -849,  -849,  -849,  -849,   447,   447,   447,
     447,   447,  1552,  2177,  2177,  2133,  2177,  2177,  2177,   566,
    -849,   281,  -849,  -849,  -849,   970,   447,   447,  -849,   964,
     312,  1839,  -849,  1457,  -849,   195,   925,    79,  -849,  2089,
     994,  2089,  2089,   672,  -849,  -849,  1457,   924,   934,   447,
     447,   947,   935,  -849,  -849,   447,  -849,   965,   447,  -849,
    -849,  -849,  -849,   979,  1007,   430,   281,   222,   281,  -849,
     240,   281,  -849,   447,   961,   246,   962,  -849,  2089,  1012,
    2089,  2089,  -849,  -849,   447,  -849,   447,  2089,  2089,   246,
     971,  1010,  1013,   217,   281,  1015,   246,  1020,  -849,  1016,
    1017,  1018,  1019,  1025,  1046,   447,  1022,  1026,   312,  -849,
    -849,   983,  -849,   281,  1030,   246,  1058,  2089,  1064,  -849,
    -849,  1024,   195,  -849,  1068,  1043,  -849,  2089,   447,  -849,
    -849,  -849,  -849,  -849,  2089,  -849,  1072,  2089,  -849,  1073,
    2089,  -849,  1074,  -849,  1071,  1075,   447,  -849,  1048,  -849,
    1077,  1078,  1080,  1032,  1082,  1083,   281,  1041,   447,  -849,
    1085,  -849,  -849,   447,  -849,  -849,  -849,  -849,  -849,  2177,
    1086,  -849,  1031,   447,  -849,  1839,  1087,  -849,  1089,  2089,
    1113,  2089,  1042,  1053,  -849,   284,   281,  1047,  -849,  -849,
     436,  -849,   364,  -849,   388,  -849,  1049,  -849,  2089,  -849,
    -849,  -849,  2089,  -849,   395,  1054,  -849,  1093,   217,  1050,
    2177,  -849,  1095,  -849,   400,  1030,  -849,  2089,  -849,   195,
    -849,  -849,  1051,   447,  2089,  -849,  2089,  -849,  2089,  -849,
    1071,  -849,  1101,  -849,   447,  1060,  -849,  1055,  -849,  -849,
    -849,  -849,   447,  -849,  -849,  -849,  -849,  -849,  -849,  -849,
    -849,  -849,  -849
};

/* YYDEFACT[STATE-NUM] -- Default reduction number in state STATE-NUM.
   Performed when YYTABLE does not specify something else to do.  Zero
   means the default is an error.  */
static const yytype_int16 yydefact[] =
{
       0,    99,   100,   101,   102,   103,   104,     0,     0,     0,
     121,   116,   117,   119,   126,   122,     0,    53,     0,     0,
       0,     0,     0,    54,     0,     0,     0,     0,     0,     0,
       0,     0,    59,    60,     0,     0,     0,     0,     0,     0,
       0,     0,    85,     0,     0,     0,     0,   175,   145,   177,
     176,     0,     5,     4,     0,     0,     0,     0,   105,   192,
     200,   208,   212,   215,   218,   223,   226,   228,   230,   232,
     234,   236,   428,     0,     0,     2,     3,   132,     0,   133,
       0,   134,   127,   118,   120,   128,   124,   123,     0,     0,
       0,    47,    48,    50,     0,     0,     0,    58,     0,     0,
       0,     0,     0,     0,     0,   111,     8,    14,   114,     0,
       0,   202,   201,   205,   206,   203,   204,   429,   431,     0,
       0,     0,     0,     0,     0,   298,   299,     0,     0,     0,
       0,   287,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,   288,   283,     0,     0,     0,
     285,   301,   314,     0,   323,   327,   330,   332,   335,   340,
     343,   345,   347,   349,   351,   353,   408,   378,   377,   387,
     409,    16,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     1,     7,     6,   106,   107,   108,
       0,     0,   160,     0,    34,   151,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
     430,   432,    46,   135,     0,     0,   109,     0,     0,     0,
      91,   139,     0,     0,    88,   457,     0,     0,    93,   130,
     129,   125,     0,     0,   444,     0,     0,    49,     0,    57,
       0,   132,   133,   134,   112,   113,    36,     0,     0,     0,
     148,   115,   147,     0,   174,     0,     0,    24,     0,     0,
     357,     0,     0,     0,   358,     0,     0,     0,     0,     0,
       0,     0,     0,   277,     0,     0,     0,     0,     0,     0,
     316,   380,   315,   379,     0,   320,   384,   321,   385,   317,
     381,   318,   382,    69,     0,    18,   284,    61,    64,    65,
       0,     0,     0,     0,     0,     0,   311,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,    95,     0,     0,     0,   277,     0,     0,     0,
       0,    70,    62,    63,    66,    94,    67,    68,     0,   149,
     150,    96,     0,     0,     0,     0,     0,     0,   196,     0,
     172,     0,   194,   195,   209,   210,   211,   213,   214,   216,
     217,   219,   221,   220,   222,   224,   225,   227,   229,   231,
     233,   235,     0,   433,   434,   435,   436,   437,   438,   439,
     440,   441,   442,   443,   110,   454,   455,   136,   137,     0,
     140,   141,     0,     0,     0,   143,     0,   131,    52,    51,
     445,   446,     0,     0,     0,   178,     0,     0,     0,     0,
       0,    13,    15,   157,   465,     0,   466,     0,     0,   146,
       0,     0,   207,    71,     0,     0,   250,     0,     0,   360,
       0,   250,     0,     0,   366,     0,     0,     0,     0,     0,
       0,   277,     0,   260,     0,     0,   280,    76,    74,    10,
      12,     0,   286,     0,    25,     0,     0,   310,   312,     0,
       0,   307,     0,   308,     0,   309,   313,   324,   388,   325,
     389,   326,   390,   328,   391,   329,   392,     0,   242,   244,
     246,   248,   331,   327,   330,   333,   393,   334,   394,   336,
     395,   338,   397,   337,   396,   339,   398,   335,   341,   399,
     342,   400,   340,   344,   401,   343,   346,   402,   345,   348,
     403,   347,   350,   404,   349,   352,   405,   354,   406,   355,
     407,    17,    28,    32,    20,    72,     0,   260,     0,    75,
      73,     9,    11,   159,     0,   410,    38,     0,     0,   473,
     472,     0,    35,     0,   162,     0,     0,     0,   197,     0,
     193,     0,   456,    90,   138,    87,   142,     0,   459,   458,
     144,   447,   448,     0,    55,    56,   137,     0,   141,     0,
       0,    37,     0,     0,     0,   166,   463,   464,   165,   152,
       0,   158,   154,   155,     0,     0,   300,    26,   251,     0,
     359,     0,     0,     0,   365,     0,     0,   267,     0,     0,
       0,   291,     0,     0,     0,     0,    79,     0,   260,     0,
       0,     0,     0,   322,   386,     0,     0,    19,    22,   302,
       0,     0,     0,     0,   356,     0,     0,     0,     0,   245,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,    33,     0,
      80,     0,     0,     0,     0,   412,     0,     0,     0,     0,
       0,     0,   271,     0,     0,     0,     0,   474,     0,   420,
      41,   163,   161,     0,     0,   189,     0,     0,   173,   237,
      89,    86,   461,     0,    92,   449,   138,   142,   144,    43,
       0,     0,   164,     0,     0,   467,   156,   153,     0,     0,
       0,     0,     0,   372,     0,     0,     0,   252,     0,     0,
       0,     0,     0,     0,     0,     0,     0,   145,     3,     0,
       0,     0,     0,     0,   261,     0,     0,     0,     0,     0,
     238,   240,     0,    78,   319,   383,    27,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,   314,
     243,   247,   249,    21,    30,    29,     0,     0,    77,     0,
     417,     0,   411,     0,    39,     0,     0,     0,   273,     0,
       0,     0,     0,     0,    97,    98,     0,     0,     0,     0,
       0,     0,   183,   186,   191,     0,   198,     0,     0,   460,
     167,   169,   170,     0,     0,     0,     0,     0,     0,   371,
       0,     0,   453,     0,   265,     0,   268,   269,     0,     0,
       0,     0,   289,   292,     0,   293,     0,     0,     0,     0,
       0,     0,     0,   278,     0,     0,     0,   258,    23,     0,
       0,     0,     0,     0,     0,     0,     0,     0,   416,   419,
     414,   413,    45,     0,   256,     0,     0,     0,     0,   468,
     475,   422,     0,   425,     0,     0,   184,     0,     0,   190,
     199,   462,   171,   168,     0,   362,     0,     0,   368,     0,
       0,   374,     0,   253,     0,     0,     0,   452,     0,   451,
       0,     0,     0,     0,     0,     0,     0,     0,     0,   281,
       0,   239,   241,     0,   259,   304,   303,   306,   305,     0,
       0,    31,     0,     0,   418,     0,     0,   257,     0,     0,
       0,     0,     0,     0,   421,   188,     0,   181,   185,   361,
       0,   367,     0,   373,     0,   266,   263,   270,     0,   290,
     295,   294,     0,   296,   260,     0,    81,     0,   279,     0,
       0,    82,     0,   415,   272,   254,   470,     0,   471,     0,
     427,   187,   179,     0,     0,   364,     0,   370,     0,   376,
       0,   450,     0,   262,   275,     0,   282,     0,   274,   255,
     469,   423,     0,   182,   363,   369,   375,   264,   297,   276,
      83,    84,   180
};

/* YYPGOTO[NTERM-NUM].  */
static const yytype_int16 yypgoto[] =
{
    -849,    -7,   665,  -849,  -849,  1117,  1118,  1121,  -415,  -849,
    -849,  -849,  -849,  -849,  -849,  -849,  -849,   -21,   -25,    95,
    -849,  1138,   -71,   -23,   302,   -32,  -849,  -849,   -17,  -849,
     589,  -849,  -829,   189,   224,  -849,   463,  -849,    92,   516,
     523,   454,   511,   978,   960,   977,  1011,   976,  -849,   819,
    -849,  -671,  -504,   535,  -849,  -371,  -258,   361,  -586,  -166,
    -536,  -848,  -710,  -654,  -758,  -128,  1084,  -849,   569,  -849,
    -122,   548,   662,  -226,   591,  -266,  -301,  -283,  -278,  -298,
     900,  -849,   392,  -849,  -849,  -269,  -272,   764,   394,   187,
    -363,  -742,  -705,  -576,  -849,  -849,  -849,  -849,   -77,  -849,
    -849,  -849,  1185,  -849,   -49,  -225,  -849,  -345,  -482,  -849
};

/* YYDEFGOTO[NTERM-NUM].  */
static const yytype_int16 yydefgoto[] =
{
       0,   508,    51,    52,   267,   147,   148,   149,   554,    53,
     374,   439,   688,   375,   440,   689,    54,    55,    56,   108,
     235,   444,   109,    58,   271,   699,   272,   195,   607,   608,
     379,    59,   886,   812,   813,   705,   706,    60,    61,    62,
      63,    64,    65,    66,    67,    68,    69,    70,    71,   565,
     761,   762,   509,   510,   511,   512,   618,   738,   693,   294,
     639,   628,   629,   694,   851,   476,   150,   151,   152,   153,
     154,   155,   156,   157,   158,   159,   160,   161,   162,   163,
     164,   165,   166,   167,   168,   280,   284,   169,   170,   171,
     685,   686,   687,   700,   807,   942,   808,   943,    73,   256,
     433,   594,   172,   237,   238,   246,   446,   447,   570,   571
};

/* YYTABLE[YYPACT[STATE-NUM]] -- What to do in state STATE-NUM.  If
   positive, shift that token.  If negative, reduce the rule whose
   number is the opposite.  If YYTABLE_NINF, syntax error.  */
static const yytype_int16 yytable[] =
{
      77,    79,    81,   103,   295,   105,   659,   102,   357,   566,
     459,   464,   654,   255,   300,   302,   305,   307,   309,   311,
     457,   681,   426,   460,   462,   194,   719,   260,   866,   242,
     837,   575,   839,   729,   474,   731,   193,   735,   798,   800,
     617,   533,   535,   535,   535,   535,   358,   542,   544,   870,
     192,   236,   470,   234,   758,   236,   955,   234,   799,   948,
     536,   538,   538,   538,   298,   622,   539,   541,   541,   567,
     568,   648,   266,   245,   528,   530,   532,   532,   532,   532,
     532,   587,   690,   193,   281,   869,   282,   697,   855,   806,
     326,   278,   261,   262,   263,    57,   741,   192,   331,   332,
     205,   206,   754,  -424,   642,   614,   475,   485,   515,   517,
     290,   291,   275,    75,    76,   279,   283,   285,   486,   292,
     834,    91,   631,    75,    76,   293,   111,   112,   113,   114,
     115,   116,   423,   588,   463,   333,   658,   742,   678,   327,
     874,   458,  1007,    75,    76,    75,    76,    57,    57,   187,
     188,   189,    75,    76,   424,    75,    76,   660,   368,   369,
     967,   370,   472,   934,   905,    88,   353,   356,   835,   193,
     193,   632,   193,  1012,   625,   972,   661,   626,   915,    89,
      75,    76,    90,   192,   192,   922,   192,   682,   875,   239,
     419,   382,   383,   973,   422,   470,   957,   264,   265,   589,
       3,     4,     5,   415,   938,   454,   497,   499,   501,    92,
      74,   217,   635,   600,   193,   755,   236,   371,   234,   872,
     236,   144,   234,    95,    78,   146,   556,   240,   192,   354,
     355,   766,   218,   483,    75,    76,  1009,    97,   292,   756,
     245,   372,   281,   103,   282,   105,    98,   102,   728,   558,
     730,   190,   734,   494,   662,   663,    75,    76,   373,   191,
     106,   783,   784,   -40,   281,   725,   282,    75,    76,   757,
     278,   456,   279,   470,   456,   461,   283,   659,   281,   243,
     282,    75,    76,   471,   473,   456,   471,   786,   937,   814,
     782,   333,   384,   385,   386,   247,   281,   107,   282,    75,
      76,   690,   759,    75,    76,   691,   944,   804,   277,   182,
     760,   787,    75,    76,   732,   491,   493,   244,   495,   507,
     998,   880,   299,   691,   184,    75,    76,   346,   897,   414,
     315,    75,    76,   248,    75,    76,   739,   507,   441,    75,
      76,   442,   551,   740,   553,   805,   900,   471,   557,   471,
     733,   103,   858,   105,   640,   102,   593,    75,    76,   643,
     347,   348,    75,    76,   641,   452,   569,   582,   836,   213,
     683,   533,   535,   535,   535,   203,   204,   542,   823,   753,
      75,    76,   810,     3,     4,     5,   183,   597,   599,   999,
     536,   538,   538,   236,   684,   234,   539,   541,    75,    76,
     889,    75,    76,  1001,   528,   530,   532,   532,   532,   532,
     809,    80,   606,   236,   236,   234,   234,   245,   214,   651,
     281,   653,   282,   193,   376,   103,   377,   105,   993,   102,
     871,   245,   796,   797,   603,   215,   604,   192,   515,   517,
     490,   232,   605,   881,   281,   450,   282,   451,   553,   456,
     931,   637,   810,   492,   456,   896,   690,   899,   627,   268,
     902,   269,   251,   456,   471,   257,   638,   270,    75,    76,
     986,    75,    76,   466,   467,   468,   469,   216,   647,   553,
      86,    75,    76,   920,   259,    87,   278,   276,   819,   196,
     286,   197,   278,   287,   988,    75,    76,    75,    76,   211,
     212,   484,   936,   567,   568,    75,    76,   488,   489,   273,
      75,    76,    75,    76,   496,   198,   199,    75,    76,   274,
       3,     4,     5,   764,    99,   100,   101,    10,    11,    12,
      13,    14,    15,   497,   499,   501,   894,   552,   249,   703,
     696,   704,   984,   250,   288,   965,   553,    75,    76,   723,
     638,   724,   193,    75,    76,   898,   895,   349,   901,   744,
     692,   746,   750,   751,    75,    76,   192,   350,   351,   289,
     445,   368,   449,   369,   296,   982,   233,   207,   208,   209,
     210,   193,   193,   297,   193,   103,   720,   105,   722,   102,
     320,   313,   321,   891,   317,   192,   192,   318,   192,     1,
       2,     3,     4,     5,     6,    99,   100,   101,    10,    11,
      12,    13,    14,    15,   319,   283,   322,   323,    82,   737,
      83,    84,   320,    85,   321,   324,   749,   200,   201,   202,
     456,   638,    48,   342,   336,   337,   338,   339,   343,   553,
     344,    27,   328,   329,   330,   620,   345,   325,   322,   323,
     624,   300,   302,   305,   307,   309,   311,   666,   667,   668,
     669,   391,   392,   393,   394,   969,   334,   335,    31,   553,
     553,   655,   656,   657,    34,    35,    36,   790,   359,   325,
     987,   985,   989,   456,   456,   692,   692,    37,   361,   803,
     360,   924,    38,    39,   340,   341,   811,   553,   103,   352,
     105,   863,   102,   567,   568,   362,   245,   363,    40,    41,
     254,   664,   665,    48,   650,   670,   671,   185,   186,   387,
     388,   364,   395,   396,    27,   919,   365,    47,   389,   390,
      49,    50,   366,   627,   367,   627,   416,   417,    27,   547,
     549,   548,   550,   420,   425,   427,   428,   429,   850,   852,
     430,    31,   592,   434,   435,   695,   -42,    34,    35,    36,
     553,   859,   860,   861,   862,    31,   378,   436,   437,   453,
      37,    34,    35,    36,   193,    38,    39,   438,   455,   850,
     867,   465,   555,   481,    37,   477,   478,   479,   192,    38,
      39,    40,    41,   930,   480,   482,   559,   563,   572,   577,
     560,   578,   884,   885,   561,   562,   580,   643,   553,   573,
      47,   245,   579,    49,    50,   581,   583,   745,   279,    72,
     283,   752,   584,   283,    47,   595,   737,    49,    50,   585,
     586,   590,   591,   601,   602,   609,   610,   911,   611,   912,
     996,    94,   612,   616,    96,   619,   471,   621,   764,   623,
     110,   630,   636,   645,   646,   633,   649,   634,   553,   117,
     118,   193,   672,   675,   676,   673,   785,   674,   677,   680,
     679,    72,    72,   -44,   698,   192,   707,   702,   701,   503,
     505,   885,   513,   513,   513,   513,   513,   513,   513,   513,
     513,   513,   513,   513,   513,   712,   710,   711,   715,   627,
     301,   303,   306,   308,   310,   312,   713,   252,   253,    72,
     714,   850,   716,   717,   258,   718,   456,   726,   727,   829,
     736,   743,   640,   832,   763,   767,   850,   519,   521,   523,
     525,   527,   527,   527,   527,   527,   527,   527,   811,   768,
     769,   780,   788,   279,   770,   283,   791,   283,   771,   792,
     795,   793,   801,   794,   802,   815,   816,   638,   193,   299,
     820,   471,   826,   825,   821,   827,   828,   692,   830,   818,
     831,   833,   192,     3,     4,     5,   811,    99,   100,   101,
      10,    11,    12,    13,    14,    15,   876,   850,   878,   879,
     842,   838,   841,   843,   840,   885,   514,   514,   514,   514,
     514,   514,   514,   514,   514,   514,   514,   514,   514,    -2,
     845,   849,   853,   854,   857,   380,   381,   844,   846,   847,
     848,   865,   856,   868,   873,   907,   877,   909,   910,   241,
     882,   887,   883,   888,   913,   914,   892,   402,   403,   404,
     405,   406,   407,   408,   409,   410,   411,   412,   413,     1,
       2,     3,     4,     5,     6,    99,   100,   101,    10,    11,
      12,    13,    14,    15,   940,   890,   893,   904,   906,   908,
     916,   917,   921,   918,   947,   432,   923,   925,   926,   927,
     928,   949,   929,   932,   951,    48,   933,   953,   448,   935,
     691,   939,   498,   500,   502,   504,   506,   941,   516,   518,
     520,   522,   524,   526,   529,   531,   534,   537,   540,   543,
     546,   219,   220,   221,   222,   223,   224,   225,   226,   227,
     228,   229,  -426,   230,   231,   945,   976,   946,   978,   950,
     952,   626,   958,   954,   959,   960,   956,   961,   962,   963,
     964,   966,   968,   971,   974,   991,   977,   970,   979,   992,
     975,   980,   994,   983,   995,   990,   997,  1002,  1008,   641,
    1010,   178,   179,    48,  1000,   180,   104,  1011,   708,   981,
     817,  1004,  1003,  1005,   398,  1006,     1,     2,     3,     4,
       5,     6,    99,   100,   101,    10,    11,    12,    13,    14,
      15,   397,   399,   401,   903,   781,   576,     3,     4,     5,
       6,    99,   100,   101,    10,    11,    12,    13,    14,    15,
     503,   505,   513,   513,   513,   513,   513,   513,   513,   513,
     513,   513,   513,   513,   779,   779,   779,   400,   316,   181,
       0,   779,   779,   779,   779,   779,   779,   779,   779,   779,
     779,   779,   779,   779,   779,   644,   545,     0,   268,   443,
     269,     0,    72,     0,     0,     0,   270,   519,   521,   523,
     525,   527,   527,   527,   527,   527,   527,     0,     0,     0,
     615,     1,     2,     3,     4,     5,     6,    99,   100,   101,
      10,    11,    12,    13,    14,    15,     0,     0,     0,     0,
      48,   652,     0,     0,     0,     0,     3,     4,     5,     6,
      99,   100,   101,    10,    11,    12,    13,    14,    15,    48,
       3,     4,     5,     6,    99,   100,   101,    10,    11,    12,
      13,    14,    15,     0,     0,     0,   514,   514,   514,   514,
     514,   514,   514,   514,   514,   514,   514,   514,     0,     0,
       0,     0,   779,   779,   779,   779,   779,   779,   574,     0,
       0,     0,     0,     1,     2,     3,     4,     5,     6,     7,
       8,     9,    10,    11,    12,    13,    14,    15,    16,    17,
      18,    19,    20,    21,    22,    23,    24,    25,    26,    27,
      28,     0,     0,     0,     0,   747,   748,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,   380,     0,
     709,     0,     0,     0,    29,    30,    31,     0,    48,   765,
      32,    33,    34,    35,    36,     0,     0,     0,     0,     0,
       0,     0,    48,   721,     0,    37,     0,     0,     0,     0,
      38,    39,     0,     3,     4,     5,     6,    99,   100,   101,
      10,    11,    12,    13,    14,    15,    40,    41,    42,     0,
       0,    43,    44,    45,    46,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,    47,     0,    48,    49,    50,
       1,     2,     3,     4,     5,     6,    99,   100,   101,    10,
      11,    12,    13,    14,    15,   613,    27,     0,     0,     0,
       0,     0,     0,     0,     0,     0,    27,     0,   779,     3,
       4,     5,   789,    99,   100,   101,    10,    11,    12,    13,
      14,    15,     0,    31,     0,     0,     0,   564,     0,    34,
      35,    36,     0,    31,     0,     0,     0,     0,     0,    34,
      35,    36,    37,     0,     0,     0,     0,    38,    39,   779,
       0,     0,    37,   824,     0,    48,     0,    38,    39,     0,
       0,     0,     0,     0,     0,     1,     2,     3,     4,     5,
       6,    99,   100,   101,    10,    11,    12,    13,    14,    15,
       0,     0,    47,     0,     0,    49,    50,     0,     0,     0,
       0,   120,    47,     0,    48,    49,    50,   122,   123,     0,
     125,   126,     0,   127,   128,   129,   130,   131,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,   135,     0,
       0,    48,     0,     0,   136,   137,   138,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,   139,     0,     0,
       0,     0,   140,   141,     3,     4,     5,     6,    99,   100,
     101,    10,    11,    12,    13,    14,    15,     3,     4,     5,
       0,    99,   100,   101,    10,    11,    12,    13,    14,    15,
       0,     0,     0,     0,     0,     0,   144,   145,     0,    48,
     146,     3,     4,     5,     0,    99,   100,   101,    10,    11,
      12,    13,    14,    15,     0,     0,   822,     3,     4,     5,
       0,    99,   100,   101,    10,    11,    12,    13,    14,    15,
       3,     4,     5,   418,    99,   100,   101,    10,    11,    12,
      13,    14,    15,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,   421,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,   596,     0,     0,    48,     0,     0,     0,
       0,   119,     0,     0,     0,   120,   598,     0,     0,    48,
     121,   122,   123,   124,   125,   126,     0,   127,   128,   129,
     130,   131,   132,     0,     0,     0,     0,     0,   133,   134,
       0,     0,   135,    48,    27,     0,     0,     0,   136,   137,
     138,     0,     0,     0,     0,     0,     0,     0,     0,    48,
       0,   139,     0,     0,     0,     0,   140,   141,     0,     0,
       0,    31,    48,     0,     0,     0,     0,    34,    35,    36,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
      37,   142,     0,     0,     0,    38,    39,   143,   173,     0,
     144,   145,   120,     0,   146,     0,     0,   121,   122,   123,
     124,   125,   126,    93,   127,   128,   129,   130,   131,   174,
       0,     0,     0,     0,     0,   175,   176,     0,    27,   135,
      47,     0,     0,    49,    50,   136,   137,   138,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,   139,     0,
       0,     0,     0,   140,   141,    31,     0,   683,     0,   564,
       0,    34,    35,    36,     0,     0,     0,     0,     0,    27,
       0,     0,     0,     0,    37,     0,     0,     0,   177,    38,
      39,   684,     0,     0,   143,     0,     0,   144,   145,    27,
       0,   146,     0,     0,     0,     0,    31,     0,     0,     0,
       0,     0,    34,    35,    36,     0,     0,     0,     0,     0,
       0,     0,     0,     0,    47,    37,    31,    49,    50,     0,
      38,    39,    34,    35,    36,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,    37,   120,     0,   431,     0,
      38,    39,   122,   123,     0,   125,   126,     0,   127,   128,
     129,   130,   131,     0,     0,    47,     0,     0,    49,    50,
       0,     0,     0,   135,     0,     0,     0,   304,     0,   136,
     137,   138,     0,     0,     0,    47,     0,     0,    49,    50,
       0,     0,   139,     0,   120,     0,     0,   140,   141,   314,
     122,   123,     0,   125,   126,     0,   127,   128,   129,   130,
     131,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,   135,     0,     0,     0,     0,     0,   136,   137,   138,
       0,   144,   145,     0,     0,   146,     0,     0,     0,     0,
     139,   120,     0,     0,     0,   140,   141,   122,   123,     0,
     125,   126,     0,   127,   128,   129,   130,   131,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,   135,   487,
       0,     0,     0,     0,   136,   137,   138,     0,     0,   144,
     145,     0,     0,   146,     0,     0,     0,   139,   120,     0,
       0,     0,   140,   141,   122,   123,     0,   125,   126,     0,
     127,   128,   129,   130,   131,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,   135,     0,     0,     0,     0,
       0,   136,   137,   138,     0,     0,   144,   145,     0,     0,
     146,     0,   120,     0,   139,     0,     0,     0,     0,   140,
     141,   125,   126,     0,   127,   128,   129,   130,   131,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,   772,
       0,     0,     0,   864,     0,   773,   774,   775,     0,     0,
       0,     0,     0,   144,   145,     0,   120,   146,   776,     0,
       0,     0,     0,   777,   778,   125,   126,     0,   127,   128,
     129,   130,   131,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,   772,     0,     0,     0,     0,     0,   773,
     774,   775,     0,     0,     0,     0,     0,   144,   145,     0,
       0,   146,   776,     0,     0,     0,     0,   777,   778,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,   144,   145,     0,     0,   146
};

static const yytype_int16 yycheck[] =
{
       7,     8,     9,    28,   132,    28,   510,    28,   174,   372,
     279,   283,   494,    90,   136,   137,   138,   139,   140,   141,
     278,   557,   247,   281,   282,    57,   602,    98,   786,    78,
     740,   376,   742,   619,   292,   621,    57,   623,   692,   693,
     455,   342,   343,   344,   345,   346,   174,   345,   346,   791,
      57,    74,    56,    74,   640,    78,   904,    78,    32,   888,
     343,   344,   345,   346,   135,    59,   344,   345,   346,    31,
      32,   486,   104,    80,   340,   341,   342,   343,   344,   345,
     346,    63,    56,   104,    56,   790,    58,   569,   759,    84,
      57,    56,    99,   100,   101,     0,    57,   104,    62,    63,
      78,    79,   638,    98,   475,   450,   110,    40,   334,   335,
      47,    48,   119,   117,   118,   122,   123,   124,    51,    56,
      61,    98,    57,   117,   118,   132,    34,    35,    36,    37,
      38,    39,    84,   115,   106,    99,   507,    98,   553,   106,
      61,   106,   990,   117,   118,   117,   118,    52,    53,    54,
      55,    56,   117,   118,   106,   117,   118,    64,   190,   191,
     918,   193,   290,   868,   835,    56,   173,   174,   109,   190,
     191,   106,   193,  1002,    57,   933,    83,    60,   849,    56,
     117,   118,    56,   190,   191,   856,   193,   558,   109,    60,
     239,   198,   199,   935,   243,    56,   906,   102,   103,   424,
       5,     6,     7,   235,   875,   276,   328,   329,   330,    98,
      60,    74,   470,   438,   235,    60,   239,    60,   239,   795,
     243,   114,   243,    56,    60,   118,   354,    98,   235,    47,
      48,   646,    95,   304,   117,   118,   994,    99,    56,    84,
     247,    84,    56,   268,    58,   268,    56,   268,   619,   110,
     621,    56,   623,   324,    62,    63,   117,   118,   101,    64,
     119,   676,   677,   106,    56,   610,    58,   117,   118,   640,
      56,   278,   279,    56,   281,   282,   283,   781,    56,    60,
      58,   117,   118,   290,   291,   292,   293,    60,   874,   704,
     661,    99,   200,   201,   202,    60,    56,   119,    58,   117,
     118,    56,    56,   117,   118,    60,   882,    60,   121,   116,
      64,    84,   117,   118,   106,   322,   323,    98,   325,    56,
     974,   803,   135,    60,     0,   117,   118,    74,   106,   234,
     143,   117,   118,    98,   117,   118,    99,    56,   112,   117,
     118,   115,   349,   106,   351,    98,   106,   354,   355,   356,
     622,   376,   767,   376,    99,   376,   433,   117,   118,   481,
     107,   108,   117,   118,   109,   273,   373,   416,   739,    75,
      58,   672,   673,   674,   675,    62,    63,   675,   723,   637,
     117,   118,    98,     5,     6,     7,   116,   436,   437,   975,
     673,   674,   675,   416,    82,   416,   674,   675,   117,   118,
     815,   117,   118,   979,   670,   671,   672,   673,   674,   675,
      56,    60,   444,   436,   437,   436,   437,   424,    77,   490,
      56,   492,    58,   444,    56,   450,    58,   450,   964,   450,
     793,   438,   690,   691,    56,    76,    58,   444,   664,   665,
      60,    98,    64,   806,    56,    56,    58,    58,   455,   456,
     865,    56,    98,    60,   461,   826,    56,   828,   465,    56,
     831,    58,    12,   470,   471,    98,   473,    64,   117,   118,
     106,   117,   118,   286,   287,   288,   289,    73,   485,   486,
      12,   117,   118,   854,    99,    17,    56,    56,   713,    56,
      56,    58,    56,    56,   106,   117,   118,   117,   118,    71,
      72,   314,   873,    31,    32,   117,   118,   320,   321,    57,
     117,   118,   117,   118,   327,    82,    83,   117,   118,    57,
       5,     6,     7,   645,     9,    10,    11,    12,    13,    14,
      15,    16,    17,   655,   656,   657,   106,   350,    12,    49,
      68,    51,   106,    17,    56,   916,   553,   117,   118,    56,
     557,    58,   573,   117,   118,   827,   825,    40,   830,   630,
     567,   632,   633,   634,   117,   118,   573,    50,    51,    56,
     268,   603,   270,   605,   116,   946,    61,    67,    68,    69,
      70,   602,   603,   119,   605,   610,   603,   610,   605,   610,
      56,   100,    58,   818,   100,   602,   603,   100,   605,     3,
       4,     5,     6,     7,     8,     9,    10,    11,    12,    13,
      14,    15,    16,    17,   100,   622,    82,    83,    12,   626,
      14,    15,    56,    17,    58,    91,   633,    64,    65,    66,
     637,   638,   117,    75,    67,    68,    69,    70,    77,   646,
      76,    29,    64,    65,    66,   458,    73,   113,    82,    83,
     463,   773,   774,   775,   776,   777,   778,    67,    68,    69,
      70,   207,   208,   209,   210,   923,    78,    79,    56,   676,
     677,    64,    65,    66,    62,    63,    64,   684,   116,   113,
     952,   950,   954,   690,   691,   692,   693,    75,   112,   696,
     119,   857,    80,    81,    71,    72,   703,   704,   723,   100,
     723,   772,   723,    31,    32,   112,   713,   112,    96,    97,
      98,    78,    79,   117,   118,    71,    72,    52,    53,   203,
     204,   112,   211,   212,    29,   853,   112,   115,   205,   206,
     118,   119,   100,   740,   112,   742,    98,    61,    29,   347,
     348,   347,   348,    61,    61,    12,    57,    57,   755,   756,
      98,    56,    57,    57,    57,   568,   106,    62,    63,    64,
     767,   768,   769,   770,   771,    56,    57,    60,    60,   100,
      75,    62,    63,    64,   795,    80,    81,    60,    51,   786,
     787,    56,   112,    57,    75,   100,   100,   100,   795,    80,
      81,    96,    97,   864,   100,    57,   112,    57,    98,   101,
     112,    57,   809,   810,   112,   112,    59,   929,   815,   106,
     115,   818,   106,   118,   119,    99,    98,   630,   825,     0,
     827,   634,    61,   830,   115,    60,   833,   118,   119,    98,
      61,    61,    98,    98,   106,    57,   106,   844,    57,   846,
     968,    22,    59,    57,    25,    99,   853,    99,   970,    99,
      31,   106,   100,    61,    51,   106,    59,   106,   865,    40,
      41,   882,    75,    73,    51,    77,   679,    76,    51,   112,
      50,    52,    53,   106,   100,   882,   101,    59,    57,   331,
     332,   888,   334,   335,   336,   337,   338,   339,   340,   341,
     342,   343,   344,   345,   346,   115,    98,    98,    57,   906,
     136,   137,   138,   139,   140,   141,   106,    88,    89,    90,
      98,   918,    61,    61,    95,    61,   923,    57,    59,   732,
      84,    57,    99,   736,   100,    51,   933,   336,   337,   338,
     339,   340,   341,   342,   343,   344,   345,   346,   945,    82,
      82,    57,   112,   950,    82,   952,   106,   954,    82,    61,
     106,    84,    32,    98,    33,    51,   100,   964,   979,   772,
      57,   968,    83,    57,    59,    57,    83,   974,    59,   106,
      83,   106,   979,     5,     6,     7,   983,     9,    10,    11,
      12,    13,    14,    15,    16,    17,   799,   994,   801,   802,
      57,    84,   106,    57,    84,  1002,   334,   335,   336,   337,
     338,   339,   340,   341,   342,   343,   344,   345,   346,    57,
      57,   109,    57,    83,    57,   196,   197,   106,   106,   106,
     106,    51,   107,    59,    99,   838,    32,   840,   841,    61,
     106,    84,    98,    98,   847,   848,    57,   218,   219,   220,
     221,   222,   223,   224,   225,   226,   227,   228,   229,     3,
       4,     5,     6,     7,     8,     9,    10,    11,    12,    13,
      14,    15,    16,    17,   877,   100,    59,   106,   106,    57,
      99,    61,    57,    60,   887,   256,    56,    61,    61,    61,
      61,   894,    57,    61,   897,   117,    60,   900,   269,   106,
      60,    33,   328,   329,   330,   331,   332,    33,   334,   335,
     336,   337,   338,   339,   340,   341,   342,   343,   344,   345,
     346,    84,    85,    86,    87,    88,    89,    90,    91,    92,
      93,    94,    98,    96,    97,    57,   939,    84,   941,    57,
      57,    60,    84,    59,    57,    57,    61,    57,   106,    57,
      57,   100,    57,   112,    57,   958,    33,    61,   106,   962,
      61,    98,    98,   106,    61,   106,    61,   106,    57,   109,
     100,    44,    44,   117,   977,    44,    28,   112,   579,   945,
     707,   984,   983,   986,   214,   988,     3,     4,     5,     6,
       7,     8,     9,    10,    11,    12,    13,    14,    15,    16,
      17,   213,   215,   217,   833,   660,   377,     5,     6,     7,
       8,     9,    10,    11,    12,    13,    14,    15,    16,    17,
     662,   663,   664,   665,   666,   667,   668,   669,   670,   671,
     672,   673,   674,   675,   655,   656,   657,   216,   144,    44,
      -1,   662,   663,   664,   665,   666,   667,   668,   669,   670,
     671,   672,   673,   674,   675,   481,   346,    -1,    56,    57,
      58,    -1,   433,    -1,    -1,    -1,    64,   666,   667,   668,
     669,   670,   671,   672,   673,   674,   675,    -1,    -1,    -1,
     451,     3,     4,     5,     6,     7,     8,     9,    10,    11,
      12,    13,    14,    15,    16,    17,    -1,    -1,    -1,    -1,
     117,   118,    -1,    -1,    -1,    -1,     5,     6,     7,     8,
       9,    10,    11,    12,    13,    14,    15,    16,    17,   117,
       5,     6,     7,     8,     9,    10,    11,    12,    13,    14,
      15,    16,    17,    -1,    -1,    -1,   664,   665,   666,   667,
     668,   669,   670,   671,   672,   673,   674,   675,    -1,    -1,
      -1,    -1,   773,   774,   775,   776,   777,   778,    57,    -1,
      -1,    -1,    -1,     3,     4,     5,     6,     7,     8,     9,
      10,    11,    12,    13,    14,    15,    16,    17,    18,    19,
      20,    21,    22,    23,    24,    25,    26,    27,    28,    29,
      30,    -1,    -1,    -1,    -1,   117,   118,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   579,    -1,
     581,    -1,    -1,    -1,    54,    55,    56,    -1,   117,   645,
      60,    61,    62,    63,    64,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,   117,   604,    -1,    75,    -1,    -1,    -1,    -1,
      80,    81,    -1,     5,     6,     7,     8,     9,    10,    11,
      12,    13,    14,    15,    16,    17,    96,    97,    98,    -1,
      -1,   101,   102,   103,   104,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,   115,    -1,   117,   118,   119,
       3,     4,     5,     6,     7,     8,     9,    10,    11,    12,
      13,    14,    15,    16,    17,    57,    29,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    29,    -1,   929,     5,
       6,     7,   683,     9,    10,    11,    12,    13,    14,    15,
      16,    17,    -1,    56,    -1,    -1,    -1,    60,    -1,    62,
      63,    64,    -1,    56,    -1,    -1,    -1,    -1,    -1,    62,
      63,    64,    75,    -1,    -1,    -1,    -1,    80,    81,   970,
      -1,    -1,    75,   724,    -1,   117,    -1,    80,    81,    -1,
      -1,    -1,    -1,    -1,    -1,     3,     4,     5,     6,     7,
       8,     9,    10,    11,    12,    13,    14,    15,    16,    17,
      -1,    -1,   115,    -1,    -1,   118,   119,    -1,    -1,    -1,
      -1,    29,   115,    -1,   117,   118,   119,    35,    36,    -1,
      38,    39,    -1,    41,    42,    43,    44,    45,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    56,    -1,
      -1,   117,    -1,    -1,    62,    63,    64,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    75,    -1,    -1,
      -1,    -1,    80,    81,     5,     6,     7,     8,     9,    10,
      11,    12,    13,    14,    15,    16,    17,     5,     6,     7,
      -1,     9,    10,    11,    12,    13,    14,    15,    16,    17,
      -1,    -1,    -1,    -1,    -1,    -1,   114,   115,    -1,   117,
     118,     5,     6,     7,    -1,     9,    10,    11,    12,    13,
      14,    15,    16,    17,    -1,    -1,    57,     5,     6,     7,
      -1,     9,    10,    11,    12,    13,    14,    15,    16,    17,
       5,     6,     7,    61,     9,    10,    11,    12,    13,    14,
      15,    16,    17,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    61,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    61,    -1,    -1,   117,    -1,    -1,    -1,
      -1,    25,    -1,    -1,    -1,    29,    61,    -1,    -1,   117,
      34,    35,    36,    37,    38,    39,    -1,    41,    42,    43,
      44,    45,    46,    -1,    -1,    -1,    -1,    -1,    52,    53,
      -1,    -1,    56,   117,    29,    -1,    -1,    -1,    62,    63,
      64,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   117,
      -1,    75,    -1,    -1,    -1,    -1,    80,    81,    -1,    -1,
      -1,    56,   117,    -1,    -1,    -1,    -1,    62,    63,    64,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      75,   105,    -1,    -1,    -1,    80,    81,   111,    25,    -1,
     114,   115,    29,    -1,   118,    -1,    -1,    34,    35,    36,
      37,    38,    39,    98,    41,    42,    43,    44,    45,    46,
      -1,    -1,    -1,    -1,    -1,    52,    53,    -1,    29,    56,
     115,    -1,    -1,   118,   119,    62,    63,    64,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    75,    -1,
      -1,    -1,    -1,    80,    81,    56,    -1,    58,    -1,    60,
      -1,    62,    63,    64,    -1,    -1,    -1,    -1,    -1,    29,
      -1,    -1,    -1,    -1,    75,    -1,    -1,    -1,   105,    80,
      81,    82,    -1,    -1,   111,    -1,    -1,   114,   115,    29,
      -1,   118,    -1,    -1,    -1,    -1,    56,    -1,    -1,    -1,
      -1,    -1,    62,    63,    64,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,   115,    75,    56,   118,   119,    -1,
      80,    81,    62,    63,    64,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    75,    29,    -1,    98,    -1,
      80,    81,    35,    36,    -1,    38,    39,    -1,    41,    42,
      43,    44,    45,    -1,    -1,   115,    -1,    -1,   118,   119,
      -1,    -1,    -1,    56,    -1,    -1,    -1,    60,    -1,    62,
      63,    64,    -1,    -1,    -1,   115,    -1,    -1,   118,   119,
      -1,    -1,    75,    -1,    29,    -1,    -1,    80,    81,    34,
      35,    36,    -1,    38,    39,    -1,    41,    42,    43,    44,
      45,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    56,    -1,    -1,    -1,    -1,    -1,    62,    63,    64,
      -1,   114,   115,    -1,    -1,   118,    -1,    -1,    -1,    -1,
      75,    29,    -1,    -1,    -1,    80,    81,    35,    36,    -1,
      38,    39,    -1,    41,    42,    43,    44,    45,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    56,    57,
      -1,    -1,    -1,    -1,    62,    63,    64,    -1,    -1,   114,
     115,    -1,    -1,   118,    -1,    -1,    -1,    75,    29,    -1,
      -1,    -1,    80,    81,    35,    36,    -1,    38,    39,    -1,
      41,    42,    43,    44,    45,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    56,    -1,    -1,    -1,    -1,
      -1,    62,    63,    64,    -1,    -1,   114,   115,    -1,    -1,
     118,    -1,    29,    -1,    75,    -1,    -1,    -1,    -1,    80,
      81,    38,    39,    -1,    41,    42,    43,    44,    45,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    56,
      -1,    -1,    -1,    60,    -1,    62,    63,    64,    -1,    -1,
      -1,    -1,    -1,   114,   115,    -1,    29,   118,    75,    -1,
      -1,    -1,    -1,    80,    81,    38,    39,    -1,    41,    42,
      43,    44,    45,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    56,    -1,    -1,    -1,    -1,    -1,    62,
      63,    64,    -1,    -1,    -1,    -1,    -1,   114,   115,    -1,
      -1,   118,    75,    -1,    -1,    -1,    -1,    80,    81,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,   114,   115,    -1,    -1,   118
};

/* YYSTOS[STATE-NUM] -- The symbol kind of the accessing symbol of
   state STATE-NUM.  */
static const yytype_uint8 yystos[] =
{
       0,     3,     4,     5,     6,     7,     8,     9,    10,    11,
      12,    13,    14,    15,    16,    17,    18,    19,    20,    21,
      22,    23,    24,    25,    26,    27,    28,    29,    30,    54,
      55,    56,    60,    61,    62,    63,    64,    75,    80,    81,
      96,    97,    98,   101,   102,   103,   104,   115,   117,   118,
     119,   122,   123,   129,   136,   137,   138,   139,   143,   151,
     157,   158,   159,   160,   161,   162,   163,   164,   165,   166,
     167,   168,   169,   218,    60,   117,   118,   121,    60,   121,
      60,   121,    12,    14,    15,    17,    12,    17,    56,    56,
      56,    98,    98,    98,   169,    56,   169,    99,    56,     9,
      10,    11,   137,   138,   141,   143,   119,   119,   139,   142,
     169,   158,   158,   158,   158,   158,   158,   169,   169,    25,
      29,    34,    35,    36,    37,    38,    39,    41,    42,    43,
      44,    45,    46,    52,    53,    56,    62,    63,    64,    75,
      80,    81,   105,   111,   114,   115,   118,   125,   126,   127,
     186,   187,   188,   189,   190,   191,   192,   193,   194,   195,
     196,   197,   198,   199,   200,   201,   202,   203,   204,   207,
     208,   209,   222,    25,    46,    52,    53,   105,   125,   126,
     127,   222,   116,   116,     0,   122,   122,   139,   139,   139,
      56,    64,   121,   137,   145,   147,    56,    58,    82,    83,
      64,    65,    66,    62,    63,    78,    79,    67,    68,    69,
      70,    71,    72,    75,    77,    76,    73,    74,    95,    84,
      85,    86,    87,    88,    89,    90,    91,    92,    93,    94,
      96,    97,    98,    61,   137,   140,   143,   223,   224,    60,
      98,    61,   224,    60,    98,   121,   225,    60,    98,    12,
      17,    12,   169,   169,    98,   218,   219,    98,   169,    99,
     142,   121,   121,   121,   139,   139,   145,   124,    56,    58,
      64,   144,   146,    57,    57,   121,    56,   209,    56,   121,
     205,    56,    58,   121,   206,   121,    56,    56,    56,    56,
      47,    48,    56,   121,   179,   185,   116,   119,   142,   209,
     190,   207,   190,   207,    60,   190,   207,   190,   207,   190,
     207,   190,   207,   100,    34,   209,   186,   100,   100,   100,
      56,    58,    82,    83,    91,   113,    57,   106,    64,    65,
      66,    62,    63,    99,    78,    79,    67,    68,    69,    70,
      71,    72,    75,    77,    76,    73,    74,   107,   108,    40,
      50,    51,   100,   121,    47,    48,   121,   179,   185,   116,
     119,   112,   112,   112,   112,   112,   100,   112,   145,   145,
     145,    60,    84,   101,   130,   133,    56,    58,    57,   150,
     169,   169,   121,   121,   158,   158,   158,   159,   159,   160,
     160,   161,   161,   161,   161,   162,   162,   163,   164,   165,
     166,   167,   169,   169,   169,   169,   169,   169,   169,   169,
     169,   169,   169,   169,   139,   145,    98,    61,    61,   224,
      61,    61,   224,    84,   106,    61,   225,    12,    57,    57,
      98,    98,   169,   220,    57,    57,    60,    60,    60,   131,
     134,   112,   115,    57,   141,   144,   226,   227,   169,   144,
      56,    58,   158,   100,   142,    51,   121,   176,   106,   205,
     176,   121,   176,   106,   206,    56,   209,   209,   209,   209,
      56,   121,   185,   121,   176,   110,   185,   100,   100,   100,
     100,    57,    57,   142,   209,    40,    51,    57,   209,   209,
      60,   121,    60,   121,   142,   121,   209,   190,   207,   190,
     207,   190,   207,   191,   207,   191,   207,    56,   121,   172,
     173,   174,   175,   191,   192,   193,   207,   193,   207,   194,
     207,   194,   207,   194,   207,   194,   207,   194,   195,   207,
     195,   207,   195,   196,   207,   196,   197,   207,   197,   198,
     207,   198,   199,   207,   199,   200,   207,   202,   208,   202,
     208,   121,   209,   121,   128,   112,   185,   121,   110,   112,
     112,   112,   112,    57,    60,   169,   210,    31,    32,   121,
     228,   229,    98,   106,    57,   227,   169,   101,    57,   106,
      59,    99,   224,    98,    61,    98,    61,    63,   115,   225,
      61,    98,    57,   218,   221,    60,    61,   224,    61,   224,
     225,    98,   106,    56,    58,    64,   145,   148,   149,    57,
     106,    57,    59,    57,   227,   169,    57,   128,   176,    99,
     209,    99,    59,    99,   209,    57,    60,   121,   181,   182,
     106,    57,   106,   106,   106,   176,   100,    56,   121,   180,
      99,   109,   175,   190,   207,    61,    51,   121,   128,    59,
     118,   142,   118,   142,   228,    64,    65,    66,   175,   172,
      64,    83,    62,    63,    78,    79,    67,    68,    69,    70,
      71,    72,    75,    77,    76,    73,    51,    51,   128,    50,
     112,   180,   175,    58,    82,   210,   211,   212,   132,   135,
      56,    60,   121,   178,   183,   209,    68,   228,   100,   145,
     213,    57,    59,    49,    51,   155,   156,   101,   150,   169,
      98,    98,   115,   106,    98,    57,    61,    61,    61,   213,
     148,   169,   148,    56,    58,   227,    57,    59,   175,   178,
     175,   178,   106,   206,   175,   178,    84,   121,   177,    99,
     106,    57,    98,    57,   142,   209,   142,   117,   118,   121,
     142,   142,   209,   176,   180,    60,    84,   175,   178,    56,
      64,   170,   171,   100,   190,   207,   128,    51,    82,    82,
      82,    82,    56,    62,    63,    64,    75,    80,    81,   188,
      57,   173,   175,   128,   128,   209,    60,    84,   112,   169,
     121,   106,    61,    84,    98,   106,   176,   176,   183,    32,
     183,    32,    33,   121,    60,    98,    84,   214,   216,    56,
      98,   121,   153,   154,   128,    51,   100,   156,   106,   225,
      57,    59,    57,   227,   169,    57,    83,    57,    83,   209,
      59,    83,   209,   106,    61,   109,   175,   182,    84,   182,
      84,   106,    57,    57,   106,    57,   106,   106,   106,   109,
     121,   184,   121,    57,    83,   171,   107,    57,   128,   121,
     121,   121,   121,   142,    60,    51,   184,   121,    59,   212,
     211,   210,   213,    99,    61,   109,   209,    32,   209,   209,
     228,   210,   106,    98,   121,   121,   152,    84,    98,   128,
     100,   225,    57,    59,   106,   205,   175,   106,   206,   175,
     106,   206,   175,   177,   106,   171,   106,   209,    57,   209,
     209,   121,   121,   209,   209,   171,    99,    61,    60,   185,
     175,    57,   171,    56,   179,    61,    61,    61,    61,    57,
     142,   128,    61,    60,   212,   106,   175,   178,   171,    33,
     209,    33,   215,   217,   213,    57,    84,   209,   152,   209,
      57,   209,    57,   209,    59,   181,    61,   182,    84,    57,
      57,    57,   106,    57,    57,   175,   100,   184,    57,   176,
      61,   112,   184,   211,    57,    61,   209,    33,   209,   106,
      98,   154,   175,   106,   106,   205,   106,   206,   106,   206,
     106,   209,   209,   180,    98,    61,   185,    61,   183,   178,
     209,   213,   106,   153,   209,   209,   209,   181,    57,   184,
     100,   112,   152
};

/* YYR1[RULE-NUM] -- Symbol kind of the left-hand side of rule RULE-NUM.  */
static const yytype_uint8 yyr1[] =
{
       0,   120,   121,   121,   122,   122,   122,   122,   123,   123,
     123,   123,   123,   123,   124,   124,   125,   125,   125,   125,
     125,   125,   125,   125,   126,   126,   126,   126,   127,   127,
     127,   127,   128,   128,   130,   129,   131,   129,   132,   129,
     133,   129,   134,   129,   135,   129,   129,   129,   129,   129,
     129,   129,   129,   129,   129,   129,   129,   129,   129,   129,
     129,   129,   129,   129,   129,   129,   129,   129,   129,   129,
     129,   129,   129,   129,   129,   129,   129,   129,   129,   129,
     129,   129,   129,   129,   129,   129,   129,   129,   129,   129,
     129,   129,   129,   129,   129,   129,   129,   129,   129,   136,
     136,   137,   137,   137,   138,   139,   139,   139,   139,   140,
     140,   141,   141,   141,   142,   142,   143,   143,   143,   143,
     143,   143,   143,   143,   143,   143,   143,   143,   143,   143,
     143,   143,   143,   143,   143,   143,   143,   143,   143,   143,
     143,   143,   143,   143,   143,   143,   144,   144,   144,   145,
     145,   145,   146,   146,   146,   146,   146,   146,   146,   147,
     147,   147,   147,   147,   148,   148,   148,   149,   149,   149,
     149,   149,   150,   150,   151,   151,   151,   151,   151,   152,
     152,   153,   153,   154,   154,   154,   155,   155,   155,   156,
     156,   156,   157,   157,   157,   157,   157,   157,   157,   157,
     158,   158,   158,   158,   158,   158,   158,   158,   159,   159,
     159,   159,   160,   160,   160,   161,   161,   161,   162,   162,
     162,   162,   162,   163,   163,   163,   164,   164,   165,   165,
     166,   166,   167,   167,   168,   168,   169,   169,   170,   170,
     171,   171,   172,   172,   173,   173,   174,   174,   175,   175,
     176,   176,   177,   177,   178,   178,   178,   178,   179,   179,
     180,   180,   180,   181,   181,   181,   181,   182,   182,   182,
     182,   183,   183,   183,   183,   184,   184,   185,   185,   185,
     185,   185,   185,   186,   186,   187,   187,   187,   187,   187,
     187,   187,   187,   187,   187,   187,   187,   187,   187,   187,
     187,   188,   188,   188,   188,   188,   188,   188,   188,   188,
     188,   188,   189,   189,   190,   190,   190,   190,   190,   190,
     190,   190,   190,   191,   191,   191,   191,   192,   192,   192,
     193,   193,   194,   194,   194,   195,   195,   195,   195,   195,
     196,   196,   196,   197,   197,   198,   198,   199,   199,   200,
     200,   201,   201,   202,   202,   202,   203,   204,   204,   205,
     205,   205,   205,   205,   205,   206,   206,   206,   206,   206,
     206,   206,   206,   206,   206,   206,   206,   207,   207,   207,
     207,   207,   207,   207,   207,   207,   207,   208,   208,   208,
     208,   208,   208,   208,   208,   208,   208,   208,   208,   208,
     208,   208,   208,   208,   208,   208,   208,   208,   209,   209,
     210,   210,   211,   211,   211,   211,   212,   212,   212,   212,
     214,   213,   215,   213,   216,   213,   217,   213,   218,   218,
     218,   218,   218,   218,   218,   218,   218,   218,   218,   218,
     218,   218,   218,   218,   219,   219,   220,   220,   221,   221,
     222,   222,   222,   222,   223,   224,   224,   225,   225,   225,
     225,   225,   225,   226,   226,   226,   227,   227,   228,   228,
     228,   228,   229,   229,   229,   229
};

/* YYR2[RULE-NUM] -- Number of symbols on the right-hand side of rule RULE-NUM.  */
static const yytype_int8 yyr2[] =
{
       0,     2,     1,     1,     1,     1,     2,     2,     2,     4,
       4,     4,     4,     4,     0,     2,     1,     3,     2,     4,
       3,     5,     4,     6,     2,     3,     4,     5,     3,     5,
       5,     7,     1,     2,     0,     4,     0,     5,     0,     6,
       0,     5,     0,     6,     0,     7,     2,     2,     2,     3,
       2,     4,     4,     1,     1,     5,     5,     3,     2,     1,
       1,     3,     3,     3,     3,     3,     3,     3,     3,     3,
       3,     4,     4,     4,     4,     4,     4,     6,     6,     5,
       5,     9,     9,    11,    11,     1,     6,     5,     3,     6,
       5,     3,     6,     3,     3,     3,     3,     6,     6,     1,
       1,     1,     1,     1,     1,     1,     2,     2,     2,     1,
       2,     1,     2,     2,     1,     2,     1,     1,     2,     1,
       2,     1,     1,     2,     2,     3,     1,     2,     2,     3,
       3,     4,     2,     2,     2,     3,     4,     4,     5,     3,
       4,     4,     5,     4,     5,     1,     2,     1,     1,     2,
       2,     1,     3,     4,     3,     3,     4,     2,     3,     3,
       1,     4,     3,     4,     2,     1,     1,     3,     4,     3,
       3,     4,     1,     3,     3,     1,     1,     1,     4,     3,
       5,     3,     5,     1,     2,     3,     2,     5,     4,     1,
       3,     2,     1,     4,     3,     3,     3,     4,     6,     7,
       1,     2,     2,     2,     2,     2,     2,     4,     1,     3,
       3,     3,     1,     3,     3,     1,     3,     3,     1,     3,
       3,     3,     3,     1,     3,     3,     1,     3,     1,     3,
       1,     3,     1,     3,     1,     3,     1,     5,     1,     3,
       1,     3,     1,     3,     1,     2,     1,     3,     1,     3,
       1,     2,     1,     3,     5,     6,     3,     4,     5,     6,
       0,     2,     6,     5,     7,     3,     5,     1,     3,     3,
       5,     1,     5,     2,     6,     4,     5,     1,     5,     7,
       2,     6,     8,     1,     2,     1,     3,     1,     1,     6,
       8,     4,     6,     6,     8,     8,     8,    10,     1,     1,
       4,     1,     4,     7,     7,     7,     7,     3,     3,     3,
       3,     2,     3,     3,     1,     2,     2,     2,     2,     5,
       2,     2,     4,     1,     3,     3,     3,     1,     3,     3,
       1,     3,     1,     3,     3,     1,     3,     3,     3,     3,
       1,     3,     3,     1,     3,     1,     3,     1,     3,     1,
       3,     1,     3,     1,     3,     3,     4,     2,     2,     3,
       2,     7,     6,     9,     8,     3,     2,     7,     6,     9,
       8,     5,     4,     7,     6,     9,     8,     1,     1,     2,
       2,     2,     2,     5,     2,     2,     4,     1,     3,     3,
       3,     3,     3,     3,     3,     3,     3,     3,     3,     3,
       3,     3,     3,     3,     3,     3,     3,     3,     1,     1,
       1,     3,     1,     3,     3,     5,     3,     2,     4,     3,
       0,     4,     0,     6,     0,     3,     0,     5,     1,     2,
       2,     2,     2,     3,     3,     3,     3,     3,     3,     3,
       3,     3,     3,     3,     1,     2,     1,     2,     1,     2,
       9,     7,     7,     6,     2,     2,     3,     1,     3,     3,
       5,     4,     6,     2,     2,     1,     1,     3,     4,     7,
       6,     6,     1,     1,     2,     4
};


enum { YYENOMEM = -2 };

#define yyerrok         (yyerrstatus = 0)
#define yyclearin       (yychar = YYEMPTY)

#define YYACCEPT        goto yyacceptlab
#define YYABORT         goto yyabortlab
#define YYERROR         goto yyerrorlab
#define YYNOMEM         goto yyexhaustedlab


#define YYRECOVERING()  (!!yyerrstatus)

#define YYBACKUP(Token, Value)                                    \
  do                                                              \
    if (yychar == YYEMPTY)                                        \
      {                                                           \
        yychar = (Token);                                         \
        yylval = (Value);                                         \
        YYPOPSTACK (yylen);                                       \
        yystate = *yyssp;                                         \
        goto yybackup;                                            \
      }                                                           \
    else                                                          \
      {                                                           \
        yyerror (path, k, env, YY_("syntax error: cannot back up")); \
        YYERROR;                                                  \
      }                                                           \
  while (0)

/* Backward compatibility with an undocumented macro.
   Use YYerror or YYUNDEF. */
#define YYERRCODE YYUNDEF


/* Enable debugging if requested.  */
#if YYDEBUG

# ifndef YYFPRINTF
#  include <stdio.h> /* INFRINGES ON USER NAME SPACE */
#  define YYFPRINTF fprintf
# endif

# define YYDPRINTF(Args)                        \
do {                                            \
  if (yydebug)                                  \
    YYFPRINTF Args;                             \
} while (0)




# define YY_SYMBOL_PRINT(Title, Kind, Value, Location)                    \
do {                                                                      \
  if (yydebug)                                                            \
    {                                                                     \
      YYFPRINTF (stderr, "%s ", Title);                                   \
      yy_symbol_print (stderr,                                            \
                  Kind, Value, path, k, env); \
      YYFPRINTF (stderr, "\n");                                           \
    }                                                                     \
} while (0)


/*-----------------------------------.
| Print this symbol's value on YYO.  |
`-----------------------------------*/

static void
yy_symbol_value_print (FILE *yyo,
                       yysymbol_kind_t yykind, YYSTYPE const * const yyvaluep, char *path, void *k, struct environment *env)
{
  FILE *yyoutput = yyo;
  YY_USE (yyoutput);
  YY_USE (path);
  YY_USE (k);
  YY_USE (env);
  if (!yyvaluep)
    return;
  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  YY_USE (yykind);
  YY_IGNORE_MAYBE_UNINITIALIZED_END
}


/*---------------------------.
| Print this symbol on YYO.  |
`---------------------------*/

static void
yy_symbol_print (FILE *yyo,
                 yysymbol_kind_t yykind, YYSTYPE const * const yyvaluep, char *path, void *k, struct environment *env)
{
  YYFPRINTF (yyo, "%s %s (",
             yykind < YYNTOKENS ? "token" : "nterm", yysymbol_name (yykind));

  yy_symbol_value_print (yyo, yykind, yyvaluep, path, k, env);
  YYFPRINTF (yyo, ")");
}

/*------------------------------------------------------------------.
| yy_stack_print -- Print the state stack from its BOTTOM up to its |
| TOP (included).                                                   |
`------------------------------------------------------------------*/

static void
yy_stack_print (yy_state_t *yybottom, yy_state_t *yytop)
{
  YYFPRINTF (stderr, "Stack now");
  for (; yybottom <= yytop; yybottom++)
    {
      int yybot = *yybottom;
      YYFPRINTF (stderr, " %d", yybot);
    }
  YYFPRINTF (stderr, "\n");
}

# define YY_STACK_PRINT(Bottom, Top)                            \
do {                                                            \
  if (yydebug)                                                  \
    yy_stack_print ((Bottom), (Top));                           \
} while (0)


/*------------------------------------------------.
| Report that the YYRULE is going to be reduced.  |
`------------------------------------------------*/

static void
yy_reduce_print (yy_state_t *yyssp, YYSTYPE *yyvsp,
                 int yyrule, char *path, void *k, struct environment *env)
{
  int yylno = yyrline[yyrule];
  int yynrhs = yyr2[yyrule];
  int yyi;
  YYFPRINTF (stderr, "Reducing stack by rule %d (line %d):\n",
             yyrule - 1, yylno);
  /* The symbols being reduced.  */
  for (yyi = 0; yyi < yynrhs; yyi++)
    {
      YYFPRINTF (stderr, "   $%d = ", yyi + 1);
      yy_symbol_print (stderr,
                       YY_ACCESSING_SYMBOL (+yyssp[yyi + 1 - yynrhs]),
                       &yyvsp[(yyi + 1) - (yynrhs)], path, k, env);
      YYFPRINTF (stderr, "\n");
    }
}

# define YY_REDUCE_PRINT(Rule)          \
do {                                    \
  if (yydebug)                          \
    yy_reduce_print (yyssp, yyvsp, Rule, path, k, env); \
} while (0)

/* Nonzero means print parse trace.  It is left uninitialized so that
   multiple parsers can coexist.  */
int yydebug;
#else /* !YYDEBUG */
# define YYDPRINTF(Args) ((void) 0)
# define YY_SYMBOL_PRINT(Title, Kind, Value, Location)
# define YY_STACK_PRINT(Bottom, Top)
# define YY_REDUCE_PRINT(Rule)
#endif /* !YYDEBUG */


/* YYINITDEPTH -- initial size of the parser's stacks.  */
#ifndef YYINITDEPTH
# define YYINITDEPTH 200
#endif

/* YYMAXDEPTH -- maximum size the stacks can grow to (effective only
   if the built-in stack extension method is used).

   Do not make this value too large; the results are undefined if
   YYSTACK_ALLOC_MAXIMUM < YYSTACK_BYTES (YYMAXDEPTH)
   evaluated with infinite-precision integer arithmetic.  */

#ifndef YYMAXDEPTH
# define YYMAXDEPTH 10000
#endif
/* Parser data structure.  */
struct yypstate
  {
    /* Number of syntax errors so far.  */
    int yynerrs;

    yy_state_fast_t yystate;
    /* Number of tokens to shift before error messages enabled.  */
    int yyerrstatus;

    /* Refer to the stacks through separate pointers, to allow yyoverflow
       to reallocate them elsewhere.  */

    /* Their size.  */
    YYPTRDIFF_T yystacksize;

    /* The state stack: array, bottom, top.  */
    yy_state_t yyssa[YYINITDEPTH];
    yy_state_t *yyss;
    yy_state_t *yyssp;

    /* The semantic value stack: array, bottom, top.  */
    YYSTYPE yyvsa[YYINITDEPTH];
    YYSTYPE *yyvs;
    YYSTYPE *yyvsp;
    /* Whether this instance has not started parsing yet.
     * If 2, it corresponds to a finished parsing.  */
    int yynew;
  };


/* Context of a parse error.  */
typedef struct
{
  yypstate* yyps;
  yysymbol_kind_t yytoken;
} yypcontext_t;

/* Put in YYARG at most YYARGN of the expected tokens given the
   current YYCTX, and return the number of tokens stored in YYARG.  If
   YYARG is null, return the number of expected tokens (guaranteed to
   be less than YYNTOKENS).  Return YYENOMEM on memory exhaustion.
   Return 0 if there are more than YYARGN expected tokens, yet fill
   YYARG up to YYARGN. */
static int
yypstate_expected_tokens (yypstate *yyps,
                          yysymbol_kind_t yyarg[], int yyargn)
{
  /* Actual size of YYARG. */
  int yycount = 0;
  int yyn = yypact[+*yyps->yyssp];
  if (!yypact_value_is_default (yyn))
    {
      /* Start YYX at -YYN if negative to avoid negative indexes in
         YYCHECK.  In other words, skip the first -YYN actions for
         this state because they are default actions.  */
      int yyxbegin = yyn < 0 ? -yyn : 0;
      /* Stay within bounds of both yycheck and yytname.  */
      int yychecklim = YYLAST - yyn + 1;
      int yyxend = yychecklim < YYNTOKENS ? yychecklim : YYNTOKENS;
      int yyx;
      for (yyx = yyxbegin; yyx < yyxend; ++yyx)
        if (yycheck[yyx + yyn] == yyx && yyx != YYSYMBOL_YYerror
            && !yytable_value_is_error (yytable[yyx + yyn]))
          {
            if (!yyarg)
              ++yycount;
            else if (yycount == yyargn)
              return 0;
            else
              yyarg[yycount++] = YY_CAST (yysymbol_kind_t, yyx);
          }
    }
  if (yyarg && yycount == 0 && 0 < yyargn)
    yyarg[0] = YYSYMBOL_YYEMPTY;
  return yycount;
}


/* Similar to the previous function.  */
static int
yypcontext_expected_tokens (const yypcontext_t *yyctx,
                            yysymbol_kind_t yyarg[], int yyargn)
{
  return yypstate_expected_tokens (yyctx->yyps, yyarg, yyargn);
}


#ifndef yystrlen
# if defined __GLIBC__ && defined _STRING_H
#  define yystrlen(S) (YY_CAST (YYPTRDIFF_T, strlen (S)))
# else
/* Return the length of YYSTR.  */
static YYPTRDIFF_T
yystrlen (const char *yystr)
{
  YYPTRDIFF_T yylen;
  for (yylen = 0; yystr[yylen]; yylen++)
    continue;
  return yylen;
}
# endif
#endif

#ifndef yystpcpy
# if defined __GLIBC__ && defined _STRING_H && defined _GNU_SOURCE
#  define yystpcpy stpcpy
# else
/* Copy YYSRC to YYDEST, returning the address of the terminating '\0' in
   YYDEST.  */
static char *
yystpcpy (char *yydest, const char *yysrc)
{
  char *yyd = yydest;
  const char *yys = yysrc;

  while ((*yyd++ = *yys++) != '\0')
    continue;

  return yyd - 1;
}
# endif
#endif

#ifndef yytnamerr
/* Copy to YYRES the contents of YYSTR after stripping away unnecessary
   quotes and backslashes, so that it's suitable for yyerror.  The
   heuristic is that double-quoting is unnecessary unless the string
   contains an apostrophe, a comma, or backslash (other than
   backslash-backslash).  YYSTR is taken from yytname.  If YYRES is
   null, do not copy; instead, return the length of what the result
   would have been.  */
static YYPTRDIFF_T
yytnamerr (char *yyres, const char *yystr)
{
  if (*yystr == '"')
    {
      YYPTRDIFF_T yyn = 0;
      char const *yyp = yystr;
      for (;;)
        switch (*++yyp)
          {
          case '\'':
          case ',':
            goto do_not_strip_quotes;

          case '\\':
            if (*++yyp != '\\')
              goto do_not_strip_quotes;
            else
              goto append;

          append:
          default:
            if (yyres)
              yyres[yyn] = *yyp;
            yyn++;
            break;

          case '"':
            if (yyres)
              yyres[yyn] = '\0';
            return yyn;
          }
    do_not_strip_quotes: ;
    }

  if (yyres)
    return yystpcpy (yyres, yystr) - yyres;
  else
    return yystrlen (yystr);
}
#endif


static int
yy_syntax_error_arguments (const yypcontext_t *yyctx,
                           yysymbol_kind_t yyarg[], int yyargn)
{
  /* Actual size of YYARG. */
  int yycount = 0;
  /* There are many possibilities here to consider:
     - If this state is a consistent state with a default action, then
       the only way this function was invoked is if the default action
       is an error action.  In that case, don't check for expected
       tokens because there are none.
     - The only way there can be no lookahead present (in yychar) is if
       this state is a consistent state with a default action.  Thus,
       detecting the absence of a lookahead is sufficient to determine
       that there is no unexpected or expected token to report.  In that
       case, just report a simple "syntax error".
     - Don't assume there isn't a lookahead just because this state is a
       consistent state with a default action.  There might have been a
       previous inconsistent state, consistent state with a non-default
       action, or user semantic action that manipulated yychar.
     - Of course, the expected token list depends on states to have
       correct lookahead information, and it depends on the parser not
       to perform extra reductions after fetching a lookahead from the
       scanner and before detecting a syntax error.  Thus, state merging
       (from LALR or IELR) and default reductions corrupt the expected
       token list.  However, the list is correct for canonical LR with
       one exception: it will still contain any token that will not be
       accepted due to an error action in a later state.
  */
  if (yyctx->yytoken != YYSYMBOL_YYEMPTY)
    {
      int yyn;
      if (yyarg)
        yyarg[yycount] = yyctx->yytoken;
      ++yycount;
      yyn = yypcontext_expected_tokens (yyctx,
                                        yyarg ? yyarg + 1 : yyarg, yyargn - 1);
      if (yyn == YYENOMEM)
        return YYENOMEM;
      else
        yycount += yyn;
    }
  return yycount;
}

/* Copy into *YYMSG, which is of size *YYMSG_ALLOC, an error message
   about the unexpected token YYTOKEN for the state stack whose top is
   YYSSP.

   Return 0 if *YYMSG was successfully written.  Return -1 if *YYMSG is
   not large enough to hold the message.  In that case, also set
   *YYMSG_ALLOC to the required number of bytes.  Return YYENOMEM if the
   required number of bytes is too large to store.  */
static int
yysyntax_error (YYPTRDIFF_T *yymsg_alloc, char **yymsg,
                const yypcontext_t *yyctx)
{
  enum { YYARGS_MAX = 5 };
  /* Internationalized format string. */
  const char *yyformat = YY_NULLPTR;
  /* Arguments of yyformat: reported tokens (one for the "unexpected",
     one per "expected"). */
  yysymbol_kind_t yyarg[YYARGS_MAX];
  /* Cumulated lengths of YYARG.  */
  YYPTRDIFF_T yysize = 0;

  /* Actual size of YYARG. */
  int yycount = yy_syntax_error_arguments (yyctx, yyarg, YYARGS_MAX);
  if (yycount == YYENOMEM)
    return YYENOMEM;

  switch (yycount)
    {
#define YYCASE_(N, S)                       \
      case N:                               \
        yyformat = S;                       \
        break
    default: /* Avoid compiler warnings. */
      YYCASE_(0, YY_("syntax error"));
      YYCASE_(1, YY_("syntax error, unexpected %s"));
      YYCASE_(2, YY_("syntax error, unexpected %s, expecting %s"));
      YYCASE_(3, YY_("syntax error, unexpected %s, expecting %s or %s"));
      YYCASE_(4, YY_("syntax error, unexpected %s, expecting %s or %s or %s"));
      YYCASE_(5, YY_("syntax error, unexpected %s, expecting %s or %s or %s or %s"));
#undef YYCASE_
    }

  /* Compute error message size.  Don't count the "%s"s, but reserve
     room for the terminator.  */
  yysize = yystrlen (yyformat) - 2 * yycount + 1;
  {
    int yyi;
    for (yyi = 0; yyi < yycount; ++yyi)
      {
        YYPTRDIFF_T yysize1
          = yysize + yytnamerr (YY_NULLPTR, yytname[yyarg[yyi]]);
        if (yysize <= yysize1 && yysize1 <= YYSTACK_ALLOC_MAXIMUM)
          yysize = yysize1;
        else
          return YYENOMEM;
      }
  }

  if (*yymsg_alloc < yysize)
    {
      *yymsg_alloc = 2 * yysize;
      if (! (yysize <= *yymsg_alloc
             && *yymsg_alloc <= YYSTACK_ALLOC_MAXIMUM))
        *yymsg_alloc = YYSTACK_ALLOC_MAXIMUM;
      return -1;
    }

  /* Avoid sprintf, as that infringes on the user's name space.
     Don't have undefined behavior even if the translation
     produced a string with the wrong number of "%s"s.  */
  {
    char *yyp = *yymsg;
    int yyi = 0;
    while ((*yyp = *yyformat) != '\0')
      if (*yyp == '%' && yyformat[1] == 's' && yyi < yycount)
        {
          yyp += yytnamerr (yyp, yytname[yyarg[yyi++]]);
          yyformat += 2;
        }
      else
        {
          ++yyp;
          ++yyformat;
        }
  }
  return 0;
}


/*-----------------------------------------------.
| Release the memory associated to this symbol.  |
`-----------------------------------------------*/

static void
yydestruct (const char *yymsg,
            yysymbol_kind_t yykind, YYSTYPE *yyvaluep, char *path, void *k, struct environment *env)
{
  YY_USE (yyvaluep);
  YY_USE (path);
  YY_USE (k);
  YY_USE (env);
  if (!yymsg)
    yymsg = "Deleting";
  YY_SYMBOL_PRINT (yymsg, yykind, yyvaluep, yylocationp);

  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  YY_USE (yykind);
  YY_IGNORE_MAYBE_UNINITIALIZED_END
}





#define yynerrs yyps->yynerrs
#define yystate yyps->yystate
#define yyerrstatus yyps->yyerrstatus
#define yyssa yyps->yyssa
#define yyss yyps->yyss
#define yyssp yyps->yyssp
#define yyvsa yyps->yyvsa
#define yyvs yyps->yyvs
#define yyvsp yyps->yyvsp
#define yystacksize yyps->yystacksize

/* Initialize the parser data structure.  */
static void
yypstate_clear (yypstate *yyps)
{
  yynerrs = 0;
  yystate = 0;
  yyerrstatus = 0;

  yyssp = yyss;
  yyvsp = yyvs;

  /* Initialize the state stack, in case yypcontext_expected_tokens is
     called before the first call to yyparse. */
  *yyssp = 0;
  yyps->yynew = 1;
}

/* Initialize the parser data structure.  */
yypstate *
yypstate_new (void)
{
  yypstate *yyps;
  yyps = YY_CAST (yypstate *, YYMALLOC (sizeof *yyps));
  if (!yyps)
    return YY_NULLPTR;
  yystacksize = YYINITDEPTH;
  yyss = yyssa;
  yyvs = yyvsa;
  yypstate_clear (yyps);
  return yyps;
}

void
yypstate_delete (yypstate *yyps)
{
  if (yyps)
    {
#ifndef yyoverflow
      /* If the stack was reallocated but the parse did not complete, then the
         stack still needs to be freed.  */
      if (yyss != yyssa)
        YYSTACK_FREE (yyss);
#endif
      YYFREE (yyps);
    }
}



/*---------------.
| yypush_parse.  |
`---------------*/

int
yypush_parse (yypstate *yyps,
              int yypushed_char, YYSTYPE const *yypushed_val, char *path, void *k, struct environment *env)
{
/* Lookahead token kind.  */
int yychar;


/* The semantic value of the lookahead symbol.  */
/* Default value used for initialization, for pacifying older GCCs
   or non-GCC compilers.  */
YY_INITIAL_VALUE (static YYSTYPE yyval_default;)
YYSTYPE yylval YY_INITIAL_VALUE (= yyval_default);

  int yyn;
  /* The return value of yyparse.  */
  int yyresult;
  /* Lookahead symbol kind.  */
  yysymbol_kind_t yytoken = YYSYMBOL_YYEMPTY;
  /* The variables used to return semantic value and location from the
     action routines.  */
  YYSTYPE yyval;

  /* Buffer for error messages, and its allocated size.  */
  char yymsgbuf[128];
  char *yymsg = yymsgbuf;
  YYPTRDIFF_T yymsg_alloc = sizeof yymsgbuf;

#define YYPOPSTACK(N)   (yyvsp -= (N), yyssp -= (N))

  /* The number of symbols on the RHS of the reduced rule.
     Keep to zero when no symbol should be popped.  */
  int yylen = 0;

  switch (yyps->yynew)
    {
    case 0:
      yyn = yypact[yystate];
      goto yyread_pushed_token;

    case 2:
      yypstate_clear (yyps);
      break;

    default:
      break;
    }

  YYDPRINTF ((stderr, "Starting parse\n"));

  yychar = YYEMPTY; /* Cause a token to be read.  */

  goto yysetstate;


/*------------------------------------------------------------.
| yynewstate -- push a new state, which is found in yystate.  |
`------------------------------------------------------------*/
yynewstate:
  /* In all cases, when you get here, the value and location stacks
     have just been pushed.  So pushing a state here evens the stacks.  */
  yyssp++;


/*--------------------------------------------------------------------.
| yysetstate -- set current state (the top of the stack) to yystate.  |
`--------------------------------------------------------------------*/
yysetstate:
  YYDPRINTF ((stderr, "Entering state %d\n", yystate));
  YY_ASSERT (0 <= yystate && yystate < YYNSTATES);
  YY_IGNORE_USELESS_CAST_BEGIN
  *yyssp = YY_CAST (yy_state_t, yystate);
  YY_IGNORE_USELESS_CAST_END
  YY_STACK_PRINT (yyss, yyssp);

  if (yyss + yystacksize - 1 <= yyssp)
#if !defined yyoverflow && !defined YYSTACK_RELOCATE
    YYNOMEM;
#else
    {
      /* Get the current used size of the three stacks, in elements.  */
      YYPTRDIFF_T yysize = yyssp - yyss + 1;

# if defined yyoverflow
      {
        /* Give user a chance to reallocate the stack.  Use copies of
           these so that the &'s don't force the real ones into
           memory.  */
        yy_state_t *yyss1 = yyss;
        YYSTYPE *yyvs1 = yyvs;

        /* Each stack pointer address is followed by the size of the
           data in use in that stack, in bytes.  This used to be a
           conditional around just the two extra args, but that might
           be undefined if yyoverflow is a macro.  */
        yyoverflow (YY_("memory exhausted"),
                    &yyss1, yysize * YYSIZEOF (*yyssp),
                    &yyvs1, yysize * YYSIZEOF (*yyvsp),
                    &yystacksize);
        yyss = yyss1;
        yyvs = yyvs1;
      }
# else /* defined YYSTACK_RELOCATE */
      /* Extend the stack our own way.  */
      if (YYMAXDEPTH <= yystacksize)
        YYNOMEM;
      yystacksize *= 2;
      if (YYMAXDEPTH < yystacksize)
        yystacksize = YYMAXDEPTH;

      {
        yy_state_t *yyss1 = yyss;
        union yyalloc *yyptr =
          YY_CAST (union yyalloc *,
                   YYSTACK_ALLOC (YY_CAST (YYSIZE_T, YYSTACK_BYTES (yystacksize))));
        if (! yyptr)
          YYNOMEM;
        YYSTACK_RELOCATE (yyss_alloc, yyss);
        YYSTACK_RELOCATE (yyvs_alloc, yyvs);
#  undef YYSTACK_RELOCATE
        if (yyss1 != yyssa)
          YYSTACK_FREE (yyss1);
      }
# endif

      yyssp = yyss + yysize - 1;
      yyvsp = yyvs + yysize - 1;

      YY_IGNORE_USELESS_CAST_BEGIN
      YYDPRINTF ((stderr, "Stack size increased to %ld\n",
                  YY_CAST (long, yystacksize)));
      YY_IGNORE_USELESS_CAST_END

      if (yyss + yystacksize - 1 <= yyssp)
        YYABORT;
    }
#endif /* !defined yyoverflow && !defined YYSTACK_RELOCATE */


  if (yystate == YYFINAL)
    YYACCEPT;

  goto yybackup;


/*-----------.
| yybackup.  |
`-----------*/
yybackup:
  /* Do appropriate processing given the current state.  Read a
     lookahead token if we need one and don't already have one.  */

  /* First try to decide what to do without reference to lookahead token.  */
  yyn = yypact[yystate];
  if (yypact_value_is_default (yyn))
    goto yydefault;

  /* Not known => get a lookahead token if don't already have one.  */

  /* YYCHAR is either empty, or end-of-input, or a valid lookahead.  */
  if (yychar == YYEMPTY)
    {
      if (!yyps->yynew)
        {
          YYDPRINTF ((stderr, "Return for a new token:\n"));
          yyresult = YYPUSH_MORE;
          goto yypushreturn;
        }
      yyps->yynew = 0;
yyread_pushed_token:
      YYDPRINTF ((stderr, "Reading a token\n"));
      yychar = yypushed_char;
      if (yypushed_val)
        yylval = *yypushed_val;
    }

  if (yychar <= YYEOF)
    {
      yychar = YYEOF;
      yytoken = YYSYMBOL_YYEOF;
      YYDPRINTF ((stderr, "Now at end of input.\n"));
    }
  else if (yychar == YYerror)
    {
      /* The scanner already issued an error message, process directly
         to error recovery.  But do not keep the error token as
         lookahead, it is too special and may lead us to an endless
         loop in error recovery. */
      yychar = YYUNDEF;
      yytoken = YYSYMBOL_YYerror;
      goto yyerrlab1;
    }
  else
    {
      yytoken = YYTRANSLATE (yychar);
      YY_SYMBOL_PRINT ("Next token is", yytoken, &yylval, &yylloc);
    }

  /* If the proper action on seeing token YYTOKEN is to reduce or to
     detect an error, take that action.  */
  yyn += yytoken;
  if (yyn < 0 || YYLAST < yyn || yycheck[yyn] != yytoken)
    goto yydefault;
  yyn = yytable[yyn];
  if (yyn <= 0)
    {
      if (yytable_value_is_error (yyn))
        goto yyerrlab;
      yyn = -yyn;
      goto yyreduce;
    }

  /* Count tokens shifted since error; after three, turn off error
     status.  */
  if (yyerrstatus)
    yyerrstatus--;

  /* Shift the lookahead token.  */
  YY_SYMBOL_PRINT ("Shifting", yytoken, &yylval, &yylloc);
  yystate = yyn;
  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  *++yyvsp = yylval;
  YY_IGNORE_MAYBE_UNINITIALIZED_END

  /* Discard the shifted token.  */
  yychar = YYEMPTY;
  goto yynewstate;


/*-----------------------------------------------------------.
| yydefault -- do the default action for the current state.  |
`-----------------------------------------------------------*/
yydefault:
  yyn = yydefact[yystate];
  if (yyn == 0)
    goto yyerrlab;
  goto yyreduce;


/*-----------------------------.
| yyreduce -- do a reduction.  |
`-----------------------------*/
yyreduce:
  /* yyn is the number of a rule to reduce with.  */
  yylen = yyr2[yyn];

  /* If YYLEN is nonzero, implement the default value of the action:
     '$$ = $1'.

     Otherwise, the following line sets YYVAL to garbage.
     This behavior is undocumented and Bison
     users should not rely upon it.  Assigning to YYVAL
     unconditionally makes the parser a bit smaller, and it avoids a
     GCC warning that YYVAL may be used uninitialized.  */
  yyval = yyvsp[1-yylen];


  YY_REDUCE_PRINT (yyn);
  switch (yyn)
    {
  case 2: /* ident: PT_TIDENT  */
#line 323 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.string) = (yyvsp[0].string); }
#line 2619 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 3: /* ident: PT_IDENT  */
#line 325 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.string) = (yyvsp[0].string); }
#line 2625 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 8: /* preprocess_cmd: PT_INCLUDE PT_STRINGLIT  */
#line 337 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      {
      if (path == NULL) {
        parse_program_path((yyvsp[0].string), k, env);
        free((yyvsp[0].string));
      } else {
        char *fpath = find_file_in_search_path(path, (yyvsp[0].string));
        free((yyvsp[0].string));
        parse_program_path(fpath, k, env);
        free(fpath);
      }
      }
#line 2641 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 9: /* preprocess_cmd: PT_SLASHSLASHAT PT_IMPORTCOQ PT_RAW PT_NEWLINE  */
#line 349 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { add_coq_module((yyvsp[-1].string), &env->persist); }
#line 2647 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 10: /* preprocess_cmd: PT_SLASHSTARAT PT_IMPORTCOQ PT_RAW PT_STARSLASH  */
#line 351 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { add_coq_module((yyvsp[-1].string), &env->persist); }
#line 2653 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 11: /* preprocess_cmd: PT_SLASHSLASHAT PT_INCLUDESTRATEGIES PT_STRINGLIT PT_NEWLINE  */
#line 353 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      {
        if (exec_type) {
          free((yyvsp[-1].string));
        }
        else {
          if (path == NULL) {
            addCustomStrategyLib((yyvsp[-1].string), env);
            free((yyvsp[-1].string));
          } else {
            char *fpath = find_file_in_same_dir(path, (yyvsp[-1].string));
            free((yyvsp[-1].string));
            addCustomStrategyLib(fpath, env);
            free(fpath);
          }
        }
      }
#line 2674 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 12: /* preprocess_cmd: PT_SLASHSTARAT PT_INCLUDESTRATEGIES PT_STRINGLIT PT_STARSLASH  */
#line 370 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      {
        if (exec_type) {
          free((yyvsp[-1].string));
        }
        else {
          if (path == NULL) {
            addCustomStrategyLib((yyvsp[-1].string), env);
            free((yyvsp[-1].string));
          } else {
            char *fpath = find_file_in_same_dir(path, (yyvsp[-1].string));
            free((yyvsp[-1].string));
            addCustomStrategyLib(fpath, env);
            free(fpath);
          }
        }
      }
#line 2695 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 13: /* preprocess_cmd: PT_LINEMARK PT_STRINGLIT natlist PT_NEWLINE  */
#line 387 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      {
        free(__current_file);
        __current_file = (yyvsp[-2].string);
        yyset_lineno((yyvsp[-3].nat).n, __current_scanner);
      }
#line 2705 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 14: /* natlist: %empty  */
#line 395 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
           {}
#line 2711 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 15: /* natlist: natlist PT_NATLIT  */
#line 396 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
                      {}
#line 2717 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 16: /* comment: ra  */
#line 401 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.partial_program) = PPAssert((yyvsp[0].RAssertion), NULL, 1, NULL); }
#line 2723 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 17: /* comment: ra PT_ATMARK ident  */
#line 403 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.partial_program) = PPAssert((yyvsp[-2].RAssertion), (yyvsp[0].string), 1, NULL); }
#line 2729 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 18: /* comment: PT_ASSERT ra  */
#line 405 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.partial_program) = PPAssert((yyvsp[0].RAssertion), NULL, 0, NULL); }
#line 2735 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 19: /* comment: PT_ASSERT ra PT_ATMARK ident  */
#line 407 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.partial_program) = PPAssert((yyvsp[-2].RAssertion), (yyvsp[0].string), 0, NULL); }
#line 2741 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 20: /* comment: ra PT_BY scope_list  */
#line 409 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.partial_program) = PPAssert((yyvsp[-2].RAssertion), NULL, 1, (yyvsp[0].string_list)); }
#line 2747 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 21: /* comment: ra PT_ATMARK ident PT_BY scope_list  */
#line 411 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.partial_program) = PPAssert((yyvsp[-4].RAssertion), (yyvsp[-2].string), 1, (yyvsp[0].string_list)); }
#line 2753 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 22: /* comment: PT_ASSERT ra PT_BY scope_list  */
#line 413 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.partial_program) = PPAssert((yyvsp[-2].RAssertion), NULL, 0, (yyvsp[0].string_list)); }
#line 2759 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 23: /* comment: PT_ASSERT ra PT_ATMARK ident PT_BY scope_list  */
#line 415 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.partial_program) = PPAssert((yyvsp[-4].RAssertion), (yyvsp[-2].string), 0, (yyvsp[0].string_list)); }
#line 2765 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 24: /* inv: PT_INV ra  */
#line 420 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.partial_program) = PPInv((yyvsp[0].RAssertion), 1, NULL); }
#line 2771 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 25: /* inv: PT_ASSERT PT_INV ra  */
#line 422 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.partial_program) = PPInv((yyvsp[0].RAssertion), 0, NULL); }
#line 2777 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 26: /* inv: PT_INV ra PT_BY scope_list  */
#line 424 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.partial_program) = PPInv((yyvsp[-2].RAssertion), 1, (yyvsp[0].string_list)); }
#line 2783 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 27: /* inv: PT_ASSERT PT_INV ra PT_BY scope_list  */
#line 426 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.partial_program) = PPInv((yyvsp[-2].RAssertion), 0, (yyvsp[0].string_list)); }
#line 2789 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 28: /* which_implies: ra PT_WHICHIMPLIES ra  */
#line 431 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.partial_program) = PPWI((yyvsp[-2].RAssertion), NULL, (yyvsp[0].RAssertion), NULL); }
#line 2795 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 29: /* which_implies: ra PT_BY scope_list PT_WHICHIMPLIES ra  */
#line 433 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.partial_program) = PPWI((yyvsp[-4].RAssertion), (yyvsp[-2].string_list), (yyvsp[0].RAssertion), NULL); }
#line 2801 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 30: /* which_implies: ra PT_WHICHIMPLIES ra PT_BY scope_list  */
#line 435 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.partial_program) = PPWI((yyvsp[-4].RAssertion), NULL, (yyvsp[-2].RAssertion), (yyvsp[0].string_list)); }
#line 2807 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 31: /* which_implies: ra PT_BY scope_list PT_WHICHIMPLIES ra PT_BY scope_list  */
#line 437 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.partial_program) = PPWI((yyvsp[-6].RAssertion), (yyvsp[-4].string_list), (yyvsp[-2].RAssertion), (yyvsp[0].string_list)); }
#line 2813 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 32: /* scope_list: ident  */
#line 442 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.string_list) = StringListCons((yyvsp[0].string), StringListNil()); }
#line 2819 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 33: /* scope_list: ident scope_list  */
#line 444 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.string_list) = StringListCons((yyvsp[-1].string), (yyvsp[0].string_list)); }
#line 2825 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 34: /* $@1: %empty  */
#line 448 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
                               { K(PPFirstDecl(1, 0, PreType((yyvsp[-1].trivtype), (yyvsp[0].derivtype)), NULL), env); }
#line 2831 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 35: /* partial_program: declaration_specifier decl $@1 PT_SEMI  */
#line 449 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { }
#line 2837 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 36: /* $@2: %empty  */
#line 450 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
                                        { K(PPFirstDecl(1, 1, PreType((yyvsp[-1].trivtype), (yyvsp[0].derivtype)), NULL), env); }
#line 2843 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 37: /* partial_program: PT_TYPEDEF parameter_specifier decl $@2 PT_SEMI  */
#line 451 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { }
#line 2849 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 38: /* $@3: %empty  */
#line 452 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
                                                 { K(PPFirstDecl(1, 0, PreType((yyvsp[-3].trivtype), (yyvsp[-2].derivtype)), (yyvsp[0].initializer)), env); }
#line 2855 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 39: /* partial_program: declaration_specifier decl PT_EQ initializer $@3 PT_SEMI  */
#line 453 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { }
#line 2861 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 40: /* $@4: %empty  */
#line 454 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
                               { K(PPFirstDecl(0, 0, PreType((yyvsp[-1].trivtype), (yyvsp[0].derivtype)), NULL), env); }
#line 2867 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 41: /* partial_program: declaration_specifier decl $@4 PT_COMMA decls  */
#line 455 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { }
#line 2873 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 42: /* $@5: %empty  */
#line 456 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
                                        { K(PPFirstDecl(0, 1, PreType((yyvsp[-1].trivtype), (yyvsp[0].derivtype)), NULL), env); }
#line 2879 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 43: /* partial_program: PT_TYPEDEF parameter_specifier decl $@5 PT_COMMA decls  */
#line 457 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { }
#line 2885 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 44: /* $@6: %empty  */
#line 458 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
                                                 { K(PPFirstDecl(0, 0, PreType((yyvsp[-3].trivtype), (yyvsp[-2].derivtype)), (yyvsp[0].initializer)), env); }
#line 2891 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 45: /* partial_program: declaration_specifier decl PT_EQ initializer $@6 PT_COMMA decls  */
#line 459 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { }
#line 2897 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 46: /* partial_program: simple_cmd PT_SEMI  */
#line 461 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { K(PPSimple((yyvsp[-1].simple_cmd)), env); }
#line 2903 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 47: /* partial_program: PT_BREAK PT_SEMI  */
#line 463 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { K(PPBreak(), env); }
#line 2909 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 48: /* partial_program: PT_CONTINUE PT_SEMI  */
#line 465 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { K(PPContinue(), env); }
#line 2915 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 49: /* partial_program: PT_RETURN expr PT_SEMI  */
#line 467 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { K(PPReturn((yyvsp[-1].expr)), env); }
#line 2921 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 50: /* partial_program: PT_RETURN PT_SEMI  */
#line 469 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { K(PPReturn(NULL), env); }
#line 2927 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 51: /* partial_program: PT_WHILE PT_LPAREN expr PT_RPAREN  */
#line 471 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { K(PPWhile((yyvsp[-1].expr)), env); }
#line 2933 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 52: /* partial_program: PT_IF PT_LPAREN expr PT_RPAREN  */
#line 473 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { K(PPIf((yyvsp[-1].expr)), env); }
#line 2939 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 53: /* partial_program: PT_ELSE  */
#line 475 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { K(PPElse(), env); }
#line 2945 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 54: /* partial_program: PT_DO  */
#line 477 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { K(PPDo(), env); }
#line 2951 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 55: /* partial_program: PT_FOR PT_LPAREN for_init for_cond for_step  */
#line 479 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { K(PPFor((yyvsp[-2].simple_cmd), (yyvsp[-1].expr), (yyvsp[0].simple_cmd)), env); }
#line 2957 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 56: /* partial_program: PT_SWITCH PT_LPAREN expr PT_RPAREN PT_LBRACE  */
#line 481 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { K(PPSwitch((yyvsp[-2].expr)), env); }
#line 2963 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 57: /* partial_program: PT_CASE expr PT_COLON  */
#line 483 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { K(PPCase((yyvsp[-1].expr)), env); }
#line 2969 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 58: /* partial_program: PT_DEFAULT PT_COLON  */
#line 485 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { K(PPDefault(), env); }
#line 2975 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 59: /* partial_program: PT_LBRACE  */
#line 487 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { K(PPBlock(), env); }
#line 2981 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 60: /* partial_program: PT_RBRACE  */
#line 489 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { K(PPEnd(), env); }
#line 2987 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 61: /* partial_program: PT_SLASHSTARAT comment PT_STARSLASH  */
#line 491 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { K((yyvsp[-1].partial_program), env); }
#line 2993 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 62: /* partial_program: PT_SLASHSLASHAT comment PT_NEWLINE  */
#line 493 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { K((yyvsp[-1].partial_program), env); }
#line 2999 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 63: /* partial_program: PT_SLASHSLASHAT inv PT_NEWLINE  */
#line 495 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { K((yyvsp[-1].partial_program), env); }
#line 3005 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 64: /* partial_program: PT_SLASHSTARAT inv PT_STARSLASH  */
#line 497 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { K((yyvsp[-1].partial_program), env); }
#line 3011 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 65: /* partial_program: PT_SLASHSTARAT which_implies PT_STARSLASH  */
#line 499 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { K((yyvsp[-1].partial_program), env); }
#line 3017 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 66: /* partial_program: PT_SLASHSLASHAT which_implies PT_NEWLINE  */
#line 501 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { K((yyvsp[-1].partial_program), env); }
#line 3023 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 67: /* partial_program: PT_SLASHSTARPROOF PT_RAW PT_STARSLASH  */
#line 503 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { K(PPProof((yyvsp[-1].string)), env); }
#line 3029 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 68: /* partial_program: PT_SLASHSLASHPROOF PT_RAW PT_NEWLINE  */
#line 505 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { K(PPProof((yyvsp[-1].string)), env); }
#line 3035 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 69: /* partial_program: PT_SLASHSTARAT PT_FILLININV PT_STARSLASH  */
#line 507 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { K(PPMissingInv(), env); }
#line 3041 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 70: /* partial_program: PT_SLASHSLASHAT PT_FILLININV PT_NEWLINE  */
#line 509 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { K(PPMissingInv(), env); }
#line 3047 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 71: /* partial_program: PT_SLASHSTARAT PT_DO ident PT_STARSLASH  */
#line 511 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { K(PPDoStrategy((yyvsp[-1].string)), env); }
#line 3053 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 72: /* partial_program: PT_SLASHSLASHAT PT_DO ident PT_NEWLINE  */
#line 513 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { K(PPDoStrategy((yyvsp[-1].string)), env); }
#line 3059 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 73: /* partial_program: PT_SLASHSLASHAT PT_EXTERNCOQ term_list PT_NEWLINE  */
#line 515 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { K(PPCoqDec((yyvsp[-1].term_list)), env); }
#line 3065 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 74: /* partial_program: PT_SLASHSTARAT PT_EXTERNCOQ term_list PT_STARSLASH  */
#line 517 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { K(PPCoqDec((yyvsp[-1].term_list)), env); }
#line 3071 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 75: /* partial_program: PT_SLASHSLASHAT PT_EXTERNCOQ paren_atype_list PT_NEWLINE  */
#line 519 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { K(PPATypeDec((yyvsp[-1].atype_list)), env); }
#line 3077 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 76: /* partial_program: PT_SLASHSTARAT PT_EXTERNCOQ paren_atype_list PT_STARSLASH  */
#line 521 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { K(PPATypeDec((yyvsp[-1].atype_list)), env); }
#line 3083 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 77: /* partial_program: PT_SLASHSLASHAT PT_EXTERNCOQ ident PT_COLONEQ atype PT_NEWLINE  */
#line 523 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { K(PPCoqTypeAlias((yyvsp[-3].string), (yyvsp[-1].atype)), env); }
#line 3089 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 78: /* partial_program: PT_SLASHSTARAT PT_EXTERNCOQ ident PT_COLONEQ atype PT_STARSLASH  */
#line 525 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { K(PPCoqTypeAlias((yyvsp[-3].string), (yyvsp[-1].atype)), env); }
#line 3095 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 79: /* partial_program: PT_SLASHSTARAT PT_EXTERNCOQ PT_FIELD term_list PT_STARSLASH  */
#line 527 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { K(PPProjDec((yyvsp[-1].term_list)), env); }
#line 3101 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 80: /* partial_program: PT_SLASHSLASHAT PT_EXTERNCOQ PT_FIELD term_list PT_NEWLINE  */
#line 529 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { K(PPProjDec((yyvsp[-1].term_list)), env); }
#line 3107 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 81: /* partial_program: PT_SLASHSTARAT PT_EXTERNCOQ PT_RECORD ident paren_atype_list_maybe_null PT_LBRACE semi_lvar_list PT_RBRACE PT_STARSLASH  */
#line 531 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { K(PPRecordDec((yyvsp[-4].atype_list), (yyvsp[-5].string), NULL, (yyvsp[-2].lvar_list)), env); }
#line 3113 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 82: /* partial_program: PT_SLASHSLASHAT PT_EXTERNCOQ PT_RECORD ident paren_atype_list_maybe_null PT_LBRACE semi_lvar_list PT_RBRACE PT_NEWLINE  */
#line 533 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { K(PPRecordDec((yyvsp[-4].atype_list), (yyvsp[-5].string), NULL, (yyvsp[-2].lvar_list)), env); }
#line 3119 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 83: /* partial_program: PT_SLASHSTARAT PT_EXTERNCOQ PT_RECORD ident paren_atype_list_maybe_null PT_EQ ident PT_LBRACE semi_lvar_list PT_RBRACE PT_STARSLASH  */
#line 535 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { K(PPRecordDec((yyvsp[-6].atype_list), (yyvsp[-7].string), (yyvsp[-4].string), (yyvsp[-2].lvar_list)), env); }
#line 3125 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 84: /* partial_program: PT_SLASHSLASHAT PT_EXTERNCOQ PT_RECORD ident paren_atype_list_maybe_null PT_EQ ident PT_LBRACE semi_lvar_list PT_RBRACE PT_NEWLINE  */
#line 537 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { K(PPRecordDec((yyvsp[-6].atype_list), (yyvsp[-7].string), (yyvsp[-4].string), (yyvsp[-2].lvar_list)), env); }
#line 3131 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 85: /* partial_program: PT_SEMI  */
#line 539 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { K(PPSkip(), env); }
#line 3137 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 86: /* partial_program: PT_UNION ident PT_LBRACE field_decs PT_RBRACE PT_SEMI  */
#line 541 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { K(PPUnionDef((yyvsp[-4].string), (yyvsp[-2].field_dec_list)), env); }
#line 3143 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 87: /* partial_program: PT_UNION ident PT_LBRACE PT_RBRACE PT_SEMI  */
#line 543 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { K(PPUnionDef((yyvsp[-3].string), NULL), env); }
#line 3149 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 88: /* partial_program: PT_UNION ident PT_SEMI  */
#line 545 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { K(PPUnionDec((yyvsp[-1].string)), env); }
#line 3155 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 89: /* partial_program: PT_STRUCT ident PT_LBRACE field_decs PT_RBRACE PT_SEMI  */
#line 547 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { K(PPStructDef((yyvsp[-4].string), (yyvsp[-2].field_dec_list)), env); }
#line 3161 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 90: /* partial_program: PT_STRUCT ident PT_LBRACE PT_RBRACE PT_SEMI  */
#line 549 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { K(PPStructDef((yyvsp[-3].string), NULL), env); }
#line 3167 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 91: /* partial_program: PT_STRUCT ident PT_SEMI  */
#line 551 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { K(PPStructDec((yyvsp[-1].string)), env); }
#line 3173 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 92: /* partial_program: PT_ENUM ident PT_LBRACE enums PT_RBRACE PT_SEMI  */
#line 553 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { K(PPEnumDef((yyvsp[-4].string), (yyvsp[-2].enum_list)), env); }
#line 3179 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 93: /* partial_program: PT_ENUM ident PT_SEMI  */
#line 555 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { K(PPEnumDec((yyvsp[-1].string)), env); }
#line 3185 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 94: /* partial_program: PT_SLASHSLASHAT sepdef PT_NEWLINE  */
#line 557 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { K((yyvsp[-1].partial_program), env); }
#line 3191 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 95: /* partial_program: PT_SLASHSTARAT sepdef PT_STARSLASH  */
#line 559 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { K((yyvsp[-1].partial_program), env); }
#line 3197 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 96: /* partial_program: declaration_specifier decl PT_LBRACE  */
#line 561 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { K(PPFuncDef(PreType((yyvsp[-2].trivtype), (yyvsp[-1].derivtype)), NULL), env); }
#line 3203 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 97: /* partial_program: declaration_specifier decl PT_SLASHSTARAT fun_contra PT_STARSLASH PT_LBRACE  */
#line 563 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { K(PPFuncDef(PreType((yyvsp[-5].trivtype), (yyvsp[-4].derivtype)), (yyvsp[-2].spec)), env); }
#line 3209 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 98: /* partial_program: declaration_specifier decl PT_SLASHSTARAT fun_contra PT_STARSLASH PT_SEMI  */
#line 565 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { K(PPFuncDec(PreType((yyvsp[-5].trivtype), (yyvsp[-4].derivtype)), (yyvsp[-2].spec)), env); }
#line 3215 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 105: /* declaration_specifier: spec  */
#line 577 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.trivtype) = (yyvsp[0].trivtype); }
#line 3221 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 106: /* declaration_specifier: storage_specifier declaration_specifier  */
#line 579 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.trivtype) = TRIVExternOrStatic((yyvsp[0].trivtype)); }
#line 3227 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 107: /* declaration_specifier: type_qualifier declaration_specifier  */
#line 581 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.trivtype) = (yyvsp[0].trivtype); }
#line 3233 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 108: /* declaration_specifier: function_specifier declaration_specifier  */
#line 583 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.trivtype) = (yyvsp[0].trivtype); }
#line 3239 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 109: /* field_specifier: spec  */
#line 588 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.trivtype) = (yyvsp[0].trivtype); }
#line 3245 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 110: /* field_specifier: type_qualifier declaration_specifier  */
#line 590 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.trivtype) = (yyvsp[0].trivtype); }
#line 3251 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 111: /* parameter_specifier: spec  */
#line 595 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.trivtype) = (yyvsp[0].trivtype); }
#line 3257 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 112: /* parameter_specifier: type_qualifier declaration_specifier  */
#line 597 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.trivtype) = (yyvsp[0].trivtype); }
#line 3263 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 113: /* parameter_specifier: function_specifier declaration_specifier  */
#line 599 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.trivtype) = (yyvsp[0].trivtype); }
#line 3269 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 114: /* type_name: declaration_specifier  */
#line 604 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.pretype) = PreType((yyvsp[0].trivtype), DERIVEnd(NULL)); }
#line 3275 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 115: /* type_name: declaration_specifier abstr_decl  */
#line 606 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.pretype) = PreType((yyvsp[-1].trivtype), (yyvsp[0].derivtype)); }
#line 3281 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 116: /* spec: PT_VOID  */
#line 611 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.trivtype) = TRIVBasic(T_VOID); }
#line 3287 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 117: /* spec: PT_CHAR  */
#line 613 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.trivtype) = TRIVBasic(T_CHAR); }
#line 3293 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 118: /* spec: PT_UNSIGNED PT_CHAR  */
#line 615 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.trivtype) = TRIVBasic(T_U8); }
#line 3299 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 119: /* spec: PT_SHORT  */
#line 617 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.trivtype) = TRIVBasic(T_SHORT); }
#line 3305 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 120: /* spec: PT_UNSIGNED PT_SHORT  */
#line 619 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.trivtype) = TRIVBasic(T_U16); }
#line 3311 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 121: /* spec: PT_INT  */
#line 621 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.trivtype) = TRIVBasic(T_INT); }
#line 3317 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 122: /* spec: PT_LONG  */
#line 623 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.trivtype) = TRIVBasic(T_INT64); }
#line 3323 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 123: /* spec: PT_LONG PT_LONG  */
#line 625 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.trivtype) = TRIVBasic(T_INT64); }
#line 3329 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 124: /* spec: PT_LONG PT_INT  */
#line 627 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.trivtype) = TRIVBasic(T_INT64); }
#line 3335 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 125: /* spec: PT_LONG PT_LONG PT_INT  */
#line 629 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.trivtype) = TRIVBasic(T_INT64); }
#line 3341 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 126: /* spec: PT_UNSIGNED  */
#line 631 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.trivtype) = TRIVBasic(T_UINT); }
#line 3347 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 127: /* spec: PT_UNSIGNED PT_INT  */
#line 633 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.trivtype) = TRIVBasic(T_UINT); }
#line 3353 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 128: /* spec: PT_UNSIGNED PT_LONG  */
#line 635 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.trivtype) = TRIVBasic(T_UINT64); }
#line 3359 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 129: /* spec: PT_UNSIGNED PT_LONG PT_LONG  */
#line 637 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.trivtype) = TRIVBasic(T_UINT64); }
#line 3365 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 130: /* spec: PT_UNSIGNED PT_LONG PT_INT  */
#line 639 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.trivtype) = TRIVBasic(T_UINT64); }
#line 3371 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 131: /* spec: PT_UNSIGNED PT_LONG PT_LONG PT_INT  */
#line 641 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.trivtype) = TRIVBasic(T_UINT64); }
#line 3377 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 132: /* spec: PT_STRUCT ident  */
#line 643 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.trivtype) = TRIVStruct((yyvsp[0].string)); }
#line 3383 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 133: /* spec: PT_UNION ident  */
#line 645 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.trivtype) = TRIVUnion((yyvsp[0].string)); }
#line 3389 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 134: /* spec: PT_ENUM ident  */
#line 647 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.trivtype) = TRIVEnum((yyvsp[0].string)); }
#line 3395 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 135: /* spec: PT_STRUCT PT_LBRACE PT_RBRACE  */
#line 649 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.trivtype) = TRIVAnonStruct(NULL, NULL); }
#line 3401 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 136: /* spec: PT_STRUCT PT_LBRACE field_decs PT_RBRACE  */
#line 651 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.trivtype) = TRIVAnonStruct(NULL, (yyvsp[-1].field_dec_list)); }
#line 3407 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 137: /* spec: PT_STRUCT ident PT_LBRACE PT_RBRACE  */
#line 653 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.trivtype) = TRIVAnonStruct((yyvsp[-2].string), NULL); }
#line 3413 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 138: /* spec: PT_STRUCT ident PT_LBRACE field_decs PT_RBRACE  */
#line 655 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.trivtype) = TRIVAnonStruct((yyvsp[-3].string), (yyvsp[-1].field_dec_list)); }
#line 3419 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 139: /* spec: PT_UNION PT_LBRACE PT_RBRACE  */
#line 657 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.trivtype) = TRIVAnonUnion(NULL, NULL); }
#line 3425 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 140: /* spec: PT_UNION PT_LBRACE field_decs PT_RBRACE  */
#line 659 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.trivtype) = TRIVAnonUnion(NULL, (yyvsp[-1].field_dec_list)); }
#line 3431 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 141: /* spec: PT_UNION ident PT_LBRACE PT_RBRACE  */
#line 661 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.trivtype) = TRIVAnonUnion((yyvsp[-2].string), NULL); }
#line 3437 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 142: /* spec: PT_UNION ident PT_LBRACE field_decs PT_RBRACE  */
#line 663 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.trivtype) = TRIVAnonUnion((yyvsp[-3].string), (yyvsp[-1].field_dec_list)); }
#line 3443 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 143: /* spec: PT_ENUM PT_LBRACE enums PT_RBRACE  */
#line 665 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.trivtype) = TRIVAnonEnum(NULL, (yyvsp[-1].enum_list)); }
#line 3449 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 144: /* spec: PT_ENUM ident PT_LBRACE enums PT_RBRACE  */
#line 667 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.trivtype) = TRIVAnonEnum((yyvsp[-3].string), (yyvsp[-1].enum_list)); }
#line 3455 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 145: /* spec: PT_TIDENT  */
#line 669 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.trivtype) = TRIVTypeAlias((yyvsp[0].string)); }
#line 3461 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 146: /* abstr_decl: PT_STAR abstr_decl  */
#line 674 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.derivtype) = DERIVPtr((yyvsp[0].derivtype)); }
#line 3467 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 147: /* abstr_decl: abstr_direct  */
#line 676 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.derivtype) = (yyvsp[0].derivtype); }
#line 3473 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 148: /* abstr_decl: PT_STAR  */
#line 678 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.derivtype) = DERIVPtr(DERIVEnd(NULL)); }
#line 3479 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 149: /* decl: PT_STAR decl  */
#line 683 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.derivtype) = DERIVPtr((yyvsp[0].derivtype)); }
#line 3485 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 150: /* decl: type_qualifier decl  */
#line 685 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.derivtype) = (yyvsp[0].derivtype); }
#line 3491 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 151: /* decl: direct  */
#line 687 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.derivtype) = (yyvsp[0].derivtype); }
#line 3497 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 152: /* abstr_direct: PT_LPAREN abstr_decl PT_RPAREN  */
#line 692 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.derivtype) = (yyvsp[-1].derivtype); }
#line 3503 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 153: /* abstr_direct: abstr_direct PT_LBRACK expr PT_RBRACK  */
#line 694 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.derivtype) = DERIVArray((yyvsp[-3].derivtype), (yyvsp[-1].expr)); }
#line 3509 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 154: /* abstr_direct: PT_LBRACK expr PT_RBRACK  */
#line 696 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.derivtype) = DERIVArray(DERIVEnd(NULL), (yyvsp[-1].expr)); }
#line 3515 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 155: /* abstr_direct: abstr_direct PT_LPAREN PT_RPAREN  */
#line 698 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.derivtype) = DERIVFunction((yyvsp[-2].derivtype), NULL); }
#line 3521 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 156: /* abstr_direct: abstr_direct PT_LPAREN paras PT_RPAREN  */
#line 700 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.derivtype) = DERIVFunction((yyvsp[-3].derivtype), (yyvsp[-1].para_list)); }
#line 3527 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 157: /* abstr_direct: PT_LPAREN PT_RPAREN  */
#line 702 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.derivtype) = DERIVFunction(DERIVEnd(NULL), NULL); }
#line 3533 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 158: /* abstr_direct: PT_LPAREN paras PT_RPAREN  */
#line 704 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.derivtype) = DERIVFunction(DERIVEnd(NULL), (yyvsp[-1].para_list)); }
#line 3539 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 159: /* direct: PT_LPAREN decl PT_RPAREN  */
#line 709 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.derivtype) = (yyvsp[-1].derivtype); }
#line 3545 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 160: /* direct: ident  */
#line 711 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.derivtype) = DERIVEnd((yyvsp[0].string)); }
#line 3551 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 161: /* direct: direct PT_LBRACK expr PT_RBRACK  */
#line 713 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.derivtype) = DERIVArray((yyvsp[-3].derivtype), (yyvsp[-1].expr)); }
#line 3557 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 162: /* direct: direct PT_LPAREN PT_RPAREN  */
#line 715 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.derivtype) = DERIVFunction((yyvsp[-2].derivtype), NULL); }
#line 3563 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 163: /* direct: direct PT_LPAREN paras PT_RPAREN  */
#line 717 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.derivtype) = DERIVFunction((yyvsp[-3].derivtype), (yyvsp[-1].para_list)); }
#line 3569 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 164: /* abstr_decl_except_function: PT_STAR abstr_decl_except_function  */
#line 722 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.derivtype) = DERIVPtr((yyvsp[0].derivtype)); }
#line 3575 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 165: /* abstr_decl_except_function: abstr_direct_except_function  */
#line 724 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.derivtype) = (yyvsp[0].derivtype); }
#line 3581 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 166: /* abstr_decl_except_function: PT_STAR  */
#line 726 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.derivtype) = DERIVPtr(DERIVEnd(NULL)); }
#line 3587 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 167: /* abstr_direct_except_function: PT_LPAREN abstr_decl_except_function PT_RPAREN  */
#line 731 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.derivtype) = (yyvsp[-1].derivtype); }
#line 3593 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 168: /* abstr_direct_except_function: abstr_direct_except_function PT_LBRACK expr PT_RBRACK  */
#line 733 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.derivtype) = DERIVArray((yyvsp[-3].derivtype), (yyvsp[-1].expr)); }
#line 3599 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 169: /* abstr_direct_except_function: PT_LBRACK expr PT_RBRACK  */
#line 735 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.derivtype) = DERIVArray(DERIVEnd(NULL), (yyvsp[-1].expr)); }
#line 3605 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 170: /* abstr_direct_except_function: abstr_direct_except_function PT_LPAREN PT_RPAREN  */
#line 737 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.derivtype) = DERIVFunction((yyvsp[-2].derivtype), NULL); }
#line 3611 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 171: /* abstr_direct_except_function: abstr_direct_except_function PT_LPAREN paras PT_RPAREN  */
#line 739 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.derivtype) = DERIVFunction((yyvsp[-3].derivtype), (yyvsp[-1].para_list)); }
#line 3617 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 172: /* exprs: expr  */
#line 747 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.expr_list) = PELCons((yyvsp[0].expr), PELNil()); }
#line 3623 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 173: /* exprs: expr PT_COMMA exprs  */
#line 749 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.expr_list) = PELCons((yyvsp[-2].expr), (yyvsp[0].expr_list)); }
#line 3629 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 174: /* expr0: PT_LPAREN expr PT_RPAREN  */
#line 754 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.expr) = (yyvsp[-1].expr); }
#line 3635 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 175: /* expr0: PT_NATLIT  */
#line 756 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.expr) = PPConst((yyvsp[0].nat).n, (yyvsp[0].nat).hex, (yyvsp[0].nat).l, (yyvsp[0].nat).u); }
#line 3641 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 176: /* expr0: PT_STRINGLIT  */
#line 758 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.expr) = PPString((yyvsp[0].string)); }
#line 3647 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 177: /* expr0: PT_IDENT  */
#line 760 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.expr) = PPVar((yyvsp[0].string)); }
#line 3653 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 178: /* expr0: PT_SIZEOF PT_LPAREN type_name PT_RPAREN  */
#line 762 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.expr) = PPSizeofType((yyvsp[-1].pretype)); }
#line 3659 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 179: /* type_arg: ident PT_EQ atype  */
#line 767 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.type_arg) = ATypeArg((yyvsp[-2].string), (yyvsp[0].atype), NULL); }
#line 3665 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 180: /* type_arg: ident PT_EQ atype PT_COMMA type_arg  */
#line 769 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.type_arg) = ATypeArg((yyvsp[-4].string), (yyvsp[-2].atype), (yyvsp[0].type_arg)); }
#line 3671 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 181: /* varg: ident PT_EQ ra  */
#line 774 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.varg) = PPVArg((yyvsp[-2].string), (yyvsp[0].RAssertion), NULL); }
#line 3677 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 182: /* varg: ident PT_EQ ra PT_COMMA varg  */
#line 776 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.varg) = PPVArg((yyvsp[-4].string), (yyvsp[-2].RAssertion), (yyvsp[0].varg)); }
#line 3683 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 183: /* call_varg: varg  */
#line 781 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.expr) = PPCall(NULL, NULL, NULL, NULL, NULL, (yyvsp[0].varg)); }
#line 3689 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 184: /* call_varg: PT_SEMI type_arg  */
#line 783 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.expr) = PPCall(NULL, NULL, NULL, NULL, (yyvsp[0].type_arg), NULL); }
#line 3695 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 185: /* call_varg: varg PT_SEMI type_arg  */
#line 785 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.expr) = PPCall(NULL, NULL, NULL, NULL, (yyvsp[0].type_arg), (yyvsp[-2].varg)); }
#line 3701 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 186: /* call_name_varg: PT_WHERE call_varg  */
#line 790 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.expr) = (yyvsp[0].expr); }
#line 3707 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 187: /* call_name_varg: PT_WHERE PT_LPAREN ident PT_RPAREN call_varg  */
#line 792 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyvsp[0].expr)->d.CALL.vargs->spec_name = (yyvsp[-2].string); (yyval.expr) = (yyvsp[0].expr); }
#line 3713 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 188: /* call_name_varg: PT_WHERE PT_LPAREN ident PT_RPAREN  */
#line 794 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.expr) = PPCall(NULL, NULL, (yyvsp[-1].string), NULL, NULL, NULL);  }
#line 3719 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 189: /* call_name_scope_varg: call_name_varg  */
#line 799 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.expr) = (yyvsp[0].expr); }
#line 3725 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 190: /* call_name_scope_varg: call_name_varg PT_BY scope_list  */
#line 801 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.expr) = (yyvsp[-2].expr); (yyval.expr)->d.CALL.vargs->scopes = (yyvsp[0].string_list); }
#line 3731 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 191: /* call_name_scope_varg: PT_BY scope_list  */
#line 803 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.expr) = PPCall(NULL, NULL, NULL, (yyvsp[0].string_list), NULL, NULL); }
#line 3737 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 192: /* expr1: expr0  */
#line 808 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.expr) = (yyvsp[0].expr); }
#line 3743 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 193: /* expr1: expr1 PT_LBRACK expr PT_RBRACK  */
#line 810 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.expr) = PPIndex((yyvsp[-3].expr), (yyvsp[-1].expr)); }
#line 3749 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 194: /* expr1: expr1 PT_DOT ident  */
#line 812 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.expr) = PPFieldof((yyvsp[-2].expr), (yyvsp[0].string)); }
#line 3755 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 195: /* expr1: expr1 PT_MINUSGREATER ident  */
#line 814 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.expr) = PPFieldofptr((yyvsp[-2].expr), (yyvsp[0].string)); }
#line 3761 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 196: /* expr1: expr1 PT_LPAREN PT_RPAREN  */
#line 816 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.expr) = PPCall((yyvsp[-2].expr), PELNil(), NULL, NULL, NULL, NULL); }
#line 3767 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 197: /* expr1: expr1 PT_LPAREN exprs PT_RPAREN  */
#line 818 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.expr) = PPCall((yyvsp[-3].expr), (yyvsp[-1].expr_list), NULL, NULL, NULL, NULL); }
#line 3773 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 198: /* expr1: expr1 PT_LPAREN PT_RPAREN PT_SLASHSTARAT call_name_scope_varg PT_STARSLASH  */
#line 820 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyvsp[-1].expr)->d.CALL.func = (yyvsp[-5].expr); (yyvsp[-1].expr)->d.CALL.args = NULL; (yyval.expr) = (yyvsp[-1].expr); }
#line 3779 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 199: /* expr1: expr1 PT_LPAREN exprs PT_RPAREN PT_SLASHSTARAT call_name_scope_varg PT_STARSLASH  */
#line 822 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyvsp[-1].expr)->d.CALL.func = (yyvsp[-6].expr); (yyvsp[-1].expr)->d.CALL.args = (yyvsp[-4].expr_list); (yyval.expr) = (yyvsp[-1].expr); }
#line 3785 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 200: /* expr2: expr1  */
#line 827 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.expr) = (yyvsp[0].expr); }
#line 3791 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 201: /* expr2: PT_MINUS expr2  */
#line 829 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.expr) = PPUnop(T_UMINUS, (yyvsp[0].expr)); }
#line 3797 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 202: /* expr2: PT_PLUS expr2  */
#line 831 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.expr) = PPUnop(T_UPLUS, (yyvsp[0].expr)); }
#line 3803 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 203: /* expr2: PT_EXCLAM expr2  */
#line 833 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.expr) = PPUnop(T_NOTBOOL, (yyvsp[0].expr)); }
#line 3809 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 204: /* expr2: PT_TLIDE expr2  */
#line 835 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.expr) = PPUnop(T_NOTINT, (yyvsp[0].expr)); }
#line 3815 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 205: /* expr2: PT_STAR expr2  */
#line 837 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.expr) = PPDeref((yyvsp[0].expr)); }
#line 3821 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 206: /* expr2: PT_AND expr2  */
#line 839 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.expr) = PPAddress((yyvsp[0].expr)); }
#line 3827 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 207: /* expr2: PT_LPAREN type_name PT_RPAREN expr2  */
#line 841 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.expr) = PPCast((yyvsp[-2].pretype), (yyvsp[0].expr)); }
#line 3833 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 208: /* expr3: expr2  */
#line 846 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.expr) = (yyvsp[0].expr); }
#line 3839 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 209: /* expr3: expr3 PT_STAR expr2  */
#line 848 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.expr) = PPBinop(T_MUL, (yyvsp[-2].expr), (yyvsp[0].expr)); }
#line 3845 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 210: /* expr3: expr3 PT_SLASH expr2  */
#line 850 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.expr) = PPBinop(T_DIV, (yyvsp[-2].expr), (yyvsp[0].expr)); }
#line 3851 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 211: /* expr3: expr3 PT_PERCENT expr2  */
#line 852 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.expr) = PPBinop(T_MOD, (yyvsp[-2].expr), (yyvsp[0].expr)); }
#line 3857 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 212: /* expr4: expr3  */
#line 857 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.expr) = (yyvsp[0].expr); }
#line 3863 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 213: /* expr4: expr4 PT_PLUS expr3  */
#line 859 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.expr) = PPBinop(T_PLUS, (yyvsp[-2].expr), (yyvsp[0].expr)); }
#line 3869 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 214: /* expr4: expr4 PT_MINUS expr3  */
#line 861 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.expr) = PPBinop(T_MINUS, (yyvsp[-2].expr), (yyvsp[0].expr)); }
#line 3875 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 215: /* expr5: expr4  */
#line 866 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.expr) = (yyvsp[0].expr); }
#line 3881 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 216: /* expr5: expr5 PT_LESSLESS expr4  */
#line 868 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.expr) = PPBinop(T_SHL, (yyvsp[-2].expr), (yyvsp[0].expr)); }
#line 3887 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 217: /* expr5: expr5 PT_GREATERGREATER expr4  */
#line 870 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.expr) = PPBinop(T_SHR, (yyvsp[-2].expr), (yyvsp[0].expr)); }
#line 3893 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 218: /* expr6: expr5  */
#line 875 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.expr) = (yyvsp[0].expr); }
#line 3899 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 219: /* expr6: expr6 PT_LESS expr5  */
#line 877 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.expr) = PPBinop(T_LT, (yyvsp[-2].expr), (yyvsp[0].expr)); }
#line 3905 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 220: /* expr6: expr6 PT_GREATER expr5  */
#line 879 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.expr) = PPBinop(T_GT, (yyvsp[-2].expr), (yyvsp[0].expr)); }
#line 3911 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 221: /* expr6: expr6 PT_LESSEQ expr5  */
#line 881 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.expr) = PPBinop(T_LE, (yyvsp[-2].expr), (yyvsp[0].expr)); }
#line 3917 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 222: /* expr6: expr6 PT_GREATEREQ expr5  */
#line 883 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.expr) = PPBinop(T_GE, (yyvsp[-2].expr), (yyvsp[0].expr)); }
#line 3923 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 223: /* expr7: expr6  */
#line 888 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.expr) = (yyvsp[0].expr); }
#line 3929 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 224: /* expr7: expr7 PT_EQEQ expr6  */
#line 890 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.expr) = PPBinop(T_EQ, (yyvsp[-2].expr), (yyvsp[0].expr)); }
#line 3935 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 225: /* expr7: expr7 PT_EXCLAMEQ expr6  */
#line 892 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.expr) = PPBinop(T_NE, (yyvsp[-2].expr), (yyvsp[0].expr)); }
#line 3941 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 226: /* expr8: expr7  */
#line 897 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.expr) = (yyvsp[0].expr); }
#line 3947 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 227: /* expr8: expr8 PT_AND expr7  */
#line 899 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.expr) = PPBinop(T_BAND, (yyvsp[-2].expr), (yyvsp[0].expr)); }
#line 3953 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 228: /* expr9: expr8  */
#line 904 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.expr) = (yyvsp[0].expr); }
#line 3959 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 229: /* expr9: expr9 PT_CARET expr8  */
#line 906 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.expr) = PPBinop(T_XOR, (yyvsp[-2].expr), (yyvsp[0].expr)); }
#line 3965 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 230: /* expr10: expr9  */
#line 911 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.expr) = (yyvsp[0].expr); }
#line 3971 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 231: /* expr10: expr10 PT_BAR expr9  */
#line 913 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.expr) = PPBinop(T_BOR, (yyvsp[-2].expr), (yyvsp[0].expr)); }
#line 3977 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 232: /* expr11: expr10  */
#line 918 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.expr) = (yyvsp[0].expr); }
#line 3983 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 233: /* expr11: expr11 PT_ANDAND expr10  */
#line 920 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.expr) = PPBinop(T_AND, (yyvsp[-2].expr), (yyvsp[0].expr)); }
#line 3989 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 234: /* expr12: expr11  */
#line 925 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.expr) = (yyvsp[0].expr); }
#line 3995 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 235: /* expr12: expr12 PT_BARBAR expr11  */
#line 927 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.expr) = PPBinop(T_OR, (yyvsp[-2].expr), (yyvsp[0].expr)); }
#line 4001 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 236: /* expr: expr12  */
#line 932 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.expr) = (yyvsp[0].expr); }
#line 4007 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 237: /* expr: expr12 PT_QUESTION expr PT_COLON expr  */
#line 934 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.expr) = PPCondition((yyvsp[-4].expr), (yyvsp[-2].expr), (yyvsp[0].expr)); }
#line 4013 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 238: /* kind0: PT_STAR  */
#line 943 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.kind) = KStar(); }
#line 4019 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 239: /* kind0: PT_LPAREN kind PT_RPAREN  */
#line 945 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.kind) = (yyvsp[-1].kind); }
#line 4025 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 240: /* kind: kind0  */
#line 950 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.kind) = (yyvsp[0].kind); }
#line 4031 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 241: /* kind: kind0 PT_EQGREATER kind  */
#line 952 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.kind) = KArrow((yyvsp[-2].kind), (yyvsp[0].kind)); }
#line 4037 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 242: /* atype0: ident  */
#line 957 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.atype) = ATTVar((yyvsp[0].string), NULL); }
#line 4043 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 243: /* atype0: PT_LPAREN atype PT_RPAREN  */
#line 959 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.atype) = (yyvsp[-1].atype); }
#line 4049 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 244: /* atype1: atype0  */
#line 964 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.atype) = (yyvsp[0].atype); }
#line 4055 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 245: /* atype1: atype1 atype0  */
#line 966 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.atype) = ATApp((yyvsp[-1].atype), (yyvsp[0].atype)); }
#line 4061 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 246: /* atype2: atype1  */
#line 971 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.atype) = (yyvsp[0].atype); }
#line 4067 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 247: /* atype2: atype2 PT_STAR atype1  */
#line 973 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.atype) = ATApp(ATApp(ATTVar(clone_str("prod"), NULL), (yyvsp[-2].atype)), (yyvsp[0].atype)); }
#line 4073 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 248: /* atype: atype2  */
#line 978 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.atype) = (yyvsp[0].atype); }
#line 4079 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 249: /* atype: atype2 PT_MINUSGREATER atype  */
#line 980 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.atype) = ATArrow((yyvsp[-2].atype), (yyvsp[0].atype)); }
#line 4085 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 250: /* ident_list_space: ident  */
#line 985 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.name_list) = NLCons((yyvsp[0].string), NULL); }
#line 4091 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 251: /* ident_list_space: ident ident_list_space  */
#line 987 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.name_list) = NLCons((yyvsp[-1].string), (yyvsp[0].name_list)); }
#line 4097 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 252: /* ident_list_comma: ident  */
#line 992 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.name_list) = NLCons((yyvsp[0].string), NULL); }
#line 4103 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 253: /* ident_list_comma: ident PT_COMMA ident_list_comma  */
#line 994 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.name_list) = NLCons((yyvsp[-2].string), (yyvsp[0].name_list)); }
#line 4109 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 254: /* brace_atype_list: PT_LBRACE ident_list_space PT_COLONCOLON kind PT_RBRACE  */
#line 999 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.atype_list) = atype_list_cons_multi((yyvsp[-3].name_list), (yyvsp[-1].kind), NULL); }
#line 4115 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 255: /* brace_atype_list: PT_LBRACE ident_list_space PT_COLONCOLON kind PT_RBRACE brace_atype_list  */
#line 1001 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.atype_list) = atype_list_cons_multi((yyvsp[-4].name_list), (yyvsp[-2].kind), (yyvsp[0].atype_list)); }
#line 4121 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 256: /* brace_atype_list: PT_LBRACE ident_list_space PT_RBRACE  */
#line 1003 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.atype_list) = atype_list_cons_multi((yyvsp[-1].name_list), NULL, NULL); }
#line 4127 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 257: /* brace_atype_list: PT_LBRACE ident_list_space PT_RBRACE brace_atype_list  */
#line 1005 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.atype_list) = atype_list_cons_multi((yyvsp[-2].name_list), NULL, (yyvsp[0].atype_list)); }
#line 4133 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 258: /* paren_atype_list: PT_LPAREN ident_list_space PT_COLONCOLON kind PT_RPAREN  */
#line 1010 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.atype_list) = atype_list_cons_multi((yyvsp[-3].name_list), (yyvsp[-1].kind), NULL); }
#line 4139 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 259: /* paren_atype_list: PT_LPAREN ident_list_space PT_COLONCOLON kind PT_RPAREN paren_atype_list  */
#line 1012 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.atype_list) = atype_list_cons_multi((yyvsp[-4].name_list), (yyvsp[-2].kind), (yyvsp[0].atype_list)); }
#line 4145 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 260: /* paren_atype_list_maybe_null: %empty  */
#line 1017 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.atype_list) = NULL; }
#line 4151 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 261: /* paren_atype_list_maybe_null: ident paren_atype_list_maybe_null  */
#line 1019 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.atype_list) = atype_list_cons((yyvsp[-1].string), NULL, (yyvsp[0].atype_list)); }
#line 4157 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 262: /* paren_atype_list_maybe_null: PT_LPAREN ident_list_space PT_COLONCOLON kind PT_RPAREN paren_atype_list_maybe_null  */
#line 1021 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.atype_list) = atype_list_cons_multi((yyvsp[-4].name_list), (yyvsp[-2].kind), (yyvsp[0].atype_list)); }
#line 4163 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 263: /* brace_comma_atype_list: PT_LBRACE ident_list_comma PT_COLONCOLON kind PT_RBRACE  */
#line 1026 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.atype_list) = atype_list_cons_multi((yyvsp[-3].name_list), (yyvsp[-1].kind), NULL); }
#line 4169 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 264: /* brace_comma_atype_list: PT_LBRACE ident_list_comma PT_COLONCOLON kind PT_RBRACE PT_COMMA brace_comma_atype_list  */
#line 1028 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.atype_list) = atype_list_cons_multi((yyvsp[-5].name_list), (yyvsp[-3].kind), (yyvsp[0].atype_list)); }
#line 4175 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 265: /* brace_comma_atype_list: PT_LBRACE ident_list_comma PT_RBRACE  */
#line 1030 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.atype_list) = atype_list_cons_multi((yyvsp[-1].name_list), NULL, NULL); }
#line 4181 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 266: /* brace_comma_atype_list: PT_LBRACE ident_list_comma PT_RBRACE PT_COMMA brace_comma_atype_list  */
#line 1032 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.atype_list) = atype_list_cons_multi((yyvsp[-3].name_list), NULL, (yyvsp[0].atype_list)); }
#line 4187 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 267: /* comma_lvar_list: ident  */
#line 1037 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.lvar_list) = lvar_list_cons((yyvsp[0].string), NULL, NULL); }
#line 4193 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 268: /* comma_lvar_list: ident PT_COLON atype  */
#line 1039 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.lvar_list) = lvar_list_cons_multi(NLCons((yyvsp[-2].string), NULL), (yyvsp[0].atype), NULL); }
#line 4199 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 269: /* comma_lvar_list: ident PT_COMMA comma_lvar_list  */
#line 1041 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.lvar_list) = lvar_list_cons((yyvsp[-2].string), NULL, (yyvsp[0].lvar_list)); }
#line 4205 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 270: /* comma_lvar_list: ident PT_COLON atype PT_COMMA comma_lvar_list  */
#line 1043 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.lvar_list) = lvar_list_cons_multi(NLCons((yyvsp[-4].string), NULL), (yyvsp[-2].atype), (yyvsp[0].lvar_list)); }
#line 4211 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 271: /* paren_lvar_list: ident  */
#line 1048 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.lvar_list) = lvar_list_cons((yyvsp[0].string), NULL, NULL); }
#line 4217 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 272: /* paren_lvar_list: PT_LPAREN ident_list_space PT_COLON atype PT_RPAREN  */
#line 1050 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.lvar_list) = lvar_list_cons_multi((yyvsp[-3].name_list), (yyvsp[-1].atype), NULL); }
#line 4223 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 273: /* paren_lvar_list: ident paren_lvar_list  */
#line 1052 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.lvar_list) = lvar_list_cons((yyvsp[-1].string), NULL, (yyvsp[0].lvar_list)); }
#line 4229 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 274: /* paren_lvar_list: PT_LPAREN ident_list_space PT_COLON atype PT_RPAREN paren_lvar_list  */
#line 1054 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.lvar_list) = lvar_list_cons_multi((yyvsp[-4].name_list), (yyvsp[-2].atype), (yyvsp[0].lvar_list)); }
#line 4235 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 275: /* semi_lvar_list: ident PT_COLON atype PT_SEMI  */
#line 1059 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.lvar_list) = lvar_list_cons((yyvsp[-3].string), (yyvsp[-1].atype), NULL); }
#line 4241 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 276: /* semi_lvar_list: ident PT_COLON atype PT_SEMI semi_lvar_list  */
#line 1061 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.lvar_list) = lvar_list_cons((yyvsp[-4].string), (yyvsp[-2].atype), (yyvsp[0].lvar_list)); }
#line 4247 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 277: /* term_list: ident  */
#line 1066 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.term_list) = term_list_cons((yyvsp[0].string), NULL, NULL, NULL); }
#line 4253 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 278: /* term_list: PT_LPAREN ident_list_space PT_COLON atype PT_RPAREN  */
#line 1068 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.term_list) = term_list_cons_multi((yyvsp[-3].name_list), NULL, (yyvsp[-1].atype), NULL); }
#line 4259 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 279: /* term_list: PT_LPAREN ident_list_space PT_COLON brace_atype_list PT_MINUSGREATER atype PT_RPAREN  */
#line 1070 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.term_list) = term_list_cons_multi((yyvsp[-5].name_list), (yyvsp[-3].atype_list), (yyvsp[-1].atype), NULL); }
#line 4265 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 280: /* term_list: ident term_list  */
#line 1072 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.term_list) = term_list_cons((yyvsp[-1].string), NULL, NULL, (yyvsp[0].term_list)); }
#line 4271 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 281: /* term_list: PT_LPAREN ident_list_space PT_COLON atype PT_RPAREN term_list  */
#line 1074 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.term_list) = term_list_cons_multi((yyvsp[-4].name_list), NULL, (yyvsp[-2].atype), (yyvsp[0].term_list)); }
#line 4277 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 282: /* term_list: PT_LPAREN ident_list_space PT_COLON brace_atype_list PT_MINUSGREATER atype PT_RPAREN term_list  */
#line 1076 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.term_list) = term_list_cons_multi((yyvsp[-6].name_list), (yyvsp[-4].atype_list), (yyvsp[-2].atype), (yyvsp[0].term_list)); }
#line 4283 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 283: /* ra0_5: PT_IDENT  */
#line 1085 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RAVar((yyvsp[0].string)); }
#line 4289 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 284: /* ra0_5: PT_HASH ra0_5  */
#line 1087 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RAShadow((yyvsp[0].RAssertion)); }
#line 4295 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 285: /* ra0: ra0_5  */
#line 1092 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = (yyvsp[0].RAssertion); }
#line 4301 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 286: /* ra0: PT_LPAREN ra PT_RPAREN  */
#line 1094 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = (yyvsp[-1].RAssertion); }
#line 4307 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 287: /* ra0: PT___TIME_COST  */
#line 1096 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RATimeCost(); }
#line 4313 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 288: /* ra0: PT_NATLIT  */
#line 1098 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RAConst((yyvsp[0].nat).n); }
#line 4319 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 289: /* ra0: PT_DATA_AT PT_LPAREN ra PT_COMMA ra PT_RPAREN  */
#line 1100 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RAData_at(NULL, (yyvsp[-3].RAssertion), (yyvsp[-1].RAssertion)); }
#line 4325 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 290: /* ra0: PT_DATA_AT PT_LPAREN ra PT_COMMA type_name PT_COMMA ra PT_RPAREN  */
#line 1102 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RAData_at((yyvsp[-3].pretype), (yyvsp[-5].RAssertion), (yyvsp[-1].RAssertion)); }
#line 4331 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 291: /* ra0: PT_UNDEF_DATA_AT PT_LPAREN ra PT_RPAREN  */
#line 1104 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RAUndef_data_at(NULL, (yyvsp[-1].RAssertion)); }
#line 4337 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 292: /* ra0: PT_UNDEF_DATA_AT PT_LPAREN ra PT_COMMA type_name PT_RPAREN  */
#line 1106 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RAUndef_data_at((yyvsp[-1].pretype), (yyvsp[-3].RAssertion)); }
#line 4343 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 293: /* ra0: PT_FIELD_ADDR PT_LPAREN ra PT_COMMA ident PT_RPAREN  */
#line 1108 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RAField_addr((yyvsp[-3].RAssertion), NULL, (yyvsp[-1].string)); }
#line 4349 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 294: /* ra0: PT_FIELD_ADDR PT_LPAREN ra PT_COMMA type_name PT_COMMA ident PT_RPAREN  */
#line 1110 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RAField_addr((yyvsp[-5].RAssertion), (yyvsp[-3].pretype), (yyvsp[-1].string)); }
#line 4355 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 295: /* ra0: PT_FIELD_ADDR PT_LPAREN ra PT_COMMA PT_IDENT PT_COMMA ident PT_RPAREN  */
#line 1112 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RAField_addr((yyvsp[-5].RAssertion), PreType(TRIVTypeAlias((yyvsp[-3].string)), DERIVEnd(NULL)), (yyvsp[-1].string)); }
#line 4361 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 296: /* ra0: PT_ARR PT_LPAREN ra PT_COMMA ra PT_COMMA ra PT_RPAREN  */
#line 1114 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RAArr((yyvsp[-5].RAssertion), NULL, (yyvsp[-3].RAssertion), (yyvsp[-1].RAssertion)); }
#line 4367 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 297: /* ra0: PT_ARR PT_LPAREN ra PT_COMMA type_name PT_COMMA ra PT_COMMA ra PT_RPAREN  */
#line 1116 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RAArr((yyvsp[-7].RAssertion), (yyvsp[-5].pretype), (yyvsp[-3].RAssertion), (yyvsp[-1].RAssertion)); }
#line 4373 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 298: /* ra0: PT_EMP  */
#line 1118 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RAEmp(); }
#line 4379 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 299: /* ra0: PT___RETURN  */
#line 1120 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RA__return(); }
#line 4385 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 300: /* ra0: PT_SIZEOF PT_LPAREN type_name PT_RPAREN  */
#line 1122 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RASizeOf((yyvsp[-1].pretype)); }
#line 4391 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 301: /* ra1: ra0  */
#line 1127 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = (yyvsp[0].RAssertion); }
#line 4397 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 302: /* ra1: ra1 PT_LBRACK ra PT_RBRACK  */
#line 1129 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RAIndex((yyvsp[-3].RAssertion), (yyvsp[-1].RAssertion)); }
#line 4403 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 303: /* ra1: ra1 PT_DOT PT_LBRACE type_name PT_DOT ident PT_RBRACE  */
#line 1131 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RAFieldof((yyvsp[-6].RAssertion), (yyvsp[-1].string), (yyvsp[-3].pretype)); }
#line 4409 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 304: /* ra1: ra1 PT_DOT PT_LBRACE PT_IDENT PT_DOT ident PT_RBRACE  */
#line 1133 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RAFieldof((yyvsp[-6].RAssertion), (yyvsp[-1].string), PreType(TRIVTypeAlias((yyvsp[-3].string)), DERIVEnd(NULL))); }
#line 4415 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 305: /* ra1: ra1 PT_MINUSGREATER PT_LBRACE type_name PT_DOT ident PT_RBRACE  */
#line 1135 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RAFieldofptr((yyvsp[-6].RAssertion), (yyvsp[-1].string), (yyvsp[-3].pretype)); }
#line 4421 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 306: /* ra1: ra1 PT_MINUSGREATER PT_LBRACE PT_IDENT PT_DOT ident PT_RBRACE  */
#line 1137 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RAFieldofptr((yyvsp[-6].RAssertion), (yyvsp[-1].string), PreType(TRIVTypeAlias((yyvsp[-3].string)), DERIVEnd(NULL))); }
#line 4427 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 307: /* ra1: ra1 PT_DOT ident  */
#line 1139 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RAFieldof((yyvsp[-2].RAssertion), (yyvsp[0].string), NULL); }
#line 4433 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 308: /* ra1: ra1 PT_MINUSGREATER ident  */
#line 1141 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RAFieldofptr((yyvsp[-2].RAssertion), (yyvsp[0].string), NULL); }
#line 4439 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 309: /* ra1: ra1 PT_AT ident  */
#line 1143 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RAOld((yyvsp[0].string), (yyvsp[-2].RAssertion)); }
#line 4445 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 310: /* ra1: ra1 PT_LPAREN PT_RPAREN  */
#line 1145 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = (yyvsp[-2].RAssertion); }
#line 4451 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 311: /* ra1: ras PT_RPAREN  */
#line 1147 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = (yyvsp[-1].RAssertion); }
#line 4457 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 312: /* ras: ra1 PT_LPAREN ra  */
#line 1152 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RAApp((yyvsp[-2].RAssertion), (yyvsp[0].RAssertion)); }
#line 4463 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 313: /* ras: ras PT_COMMA ra  */
#line 1154 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RAApp((yyvsp[-2].RAssertion), (yyvsp[0].RAssertion)); }
#line 4469 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 314: /* ra2: ra1  */
#line 1159 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = (yyvsp[0].RAssertion); }
#line 4475 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 315: /* ra2: PT_MINUS ra2  */
#line 1161 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RAUnop(T_UMINUS, (yyvsp[0].RAssertion)); }
#line 4481 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 316: /* ra2: PT_PLUS ra2  */
#line 1163 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RAUnop(T_UPLUS, (yyvsp[0].RAssertion)); }
#line 4487 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 317: /* ra2: PT_EXCLAM ra2  */
#line 1165 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RAUnop(T_NOTBOOL, (yyvsp[0].RAssertion)); }
#line 4493 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 318: /* ra2: PT_TLIDE ra2  */
#line 1167 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RAUnop(T_NOTINT, (yyvsp[0].RAssertion)); }
#line 4499 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 319: /* ra2: PT_STAR PT_LBRACE type_name PT_RBRACE ra2  */
#line 1169 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RADeref((yyvsp[-2].pretype), (yyvsp[0].RAssertion)); }
#line 4505 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 320: /* ra2: PT_STAR ra2  */
#line 1171 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RADeref(NULL, (yyvsp[0].RAssertion)); }
#line 4511 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 321: /* ra2: PT_AND ra2  */
#line 1173 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RAAddress((yyvsp[0].RAssertion)); }
#line 4517 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 322: /* ra2: PT_LPAREN type_name PT_RPAREN ra2  */
#line 1175 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RACast((yyvsp[-2].pretype), (yyvsp[0].RAssertion)); }
#line 4523 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 323: /* ra3: ra2  */
#line 1180 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = (yyvsp[0].RAssertion); }
#line 4529 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 324: /* ra3: ra3 PT_STAR ra2  */
#line 1182 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RABinop(T_MUL, (yyvsp[-2].RAssertion), (yyvsp[0].RAssertion)); }
#line 4535 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 325: /* ra3: ra3 PT_SLASH ra2  */
#line 1184 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RABinop(T_DIV, (yyvsp[-2].RAssertion), (yyvsp[0].RAssertion)); }
#line 4541 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 326: /* ra3: ra3 PT_PERCENT ra2  */
#line 1186 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RABinop(T_MOD, (yyvsp[-2].RAssertion), (yyvsp[0].RAssertion)); }
#line 4547 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 327: /* ra4: ra3  */
#line 1191 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = (yyvsp[0].RAssertion); }
#line 4553 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 328: /* ra4: ra4 PT_PLUS ra3  */
#line 1193 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RABinop(T_PLUS, (yyvsp[-2].RAssertion), (yyvsp[0].RAssertion)); }
#line 4559 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 329: /* ra4: ra4 PT_MINUS ra3  */
#line 1195 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RABinop(T_MINUS, (yyvsp[-2].RAssertion), (yyvsp[0].RAssertion)); }
#line 4565 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 330: /* ra4_75: ra4  */
#line 1200 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = (yyvsp[0].RAssertion); }
#line 4571 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 331: /* ra4_75: ra4 PT_COLON atype  */
#line 1202 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RAAnn((yyvsp[0].atype), (yyvsp[-2].RAssertion)); }
#line 4577 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 332: /* ra5: ra4_75  */
#line 1207 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = (yyvsp[0].RAssertion); }
#line 4583 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 333: /* ra5: ra5 PT_LESSLESS ra4_75  */
#line 1209 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RABinop(T_SHL, (yyvsp[-2].RAssertion), (yyvsp[0].RAssertion)); }
#line 4589 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 334: /* ra5: ra5 PT_GREATERGREATER ra4_75  */
#line 1211 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RABinop(T_SHR, (yyvsp[-2].RAssertion), (yyvsp[0].RAssertion)); }
#line 4595 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 335: /* ra6: ra5  */
#line 1216 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = (yyvsp[0].RAssertion); }
#line 4601 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 336: /* ra6: ra6 PT_LESS ra5  */
#line 1218 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RABinop(T_LT, (yyvsp[-2].RAssertion), (yyvsp[0].RAssertion)); }
#line 4607 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 337: /* ra6: ra6 PT_GREATER ra5  */
#line 1220 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RABinop(T_GT, (yyvsp[-2].RAssertion), (yyvsp[0].RAssertion)); }
#line 4613 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 338: /* ra6: ra6 PT_LESSEQ ra5  */
#line 1222 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RABinop(T_LE, (yyvsp[-2].RAssertion), (yyvsp[0].RAssertion)); }
#line 4619 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 339: /* ra6: ra6 PT_GREATEREQ ra5  */
#line 1224 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RABinop(T_GE, (yyvsp[-2].RAssertion), (yyvsp[0].RAssertion)); }
#line 4625 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 340: /* ra7: ra6  */
#line 1229 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = (yyvsp[0].RAssertion); }
#line 4631 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 341: /* ra7: ra7 PT_EQEQ ra6  */
#line 1231 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RABinop(T_EQ, (yyvsp[-2].RAssertion), (yyvsp[0].RAssertion)); }
#line 4637 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 342: /* ra7: ra7 PT_EXCLAMEQ ra6  */
#line 1233 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RABinop(T_NE, (yyvsp[-2].RAssertion), (yyvsp[0].RAssertion)); }
#line 4643 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 343: /* ra8: ra7  */
#line 1238 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = (yyvsp[0].RAssertion); }
#line 4649 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 344: /* ra8: ra8 PT_AND ra7  */
#line 1240 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RABinop(T_BAND, (yyvsp[-2].RAssertion), (yyvsp[0].RAssertion)); }
#line 4655 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 345: /* ra9: ra8  */
#line 1245 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = (yyvsp[0].RAssertion); }
#line 4661 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 346: /* ra9: ra9 PT_CARET ra8  */
#line 1247 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RABinop(T_XOR, (yyvsp[-2].RAssertion), (yyvsp[0].RAssertion)); }
#line 4667 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 347: /* ra10: ra9  */
#line 1252 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = (yyvsp[0].RAssertion); }
#line 4673 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 348: /* ra10: ra10 PT_BAR ra9  */
#line 1254 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RABinop(T_BOR, (yyvsp[-2].RAssertion), (yyvsp[0].RAssertion)); }
#line 4679 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 349: /* ra11: ra10  */
#line 1259 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = (yyvsp[0].RAssertion); }
#line 4685 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 350: /* ra11: ra11 PT_ANDAND ra10  */
#line 1261 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RABinop(T_AND, (yyvsp[-2].RAssertion), (yyvsp[0].RAssertion)); }
#line 4691 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 351: /* ra12: ra11  */
#line 1266 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = (yyvsp[0].RAssertion); }
#line 4697 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 352: /* ra12: ra12 PT_BARBAR ra11  */
#line 1268 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RABinop(T_OR, (yyvsp[-2].RAssertion), (yyvsp[0].RAssertion)); }
#line 4703 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 353: /* ra13: ra12  */
#line 1273 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = (yyvsp[0].RAssertion); }
#line 4709 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 354: /* ra13: ra12 PT_EQGREATER ra13  */
#line 1275 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RAConn(A_IMPLY, (yyvsp[-2].RAssertion), (yyvsp[0].RAssertion)); }
#line 4715 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 355: /* ra13: ra12 PT_LESSEQGREATER ra13  */
#line 1277 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RAConn(A_IFF, (yyvsp[-2].RAssertion), (yyvsp[0].RAssertion)); }
#line 4721 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 356: /* ra14: ra1 PT_BAREQ type_name fun_contra_body  */
#line 1282 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
    { (yyval.RAssertion) = RASpec((yyvsp[-3].RAssertion), (yyvsp[-1].pretype), (yyvsp[0].spec)); }
#line 4727 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 357: /* raq: PT_FORALL forall_aux  */
#line 1287 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = (yyvsp[0].RAssertion); }
#line 4733 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 358: /* raq: PT_EXISTS exists_aux  */
#line 1289 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = (yyvsp[0].RAssertion); }
#line 4739 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 359: /* forall_aux: ident PT_COMMA ra  */
#line 1294 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RAQfop(A_FORALL, 0, (yyvsp[-2].string), NULL, NULL, (yyvsp[0].RAssertion)); }
#line 4745 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 360: /* forall_aux: ident forall_aux  */
#line 1296 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RAQfop(A_FORALL, 0, (yyvsp[-1].string), NULL, NULL, (yyvsp[0].RAssertion)); }
#line 4751 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 361: /* forall_aux: PT_LPAREN ident_list_space PT_COLON atype PT_RPAREN PT_COMMA ra  */
#line 1298 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RAMultiQfop(A_FORALL, 0, (yyvsp[-5].name_list), NULL, (yyvsp[-3].atype), (yyvsp[0].RAssertion)); }
#line 4757 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 362: /* forall_aux: PT_LPAREN ident_list_space PT_COLON atype PT_RPAREN forall_aux  */
#line 1300 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RAMultiQfop(A_FORALL, 0, (yyvsp[-4].name_list), NULL, (yyvsp[-2].atype), (yyvsp[0].RAssertion)); }
#line 4763 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 363: /* forall_aux: PT_LPAREN ident_list_space PT_COLON brace_atype_list PT_MINUSGREATER atype PT_RPAREN PT_COMMA ra  */
#line 1302 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RAMultiQfop(A_FORALL, 0, (yyvsp[-7].name_list), (yyvsp[-5].atype_list), (yyvsp[-3].atype), (yyvsp[0].RAssertion)); }
#line 4769 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 364: /* forall_aux: PT_LPAREN ident_list_space PT_COLON brace_atype_list PT_MINUSGREATER atype PT_RPAREN forall_aux  */
#line 1304 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RAMultiQfop(A_FORALL, 0, (yyvsp[-6].name_list), (yyvsp[-4].atype_list), (yyvsp[-2].atype), (yyvsp[0].RAssertion)); }
#line 4775 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 365: /* exists_aux: ident PT_COMMA ra  */
#line 1309 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RAQfop(A_EXISTS, 0, (yyvsp[-2].string), NULL, NULL, (yyvsp[0].RAssertion)); }
#line 4781 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 366: /* exists_aux: ident exists_aux  */
#line 1311 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RAQfop(A_EXISTS, 0, (yyvsp[-1].string), NULL, NULL, (yyvsp[0].RAssertion)); }
#line 4787 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 367: /* exists_aux: PT_LPAREN ident_list_space PT_COLON atype PT_RPAREN PT_COMMA ra  */
#line 1313 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RAMultiQfop(A_EXISTS, 0, (yyvsp[-5].name_list), NULL, (yyvsp[-3].atype), (yyvsp[0].RAssertion)); }
#line 4793 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 368: /* exists_aux: PT_LPAREN ident_list_space PT_COLON atype PT_RPAREN exists_aux  */
#line 1315 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RAMultiQfop(A_EXISTS, 0, (yyvsp[-4].name_list), NULL, (yyvsp[-2].atype), (yyvsp[0].RAssertion)); }
#line 4799 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 369: /* exists_aux: PT_LPAREN ident_list_space PT_COLON brace_atype_list PT_MINUSGREATER atype PT_RPAREN PT_COMMA ra  */
#line 1317 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RAMultiQfop(A_EXISTS, 0, (yyvsp[-7].name_list), (yyvsp[-5].atype_list), (yyvsp[-3].atype), (yyvsp[0].RAssertion)); }
#line 4805 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 370: /* exists_aux: PT_LPAREN ident_list_space PT_COLON brace_atype_list PT_MINUSGREATER atype PT_RPAREN exists_aux  */
#line 1319 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RAMultiQfop(A_EXISTS, 0, (yyvsp[-6].name_list), (yyvsp[-4].atype_list), (yyvsp[-2].atype), (yyvsp[0].RAssertion)); }
#line 4811 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 371: /* exists_aux: PT_LBRACK ident PT_RBRACK PT_COMMA ra  */
#line 1321 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RAQfop(A_EXISTS, 1, (yyvsp[-3].string), NULL, NULL, (yyvsp[0].RAssertion)); }
#line 4817 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 372: /* exists_aux: PT_LBRACK ident PT_RBRACK exists_aux  */
#line 1323 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RAQfop(A_EXISTS, 1, (yyvsp[-2].string), NULL, NULL, (yyvsp[0].RAssertion)); }
#line 4823 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 373: /* exists_aux: PT_LBRACK ident_list_space PT_COLON atype PT_RBRACK PT_COMMA ra  */
#line 1325 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RAMultiQfop(A_EXISTS, 1, (yyvsp[-5].name_list), NULL, (yyvsp[-3].atype), (yyvsp[0].RAssertion)); }
#line 4829 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 374: /* exists_aux: PT_LBRACK ident_list_space PT_COLON atype PT_RBRACK exists_aux  */
#line 1327 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RAMultiQfop(A_EXISTS, 1, (yyvsp[-4].name_list), NULL, (yyvsp[-2].atype), (yyvsp[0].RAssertion)); }
#line 4835 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 375: /* exists_aux: PT_LBRACK ident_list_space PT_COLON brace_atype_list PT_MINUSGREATER atype PT_RBRACK PT_COMMA ra  */
#line 1329 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RAMultiQfop(A_EXISTS, 1, (yyvsp[-7].name_list), (yyvsp[-5].atype_list), (yyvsp[-3].atype), (yyvsp[0].RAssertion)); }
#line 4841 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 376: /* exists_aux: PT_LBRACK ident_list_space PT_COLON brace_atype_list PT_MINUSGREATER atype PT_RBRACK exists_aux  */
#line 1331 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RAMultiQfop(A_EXISTS, 1, (yyvsp[-6].name_list), (yyvsp[-4].atype_list), (yyvsp[-2].atype), (yyvsp[0].RAssertion)); }
#line 4847 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 377: /* tail0: raq  */
#line 1336 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = (yyvsp[0].RAssertion); }
#line 4853 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 378: /* tail0: ra14  */
#line 1338 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = (yyvsp[0].RAssertion); }
#line 4859 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 379: /* tail0: PT_MINUS tail0  */
#line 1340 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RAUnop(T_UMINUS, (yyvsp[0].RAssertion)); }
#line 4865 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 380: /* tail0: PT_PLUS tail0  */
#line 1342 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RAUnop(T_UPLUS, (yyvsp[0].RAssertion)); }
#line 4871 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 381: /* tail0: PT_EXCLAM tail0  */
#line 1344 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RAUnop(T_NOTBOOL, (yyvsp[0].RAssertion)); }
#line 4877 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 382: /* tail0: PT_TLIDE tail0  */
#line 1346 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RAUnop(T_NOTINT, (yyvsp[0].RAssertion)); }
#line 4883 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 383: /* tail0: PT_STAR PT_LBRACE type_name PT_RBRACE tail0  */
#line 1348 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RADeref((yyvsp[-2].pretype), (yyvsp[0].RAssertion)); }
#line 4889 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 384: /* tail0: PT_STAR tail0  */
#line 1350 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RADeref(NULL, (yyvsp[0].RAssertion)); }
#line 4895 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 385: /* tail0: PT_AND tail0  */
#line 1352 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RAAddress((yyvsp[0].RAssertion)); }
#line 4901 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 386: /* tail0: PT_LPAREN type_name PT_RPAREN tail0  */
#line 1354 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RACast((yyvsp[-2].pretype), (yyvsp[0].RAssertion)); }
#line 4907 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 387: /* tail: tail0  */
#line 1359 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = (yyvsp[0].RAssertion); }
#line 4913 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 388: /* tail: ra3 PT_STAR tail0  */
#line 1361 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RABinop(T_MUL, (yyvsp[-2].RAssertion), (yyvsp[0].RAssertion)); }
#line 4919 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 389: /* tail: ra3 PT_SLASH tail0  */
#line 1363 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RABinop(T_DIV, (yyvsp[-2].RAssertion), (yyvsp[0].RAssertion)); }
#line 4925 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 390: /* tail: ra3 PT_PERCENT tail0  */
#line 1365 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RABinop(T_MOD, (yyvsp[-2].RAssertion), (yyvsp[0].RAssertion)); }
#line 4931 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 391: /* tail: ra4 PT_PLUS tail0  */
#line 1367 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RABinop(T_PLUS, (yyvsp[-2].RAssertion), (yyvsp[0].RAssertion)); }
#line 4937 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 392: /* tail: ra4 PT_MINUS tail0  */
#line 1369 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RABinop(T_MINUS, (yyvsp[-2].RAssertion), (yyvsp[0].RAssertion)); }
#line 4943 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 393: /* tail: ra5 PT_LESSLESS tail0  */
#line 1371 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RABinop(T_SHL, (yyvsp[-2].RAssertion), (yyvsp[0].RAssertion)); }
#line 4949 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 394: /* tail: ra5 PT_GREATERGREATER tail0  */
#line 1373 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RABinop(T_SHR, (yyvsp[-2].RAssertion), (yyvsp[0].RAssertion)); }
#line 4955 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 395: /* tail: ra6 PT_LESS tail0  */
#line 1375 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RABinop(T_LT, (yyvsp[-2].RAssertion), (yyvsp[0].RAssertion)); }
#line 4961 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 396: /* tail: ra6 PT_GREATER tail0  */
#line 1377 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RABinop(T_GT, (yyvsp[-2].RAssertion), (yyvsp[0].RAssertion)); }
#line 4967 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 397: /* tail: ra6 PT_LESSEQ tail0  */
#line 1379 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RABinop(T_LE, (yyvsp[-2].RAssertion), (yyvsp[0].RAssertion)); }
#line 4973 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 398: /* tail: ra6 PT_GREATEREQ tail0  */
#line 1381 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RABinop(T_GE, (yyvsp[-2].RAssertion), (yyvsp[0].RAssertion)); }
#line 4979 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 399: /* tail: ra7 PT_EQEQ tail0  */
#line 1383 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RABinop(T_EQ, (yyvsp[-2].RAssertion), (yyvsp[0].RAssertion)); }
#line 4985 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 400: /* tail: ra7 PT_EXCLAMEQ tail0  */
#line 1385 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RABinop(T_NE, (yyvsp[-2].RAssertion), (yyvsp[0].RAssertion)); }
#line 4991 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 401: /* tail: ra8 PT_AND tail0  */
#line 1387 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RABinop(T_BAND, (yyvsp[-2].RAssertion), (yyvsp[0].RAssertion)); }
#line 4997 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 402: /* tail: ra9 PT_CARET tail0  */
#line 1389 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RABinop(T_XOR, (yyvsp[-2].RAssertion), (yyvsp[0].RAssertion)); }
#line 5003 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 403: /* tail: ra10 PT_BAR tail0  */
#line 1391 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RABinop(T_BOR, (yyvsp[-2].RAssertion), (yyvsp[0].RAssertion)); }
#line 5009 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 404: /* tail: ra11 PT_ANDAND tail0  */
#line 1393 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RABinop(T_AND, (yyvsp[-2].RAssertion), (yyvsp[0].RAssertion)); }
#line 5015 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 405: /* tail: ra12 PT_BARBAR tail0  */
#line 1395 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RABinop(T_OR, (yyvsp[-2].RAssertion), (yyvsp[0].RAssertion)); }
#line 5021 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 406: /* tail: ra12 PT_EQGREATER tail  */
#line 1397 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RAConn(A_IMPLY, (yyvsp[-2].RAssertion), (yyvsp[0].RAssertion)); }
#line 5027 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 407: /* tail: ra12 PT_LESSEQGREATER tail  */
#line 1399 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = RAConn(A_IFF, (yyvsp[-2].RAssertion), (yyvsp[0].RAssertion)); }
#line 5033 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 408: /* ra: ra13  */
#line 1406 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = (yyvsp[0].RAssertion); }
#line 5039 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 409: /* ra: tail  */
#line 1408 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.RAssertion) = (yyvsp[0].RAssertion); }
#line 5045 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 410: /* initializer: expr  */
#line 1416 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.initializer) = PPSingleExpr((yyvsp[0].expr)); }
#line 5051 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 411: /* initializer: PT_LBRACE initializer_list PT_RBRACE  */
#line 1418 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.initializer) = PPInitList((yyvsp[-1].initializer_list)); }
#line 5057 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 412: /* initializer_list: initializer  */
#line 1423 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.initializer_list) = PPNext((yyvsp[0].initializer), NULL); }
#line 5063 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 413: /* initializer_list: designator PT_EQ initializer  */
#line 1425 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.initializer_list) = PPDesig((yyvsp[-2].designator), (yyvsp[0].initializer), NULL); }
#line 5069 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 414: /* initializer_list: initializer PT_COMMA initializer_list  */
#line 1427 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.initializer_list) = PPNext((yyvsp[-2].initializer), (yyvsp[0].initializer_list)); }
#line 5075 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 415: /* initializer_list: designator PT_EQ initializer PT_COMMA initializer_list  */
#line 1429 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.initializer_list) = PPDesig((yyvsp[-4].designator), (yyvsp[-2].initializer), (yyvsp[0].initializer_list)); }
#line 5081 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 416: /* designator: PT_LBRACK expr PT_RBRACK  */
#line 1434 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.designator) = PPAtIndex((yyvsp[-1].expr), NULL); }
#line 5087 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 417: /* designator: PT_DOT ident  */
#line 1436 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.designator) = PPAtMember((yyvsp[0].string), NULL); }
#line 5093 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 418: /* designator: PT_LBRACK expr PT_RBRACK designator  */
#line 1438 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.designator) = PPAtIndex((yyvsp[-2].expr), (yyvsp[0].designator)); }
#line 5099 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 419: /* designator: PT_DOT ident designator  */
#line 1440 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.designator) = PPAtMember((yyvsp[-1].string), (yyvsp[0].designator)); }
#line 5105 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 420: /* $@7: %empty  */
#line 1447 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
         { K(PPMoreDecl(0, (yyvsp[0].derivtype), NULL), env); }
#line 5111 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 421: /* decls: decl $@7 PT_COMMA decls  */
#line 1448 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { }
#line 5117 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 422: /* $@8: %empty  */
#line 1449 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
                           { K(PPMoreDecl(0, (yyvsp[-2].derivtype), (yyvsp[0].initializer)), env); }
#line 5123 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 423: /* decls: decl PT_EQ initializer $@8 PT_COMMA decls  */
#line 1450 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { }
#line 5129 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 424: /* $@9: %empty  */
#line 1451 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
         { K(PPMoreDecl(1, (yyvsp[0].derivtype), NULL), env); }
#line 5135 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 425: /* decls: decl $@9 PT_SEMI  */
#line 1452 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { }
#line 5141 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 426: /* $@10: %empty  */
#line 1453 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
                           { K(PPMoreDecl(1, (yyvsp[-2].derivtype), (yyvsp[0].initializer)), env); }
#line 5147 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 427: /* decls: decl PT_EQ initializer $@10 PT_SEMI  */
#line 1454 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { }
#line 5153 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 428: /* simple_cmd: expr  */
#line 1459 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.simple_cmd) = PPComputation((yyvsp[0].expr)); }
#line 5159 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 429: /* simple_cmd: PT_PLUSPLUS expr  */
#line 1461 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.simple_cmd) = PPIncDec(T_INC_F, (yyvsp[0].expr)); }
#line 5165 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 430: /* simple_cmd: expr PT_PLUSPLUS  */
#line 1463 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.simple_cmd) = PPIncDec(T_INC_B, (yyvsp[-1].expr)); }
#line 5171 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 431: /* simple_cmd: PT_MINUSMINUS expr  */
#line 1465 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.simple_cmd) = PPIncDec(T_DEC_F, (yyvsp[0].expr)); }
#line 5177 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 432: /* simple_cmd: expr PT_MINUSMINUS  */
#line 1467 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.simple_cmd) = PPIncDec(T_DEC_B, (yyvsp[-1].expr)); }
#line 5183 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 433: /* simple_cmd: expr PT_EQ expr  */
#line 1469 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.simple_cmd) = PPAsgn(T_ASSIGN, (yyvsp[-2].expr), (yyvsp[0].expr)); }
#line 5189 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 434: /* simple_cmd: expr PT_PLUSEQ expr  */
#line 1471 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.simple_cmd) = PPAsgn(T_ADD_ASSIGN, (yyvsp[-2].expr), (yyvsp[0].expr)); }
#line 5195 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 435: /* simple_cmd: expr PT_MINUSEQ expr  */
#line 1473 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.simple_cmd) = PPAsgn(T_SUB_ASSIGN, (yyvsp[-2].expr), (yyvsp[0].expr)); }
#line 5201 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 436: /* simple_cmd: expr PT_STAREQ expr  */
#line 1475 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.simple_cmd) = PPAsgn(T_MUL_ASSIGN, (yyvsp[-2].expr), (yyvsp[0].expr)); }
#line 5207 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 437: /* simple_cmd: expr PT_SLASHEQ expr  */
#line 1477 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.simple_cmd) = PPAsgn(T_DIV_ASSIGN, (yyvsp[-2].expr), (yyvsp[0].expr)); }
#line 5213 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 438: /* simple_cmd: expr PT_PERCENTEQ expr  */
#line 1479 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.simple_cmd) = PPAsgn(T_MOD_ASSIGN, (yyvsp[-2].expr), (yyvsp[0].expr)); }
#line 5219 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 439: /* simple_cmd: expr PT_ANDEQ expr  */
#line 1481 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.simple_cmd) = PPAsgn(T_BAND_ASSIGN, (yyvsp[-2].expr), (yyvsp[0].expr)); }
#line 5225 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 440: /* simple_cmd: expr PT_BAREQ expr  */
#line 1483 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.simple_cmd) = PPAsgn(T_BOR_ASSIGN, (yyvsp[-2].expr), (yyvsp[0].expr)); }
#line 5231 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 441: /* simple_cmd: expr PT_CARETEQ expr  */
#line 1485 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.simple_cmd) = PPAsgn(T_XOR_ASSIGN, (yyvsp[-2].expr), (yyvsp[0].expr)); }
#line 5237 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 442: /* simple_cmd: expr PT_LESSLESSEQ expr  */
#line 1487 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.simple_cmd) = PPAsgn(T_SHL_ASSIGN, (yyvsp[-2].expr), (yyvsp[0].expr)); }
#line 5243 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 443: /* simple_cmd: expr PT_GREATERGREATEREQ expr  */
#line 1489 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.simple_cmd) = PPAsgn(T_SHR_ASSIGN, (yyvsp[-2].expr), (yyvsp[0].expr)); }
#line 5249 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 444: /* for_init: PT_SEMI  */
#line 1494 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.simple_cmd) = NULL; }
#line 5255 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 445: /* for_init: simple_cmd PT_SEMI  */
#line 1496 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.simple_cmd) = (yyvsp[-1].simple_cmd); }
#line 5261 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 446: /* for_cond: PT_SEMI  */
#line 1501 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.expr) = NULL; }
#line 5267 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 447: /* for_cond: expr PT_SEMI  */
#line 1503 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.expr) = (yyvsp[-1].expr); }
#line 5273 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 448: /* for_step: PT_RPAREN  */
#line 1508 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.simple_cmd) = NULL; }
#line 5279 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 449: /* for_step: simple_cmd PT_RPAREN  */
#line 1510 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.simple_cmd) = (yyvsp[-1].simple_cmd); }
#line 5285 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 450: /* sepdef: PT_LET ident PT_LPAREN brace_comma_atype_list PT_SEMI comma_lvar_list PT_RPAREN PT_EQ ra  */
#line 1519 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.partial_program) = PPSepdef((yyvsp[-7].string), (yyvsp[-5].atype_list), (yyvsp[-3].lvar_list), (yyvsp[0].RAssertion));}
#line 5291 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 451: /* sepdef: PT_LET ident PT_LPAREN comma_lvar_list PT_RPAREN PT_EQ ra  */
#line 1521 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.partial_program) = PPSepdef((yyvsp[-5].string), NULL, (yyvsp[-3].lvar_list), (yyvsp[0].RAssertion)); }
#line 5297 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 452: /* sepdef: PT_LET ident PT_LPAREN brace_comma_atype_list PT_RPAREN PT_EQ ra  */
#line 1523 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.partial_program) = PPSepdef((yyvsp[-5].string), (yyvsp[-3].atype_list), NULL, (yyvsp[0].RAssertion)); }
#line 5303 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 453: /* sepdef: PT_LET ident PT_LPAREN PT_RPAREN PT_EQ ra  */
#line 1525 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.partial_program) = PPSepdef((yyvsp[-4].string), NULL, NULL, (yyvsp[0].RAssertion)); }
#line 5309 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 454: /* field_dec: field_specifier decl  */
#line 1530 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.field_dec) = TAnnot(PreType((yyvsp[-1].trivtype), (yyvsp[0].derivtype))); }
#line 5315 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 455: /* field_decs: field_dec PT_SEMI  */
#line 1535 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.field_dec_list) = ALCons((yyvsp[-1].field_dec), NULL); }
#line 5321 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 456: /* field_decs: field_dec PT_SEMI field_decs  */
#line 1537 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.field_dec_list) = ALCons((yyvsp[-2].field_dec), (yyvsp[0].field_dec_list)); }
#line 5327 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 457: /* enums: ident  */
#line 1542 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.enum_list) = pp_enum_list_cons((yyvsp[0].string), 0, 0, 0, NULL); }
#line 5333 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 458: /* enums: ident PT_COMMA enums  */
#line 1544 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.enum_list) = pp_enum_list_cons((yyvsp[-2].string), 0, 0, 0, (yyvsp[0].enum_list)); }
#line 5339 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 459: /* enums: ident PT_EQ PT_NATLIT  */
#line 1546 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.enum_list) = pp_enum_list_cons((yyvsp[-2].string), 1, 0, (yyvsp[0].nat).n, NULL); }
#line 5345 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 460: /* enums: ident PT_EQ PT_NATLIT PT_COMMA enums  */
#line 1548 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.enum_list) = pp_enum_list_cons((yyvsp[-4].string), 1, 0, (yyvsp[-2].nat).n, (yyvsp[0].enum_list)); }
#line 5351 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 461: /* enums: ident PT_EQ PT_MINUS PT_NATLIT  */
#line 1550 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.enum_list) = pp_enum_list_cons((yyvsp[-3].string), 1, 1, (yyvsp[0].nat).n, NULL); }
#line 5357 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 462: /* enums: ident PT_EQ PT_MINUS PT_NATLIT PT_COMMA enums  */
#line 1552 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.enum_list) = pp_enum_list_cons((yyvsp[-5].string), 1, 1, (yyvsp[-2].nat).n, (yyvsp[0].enum_list)); }
#line 5363 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 463: /* para: parameter_specifier decl  */
#line 1557 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.para) = TAnnot(PreType((yyvsp[-1].trivtype), (yyvsp[0].derivtype))); }
#line 5369 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 464: /* para: parameter_specifier abstr_decl_except_function  */
#line 1559 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.para) = TAnnot(PreType((yyvsp[-1].trivtype), (yyvsp[0].derivtype))); }
#line 5375 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 465: /* para: parameter_specifier  */
#line 1561 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.para) = TAnnot(PreType((yyvsp[0].trivtype), DERIVEnd(NULL))); }
#line 5381 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 466: /* paras: para  */
#line 1566 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.para_list) = ALCons((yyvsp[0].para), ALNil()); }
#line 5387 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 467: /* paras: para PT_COMMA paras  */
#line 1568 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.para_list) = ALCons((yyvsp[-2].para), (yyvsp[0].para_list)); }
#line 5393 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 468: /* fun_contra_body: PT_REQUIRE ra PT_ENSURE ra  */
#line 1573 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.spec) = PPSpec(NULL, NULL, NULL, NULL, (yyvsp[-2].RAssertion), (yyvsp[0].RAssertion)); }
#line 5399 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 469: /* fun_contra_body: PT_WITH brace_atype_list paren_lvar_list PT_REQUIRE ra PT_ENSURE ra  */
#line 1577 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.spec) = PPSpec(NULL, NULL, (yyvsp[-5].atype_list), (yyvsp[-4].lvar_list), (yyvsp[-2].RAssertion), (yyvsp[0].RAssertion)); }
#line 5405 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 470: /* fun_contra_body: PT_WITH brace_atype_list PT_REQUIRE ra PT_ENSURE ra  */
#line 1580 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.spec) = PPSpec(NULL, NULL, (yyvsp[-4].atype_list), NULL, (yyvsp[-2].RAssertion), (yyvsp[0].RAssertion)); }
#line 5411 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 471: /* fun_contra_body: PT_WITH paren_lvar_list PT_REQUIRE ra PT_ENSURE ra  */
#line 1583 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.spec) = PPSpec(NULL, NULL, NULL, (yyvsp[-4].lvar_list), (yyvsp[-2].RAssertion), (yyvsp[0].RAssertion)); }
#line 5417 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 472: /* fun_contra: fun_contra_body  */
#line 1588 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.spec) = (yyvsp[0].spec); }
#line 5423 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 473: /* fun_contra: ident  */
#line 1590 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyval.spec) = PPSpec((yyvsp[0].string), NULL, NULL, NULL, NULL, NULL); }
#line 5429 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 474: /* fun_contra: ident fun_contra_body  */
#line 1592 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyvsp[0].spec)->name = (yyvsp[-1].string); (yyval.spec) = (yyvsp[0].spec); }
#line 5435 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;

  case 475: /* fun_contra: ident PT_LESSEQ ident fun_contra_body  */
#line 1594 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"
      { (yyvsp[0].spec)->name = (yyvsp[-3].string); (yyvsp[0].spec)->derived_by = (yyvsp[-1].string); (yyval.spec) = (yyvsp[0].spec); }
#line 5441 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"
    break;


#line 5445 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.c"

      default: break;
    }
  /* User semantic actions sometimes alter yychar, and that requires
     that yytoken be updated with the new translation.  We take the
     approach of translating immediately before every use of yytoken.
     One alternative is translating here after every semantic action,
     but that translation would be missed if the semantic action invokes
     YYABORT, YYACCEPT, or YYERROR immediately after altering yychar or
     if it invokes YYBACKUP.  In the case of YYABORT or YYACCEPT, an
     incorrect destructor might then be invoked immediately.  In the
     case of YYERROR or YYBACKUP, subsequent parser actions might lead
     to an incorrect destructor call or verbose syntax error message
     before the lookahead is translated.  */
  YY_SYMBOL_PRINT ("-> $$ =", YY_CAST (yysymbol_kind_t, yyr1[yyn]), &yyval, &yyloc);

  YYPOPSTACK (yylen);
  yylen = 0;

  *++yyvsp = yyval;

  /* Now 'shift' the result of the reduction.  Determine what state
     that goes to, based on the state we popped back to and the rule
     number reduced by.  */
  {
    const int yylhs = yyr1[yyn] - YYNTOKENS;
    const int yyi = yypgoto[yylhs] + *yyssp;
    yystate = (0 <= yyi && yyi <= YYLAST && yycheck[yyi] == *yyssp
               ? yytable[yyi]
               : yydefgoto[yylhs]);
  }

  goto yynewstate;


/*--------------------------------------.
| yyerrlab -- here on detecting error.  |
`--------------------------------------*/
yyerrlab:
  /* Make sure we have latest lookahead translation.  See comments at
     user semantic actions for why this is necessary.  */
  yytoken = yychar == YYEMPTY ? YYSYMBOL_YYEMPTY : YYTRANSLATE (yychar);
  /* If not already recovering from an error, report this error.  */
  if (!yyerrstatus)
    {
      ++yynerrs;
      {
        yypcontext_t yyctx
          = {yyps, yytoken};
        char const *yymsgp = YY_("syntax error");
        int yysyntax_error_status;
        yysyntax_error_status = yysyntax_error (&yymsg_alloc, &yymsg, &yyctx);
        if (yysyntax_error_status == 0)
          yymsgp = yymsg;
        else if (yysyntax_error_status == -1)
          {
            if (yymsg != yymsgbuf)
              YYSTACK_FREE (yymsg);
            yymsg = YY_CAST (char *,
                             YYSTACK_ALLOC (YY_CAST (YYSIZE_T, yymsg_alloc)));
            if (yymsg)
              {
                yysyntax_error_status
                  = yysyntax_error (&yymsg_alloc, &yymsg, &yyctx);
                yymsgp = yymsg;
              }
            else
              {
                yymsg = yymsgbuf;
                yymsg_alloc = sizeof yymsgbuf;
                yysyntax_error_status = YYENOMEM;
              }
          }
        yyerror (path, k, env, yymsgp);
        if (yysyntax_error_status == YYENOMEM)
          YYNOMEM;
      }
    }

  if (yyerrstatus == 3)
    {
      /* If just tried and failed to reuse lookahead token after an
         error, discard it.  */

      if (yychar <= YYEOF)
        {
          /* Return failure if at end of input.  */
          if (yychar == YYEOF)
            YYABORT;
        }
      else
        {
          yydestruct ("Error: discarding",
                      yytoken, &yylval, path, k, env);
          yychar = YYEMPTY;
        }
    }

  /* Else will try to reuse lookahead token after shifting the error
     token.  */
  goto yyerrlab1;


/*---------------------------------------------------.
| yyerrorlab -- error raised explicitly by YYERROR.  |
`---------------------------------------------------*/
yyerrorlab:
  /* Pacify compilers when the user code never invokes YYERROR and the
     label yyerrorlab therefore never appears in user code.  */
  if (0)
    YYERROR;
  ++yynerrs;

  /* Do not reclaim the symbols of the rule whose action triggered
     this YYERROR.  */
  YYPOPSTACK (yylen);
  yylen = 0;
  YY_STACK_PRINT (yyss, yyssp);
  yystate = *yyssp;
  goto yyerrlab1;


/*-------------------------------------------------------------.
| yyerrlab1 -- common code for both syntax error and YYERROR.  |
`-------------------------------------------------------------*/
yyerrlab1:
  yyerrstatus = 3;      /* Each real token shifted decrements this.  */

  /* Pop stack until we find a state that shifts the error token.  */
  for (;;)
    {
      yyn = yypact[yystate];
      if (!yypact_value_is_default (yyn))
        {
          yyn += YYSYMBOL_YYerror;
          if (0 <= yyn && yyn <= YYLAST && yycheck[yyn] == YYSYMBOL_YYerror)
            {
              yyn = yytable[yyn];
              if (0 < yyn)
                break;
            }
        }

      /* Pop the current state because it cannot handle the error token.  */
      if (yyssp == yyss)
        YYABORT;


      yydestruct ("Error: popping",
                  YY_ACCESSING_SYMBOL (yystate), yyvsp, path, k, env);
      YYPOPSTACK (1);
      yystate = *yyssp;
      YY_STACK_PRINT (yyss, yyssp);
    }

  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  *++yyvsp = yylval;
  YY_IGNORE_MAYBE_UNINITIALIZED_END


  /* Shift the error token.  */
  YY_SYMBOL_PRINT ("Shifting", YY_ACCESSING_SYMBOL (yyn), yyvsp, yylsp);

  yystate = yyn;
  goto yynewstate;


/*-------------------------------------.
| yyacceptlab -- YYACCEPT comes here.  |
`-------------------------------------*/
yyacceptlab:
  yyresult = 0;
  goto yyreturnlab;


/*-----------------------------------.
| yyabortlab -- YYABORT comes here.  |
`-----------------------------------*/
yyabortlab:
  yyresult = 1;
  goto yyreturnlab;


/*-----------------------------------------------------------.
| yyexhaustedlab -- YYNOMEM (memory exhaustion) comes here.  |
`-----------------------------------------------------------*/
yyexhaustedlab:
  yyerror (path, k, env, YY_("memory exhausted"));
  yyresult = 2;
  goto yyreturnlab;


/*----------------------------------------------------------.
| yyreturnlab -- parsing is finished, clean up and return.  |
`----------------------------------------------------------*/
yyreturnlab:
  if (yychar != YYEMPTY)
    {
      /* Make sure we have latest lookahead translation.  See comments at
         user semantic actions for why this is necessary.  */
      yytoken = YYTRANSLATE (yychar);
      yydestruct ("Cleanup: discarding lookahead",
                  yytoken, &yylval, path, k, env);
    }
  /* Do not reclaim the symbols of the rule whose action triggered
     this YYABORT or YYACCEPT.  */
  YYPOPSTACK (yylen);
  YY_STACK_PRINT (yyss, yyssp);
  while (yyssp != yyss)
    {
      yydestruct ("Cleanup: popping",
                  YY_ACCESSING_SYMBOL (+*yyssp), yyvsp, path, k, env);
      YYPOPSTACK (1);
    }
  yyps->yynew = 2;
  goto yypushreturn;


/*-------------------------.
| yypushreturn -- return.  |
`-------------------------*/
yypushreturn:
  if (yymsg != yymsgbuf)
    YYSTACK_FREE (yymsg);
  return yyresult;
}
#undef yynerrs
#undef yystate
#undef yyerrstatus
#undef yyssa
#undef yyss
#undef yyssp
#undef yyvsa
#undef yyvs
#undef yyvsp
#undef yystacksize
#line 1598 "/mnt/d/sjtu/cs2612-2024fall/cs2612-2024fall/QCP/SymbolicExe/test/../compiler/parser.y"


void yyerror(char *path, void *k, struct environment *env, char* s) {
  failwith("bison: %s", s);
  exit(0);
}
