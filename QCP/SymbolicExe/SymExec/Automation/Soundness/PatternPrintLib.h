#ifndef __PATTERN_PRINT_LIB_H__
#define __PATTERN_PRINT_LIB_H__

#include "../PatternASTDef/PatternASTDef.h"
#include "../Util/Error.h"
#include "../TypeInference/TypeInference.h"
#include "../Mapping/Mapping.h"
#include <stdlib.h>

#define TAB "  "

/*
 * Print num_tabs * TAB to a file.
 */
void print_tabs(int num_tabs, FILE * fp);

/*
 * Print a pattern expression to a file.
 *
 * Print exactly "%s" or "(%s)" with no extra spaces or brackets.
 * e.g. (EConst 3) -> "3"
 *      (EVar x) -> "x"
 *      (EField x "list" "head") -> "(field_address x \"list\" \"head\")"
 */
void printPatternExpr(struct PatternExpr * expr, FILE * fp, struct charMapping * type_mapping, struct environment * env);

/*
 * Print a list of pattern expressions to a file.
 *
 * Print exactly " %s %s %s ..." with exact one extra space before the first expression
 * e.g. ((EConst 3), (EVar x), (EField x "list" "head")) ->
 *      " 3 x (field_address x \"list\" \"head\")"
 */
void printPatternExprList(struct PatternExprList * expr, FILE * fp, struct charMapping * type_mapping, struct environment * env);

void printPatternPolyType(struct PatternPolyType * type, FILE * fp);

void printPatternPolyTypeList(struct PatternPolyTypeList * tl, FILE * fp);

void printPatternCType(struct PatternCType * type, FILE * fp);

/*
 * Print a pattern proposition to a file.
 *
 * Print exactly "%s" or "(%s)" with no extra spaces or brackets.
 * e.g. (TPropTrue) -> "True"
 *      (TPropAnd x y) -> "(x /\\ y)"
 */
void printPatternProp(struct PatternProp * prop, FILE * fp, struct charMapping * type_mapping, struct environment * env);

/*
 * Print a list of pattern propositions sequenced through SEQ to a file.
 * ty = 0 -> SEQ = "&&"
 * ty = 1 -> SEQ = "||"
 *
 */
void printPatternPropList(struct PatternPropList * pl, FILE * fp, int ty, struct charMapping * type_mapping, struct environment * env);

/*
 * Print a list of pattern propositions to a file.
 *
 * Print exactly the following:
TAB * num_tabs [| propn |] &&
TAB * num_tabs [| propn-1 |] &&
...
TAB * num_tabs [| prop1 |]
 */
void printPatternPropLList(struct PatternPropLList * pl, FILE * fp, int num_tabs, struct charMapping * type_mapping, struct environment * env);

/*
 * Print a pattern separation to a file.
 */
void printPatternSep(struct PatternSep * sep, FILE * fp, struct charMapping * type_mapping, struct environment * env);

/*
 * Print a list of pattern separations sequenced through SEQ to a file.
 * ty = 0 -> SEQ = "&&"
 * ty = 1 -> SEQ = "||"
 *
 */
void printPatternSepList(struct PatternSepList * sl, FILE * fp, int ty, struct charMapping * type_mapping, struct environment * env);

/*
 * Print a list of pattern separations to a file.
 *
 * Print exactly the following:
TAB * num_tabs sepn **
TAB * num_tabs sepn-1 **
...
TAB * num_tabs sep1
 */
void printPatternSepLList(struct PatternSepLList * sl, FILE * fp, int num_tabs, struct charMapping * type_mapping, struct environment * env);

#endif