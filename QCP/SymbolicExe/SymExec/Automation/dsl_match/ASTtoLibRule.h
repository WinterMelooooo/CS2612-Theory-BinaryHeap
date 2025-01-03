#ifndef __ASTTOLIBRULE_H__
#define __ASTTOLIBRULE_H__

#define PRINT_INFORMATION 0
#define NOT_WITHIN_REQUIRED_SCOPE 1

#include "../../../dsl_parser/lang.h"
#include "../../../dsl_parser/lexer.h"
#include "../../../dsl_parser/parser.h"
#include "../StrategyLibDef/StrategyLib.h"
#include "../TypeInference/TypeInference.h"
#include "../Mapping/Mapping.h"
#include "../../Paras.h"

struct StrategyLibRuleNode{
    char *scope;
    struct StrategyLibRule *strategy;
    struct StrategyLibRuleNode *next;
};

void appendStrategyLibRuleNode(struct StrategyLibRuleNode **head,char *scope,struct StrategyLibRule *strategy);
void freeStrategyLibRuleNode(struct StrategyLibRuleNode *head);

struct StrategyLibNode{
    char *scope;
    struct StrategyLib *lib;
    struct StrategyLibNode *next;
};

void appendStrategyLibNode(struct StrategyLibNode **head,char *scope,struct StrategyLib *lib);
struct StrategyLib* findLibByScope(char *scope,bool search);
void freeStrategyLibNode(struct StrategyLibNode *head);
void freeStrategyLibs();

struct StrategyLibRule * AST_to_LibRule(struct lang_cmd * root,char * file,int prio,struct environment * env);

struct StrategyLibPatternLList * cmd_pattern_to_LList(struct lang_pattern_list * exprs,struct environment * env);
struct StrategyLibPatternList * cmd_pattern_to_List(struct lang_expr * expr,struct environment * env);
struct StrategyLibActionList * cmd_action_to_AList(struct lang_action_list * actions,struct environment * env);
struct StrategyLibCheckList * cmd_check_to_CList(struct lang_action_list * checks,struct environment * env);

struct StrategyLibAction  *actToLibAction(struct lang_action *act,struct environment * env);
struct StrategyLibCheck *checkToLibCheck(struct lang_action *act,struct environment * env);

struct PatternExprList * expr_to_PExprList(struct lang_expr_list *args,struct environment * env);
struct PatternExpr * Get_Expr_expr(struct lang_expr * expr,struct environment * env);

struct StrategyLibPattern *getLibPattern(struct lang_expr*expr, struct environment * env);
struct StrategyLibPattern * Get_Expr_BinOP(struct lang_expr * expr,struct environment * env);
struct PatternProp *getPatternProp(struct lang_expr *expr,struct environment * env);
struct PatternSep *getPatternSeq(struct lang_expr *expr, struct environment * env);
struct PatternPolyTypeList *getPolyTypeList(struct PatternPolyTypeList *types,struct environment * env);
struct PatternPolyType *getPolyType(struct lang_expr *expr,struct environment * env);

void addCustomStrategyLib(char *file,struct environment * env);
void addIncludePath(char *file);

struct StringList *getIncludePath();
void freeIncludePath();
void initIncludePaths();

void checkDSLFiles(char* file);


#endif