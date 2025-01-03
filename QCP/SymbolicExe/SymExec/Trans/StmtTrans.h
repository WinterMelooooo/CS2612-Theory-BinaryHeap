// Trans from AST to partial statament
#ifndef STMTTRANS_INCLUDED
#define STMTTRNAS_INCLUDED
#include "../../compiler/lang.h"
#include "../../compiler/plang.h"
#include "../CDef/PartialStmt.h"
#include "../CDef/Cexpr.h"
#include "PS_ExprTrans.h"
#include "../AsrtDef/AssDef.h"
#include "../Utility/InnerAsrtCollector.h"

struct PartialStmtList * StmtTrans(struct cmd *cmd, struct environment * env, int block_killer);
struct Cexpr *PS_PPExprTrans(struct pp_expr * e, struct environment *env);
struct CSimpleCommand * PPSimpleCommandTrans(struct pp_simple *c, struct environment * env);
struct PartialStmt * SingleStmtTrans(struct partial_program *c, struct environment * env);

#endif
