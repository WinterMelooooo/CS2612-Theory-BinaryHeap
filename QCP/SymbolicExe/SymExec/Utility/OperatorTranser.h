#ifndef OPERATOR_TRANSER_INCLUDED
#define OPERATOR_TRANSER_INCLUDED

#include "../AsrtDef/AssDef.h"
#include "../AsrtDef/ExistDef.h"
#include "../AsrtDef/LocalDef.h"
#include "../AsrtDef/PropDef.h"
#include "../AsrtDef/SepDef.h"
#include "../AsrtDef/ExprValDef.h"
#include "../../compiler/lang.h"

enum InnerBinaryOperation AriBinOpTrans(enum BinOpType op);
enum BinOpType InnerBinOpToUserBinOp(enum InnerBinaryOperation op);
int IsCmpBinOp(enum BinOpType op);
enum PropCompOp BinCompareOpToPropComp(enum BinOpType op);
enum InnerUnaryOperation UserUnaryToInnerUnary(enum UnOpType op);
enum UnOpType InnerUnaryToUserUnary(enum InnerUnaryOperation op);
enum PropCompOp PropCompareOpReverse(enum PropCompOp op);
enum InnerBinaryOperation AriAsignOpTrans(enum AssignType op);
enum BinOpType InnerToUserPropCompOpTrans(enum PropCompOp op);

#endif // OPERATOR_TRANSER_INCLUDED